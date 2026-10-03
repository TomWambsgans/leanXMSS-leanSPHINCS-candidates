//! End-to-end tests: correctness against the clear evaluation and BLAKE2s, traffic, and corrupt
//! coalitions (faults on every message kind, consistent and split lies, rushing, forgeries), with a
//! two-world test that what they see opened does not depend on the honest parties' secrets.

use std::sync::Arc;

use mpc::blake2s_circuit::{Word, add2, add3, split_prefixes, th_circuit};
use mpc::circuit::{Builder, Program};

use crate::engine::{Cheat, Party, Record, Shares};
use crate::net::{Abort, Fault, Stats, Tamper, network};
use crate::setup::{Keys, SessionId, deal, establish, keygen, share};
use crate::structure::Structure;

fn rng(seed: u64) -> impl FnMut() -> u64 {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    }
}

fn tail(n: usize) -> u64 {
    if n.is_multiple_of(64) { u64::MAX } else { (1 << (n % 64)) - 1 }
}

/// A small circuit with a few AND levels: `(x + y + z) + (x & public)` on 6-bit words.
fn toy() -> Program {
    let mut b = Builder::new();
    let p: Vec<_> = (0..6).map(|_| b.pub_input()).collect();
    let word = |b: &mut Builder| -> Word { std::array::from_fn(|i| if i < 6 { b.sec_input() } else { 0 }) };
    let (x, y, z) = (word(&mut b), word(&mut b), word(&mut b));
    let s = add3(&mut b, &x, &y, &z);
    let m: Word = std::array::from_fn(|i| if i < 6 { b.and(x[i], p[i]) } else { 0 });
    let out = add2(&mut b, &s, &m);
    for &bit in out.iter().take(6) {
        b.output(bit);
    }
    b.compile()
}

/// The `Th` circuit on `n` instances with public prefixes, and its public inputs.
fn th(n: usize) -> (Program, Vec<Vec<u64>>, Vec<[u8; 32]>) {
    let prefixes: Vec<[u8; 32]> = (0..n as u32)
        .map(|k| {
            let mut p = [3u8; 32];
            p[12..16].copy_from_slice(&(k * 7).to_le_bytes());
            p
        })
        .collect();
    let (layout, pub_in) = split_prefixes(&prefixes);
    (th_circuit(&layout).compile(), pub_in, prefixes)
}

fn random_inputs(prog: &Program, n: usize, seed: u64) -> (Vec<Vec<u64>>, Vec<Vec<u64>>) {
    let mut r = rng(seed);
    let words = n.div_ceil(64);
    let mut v = || {
        let mut x: Vec<u64> = (0..words).map(|_| r()).collect();
        *x.last_mut().unwrap() &= tail(n);
        x
    };
    ((0..prog.n_pub_inputs).map(|_| v()).collect(), (0..prog.n_sec_inputs).map(|_| v()).collect())
}

/// The clear evaluation, beyond-`n` bits cleared (the MPC keeps them zero).
fn clear(prog: &Program, n: usize, pub_in: &[Vec<u64>], sec_in: &[Vec<u64>]) -> Vec<Vec<u64>> {
    let mut out = prog.eval_plain(n.div_ceil(64), pub_in, sec_in);
    for v in &mut out {
        *v.last_mut().unwrap() &= tail(n);
    }
    out
}

/// A deterministic replicated sharing of `value`: all terms but the last from `seed`, by global term.
fn share_det(s: &Structure, value: &[u64], seed: u64) -> Vec<Vec<u64>> {
    let mut r = rng(seed);
    let mut terms: Vec<Vec<u64>> = (1..s.terms.len()).map(|_| value.iter().map(|_| r()).collect()).collect();
    let last = (0..value.len()).map(|w| terms.iter().fold(value[w], |a, t| a ^ t[w])).collect();
    terms.push(last);
    terms
}

fn party_shares(s: &Structure, terms: &[Vec<u64>], i: usize) -> Shares {
    Shares::input(s.held[i].iter().map(|&t| terms[t].clone()).collect())
}

/// A corrupt party: network faults (and rushing), a protocol cheat, and whether it ignores checks.
#[derive(Clone, Default)]
struct Bad {
    party: usize,
    tamper: Tamper,
    cheat: Cheat,
    complicit: bool,
}

/// A party's opened outputs, and its traffic after evaluation, verification and opening.
type Opened = (Vec<Vec<u64>>, [Stats; 3]);

struct Out<T> {
    result: Result<T, Abort>,
    stats: Stats,
    /// The (round, recipient) of the messages this party's faults flipped.
    hits: Vec<(u64, usize)>,
    record: Record,
}

/// Runs `f` for every party of a session (each on its own thread): established fresh, or `fixed`.
fn session<T: Send>(s: &Arc<Structure>, keys: &[Keys], fixed: Option<[u8; 16]>, n: usize, bad: &[Bad], f: impl Fn(&mut Party) -> Result<T, Abort> + Sync) -> Vec<Out<T>> {
    let f = &f;
    // The coalition: every party listed in `bad`.
    let coalition = bad.iter().fold(0u32, |m, b| m | 1 << b.party);
    std::thread::scope(|scope| {
        let handles: Vec<_> = network(s.n)
            .into_iter()
            .map(|mut net| {
                let b = bad.iter().find(|b| b.party == net.id).cloned();
                scope.spawn(move || {
                    let i = net.id;
                    if let Some(b) = &b {
                        net.tamper = b.tamper.clone();
                    }
                    let id = match fixed {
                        Some(x) => SessionId::fixed(x),
                        None => match establish(&mut net) {
                            Ok(id) => id,
                            Err(e) => return Out { result: Err(e), stats: net.stats, hits: net.tamper.hits, record: Record::default() },
                        },
                    };
                    let mut p = Party::new(net, s.clone(), keys[i].clone(), id, n);
                    p.threads = 1;
                    if let Some(b) = b {
                        p.cheat = b.cheat;
                        p.complicit = b.complicit.then_some(coalition);
                    }
                    let result = f(&mut p);
                    Out { result, stats: p.net.stats, hits: p.net.tamper.hits.clone(), record: p.record.clone() }
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("party thread panicked")).collect()
    })
}

/// A test case: a structure and keys, a program and its inputs (shared by global term), the answer.
struct Case {
    s: Arc<Structure>,
    keys: Vec<Keys>,
    prog: Program,
    n: usize,
    pub_in: Vec<Vec<u64>>,
    terms: Vec<Vec<Vec<u64>>>,
    want: Vec<Vec<u64>>,
}

impl Case {
    fn new(parties: usize, prog: Program, n: usize, seed: u64) -> Self {
        let s = Arc::new(Structure::new(parties));
        let (pub_in, sec_in) = random_inputs(&prog, n, seed);
        Self::with(s, prog, n, pub_in, &sec_in, seed)
    }

    fn with(s: Arc<Structure>, prog: Program, n: usize, pub_in: Vec<Vec<u64>>, sec_in: &[Vec<u64>], seed: u64) -> Self {
        let want = clear(&prog, n, &pub_in, sec_in);
        let terms = sec_in.iter().enumerate().map(|(k, v)| share_det(&s, v, seed * 1000 + k as u64)).collect();
        Self { keys: deal(&s), s, prog, n, pub_in, terms, want }
    }

    /// Evaluates, verifies, opens. Per party: the outcome, with stats after each phase.
    fn run(&self, fixed: Option<[u8; 16]>, bad: &[Bad], limit: Option<usize>) -> Vec<Out<Opened>> {
        session(&self.s, &self.keys, fixed, self.n, bad, |p| {
            p.materialize_limit = limit;
            let mine: Vec<Shares> = self.terms.iter().map(|t| party_shares(&self.s, t, p.id)).collect();
            let out = p.eval(&self.prog, &self.pub_in, &mine)?;
            let e = p.net.stats;
            p.verify()?;
            let v = p.net.stats;
            let opened = p.open(&out)?;
            Ok((opened, [e, v, p.net.stats]))
        })
    }

    fn honest(&self, bad: &[Bad]) -> Vec<usize> {
        (0..self.s.n).filter(|i| bad.iter().all(|b| b.party != *i)).collect()
    }

    /// No honest party outputs a wrong value; returns whether an honest party aborted.
    fn no_wrong_output(&self, run: &[Out<Opened>], bad: &[Bad], what: &str) -> bool {
        let mut aborted = false;
        for i in self.honest(bad) {
            match &run[i].result {
                Ok((v, _)) => assert_eq!(v, &self.want, "{what}: honest party {i} accepted a wrong output"),
                Err(_) => aborted = true,
            }
        }
        aborted
    }
}

#[test]
fn toy_circuit_matches_clear_evaluation() {
    for parties in [3, 5, 7] {
        for n in [1usize, 5, 64, 100] {
            let case = Case::new(parties, toy(), n, n as u64 + parties as u64);
            for out in case.run(None, &[], None) {
                assert_eq!(out.result.unwrap().0, case.want, "n = {parties}, batch {n}");
            }
        }
    }
}

#[test]
fn th_in_mpc_matches_blake2s() {
    let n = 130;
    let (prog, pub_in, prefixes) = th(n);
    let mut r = rng(5);
    let secrets: Vec<[u8; 16]> = (0..n).map(|_| std::array::from_fn(|_| r() as u8)).collect();
    let words = n.div_ceil(64);
    let sec_in: Vec<Vec<u64>> = (0..128)
        .map(|bit| {
            let mut v = vec![0u64; words];
            for (k, s) in secrets.iter().enumerate() {
                v[k / 64] |= u64::from((s[bit / 8] >> (bit % 8)) & 1) << (k % 64);
            }
            v
        })
        .collect();
    for parties in [3, 5, 7] {
        let s = Arc::new(Structure::new(parties));
        let case = Case::with(s, prog.clone(), n, pub_in.clone(), &sec_in, 6);
        let run = case.run(None, &[], None);
        for out in &run {
            let out = &out.result.as_ref().unwrap().0;
            for k in 0..n {
                let mut input = prefixes[k].to_vec();
                input.extend_from_slice(&secrets[k]);
                let want = blake2s::hash(&input);
                for bit in 0..128 {
                    assert_eq!((out[bit][k / 64] >> (k % 64)) & 1, u64::from((want[bit / 8] >> (bit % 8)) & 1), "n = {parties}");
                }
            }
        }
        // AND traffic: (n - 1) + f bit-vectors per AND in total; two rounds per AND level.
        let f = (parties - 1) / 2;
        let and_bytes: u64 = run.iter().map(|o| o.result.as_ref().unwrap().1[0].bytes_sent).sum::<u64>() - (parties * (parties - 1) * 16) as u64;
        assert_eq!(and_bytes, (prog.n_and * words * 8 * (parties - 1 + f)) as u64, "n = {parties}");
        let [e, v, o] = run[0].result.as_ref().unwrap().1;
        assert_eq!(e.rounds as usize, 1 + 2 * prog.depth);
        let r = prog.n_and.next_power_of_two().trailing_zeros() as usize + n.next_power_of_two().trailing_zeros() as usize;
        assert_eq!((v.rounds - e.rounds) as usize, 2 * r + 5);
        assert_eq!(o.rounds - v.rounds, 5);
        assert!(v.bytes_sent - e.bytes_sent < 16_000, "verification bytes {}", v.bytes_sent - e.bytes_sent);
    }
}

#[test]
fn three_parties_send_one_bit_per_and() {
    // n = 3: every party sends exactly one bit per AND (a contribution, or a forward as the collector).
    let n = 256;
    let (prog, pub_in, _) = th(n);
    let (_, sec_in) = random_inputs(&prog, n, 7);
    let case = Case::with(Arc::new(Structure::new(3)), prog.clone(), n, pub_in, &sec_in, 7);
    for out in case.run(None, &[], None) {
        let [e, _, _] = out.result.unwrap().1;
        assert_eq!(e.bytes_sent - 32, (prog.n_and * n / 8) as u64);
    }
}

#[test]
fn streamed_first_round() {
    // A tiny materialization budget streams the first round from the bit transcript.
    for parties in [3, 5] {
        let case = Case::new(parties, toy(), 100, 8);
        for out in case.run(None, &[], Some(1)) {
            assert_eq!(out.result.unwrap().0, case.want);
        }
        for bad in 0..parties {
            let b = [Bad { party: bad, cheat: Cheat::FlipAnd { and: 7, bit: 77, split: false }, ..Default::default() }];
            let run = case.run(None, &b, Some(1));
            assert!(run.iter().all(|o| o.result.is_err()), "n = {parties}, party {bad}");
        }
    }
}

#[test]
fn flipped_and_messages_always_abort() {
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 100, 9);
        let k = case.prog.n_and;
        for bad in 0..parties {
            for and in [0, k / 2, k - 1] {
                for split in [false, true] {
                    for bit in [0usize, 63, 99] {
                        let b = [Bad { party: bad, cheat: Cheat::FlipAnd { and, bit, split }, complicit: true, ..Default::default() }];
                        let run = case.run(None, &b, None);
                        case.no_wrong_output(&run, &b, "flip");
                        for i in case.honest(&b) {
                            assert!(run[i].result.is_err(), "n = {parties}: honest party {i} accepted (bad {bad}, and {and}, split {split})");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn local_deviations_never_give_a_wrong_output() {
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 100, 10);
        let (mut caught, mut total) = (0, 0);
        for bad in 0..parties {
            for and in 0..case.prog.n_and {
                let b = [Bad { party: bad, cheat: Cheat::LocalTerm { and, bit: 3 + and }, complicit: true, ..Default::default() }];
                let run = case.run(None, &b, None);
                caught += usize::from(case.no_wrong_output(&run, &b, "local term"));
                total += 1;
            }
        }
        assert!(caught > total / 4, "{caught} of {total}");
    }
}

/// Every round of an honest run, by party: (round, messages to each party nonempty).
fn round_count(case: &Case) -> u64 {
    case.run(None, &[], None)[0].stats.rounds
}

#[test]
fn any_flipped_bit_is_caught() {
    // One corrupt party, every round, a flip to one party (split) or to all (consistent), at three
    // positions; the corrupt party ignores failed checks. Every flip that reaches an honest party
    // makes an honest party abort, and none outputs a wrong value.
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 70, 11);
        let rounds = round_count(&case);
        let mut caught = 0;
        for bad in [0, parties / 2, parties - 1] {
            for round in 0..rounds {
                for to in [None, Some((bad + 1) % parties), Some((bad + parties - 1) % parties)] {
                    for bit in [0usize, 1000, 1 << 20] {
                        let tamper = Tamper { faults: vec![Fault { round, to, bit }], ..Default::default() };
                        let b = [Bad { party: bad, tamper, complicit: true, ..Default::default() }];
                        let run = case.run(None, &b, None);
                        let aborted = case.no_wrong_output(&run, &b, "flip");
                        if !run[bad].hits.is_empty() {
                            assert!(aborted, "n = {parties}: party {bad}, round {round}, to {to:?}, bit {bit}: an applied flip went unnoticed");
                            caught += 1;
                        }
                    }
                }
            }
        }
        assert!(caught as u64 > 3 * rounds, "n = {parties}: {caught}");
    }
}

/// The corrupt sets of size `f` (and smaller) tried in the coalition tests.
fn coalitions(parties: usize) -> Vec<Vec<usize>> {
    let f = (parties - 1) / 2;
    let mut out = vec![(0..f).collect::<Vec<_>>(), (parties - f..parties).collect(), (0..f).map(|k| 2 * k + 1).collect()];
    if f > 1 {
        out.push(vec![parties / 2]);
    }
    out
}

#[test]
fn coalitions_with_flips_throughout_are_caught() {
    // Up to f corrupt parties, each flipping bits in several rounds (split or consistent), all of
    // them ignoring failed checks.
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 100, 12);
        let rounds = round_count(&case);
        let mut r = rng(13);
        let mut hit = 0;
        for set in coalitions(parties) {
            let corrupt = set.iter().fold(0u32, |m, &i| m | 1 << i);
            for _ in 0..40 {
                let bad: Vec<Bad> = set
                    .iter()
                    .map(|&party| {
                        let faults = (0..(r() % 3))
                            .map(|_| Fault { round: r() % rounds, to: if r().is_multiple_of(2) { None } else { Some((r() % parties as u64) as usize) }, bit: r() as usize })
                            .collect();
                        Bad { party, tamper: Tamper { faults, corrupt, ..Default::default() }, complicit: true, ..Default::default() }
                    })
                    .collect();
                let run = case.run(None, &bad, None);
                let aborted = case.no_wrong_output(&run, &bad, "coalition");
                // A flip to an honest party is always caught; flips among corrupt parties may not be.
                let to_honest = bad.iter().any(|b| run[b.party].hits.iter().any(|&(_, t)| corrupt >> t & 1 == 0));
                if to_honest {
                    assert!(aborted, "n = {parties}, coalition {set:?}: flips to honest parties went unnoticed");
                    hit += 1;
                }
            }
        }
        assert!(hit > 20, "n = {parties}: {hit}");
    }
}

#[test]
fn split_and_consistent_forwards_by_a_coalition() {
    // The collector lies to one holder, or to all consistently; corrupt holders stay silent.
    for parties in [5, 7] {
        let case = Case::new(parties, toy(), 64, 14);
        let s = &case.s;
        for set in coalitions(parties) {
            let corrupt = set.iter().fold(0u32, |m, &i| m | 1 << i);
            // A gate whose collector is the first corrupt party.
            let Some(and) = (0..case.prog.n_and).find(|&g| s.collector(g as u64).1 == set[0]) else { continue };
            for split in [false, true] {
                let bad: Vec<Bad> = set
                    .iter()
                    .map(|&party| {
                        let cheat = if party == set[0] { Cheat::FlipAnd { and, bit: 5, split } } else { Cheat::Honest };
                        Bad { party, cheat, complicit: true, tamper: Tamper { corrupt, ..Default::default() } }
                    })
                    .collect();
                let run = case.run(None, &bad, None);
                case.no_wrong_output(&run, &bad, "forward");
                // A split lie to a corrupt holder changes nothing the honest parties hold.
                let (t, _) = s.collector(and as u64);
                let first_other = s.holders(t).find(|&h| h != set[0]).unwrap();
                if !split || corrupt >> first_other & 1 == 0 {
                    for i in case.honest(&bad) {
                        assert!(run[i].result.is_err(), "n = {parties}, {set:?}, split {split}: honest {i} accepted");
                    }
                }
            }
        }
    }
}

#[test]
fn rushing_adversaries() {
    // Rushing corrupt parties: one rewrites its messages to honest parties after seeing the round's
    // honest messages (a bit chosen from what it received); all ignore failed checks. (Two rewriting
    // the same bit of their shares of one sum would cancel out: a no-op, not an attack.)
    use std::sync::atomic::{AtomicBool, Ordering};
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 100, 15);
        let rounds = round_count(&case);
        let mut caught = 0;
        for set in coalitions(parties) {
            let corrupt = set.iter().fold(0u32, |m, &i| m | 1 << i);
            for target in (0..rounds).step_by(2) {
                let rewrote = Arc::new(AtomicBool::new(false));
                let flag = rewrote.clone();
                let adapt: crate::net::Adapt = Arc::new(move |round, got: &[Vec<u8>], out: &mut [Vec<u8>]| {
                    if round != target {
                        return;
                    }
                    let h = blake2s::hash(&got.concat());
                    let pick = u64::from_le_bytes(h[..8].try_into().unwrap()) as usize;
                    // Only messages to honest parties are left here.
                    for m in out.iter_mut().filter(|m| !m.is_empty()) {
                        let bit = pick % (8 * m.len());
                        m[bit / 8] ^= 1 << (bit % 8);
                        flag.store(true, Ordering::Relaxed);
                    }
                });
                let bad: Vec<Bad> = set
                    .iter()
                    .map(|&party| {
                        let adapt = (party == set[0]).then(|| adapt.clone());
                        Bad { party, tamper: Tamper { rush: true, corrupt, adapt, ..Default::default() }, complicit: true, ..Default::default() }
                    })
                    .collect();
                let run = case.run(None, &bad, None);
                let aborted = case.no_wrong_output(&run, &bad, "rushing");
                if rewrote.load(Ordering::Relaxed) {
                    assert!(aborted, "n = {parties}, {set:?}, round {target}: a rushing rewrite went unnoticed");
                    caught += 1;
                }
            }
        }
        assert!(caught > 10, "n = {parties}: {caught}");
    }
}

#[test]
fn two_worlds_look_the_same_to_a_coalition() {
    // Two worlds differ only in the honest parties' secrets: the sharings differ only in the term the
    // coalition lacks. Same keys, same session id (both deterministic), same corrupt behaviour. What
    // the coalition sees opened in the checks (coins, discrepancies) and whether each honest party
    // aborts, and why, must be the same.
    for parties in [5, 7] {
        let s = Arc::new(Structure::new(parties));
        let prog = toy();
        let n = 64;
        let (pub_in, sec_a) = random_inputs(&prog, n, 16);
        let (_, sec_b) = random_inputs(&prog, n, 17);
        let keys = deal(&s);
        let rounds = {
            let c = Case { keys: keys.clone(), ..Case::with(s.clone(), prog.clone(), n, pub_in.clone(), &sec_a, 18) };
            c.run(Some([9; 16]), &[], None)[0].stats.rounds
        };
        let mut compared = 0;
        for set in coalitions(parties) {
            let corrupt = set.iter().fold(0u32, |m, &i| m | 1 << i);
            // The term the coalition misses: its own set, filled up with honest parties.
            let mut mask = corrupt;
            for i in 0..parties {
                if mask.count_ones() < s.f as u32 && mask >> i & 1 == 0 {
                    mask |= 1 << i;
                }
            }
            let tc = s.terms.iter().position(|&t| t == mask).unwrap();
            let world = |sec: &[Vec<u64>]| {
                let mut c = Case::with(s.clone(), prog.clone(), n, pub_in.clone(), &sec_a, 18);
                c.keys = keys.clone();
                c.want = clear(&prog, n, &pub_in, sec);
                for (k, t) in c.terms.iter_mut().enumerate() {
                    for w in 0..t[tc].len() {
                        t[tc][w] ^= sec_a[k][w] ^ sec[k][w];
                    }
                }
                c
            };
            let (wa, wb) = (world(&sec_a), world(&sec_b));
            for round in 0..rounds {
                // A split flip goes to the first honest party. A local deviation is on a first-level
                // AND: later ones read terms that differ between the worlds (masked, but not equal).
                let first_honest = (0..parties).find(|&i| corrupt >> i & 1 == 0).unwrap();
                let level1 = prog.steps.iter().find(|st| !st.ands.is_empty()).unwrap().ands.len();
                for (to, cheat) in [(None, Cheat::Honest), (Some(first_honest), Cheat::Honest), (None, Cheat::LocalTerm { and: round as usize % level1, bit: 9 })] {
                    let bad: Vec<Bad> = set
                        .iter()
                        .enumerate()
                        .map(|(k, &party)| {
                            let faults = if k == 0 && cheat == Cheat::Honest { vec![Fault { round, to, bit: 77 + round as usize }] } else { vec![] };
                            let cheat = if k == 0 { cheat } else { Cheat::Honest };
                            Bad { party, tamper: Tamper { faults, corrupt, ..Default::default() }, cheat, complicit: true }
                        })
                        .collect();
                    let (ra, rb) = (wa.run(Some([9; 16]), &bad, None), wb.run(Some([9; 16]), &bad, None));
                    wa.no_wrong_output(&ra, &bad, "world a");
                    wb.no_wrong_output(&rb, &bad, "world b");
                    for &i in &set {
                        assert_eq!(ra[i].record.checks, rb[i].record.checks, "n = {parties}, {set:?}, round {round}: the checks depend on secrets");
                    }
                    for i in wa.honest(&bad) {
                        let why = |r: &Result<_, Abort>| r.as_ref().err().map(|e| e.0.clone());
                        assert_eq!(why(&ra[i].result), why(&rb[i].result), "n = {parties}, {set:?}, round {round}: an abort depends on secrets");
                    }
                    compared += 1;
                }
            }
        }
        assert!(compared > 100);
    }
}

/// Runs a session of the two-level circuit with session id `fixed` (or a fresh one), party 0
/// cheating as `cheat`; returns each party's opened value and the first challenge it saw.
fn forge_run(case: &Case, fixed: Option<[u8; 16]>, cheat: Cheat) -> Vec<Result<(u64, Option<u128>), Abort>> {
    session(&case.s, &case.keys, fixed, case.n, &[Bad { party: 0, cheat, ..Default::default() }], |p| {
        let mine: Vec<Shares> = case.terms.iter().map(|t| party_shares(&case.s, t, p.id)).collect();
        let out = p.eval(&case.prog, &case.pub_in, &mine)?;
        p.verify()?;
        let r1 = p.record.r1;
        Ok((p.open(&out)?[0][0], r1))
    })
    .into_iter()
    .map(|o| o.result)
    .collect()
}

fn two_levels() -> Program {
    let mut b = Builder::new();
    let (u, v) = (b.sec_input(), b.sec_input());
    let o = b.and(u, v);
    let o2 = b.and(o, u);
    b.output(o2);
    b.compile()
}

#[test]
fn a_repeated_session_id_would_let_a_party_forge_but_ids_are_fresh() {
    for parties in [3, 5, 7] {
        // u = 1 everywhere: the flipped first AND changes the output at instance 5.
        let sec_in = vec![vec![u64::from(u32::MAX)], vec![0x1234_5678]];
        let case = Case::with(Arc::new(Structure::new(parties)), two_levels(), 32, vec![], &sec_in, 19);
        let want = forge_run(&case, Some([4; 16]), Cheat::Honest)[1].as_ref().unwrap().0;
        let forge = |r1| Cheat::Forge { and: 0, bit: 5, r1 };
        // With one id used twice, party 0 forges with the challenge of the first run: a wrong output.
        let first = forge_run(&case, Some([3; 16]), Cheat::Honest);
        let r1 = first[0].as_ref().unwrap().1.unwrap();
        let replay = forge_run(&case, Some([3; 16]), forge(r1));
        assert_ne!(replay[1].as_ref().unwrap().0, want, "the forgery goes through with a repeated id");
        // With established ids, the old challenge is useless.
        let first = forge_run(&case, None, Cheat::Honest);
        let r1 = first[0].as_ref().unwrap().1.unwrap();
        let again = forge_run(&case, None, forge(r1));
        assert!(again[1..].iter().all(|r| r.is_err()), "a fresh session rejects the forgery");
    }
}

#[test]
fn a_party_that_aborted_never_opens() {
    let case = Case::new(5, toy(), 70, 20);
    let bad = [Bad { party: 0, cheat: Cheat::FlipAnd { and: 3, bit: 1, split: false }, ..Default::default() }];
    let run = session(&case.s, &case.keys, None, case.n, &bad, |p| {
        let mine: Vec<Shares> = case.terms.iter().map(|t| party_shares(&case.s, t, p.id)).collect();
        let out = p.eval(&case.prog, &case.pub_in, &mine)?;
        let verdict = p.verify();
        Ok((verdict.is_err(), p.open(&out).is_err()))
    });
    for out in &run[1..] {
        assert_eq!(out.result.clone().unwrap(), (true, true));
    }
}

#[test]
fn keygen_then_compute() {
    for parties in [3, 5, 7] {
        let s = Arc::new(Structure::new(parties));
        let keys: Vec<Keys> = std::thread::scope(|scope| {
            let s = &s;
            let hs: Vec<_> = network(parties).into_iter().map(|mut net| scope.spawn(move || keygen(&mut net, s).unwrap())).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        // Holders agree on every seed, pairs on their keys.
        for t in 0..s.terms.len() {
            let seeds: Vec<_> = s.holders(t).map(|h| keys[h].prss[s.local(h, t).unwrap()]).collect();
            assert!(seeds.iter().all(|k| *k == seeds[0]));
        }
        let mut case = Case::new(parties, toy(), 64, 21);
        case.keys = keys;
        for out in case.run(None, &[], None) {
            assert_eq!(out.result.unwrap().0, case.want);
        }
        // A holder that sends different contributions is caught.
        let r = std::thread::scope(|scope| {
            let s = &s;
            let hs: Vec<_> = network(parties)
                .into_iter()
                .map(|mut net| {
                    if net.id == 0 {
                        net.tamper.faults = vec![Fault { round: 0, to: Some(1), bit: 3 }];
                    }
                    scope.spawn(move || keygen(&mut net, s).map(|_| ()))
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect::<Vec<_>>()
        });
        assert!(r[1].is_err());
    }
}

#[test]
fn sharing_helpers() {
    let s = Structure::new(5);
    let v = vec![0xdead_beef_u64, 7];
    let sh = share(&s, &v);
    // Any f + 1 parties hold every term; the terms add up to the value.
    let mut terms = vec![None; s.terms.len()];
    for i in [0, 2, 4] {
        for (l, &t) in s.held[i].iter().enumerate() {
            terms[t] = Some(sh[i].0[l].clone());
        }
    }
    let sum = terms.iter().fold(vec![0u64; 2], |acc, t| acc.iter().zip(t.as_ref().unwrap()).map(|(a, b)| a ^ b).collect());
    assert_eq!(sum, v);
}

#[test]
fn every_streaming_level() {
    // Budgets that stream 1, 2, 3 rounds, or every AND bit, from the bit transcript.
    let n = 130;
    let (prog, pub_in, _) = th(n);
    let (_, sec_in) = random_inputs(&prog, n, 22);
    let rounds = prog.n_and.next_power_of_two().trailing_zeros() as usize + n.next_power_of_two().trailing_zeros() as usize;
    for parties in [3, 5] {
        let case = Case::with(Arc::new(Structure::new(parties)), prog.clone(), n, pub_in.clone(), &sec_in, 22);
        for streamed in [1, 2, 3, rounds] {
            let limit = Some(32usize << (rounds - streamed.min(rounds)));
            for out in case.run(None, &[], limit) {
                assert_eq!(out.result.unwrap().0, case.want, "n = {parties}, {streamed} streamed");
            }
            let b = [Bad { party: 1, cheat: Cheat::FlipAnd { and: 9000, bit: 77, split: false }, complicit: true, ..Default::default() }];
            let run = case.run(None, &b, limit);
            assert!(case.honest(&b).iter().all(|&i| run[i].result.is_err()), "n = {parties}, {streamed} streamed");
        }
    }
}

/// Indices of a nonempty subset of `elems` summing to zero over GF(2), if one exists.
fn kernel(elems: &[mpc::gf128::Gf128]) -> Option<Vec<usize>> {
    let words = elems.len().div_ceil(64);
    let mut basis: Vec<(u128, Vec<u64>)> = vec![];
    for (t, &e) in elems.iter().enumerate() {
        let mut v = e.0;
        let mut combo = vec![0u64; words];
        combo[t / 64] |= 1 << (t % 64);
        for (b, c) in &basis {
            let top = 127 - b.leading_zeros();
            if v >> top & 1 == 1 {
                v ^= b;
                for k in 0..words {
                    combo[k] ^= c[k];
                }
            }
        }
        if v == 0 {
            return Some((0..elems.len()).filter(|&k| combo[k / 64] >> (k % 64) & 1 == 1).collect());
        }
        basis.push((v, combo));
        basis.sort_by_key(|(b, _)| std::cmp::Reverse(127 - b.leading_zeros()));
    }
    None
}

/// A lie for the king of output 0 in its next opening, in the kernel of the coin of the opening it
/// saw last (zero against that coin's check): the instances to flip.
fn lie_from_last_coin(p: &mut Party, outputs: usize) -> Vec<usize> {
    use mpc::gf128::Gf128;
    let v = p.record.checks.iter().rev().find(|c| c.0 == "coin").unwrap().1;
    let key = p.coin_key(b"open-gamma", 0, Gf128(v));
    let ctag = p.vtag(b"open-gamma-expand", 0);
    let gamma = mpc::prf::prf_fields(&key, &ctag, 0, outputs);
    let c = crate::verify::ceil_log2(p.n);
    let sigma = mpc::prf::prf_fields(&key, &ctag, 1, c);
    let weight = crate::verify::tensor(c, |t| (Gf128::ONE, sigma[t]));
    let elems: Vec<Gf128> = (0..p.n).map(|t| gamma[0] * weight[t]).collect();
    kernel(&elems).expect("more instances than the field's dimension")
}

/// Makes king `p` send the lie `instances` (flipped in output 0) to everyone in round `round` (the
/// opening's round 2), and, rushing, cast in the vote three rounds later the vote of an honest party.
fn lie_as_king(p: &mut Party, instances: &[usize], round: u64) {
    let me = p.id;
    p.net.tamper.faults = instances.iter().map(|&t| Fault { round, to: None, bit: t }).collect();
    p.net.tamper.rush = true;
    p.net.tamper.corrupt = 1 << me;
    p.net.tamper.adapt = Some(Arc::new(move |r, got: &[Vec<u8>], out: &mut [Vec<u8>]| {
        if r == round + 3 {
            let honest = got.iter().enumerate().find(|(j, _)| *j != me).unwrap().1.clone();
            for m in out.iter_mut().filter(|m| !m.is_empty()) {
                *m = honest.clone();
            }
        }
    }));
}

/// Regression (review): two openings used the same coin, so a corrupt king that saw the first one
/// lied undetected in the second. Coins now carry a per-call epoch.
#[test]
fn a_king_cannot_reuse_an_old_coin_to_forge_an_opening() {
    for parties in [3, 5, 7] {
        let s = Arc::new(Structure::new(parties));
        let keys = deal(&s);
        let inst = 256;
        let values = |seed: u64| -> Vec<Vec<u64>> { (0..parties).map(|k| (0..inst / 64).map(|q| (seed + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left((k * 7 + q) as u32)).collect()).collect() };
        let (v1, v2) = (values(1), values(2));
        let (sh1, sh2): (Vec<Vec<Shares>>, Vec<Vec<Shares>>) = (v1.iter().map(|x| share(&s, x)).collect(), v2.iter().map(|x| share(&s, x)).collect());
        let king = 0;
        let run = session(&s, &keys, None, inst, &[Bad { party: king, ..Default::default() }], |p| {
            let i = p.id;
            let a = p.open(&sh1.iter().map(|v| v[i].clone()).collect::<Vec<_>>())?;
            if i == king {
                let lie = lie_from_last_coin(p, parties);
                let round = p.net.stats.rounds + 1;
                lie_as_king(p, &lie, round);
            }
            let b = p.open(&sh2.iter().map(|v| v[i].clone()).collect::<Vec<_>>())?;
            Ok((a, b))
        });
        for i in 1..parties {
            assert!(run[i].result.is_err(), "n = {parties}: honest party {i} accepted a forged opening");
        }
        // The two openings' coins differ.
        let coins: Vec<u128> = run[1].record.checks.iter().filter(|c| c.0 == "coin").map(|c| c.1).collect();
        assert!(coins.len() == 2 && coins[0] != coins[1]);
    }
}

#[test]
fn interleaved_opens_and_verifies_with_a_corrupt_king() {
    // eval, verify, open, open, eval, verify, verify (nothing new), open, open: the king of output 0
    // lies in one of the four openings (to everyone, chosen against the previous opening's coin).
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 256, 23);
        let script = |target: Option<usize>| {
            // The king ignores its own failed checks, so the script runs on unless an honest party aborts.
            let bad = target.map(|_| Bad { party: 0, complicit: true, ..Default::default() });
            session(&case.s, &case.keys, None, case.n, bad.as_slice(), |p| {
                let mine: Vec<Shares> = case.terms.iter().map(|t| party_shares(&case.s, t, p.id)).collect();
                let mut opened = vec![];
                let mut open = |p: &mut Party, xs: &[Shares], k: usize| -> Result<(), Abort> {
                    if p.id == 0 && target == Some(k) {
                        let lie = if k == 0 { vec![3, 70] } else { lie_from_last_coin(p, xs.len()) };
                        let round = p.net.stats.rounds + 1;
                        lie_as_king(p, &lie, round);
                    }
                    opened.push(p.open(xs)?);
                    Ok(())
                };
                let out = p.eval(&case.prog, &case.pub_in, &mine)?;
                p.verify()?;
                open(p, &out, 0)?;
                open(p, &out, 1)?;
                let out2 = p.eval(&case.prog, &case.pub_in, &mine)?;
                p.verify()?;
                p.verify()?;
                open(p, &out2, 2)?;
                open(p, &out2[..3], 3)?;
                Ok(opened)
            })
        };
        for out in script(None) {
            let opened = out.result.unwrap();
            assert_eq!(opened[..3], [case.want.clone(), case.want.clone(), case.want.clone()]);
            assert_eq!(opened[3], case.want[..3]);
        }
        for target in 0..4 {
            for (i, out) in script(Some(target)).iter().enumerate().skip(1) {
                assert!(out.result.is_err(), "n = {parties}: the lie in opening {target} was accepted by party {i}");
            }
        }
    }
}

#[test]
fn an_opening_lie_to_some_honest_parties_aborts_them_all() {
    // The king of output 0 (with a complicit coalition voting to accept) sends a wrong value to one
    // honest party only: that party's check fails, and its vote makes every honest party abort.
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 64, 24);
        let rounds = round_count(&case);
        for set in coalitions(parties).into_iter().filter(|c| c.contains(&0)).chain([vec![0]]) {
            let victim = (0..parties).find(|i| !set.contains(i)).unwrap();
            // Round 2 of the opening: the kings' values to everyone.
            let fault = Fault { round: rounds - 4, to: Some(victim), bit: 5 };
            let bad: Vec<Bad> = set
                .iter()
                .map(|&party| Bad { party, tamper: Tamper { faults: if party == 0 { vec![fault] } else { vec![] }, ..Default::default() }, complicit: true, ..Default::default() })
                .collect();
            let run = case.run(None, &bad, None);
            assert!(!run[0].hits.is_empty());
            for i in case.honest(&bad) {
                assert!(run[i].result.is_err(), "n = {parties}, {set:?}: honest party {i} output alone");
            }
        }
    }
}

#[test]
fn coordinated_additive_attacks_are_caught() {
    // All corrupt parties add errors to the same AND output: at distinct instances, at the same one
    // (cancelling when their number is even), or one flips and another covers the claim in the check
    // with a guessed challenge.
    for parties in [3, 5, 7] {
        let case = Case::new(parties, toy(), 100, 25);
        let and = case.prog.n_and / 2;
        for set in coalitions(parties) {
            for variant in 0..3 {
                let bad: Vec<Bad> = set
                    .iter()
                    .enumerate()
                    .map(|(k, &party)| {
                        let cheat = match variant {
                            0 => Cheat::FlipAnd { and, bit: 5 + 11 * k, split: false },
                            1 => Cheat::FlipAnd { and, bit: 5, split: false },
                            _ if k == 0 => Cheat::FlipAnd { and, bit: 5, split: false },
                            _ => Cheat::Cover { and, bit: 5, r1: 0x1234_5678 },
                        };
                        Bad { party, cheat, complicit: true, ..Default::default() }
                    })
                    .collect();
                let run = case.run(None, &bad, None);
                case.no_wrong_output(&run, &bad, "coordinated");
                let net_error = variant != 1 || set.len() % 2 == 1;
                for i in case.honest(&bad) {
                    assert_eq!(run[i].result.is_err(), net_error, "n = {parties}, {set:?}, variant {variant}");
                }
            }
        }
    }
}

#[test]
fn inconsistent_input_terms_are_caught_before_any_opening() {
    // A dealer gives party 0 a different copy of a term it shares with others.
    let xor_only = || {
        let mut b = Builder::new();
        let (x, y) = (b.sec_input(), b.sec_input());
        let z = b.xor(x, y);
        b.output(z);
        b.compile()
    };
    for parties in [3, 5, 7] {
        for (prog, why) in [(toy(), "inconsistent reshared or input terms"), (xor_only(), "inconsistent input terms")] {
            let case = Case::new(parties, prog, 64, 26);
            let run = session(&case.s, &case.keys, None, case.n, &[], |p| {
                let mut mine: Vec<Shares> = case.terms.iter().map(|t| party_shares(&case.s, t, p.id)).collect();
                if p.id == 0 {
                    mine[0].0[0][0] ^= 1 << 9;
                }
                let out = p.eval(&case.prog, &case.pub_in, &mine)?;
                p.verify()?;
                p.open(&out)
            });
            for (i, out) in run.iter().enumerate() {
                let err = out.result.as_ref().unwrap_err().0.clone();
                // The holders that compare with party 0 see it; the others see a party leave.
                assert!(err == why || err == "a party left", "n = {parties}, party {i}: {err}");
            }
            assert_eq!(run[0].result.as_ref().unwrap_err().0, why);
        }
        // Opening dealt shares directly: the opening compares the terms first.
        let case = Case::new(parties, toy(), 64, 27);
        let run = session(&case.s, &case.keys, None, case.n, &[], |p| {
            let mut mine: Vec<Shares> = case.terms.iter().map(|t| party_shares(&case.s, t, p.id)).collect();
            if p.id == 0 {
                mine[1].0[0][0] ^= 1;
            }
            p.open(&mine)
        });
        assert_eq!(run[0].result.as_ref().unwrap_err().0, "inconsistent terms to open");
        assert!(run.iter().all(|o| o.result.is_err()));
    }
}

#[test]
fn keygen_prf_inputs_mpc_outputs_end_to_end() {
    // No dealer: keys by keygen, inputs F(addr) = XOR_T H(k_T, addr) computed locally from the PRF
    // seeds, then Th(P, tw, F(addr)) in MPC, verified and opened.
    use crate::setup::{prf_inputs, prf_term};
    for parties in [3, 5, 7] {
        let s = Arc::new(Structure::new(parties));
        let keys: Vec<Keys> = std::thread::scope(|scope| {
            let s = &s;
            let hs: Vec<_> = network(parties).into_iter().map(|mut net| scope.spawn(move || keygen(&mut net, s).unwrap())).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let n = 100;
        let (prog, pub_in, prefixes) = th(n);
        let addrs: Vec<[u8; 32]> = (0..n as u32)
            .map(|k| {
                let mut a = [0u8; 32];
                a[..4].copy_from_slice(&k.to_le_bytes());
                a[4] = 0xf0;
                a
            })
            .collect();
        let run = session(&s, &keys, None, n, &[], |p| {
            let x = prf_inputs(&p.s, &keys[p.id], &addrs);
            let out = p.eval(&prog, &pub_in, &x)?;
            p.verify()?;
            p.open(&out)
        });
        let seed = |t: usize| {
            let h = s.holders(t).next().unwrap();
            keys[h].prf[s.local(h, t).unwrap()]
        };
        for k in 0..n {
            let fk = (0..s.terms.len()).fold([0u8; 16], |acc, t| {
                let h = prf_term(&seed(t), &addrs[k]);
                std::array::from_fn(|b| acc[b] ^ h[b])
            });
            let mut input = prefixes[k].to_vec();
            input.extend_from_slice(&fk);
            let want = blake2s::hash(&input);
            for out in &run {
                let out = out.result.as_ref().unwrap();
                for bit in 0..128 {
                    assert_eq!((out[bit][k / 64] >> (k % 64)) & 1, u64::from((want[bit / 8] >> (bit % 8)) & 1), "n = {parties}");
                }
            }
        }
    }
}

/// Analytic masking check (from the review): for every coalition `C` of size `f`, every collector
/// rotation entry `(T*, c)` and every reshare term `T*`, the messages `C` receives have a random part
/// (honest-only pair keys and PRSS seeds) of full rank over GF(2).
#[test]
fn every_message_to_a_coalition_has_a_fresh_mask() {
    for n in [3, 5, 7] {
        let s = Structure::new(n);
        let f = s.f;
        let nt = s.terms.len();
        for cm in (0u32..1 << n).filter(|m| m.count_ones() as usize == f) {
            let corrupt = |i: usize| cm >> i & 1 == 1;
            let honest: Vec<usize> = (0..n).filter(|&i| !corrupt(i)).collect();
            // Unknown random variables: honest pairs, and terms with no corrupt holder.
            let mut vars: Vec<(usize, usize)> = vec![];
            for (a, &i) in honest.iter().enumerate() {
                for &j in &honest[a + 1..] {
                    vars.push((i, j));
                }
            }
            let hidden: Vec<usize> = (0..nt).filter(|&t| s.holders(t).all(|h| !corrupt(h))).collect();
            assert_eq!(hidden.len(), 1);
            assert!(vars.len() + hidden.len() <= 128);
            let row_of = |i: usize, tstar: usize| -> u128 {
                let mut r = 0u128;
                for (k, &(a, b)) in vars.iter().enumerate() {
                    if a == i || b == i {
                        r |= 1 << k;
                    }
                }
                for (k, &t) in hidden.iter().enumerate() {
                    if t != tstar && s.owner[t] == i {
                        r |= 1 << (vars.len() + k);
                    }
                }
                r
            };
            let rank = |rows: &[u128]| -> usize {
                let mut b: Vec<u128> = vec![];
                for &r in rows {
                    let mut v = r;
                    for &x in &b {
                        v = v.min(v ^ x);
                    }
                    if v != 0 {
                        b.push(v);
                        b.sort_by(|a, c| c.cmp(a));
                    }
                }
                b.len()
            };
            // AND gates: a corrupt collector sees every honest contribution; corrupt holders of T*
            // see their sum.
            for g in 0..((f + 1) * nt) as u64 {
                let (tstar, c) = s.collector(g);
                let rows: Vec<u128> = if corrupt(c) {
                    honest.iter().map(|&i| row_of(i, tstar)).collect()
                } else if s.holders(tstar).any(corrupt) {
                    vec![honest.iter().fold(0, |a, &i| a ^ row_of(i, tstar))]
                } else {
                    vec![]
                };
                assert_eq!(rank(&rows), rows.len(), "n = {n}, C = {cm:b}, gate {g}: a message to C is not masked");
            }
            // Reshares in the check: every party sends to all holders of T*.
            for tstar in 0..nt {
                let rows: Vec<u128> = if s.holders(tstar).any(corrupt) { honest.iter().map(|&i| row_of(i, tstar)).collect() } else { vec![] };
                assert_eq!(rank(&rows), rows.len(), "n = {n}, C = {cm:b}, reshare T* = {tstar}");
            }
        }
    }
}

/// Two AND levels on 4 secret inputs.
fn toy2() -> Program {
    let mut b = Builder::new();
    let x: Vec<_> = (0..4).map(|_| b.sec_input()).collect();
    let a = b.and(x[0], x[1]);
    let c = b.and(x[2], x[3]);
    let d = b.and(a, c);
    let e = b.and(d, x[0]);
    b.output(e);
    b.output(a);
    b.compile()
}

/// Empirical two-world test on the messages themselves (from the review): the coalition's keys and
/// the session id are fixed, only honest-only keys are fresh per trial. A received bit that is
/// constant across trials is not masked by honest randomness; it must then be the same in both
/// worlds, and a masked bit must look the same in both.
#[test]
fn coalition_views_two_worlds_messages() {
    use std::sync::Mutex;
    for (parties, set) in [(3usize, vec![0usize]), (3, vec![2]), (5, vec![0, 1]), (5, vec![1, 3]), (7, vec![0, 1, 2]), (7, vec![2, 4, 6])] {
        let s = Arc::new(Structure::new(parties));
        let corrupt = set.iter().fold(0u32, |m, &i| m | 1 << i);
        let base = deal(&s);
        let prog = toy2();
        let inst = 64;
        let tc = s.terms.iter().position(|&t| t == corrupt).unwrap();
        let secrets = |seed: u64| -> Vec<u64> {
            let mut r = rng(seed);
            (0..4).map(|_| r()).collect()
        };
        // Sharings identical in both worlds except the term the coalition lacks.
        let fixed: Vec<u64> = (0..4 * s.terms.len()).map(|k| (k as u64 + 77).wrapping_mul(0xd6e8_feb8_6659_fd93)).collect();
        let shares_for = |sec: &[u64]| -> Vec<Vec<Shares>> {
            (0..4)
                .map(|k| {
                    let mut terms: Vec<u64> = (0..s.terms.len()).map(|t| fixed[k * s.terms.len() + t]).collect();
                    terms[tc] = (0..s.terms.len()).filter(|&t| t != tc).fold(sec[k], |a, t| a ^ terms[t]);
                    (0..parties).map(|i| Shares::input(s.held[i].iter().map(|&t| vec![terms[t]]).collect())).collect()
                })
                .collect()
        };
        let worlds = [shares_for(&secrets(1)), shares_for(&secrets(2))];
        let trials = 96;
        let mut counts: [Vec<u32>; 2] = [vec![], vec![]];
        for (wi, shares) in worlds.iter().enumerate() {
            for _ in 0..trials {
                let mut keys: Vec<Keys> = base.clone();
                for t in 0..s.terms.len() {
                    if s.holders(t).all(|h| corrupt >> h & 1 == 0) {
                        let k: [u8; 32] = mpc::prf::os_random();
                        for h in s.holders(t) {
                            keys[h].prss[s.local(h, t).unwrap()] = k;
                        }
                    }
                }
                for i in 0..parties {
                    for j in i + 1..parties {
                        if corrupt >> i & 1 == 0 && corrupt >> j & 1 == 0 {
                            let k: [u8; 32] = mpc::prf::os_random();
                            keys[i].pair[j] = k;
                            keys[j].pair[i] = k;
                        }
                    }
                }
                let views: Vec<Arc<Mutex<Vec<u8>>>> = (0..parties).map(|_| Arc::new(Mutex::new(vec![]))).collect();
                std::thread::scope(|scope| {
                    let hs: Vec<_> = network(parties)
                        .into_iter()
                        .map(|mut net| {
                            let (s, keys, prog, views) = (&s, &keys, &prog, &views);
                            scope.spawn(move || {
                                let i = net.id;
                                if corrupt >> i & 1 == 1 {
                                    let v = views[i].clone();
                                    let adapt: crate::net::Adapt = Arc::new(move |_r, got: &[Vec<u8>], _out: &mut [Vec<u8>]| {
                                        let mut g = v.lock().unwrap();
                                        for m in got {
                                            g.extend_from_slice(m);
                                        }
                                    });
                                    net.tamper = Tamper { rush: true, corrupt, adapt: Some(adapt), ..Default::default() };
                                }
                                let mut p = Party::new(net, s.clone(), keys[i].clone(), SessionId::fixed([7; 16]), inst);
                                p.threads = 1;
                                let mine: Vec<Shares> = shares.iter().map(|v| v[i].clone()).collect();
                                p.eval(prog, &[], &mine).unwrap();
                                p.verify().unwrap();
                            })
                        })
                        .collect();
                    for h in hs {
                        h.join().unwrap();
                    }
                });
                let view: Vec<u8> = set.iter().flat_map(|&i| views[i].lock().unwrap().clone()).collect();
                if counts[wi].is_empty() {
                    counts[wi] = vec![0; view.len() * 8];
                }
                assert_eq!(counts[wi].len(), view.len() * 8);
                for (b, c) in counts[wi].iter_mut().enumerate() {
                    *c += u32::from(view[b / 8] >> (b % 8) & 1);
                }
            }
        }
        let t = trials as u32;
        let (mut constant, mut masked) = (0, 0);
        for b in 0..counts[0].len() {
            let (ca, cb) = (counts[0][b], counts[1][b]);
            let (const_a, const_b) = (ca == 0 || ca == t, cb == 0 || cb == t);
            if const_a && const_b && ca == cb {
                constant += 1;
            } else if !const_a && !const_b && (ca as i64 - cb as i64).abs() < t as i64 / 3 {
                masked += 1;
            } else {
                panic!("n = {parties}, C = {set:?}: view bit {b} is {ca} vs {cb} of {t} in the two worlds");
            }
        }
        assert!(constant > 0 && masked > 0);
    }
}

/// Session 1 evaluates `z = x & y` (x = y = all ones), with party 0 flipping instance 5 of the AND
/// as the reviewer's reproduction did; `verify_first` says whether session 1 verifies its ANDs. Then
/// session 2, fresh and honest, verifies (nothing) and opens session 1's outputs, or uses them as the
/// input of another evaluation.
fn cross_session(parties: usize, cheat: Cheat, verify_first: bool, reuse: bool) -> Vec<Result<Vec<Vec<u64>>, Abort>> {
    let s = Arc::new(Structure::new(parties));
    let keys = deal(&s);
    let n = 64;
    let mut b = Builder::new();
    let (x, y) = (b.sec_input(), b.sec_input());
    let z = b.and(x, y);
    b.output(z);
    let prog = b.compile();
    let mut b = Builder::new();
    let x = b.sec_input();
    let y = b.not(x);
    b.output(y);
    let negate = b.compile();
    let ones = vec![u64::MAX];
    let (sx, sy) = (crate::setup::share(&s, &ones), crate::setup::share(&s, &ones));
    let bad = [Bad { party: 0, cheat, ..Default::default() }];
    let first = session(&s, &keys, None, n, &bad, |p| {
        let i = p.id;
        let out = p.eval(&prog, &[], &[sx[i].clone(), sy[i].clone()])?;
        if verify_first {
            p.verify()?;
        }
        Ok(out)
    });
    let outs: Vec<Vec<Shares>> = first.into_iter().map(|o| o.result.unwrap_or_default()).collect();
    if outs.iter().any(Vec::is_empty) {
        return vec![Err(Abort("session 1 aborted".into())); parties];
    }
    session(&s, &keys, None, n, &[], |p| {
        let mine = outs[p.id].clone();
        let mine = if reuse {
            let negated = p.eval(&negate, &[], &mine)?;
            p.verify()?;
            negated
        } else {
            p.verify()?;
            mine
        };
        p.open(&mine)
    })
    .into_iter()
    .map(|o| o.result)
    .collect()
}

#[test]
fn unverified_shares_cannot_cross_sessions() {
    let flip = Cheat::FlipAnd { and: 0, bit: 5, split: false };
    for parties in [3, 5, 7] {
        // Session 1 never verifies its (corrupted) AND: session 2 refuses to open the outputs, or to
        // use them as inputs.
        for reuse in [false, true] {
            for (i, r) in cross_session(parties, flip, false, reuse).iter().enumerate() {
                assert!(r.is_err(), "n = {parties}, reuse {reuse}: party {i} accepted {r:?}");
            }
        }
        // Verified in session 1, they open (or are used) in session 2; a corrupted AND makes
        // session 1's verification abort instead.
        for reuse in [false, true] {
            let want = if reuse { 0 } else { u64::MAX };
            for r in cross_session(parties, Cheat::Honest, true, reuse) {
                assert_eq!(r.unwrap(), vec![vec![want]], "n = {parties}, reuse {reuse}");
            }
            assert!(cross_session(parties, flip, true, reuse).iter().all(|r| r.is_err()), "n = {parties}");
        }
    }
}

#[test]
fn trailing_bytes_are_rejected_in_every_round() {
    use std::sync::atomic::{AtomicBool, Ordering};
    for parties in [3, 5] {
        let case = Case::new(parties, toy(), 100, 31);
        let rounds = round_count(&case);
        let mut tested = 0;
        for round in 0..rounds {
            let appended = Arc::new(AtomicBool::new(false));
            let flag = appended.clone();
            let adapt: crate::net::Adapt = Arc::new(move |r, _got, out| {
                if r == round {
                    for m in out.iter_mut().filter(|m| !m.is_empty()) {
                        m.push(0);
                        flag.store(true, Ordering::Relaxed);
                    }
                }
            });
            let tamper = Tamper { rush: true, corrupt: 1, adapt: Some(adapt), ..Default::default() };
            let b = [Bad { party: 0, tamper, ..Default::default() }];
            let run = case.run(None, &b, None);
            if appended.load(Ordering::Relaxed) {
                tested += 1;
                for i in case.honest(&b) {
                    assert!(run[i].result.is_err(), "n = {parties}: a trailing byte in round {round} was accepted by party {i}");
                }
            }
        }
        assert!(tested as u64 > rounds / 2, "n = {parties}: only {tested} of {rounds} rounds carried a message");
    }
}
