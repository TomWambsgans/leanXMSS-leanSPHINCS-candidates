//! End-to-end tests of the MPC: correctness against the clear evaluation, and cheating parties.

use crate::blake2s_circuit::{Word, add2, add3, split_prefixes, th_circuit};
use crate::circuit::{Builder, Program};
use crate::engine::{Cheat, Party, Shares};
use crate::net::{Abort, Fault, ring};
use crate::prf::Key;
use crate::session::{Bad, Outcome, SessionId, random_keys, run, share};

fn rng(seed: u64) -> impl FnMut() -> u64 {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    }
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
fn th(n: usize) -> (Program, Vec<Vec<u64>>) {
    let prefixes: Vec<[u8; 32]> = (0..n as u32)
        .map(|k| {
            let mut p = [3u8; 32];
            p[12..16].copy_from_slice(&k.to_le_bytes());
            p
        })
        .collect();
    let (layout, pub_in) = split_prefixes(&prefixes);
    (th_circuit(&layout).compile(), pub_in)
}

/// Evaluates `prog` in MPC, verifies, opens; `bad` cheats as told; `limit` sets the prover's
/// materialization memory.
fn mpc(prog: &Program, n: usize, pub_in: &[Vec<u64>], sec_in: &[Vec<u64>], bad: Option<Bad>, limit: Option<usize>) -> [Outcome<Vec<Vec<u64>>>; 3] {
    let shares: Vec<[Shares; 3]> = sec_in.iter().map(|v| share(v)).collect();
    run(&random_keys(), n, bad, |p| {
        p.materialize_limit = limit;
        let mine: Vec<Shares> = shares.iter().map(|s| s[p.id].clone()).collect();
        let out = p.eval(prog, pub_in, &mine)?;
        p.verify()?;
        p.open(&out)
    })
}

/// The clear evaluation, beyond-`n` bits cleared (the MPC keeps them zero).
fn clear(prog: &Program, n: usize, pub_in: &[Vec<u64>], sec_in: &[Vec<u64>]) -> Vec<Vec<u64>> {
    let tail = if n.is_multiple_of(64) { u64::MAX } else { (1 << (n % 64)) - 1 };
    let mut out = prog.eval_plain(n.div_ceil(64), pub_in, sec_in);
    for v in &mut out {
        *v.last_mut().unwrap() &= tail;
    }
    out
}

fn random_inputs(prog: &Program, n: usize, seed: u64) -> (Vec<Vec<u64>>, Vec<Vec<u64>>) {
    let mut r = rng(seed);
    let words = n.div_ceil(64);
    let tail = if n.is_multiple_of(64) { u64::MAX } else { (1 << (n % 64)) - 1 };
    let mut v = || {
        let mut x: Vec<u64> = (0..words).map(|_| r()).collect();
        *x.last_mut().unwrap() &= tail;
        x
    };
    ((0..prog.n_pub_inputs).map(|_| v()).collect(), (0..prog.n_sec_inputs).map(|_| v()).collect())
}

/// Every honest party aborts or outputs the right value, never a wrong one; returns whether one aborted.
fn check_no_wrong_output(run: &[Outcome<Vec<Vec<u64>>>; 3], want: &[Vec<u64>], bad: usize) -> bool {
    let mut aborted = false;
    for (i, out) in run.iter().enumerate() {
        if i == bad {
            continue;
        }
        match &out.result {
            Ok(v) => assert_eq!(v, want, "an honest party accepted a wrong output"),
            Err(_) => aborted = true,
        }
    }
    aborted
}

/// Whether a flip of `bit` in the message of round `round` is harmless by design: an AND message
/// bit past the batch size `n` (in a gate's last word), which every receiver masks off. Round 0 is
/// the session round; the AND rounds follow it.
fn benign(prog: &Program, n: usize, round: u64, to_next: bool, bit: usize) -> bool {
    let words = n.div_ceil(64);
    let levels: Vec<usize> = prog.steps.iter().filter(|s| !s.ands.is_empty()).map(|s| s.ands.len()).collect();
    let Some(&gates) = round.checked_sub(1).and_then(|r| levels.get(r as usize)) else { return false };
    let bit = bit % (gates * words * 64);
    to_next && !n.is_multiple_of(64) && (bit / 64) % words == words - 1 && bit % 64 >= n % 64
}

#[test]
fn toy_circuit_matches_clear_evaluation() {
    let prog = toy();
    for n in [1usize, 5, 64, 100] {
        let (pub_in, sec_in) = random_inputs(&prog, n, n as u64);
        let want = clear(&prog, n, &pub_in, &sec_in);
        for out in mpc(&prog, n, &pub_in, &sec_in, None, None) {
            assert_eq!(out.result.unwrap(), want, "n = {n}");
        }
    }
}

#[test]
fn th_in_mpc_matches_blake2s() {
    let n: usize = 300;
    let mut r = rng(5);
    let prefixes: Vec<[u8; 32]> = (0..n as u32)
        .map(|k| {
            let mut p = [0u8; 32];
            p[0] = 1;
            p[12..16].copy_from_slice(&(k * 3).to_le_bytes());
            p[16..].copy_from_slice(&[0x5a; 16]);
            p
        })
        .collect();
    let secrets: Vec<[u8; 16]> = (0..n).map(|_| std::array::from_fn(|_| r() as u8)).collect();
    let (layout, pub_in) = split_prefixes(&prefixes);
    let prog = th_circuit(&layout).compile();
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
    let run = mpc(&prog, n, &pub_in, &sec_in, None, None);
    let out = run[1].result.as_ref().unwrap();
    for k in 0..n {
        let mut input = prefixes[k].to_vec();
        input.extend_from_slice(&secrets[k]);
        let want = blake2s::hash(&input);
        for bit in 0..128 {
            assert_eq!((out[bit][k / 64] >> (k % 64)) & 1, u64::from((want[bit / 8] >> (bit % 8)) & 1));
        }
    }
    // About one bit per AND per party, plus the opening and a proof of a few KB; rounds: the session
    // round, the depth, and the proof.
    let s = run[0].stats;
    let and_bytes = (prog.n_and * words * 8) as u64;
    let open_bytes = (128 * words * 8 + 32) as u64;
    assert!(s.bytes_sent >= and_bytes + open_bytes && s.bytes_sent < and_bytes + open_bytes + 8192, "{s:?}, {and_bytes}");
    assert!(s.rounds as usize > prog.depth && (s.rounds as usize) < prog.depth + 64, "{s:?}");
}

#[test]
fn any_flipped_bit_is_caught() {
    // Every round, both links, every party, bits spread over each whole message.
    let prog = toy();
    let n = 70;
    let (pub_in, sec_in) = random_inputs(&prog, n, 11);
    let want = clear(&prog, n, &pub_in, &sec_in);
    let rounds = mpc(&prog, n, &pub_in, &sec_in, None, None)[0].stats.rounds;
    let (mut applied, mut caught) = (0, 0);
    for bad in 0..3 {
        for round in 0..rounds {
            for to_next in [false, true] {
                for bit in (0..4096usize).step_by(61) {
                    let fault = Fault { round, to_next, bit };
                    let run = mpc(&prog, n, &pub_in, &sec_in, Some(Bad { party: bad, fault: Some(fault), cheat: Cheat::Honest }), None);
                    let aborted = check_no_wrong_output(&run, &want, bad);
                    if !run[bad].fault_applied {
                        continue;
                    }
                    applied += 1;
                    if !benign(&prog, n, round, to_next, bit) {
                        assert!(aborted, "party {bad}, round {round}, to_next {to_next}, bit {bit}: an applied flip went unnoticed");
                        caught += 1;
                    }
                }
            }
        }
    }
    assert!(caught > 1000, "{caught} of {applied}");
}

#[test]
fn flipped_and_messages_always_abort() {
    let prog = toy();
    let n = 100;
    let (pub_in, sec_in) = random_inputs(&prog, n, 12);
    let want = clear(&prog, n, &pub_in, &sec_in);
    for bad in 0..3 {
        for and in [0, prog.n_and / 2, prog.n_and - 1] {
            for consistent in [false, true] {
                for bit in [0usize, 63, 99] {
                    let cheat = Cheat::FlipAnd { and, bit, consistent };
                    let run = mpc(&prog, n, &pub_in, &sec_in, Some(Bad { party: bad, fault: None, cheat }), None);
                    assert!(check_no_wrong_output(&run, &want, bad), "undetected: party {bad}, AND {and}, consistent {consistent}");
                    for (i, out) in run.iter().enumerate() {
                        if i != bad {
                            assert!(out.result.is_err(), "honest party {i} accepted");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn flipped_blake2s_messages_abort() {
    let n: usize = 70;
    let (prog, pub_in) = th(n);
    let (_, sec_in) = random_inputs(&prog, n, 13);
    let want = clear(&prog, n, &pub_in, &sec_in);
    let rounds = mpc(&prog, n, &pub_in, &sec_in, None, None)[0].stats.rounds;
    let mut r = rng(14);
    let (mut applied, mut caught) = (0, 0);
    while applied < 60 {
        let bad = (r() % 3) as usize;
        let fault = Fault { round: r() % rounds, to_next: r().is_multiple_of(2), bit: r() as usize };
        let run = mpc(&prog, n, &pub_in, &sec_in, Some(Bad { party: bad, fault: Some(fault), cheat: Cheat::Honest }), None);
        let aborted = check_no_wrong_output(&run, &want, bad);
        if !run[bad].fault_applied {
            continue;
        }
        applied += 1;
        if !benign(&prog, n, fault.round, fault.to_next, fault.bit) {
            assert!(aborted, "an applied, non-benign flip went unnoticed: party {bad}, {fault:?}");
            caught += 1;
        }
    }
    // About half the bits of an AND message are past n = 70 in a gate's last word, hence benign.
    assert!(caught > 15, "{caught} of {applied}");
    for bad in 0..3 {
        let cheat = Cheat::FlipAnd { and: (r() as usize) % prog.n_and, bit: r() as usize, consistent: true };
        let run = mpc(&prog, n, &pub_in, &sec_in, Some(Bad { party: bad, fault: None, cheat }), None);
        assert!(run.iter().enumerate().all(|(i, o)| i == bad || o.result.is_err()));
    }
}

#[test]
fn streamed_and_bit_level_prover_rounds() {
    // A tiny materialization budget forces the bit-level and streamed rounds; a medium one, a few of
    // each before materializing.
    let n = 300;
    let (prog, pub_in) = th(n);
    let (_, sec_in) = random_inputs(&prog, n, 15);
    let want = clear(&prog, n, &pub_in, &sec_in);
    for limit in [Some(1), Some(1 << 16), None] {
        for out in mpc(&prog, n, &pub_in, &sec_in, None, limit) {
            assert_eq!(out.result.unwrap(), want, "limit {limit:?}");
        }
        for bad in 0..3 {
            for consistent in [false, true] {
                let cheat = Cheat::FlipAnd { and: 4321 % prog.n_and, bit: 77, consistent };
                let run = mpc(&prog, n, &pub_in, &sec_in, Some(Bad { party: bad, fault: None, cheat }), limit);
                assert!(run.iter().enumerate().all(|(i, o)| i == bad || o.result.is_err()), "limit {limit:?}, party {bad}");
            }
        }
    }
}

/// One AND gate and a second level, on 32 instances.
fn two_levels() -> Program {
    let mut b = Builder::new();
    let (u, v) = (b.sec_input(), b.sec_input());
    let o = b.and(u, v);
    let o2 = b.and(o, u);
    b.output(o2);
    b.compile()
}

#[test]
fn a_malicious_verifier_cannot_choose_the_coins() {
    // Party 1 (V+ of prover 0) sends prover 0 coins of its choice; the reviewer's attack then read
    // prover 0's missing share off V-'s final message. Prover 0 now sees that its two verifiers
    // disagree and aborts before sending any proof message. The same for party 2 (V- of prover 0)
    // sending a wrong challenge.
    let prog = two_levels();
    let n = 32;
    let (_, sec_in) = random_inputs(&prog, n, 16);
    for (bad, cheat, why) in [(1, Cheat::BadBeta, "batching coins"), (2, Cheat::BadChallenge, "challenges")] {
        let run = mpc(&prog, n, &[], &sec_in, Some(Bad { party: bad, fault: None, cheat }), None);
        let err = run[0].result.as_ref().unwrap_err();
        assert!(err.0.contains(why), "prover 0 should reject the {why}: {err}");
        assert!(run.iter().all(|o| o.result.is_err()), "nothing is opened");
    }
}

/// Runs a session of `prog` with keys `keys` and the session id `session` (if `Some`, reused as is;
/// if `None`, freshly established), prover 0 cheating as `cheat`; returns the opened value and the
/// first challenge prover 0 saw.
fn session_run(prog: &Program, keys: &[Key; 3], session: Option<[u8; 16]>, sec: &[[Shares; 3]], cheat: Cheat) -> [Result<(u64, Option<u128>), Abort>; 3] {
    std::thread::scope(|scope| {
        ring()
            .map(|mut link| {
                scope.spawn(move || {
                    let i = link.id;
                    let id = match session {
                        Some(s) => SessionId::fixed(s),
                        None => crate::session::establish(&mut link)?,
                    };
                    let mut p = Party::new(link, keys[i], keys[(i + 2) % 3], id, 32);
                    if i == 0 {
                        p.cheat = cheat;
                    }
                    let mine: Vec<Shares> = sec.iter().map(|s| s[i].clone()).collect();
                    let out = p.eval(prog, &[], &mine)?;
                    p.verify()?;
                    let opened = p.open(&out)?;
                    Ok((opened[0][0], p.seen_r0))
                })
            })
            .map(|h| h.join().unwrap())
    })
}

#[test]
fn a_repeated_session_id_would_let_a_prover_forge_but_ids_are_fresh() {
    let prog = two_levels();
    let (_, sec_in) = random_inputs(&prog, 32, 17);
    let sec: Vec<[Shares; 3]> = sec_in.iter().map(|v| share(v)).collect();
    let want = clear(&prog, 32, &[], &sec_in)[0][0];
    let keys = random_keys();
    let forge = |r0| Cheat::Forge { and: 1, bit: 5, r0 };
    // Why ids must be fresh: with one id reused, prover 0 forges with the challenge it saw before,
    // and a wrong output opens.
    let first = session_run(&prog, &keys, Some([3; 16]), &sec, Cheat::Honest);
    let r0 = first[0].as_ref().unwrap().1.unwrap();
    let replay = session_run(&prog, &keys, Some([3; 16]), &sec, forge(r0));
    let got = replay[1].as_ref().unwrap().0;
    assert_ne!(got, want, "the forgery goes through with a repeated id");
    // With established ids (the only ones the protocols use), the old challenge is useless.
    let first = session_run(&prog, &keys, None, &sec, Cheat::Honest);
    let r0 = first[0].as_ref().unwrap().1.unwrap();
    let again = session_run(&prog, &keys, None, &sec, forge(r0));
    assert!(again[1].is_err() && again[2].is_err(), "a fresh session rejects the forgery");
}

#[test]
fn a_party_that_aborted_never_opens() {
    let prog = toy();
    let n = 70;
    let (pub_in, sec_in) = random_inputs(&prog, n, 18);
    let shares: Vec<[Shares; 3]> = sec_in.iter().map(|v| share(v)).collect();
    let bad = Bad { party: 0, fault: None, cheat: Cheat::FlipAnd { and: 3, bit: 1, consistent: false } };
    let run = run(&random_keys(), n, Some(bad), |p| {
        let mine: Vec<Shares> = shares.iter().map(|s| s[p.id].clone()).collect();
        let out = p.eval(&prog, &pub_in, &mine)?;
        let verdict = p.verify();
        // Whatever the caller does with the error, the party refuses to open afterwards.
        let open = p.open(&out);
        Ok((verdict.is_err(), open.is_err()))
    });
    for i in 1..3 {
        let (rejected, refused) = run[i].result.clone().unwrap();
        assert!(rejected && refused, "party {i}");
    }
}
