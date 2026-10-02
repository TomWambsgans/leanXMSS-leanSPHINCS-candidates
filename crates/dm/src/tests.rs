//! End-to-end tests: honest runs match the circuit (BLAKE2s included); corrupt parties deviating in
//! any message, together, or rushing, make the honest parties abort, never output a wrong value,
//! and learn nothing that depends on the honest parties' secrets before the abort.

use std::sync::{Arc, Mutex};

use mpc::blake2s_circuit::{Word, compress};
use mpc::circuit::{Builder, Program};

use crate::aes::Stream;
use crate::dealer::{Config, Dealer, Tier};
use crate::net::{Abort, Recorder, Tamper, View};
use crate::pcg::{Noise, Params};
use crate::protocol::{Options, Output, Report, session};

const SMALL: Params = Params { n: 6, c: 2, tau: 1, leaf: 2 };
const SESSION: u128 = 0x5e55_1011;

/// A fresh setup (one session's material) with a fixed session id.
fn dealer(tier: Tier, batches: usize, seed: u128) -> Arc<Dealer> {
    let mut cfg = Config::new(SMALL, tier, batches, seed);
    cfg.balance = if tier == Tier::Plain { 2 } else { 1 };
    cfg.session = SESSION;
    Arc::new(Dealer::new(cfg))
}

/// A small circuit: two AND levels, XORs, NOTs, inputs reused.
fn small_circuit() -> Program {
    let mut b = Builder::new();
    let a: Vec<_> = (0..8).map(|_| b.sec_input()).collect();
    let c: Vec<_> = (0..7).map(|i| b.and(a[i], a[i + 1])).collect();
    let mut outs = vec![];
    for i in 0..6 {
        let x = b.xor(a[i + 2], c[i + 1]);
        let nx = b.not(x);
        outs.push(b.and(c[i], nx));
    }
    let t = b.not(a[7]);
    outs.push(b.xor(c[0], t));
    outs.push(b.and(outs[0], outs[5]));
    for o in outs {
        b.output(o);
    }
    b.compile()
}

fn random_inputs(prog: &Program, instances: usize, seed: u128) -> [Vec<Vec<u64>>; 3] {
    let mut s = Stream::new(seed);
    let words = instances.div_ceil(64);
    std::array::from_fn(|_| (0..prog.n_sec_inputs).map(|_| (0..words).map(|_| s.next_u64()).collect()).collect())
}

fn expected(prog: &Program, instances: usize, inputs: &[Vec<Vec<u64>>; 3]) -> Vec<Vec<u64>> {
    let words = instances.div_ceil(64);
    let x: Vec<Vec<u64>> = (0..prog.n_sec_inputs).map(|i| (0..words).map(|w| inputs[0][i][w] ^ inputs[1][i][w] ^ inputs[2][i][w]).collect()).collect();
    let mut out = prog.eval_plain(words, &[], &x);
    for o in out.iter_mut() {
        for (w, v) in o.iter_mut().enumerate() {
            if instances - 64 * w < 64 {
                *v &= (1u64 << (instances - 64 * w)) - 1;
            }
        }
    }
    out
}

fn opts(threads: usize) -> Options {
    Options { threads, coins: Some([11, 22, 33]), ..Default::default() }
}

#[test]
fn honest_runs_compute_the_circuit() {
    let prog = Arc::new(small_circuit());
    for tier in [Tier::Plain, Tier::Ssd, Tier::Dssd] {
        for (batches, instances) in [(1, 64), (2, 70), (3, 120)] {
            let inputs = random_inputs(&prog, instances, 77);
            let want = expected(&prog, instances, &inputs);
            for (r, h) in session(dealer(tier, batches, 1), prog.clone(), instances, inputs, opts(2)).into_iter().zip(0..) {
                let o = r.unwrap_or_else(|e| panic!("{tier:?} party {h}: {e}"));
                assert_eq!(o.out, want);
                assert!(o.report.counts.fmul > 0 && o.report.counts.fuv > 0, "{tier:?}");
            }
        }
    }
}

#[test]
fn groups_of_batches() {
    // Five batches in groups of two (fresh positions, and DSSD matrices, per group), the F_Mul
    // rounds two groups at a time.
    let prog = Arc::new(small_circuit());
    let instances = 64 * 4;
    let inputs = random_inputs(&prog, instances, 3);
    let want = expected(&prog, instances, &inputs);
    for tier in [Tier::Plain, Tier::Ssd, Tier::Dssd] {
        let mut cfg = Config::new(SMALL, tier, 5, 9);
        cfg.balance = 2;
        if tier != Tier::Plain {
            (cfg.group, cfg.balance) = (2, 1);
        }
        cfg.chunk = 2;
        let res = session(Arc::new(Dealer::new(cfg)), prog.clone(), instances, inputs.clone(), opts(2));
        for r in res {
            assert_eq!(r.unwrap().out, want, "{tier:?}");
        }
    }
}

#[test]
fn setup_material_is_single_use() {
    let prog = Arc::new(small_circuit());
    let d = dealer(Tier::Dssd, 1, 2);
    let inputs = random_inputs(&prog, 64, 4);
    assert!(session(d.clone(), prog.clone(), 64, inputs.clone(), opts(1)).iter().all(|r| r.is_ok()));
    for r in session(d, prog, 64, inputs, opts(1)) {
        assert_eq!(r.err().unwrap().0, "setup material already used");
    }
}

#[test]
fn blake2s_compression_in_every_tier() {
    let mut b = Builder::new();
    let h: [Word; 8] = std::array::from_fn(|_| std::array::from_fn(|_| b.sec_input()));
    let m: [Word; 16] = std::array::from_fn(|_| std::array::from_fn(|_| b.sec_input()));
    for w in &compress(&mut b, &h, &m, 64, true) {
        for &bit in w {
            b.output(bit);
        }
    }
    let prog = Arc::new(b.compile());
    assert_eq!(prog.n_and, 14_714);
    let instances = 3;
    let inputs = random_inputs(&prog, instances, 5);
    for tier in [Tier::Plain, Tier::Ssd, Tier::Dssd] {
        let mut cfg = Config::new(Params { n: 9, c: 2, tau: 1, leaf: 3 }, tier, 2, 6);
        cfg.balance = if tier == Tier::Plain { 2 } else { 1 };
        let res = session(Arc::new(Dealer::new(cfg)), prog.clone(), instances, inputs.clone(), opts(2));
        let outs: Vec<Output> = res.into_iter().map(|r| r.unwrap()).collect();
        for k in 0..instances {
            let word = |i: usize| (0..32).fold(0u32, |acc, j| acc | ((((inputs[0][32 * i + j][0] ^ inputs[1][32 * i + j][0] ^ inputs[2][32 * i + j][0]) >> k) & 1) as u32) << j);
            let mut hh: [u32; 8] = std::array::from_fn(word);
            let mm: [u32; 16] = std::array::from_fn(|i| word(8 + i));
            blake2s::compress(&mut hh, &mm, 64, true);
            for o in &outs {
                for i in 0..256 {
                    assert_eq!((o.out[i][0] >> k) & 1, u64::from((hh[i / 32] >> (i % 32)) & 1), "{tier:?} instance {k} bit {i}");
                }
            }
        }
    }
}

/// Flips the first, a middle or the last bit of a party's message in round `round`: toward both
/// parties (a consistent lie) or toward its successor only (equivocation).
fn flip(round: u64, which: usize, both: bool) -> Tamper {
    Box::new(move |r, _, to_prev, to_next| {
        let n = 8 * to_next.len();
        if r == round && n > 0 {
            let bit = [0, n / 2 + 3, n - 1][which] % n;
            to_next[bit / 8] ^= 1 << (bit % 8);
            if both {
                to_prev[bit / 8] ^= 1 << (bit % 8);
            }
        }
    })
}

/// The phase each round of an honest run belongs to.
fn round_phases(r: &Report) -> Vec<&'static str> {
    r.phases.iter().flat_map(|p| std::iter::repeat_n(p.name, p.stats.rounds as usize)).collect()
}

/// The aborts a consistent lie in a phase may cause.
fn allowed(phase: &str) -> &'static [&'static str] {
    match phase {
        "inputs" => &[],
        "evaluation" => &["verification failed"],
        "verify: coefficients" => &["bad coin opening", "inconsistent broadcasts"],
        "verify: sumcheck" => &["bad coin opening", "verification failed"],
        "verify: FMul (balancing)" | "verify: FMul (payloads)" => &["bad coin opening", "MAC check failed"],
        "verify: open and check" => &["bad coin opening", "MAC check failed", "bad MAC-check opening", "inconsistent broadcasts"],
        "outputs" => &["bad coin opening", "MAC check failed", "bad MAC-check opening", "inconsistent broadcasts", "no agreement to output"],
        _ => panic!("unexpected phase {phase}"),
    }
}

type Outcome = Result<Vec<Vec<u64>>, String>;

/// Runs a session with the given corrupt behaviour; returns the honest outcomes and corrupt views.
fn attack(d: Arc<Dealer>, prog: &Arc<Program>, inputs: &[Vec<Vec<u64>>; 3], tamper: [Option<Tamper>; 3], rush: [bool; 3]) -> ([Outcome; 3], [View; 3]) {
    let rec: [Recorder; 3] = std::array::from_fn(|_| Arc::new(Mutex::new(View::default())));
    let o = Options { threads: 1, tamper, rush, record: rec.clone().map(Some), coins: Some([11, 22, 33]) };
    let res = session(d, prog.clone(), 64, inputs.clone(), o);
    let out = res.map(|r| r.map(|o| o.out).map_err(|e: Abort| e.0));
    (out, rec.map(|r| r.lock().unwrap().clone()))
}

/// The check values a corrupt party saw opened.
fn checks_seen(v: &View) -> Vec<Vec<u128>> {
    v.opened.iter().filter(|(w, _)| *w == "checks").map(|(_, x)| x.clone()).collect()
}

#[test]
fn cheaters_are_caught_and_learn_nothing() {
    let prog = Arc::new(small_circuit());
    let instances = 64;
    // Two worlds that differ in the honest parties' secrets (setup and inputs), not in the
    // corrupt party's inputs nor in the coins.
    let inputs_a = random_inputs(&prog, instances, 9);
    let mut inputs_b = random_inputs(&prog, instances, 10);
    inputs_b[1] = inputs_a[1].clone();
    let want = expected(&prog, instances, &inputs_a);
    let words = instances.div_ceil(64);
    // Party 1 flipping a bit of its masked input is a legitimate change of its own input.
    let want_flipped: Vec<Vec<Vec<u64>>> = (0..3)
        .map(|which| {
            let n = 64 * prog.n_sec_inputs * words;
            let bit = [0, n / 2 + 3, n - 1][which];
            let mut flipped = inputs_a.clone();
            flipped[1][bit / 64 / words][(bit / 64) % words] ^= 1 << (bit % 64);
            expected(&prog, instances, &flipped)
        })
        .collect();
    for tier in [Tier::Plain, Tier::Ssd, Tier::Dssd] {
        let honest_run = session(dealer(tier, 2, 1), prog.clone(), instances, inputs_a.clone(), opts(1));
        let report = &honest_run[0].as_ref().unwrap().report;
        let phases = round_phases(report);
        let rounds = phases.len() as u64;
        let (mut aborted, mut cases) = (0, 0);
        for round in 0..rounds {
            let phase = phases[round as usize];
            // (corrupt set, both directions): one cheater consistent or equivocating; two cheaters,
            // the second staying silent about the first's lie.
            for (two, both, which) in (0..12).map(|k| (k & 1 == 1, k & 2 == 0, k / 4)) {
                let honest: Vec<usize> = if two { vec![0] } else { vec![0, 2] };
                let run = |seed: u128, inputs: &[Vec<Vec<u64>>; 3]| {
                    let mut t: [Option<Tamper>; 3] = [None, None, None];
                    t[1] = Some(flip(round, which, both));
                    attack(dealer(tier, 2, seed), &prog, inputs, t, [false; 3])
                };
                let (out_a, view_a) = run(1, &inputs_a);
                let (out_b, view_b) = run(2, &inputs_b);
                // Nothing the corrupt party sees opened, nor whether the honest parties abort,
                // depends on the honest parties' secrets.
                assert_eq!(checks_seen(&view_a[1]), checks_seen(&view_b[1]), "{tier:?} round {round}: checks depend on secrets");
                for &h in &honest {
                    assert_eq!(out_a[h].is_err(), out_b[h].is_err(), "{tier:?} round {round}: abort depends on secrets");
                    cases += 1;
                    match &out_a[h] {
                        Err(e) => {
                            aborted += 1;
                            assert_eq!(Some(e), out_b[h].as_ref().err(), "{tier:?} round {round}");
                            if both && !two {
                                assert!(allowed(phase).iter().any(|a| e.starts_with(a)), "{tier:?} round {round} ({phase}): {e}");
                            }
                        }
                        Ok(o) => {
                            let ok = *o == want || (phase == "inputs" && *o == want_flipped[which]);
                            assert!(ok, "{tier:?}: party {h} output a wrong value (round {round}, two {two}, both {both})");
                            // Only a change of the cheater's own input passes, or a lie sent to
                            // the other party too late to change anything this party sees.
                            let late = !both && h != 2 && round + 2 >= rounds;
                            assert!((both && phase == "inputs") || late, "{tier:?}: undetected cheat in round {round} (two {two}, both {both}, which {which}, party {h})");
                        }
                    }
                }
            }
        }
        assert!(aborted * 10 >= cases * 9, "{tier:?}: {aborted} aborts of {cases}");
    }
}

/// The reviewer's attack: errors on the opened `δ` of the payload `F_Mul`s of the honest party's
/// own noise points would make the check value equal its PCG noise payloads, if the check were
/// opened before the MAC check. One or two corrupt parties.
#[test]
fn fmul_error_leaks_honest_noise_before_mac_check() {
    let p = SMALL;
    let prog = Arc::new(small_circuit());
    let inputs = random_inputs(&prog, 64, 12);
    let t = p.t();
    // Queries of vectors E then F, block b, entry 0: party 0's own noise point.
    let targets: Vec<usize> = (0..2 * p.c).flat_map(|v| (0..t).map(move |b| (v * t + b) * 3)).collect();
    let want_len = 32 + 16 * 2 * (2 * p.weight());
    let lie = |seed: u64| -> Tamper {
        let tg = targets.clone();
        Box::new(move |_, _, to_prev, to_next| {
            if to_next.len() == want_len {
                for (i, &q) in tg.iter().enumerate() {
                    for s in 0..2 {
                        let off = 32 + 16 * (2 * (2 * q + s) + 1);
                        let err = (1u128 << (2 * i + s)) ^ u128::from(seed);
                        for m in [&mut *to_prev, &mut *to_next] {
                            let x = u128::from_le_bytes(m[off..off + 16].try_into().unwrap()) ^ err;
                            m[off..off + 16].copy_from_slice(&x.to_le_bytes());
                        }
                    }
                }
            }
        })
    };
    for two in [false, true] {
        let tamper = [None, Some(lie(0)), if two { Some(lie(7)) } else { None }];
        let (out, views) = attack(dealer(Tier::Plain, 1, 0xabcd), &prog, &inputs, tamper, [false; 3]);
        for h in if two { vec![0] } else { vec![0, 2] } {
            assert_eq!(out[h].as_ref().err().map(|e| e.as_str()), Some("MAC check failed"));
        }
        // The F_Mul MACs fail before any check value is opened: nothing leaks.
        assert!(checks_seen(&views[1]).is_empty());
        // Sanity: the attack does target the honest party's noise.
        let noise: Noise = dealer(Tier::Plain, 1, 0xabcd).noise(0, 0);
        assert!(noise.val.iter().all(|&v| v != 0));
    }
}

/// Two corrupt parties deviating together: lies that cancel go unnoticed and change nothing;
/// lies that add up are caught.
#[test]
fn coordinated_cheaters() {
    let prog = Arc::new(small_circuit());
    let inputs = random_inputs(&prog, 64, 13);
    let want = expected(&prog, 64, &inputs);
    for tier in [Tier::Plain, Tier::Ssd, Tier::Dssd] {
        let eval_round = 1; // the first AND level
        for (bit1, bit2, caught) in [(0, 0, false), (0, 9, true), (64, 64, false), (3, 200, true)] {
            let tamper = |bit: usize| -> Tamper {
                Box::new(move |r, _, to_prev, to_next| {
                    if r == eval_round {
                        to_prev[bit / 8] ^= 1 << (bit % 8);
                        to_next[bit / 8] ^= 1 << (bit % 8);
                    }
                })
            };
            let (out, _) = attack(dealer(tier, 2, 5), &prog, &inputs, [None, Some(tamper(bit1)), Some(tamper(bit2))], [false; 3]);
            if caught {
                assert!(out[0].as_ref().err().unwrap().starts_with("verification failed"), "{tier:?}");
            } else {
                assert_eq!(out[0].as_ref().unwrap(), &want, "{tier:?}");
            }
        }
    }
}

/// A rushing party reads the honest shares of the check values before sending its own, and zeroes
/// the opened checks after cheating in the evaluation: the MAC check still catches it.
#[test]
fn rushing_cheater() {
    let prog = Arc::new(small_circuit());
    let inputs = random_inputs(&prog, 64, 14);
    for tier in [Tier::Plain, Tier::Ssd, Tier::Dssd] {
        for two in [false, true] {
            let honest = session(dealer(tier, 2, 1), prog.clone(), 64, inputs.clone(), opts(1));
            let report = &honest[0].as_ref().unwrap().report;
            let phases = round_phases(report);
            let start = phases.iter().position(|&p| p == "verify: open and check").unwrap() as u64;
            let check_round = start + 2;
            let tamper: Tamper = Box::new(move |r, got, to_prev, to_next| {
                if r == 1 {
                    to_prev[0] ^= 1;
                    to_next[0] ^= 1;
                }
                if r == check_round {
                    let got = got.expect("rushing");
                    let n = (to_next.len() - 32) / 16;
                    for k in 0..n {
                        let at = 32 + 16 * k;
                        let share = |m: &Vec<u8>| u128::from_le_bytes(m[at..at + 16].try_into().unwrap());
                        let zeroing = (share(&got[0]) ^ share(&got[1])).to_le_bytes();
                        to_prev[at..at + 16].copy_from_slice(&zeroing);
                        to_next[at..at + 16].copy_from_slice(&zeroing);
                    }
                }
            });
            let mut t: [Option<Tamper>; 3] = [None, Some(tamper), None];
            if two {
                t[2] = Some(Box::new(|_, _, _, _| {}));
            }
            let (out, views) = attack(dealer(tier, 2, 1), &prog, &inputs, t, [false, true, false]);
            // The rushing party did open all-zero checks; the honest parties still abort.
            assert!(checks_seen(&views[1]).iter().all(|c| c.iter().all(|&x| x == 0)));
            for h in if two { vec![0] } else { vec![0, 2] } {
                assert_eq!(out[h].as_ref().err().map(|e| e.as_str()), Some("MAC check failed"), "{tier:?}");
            }
        }
    }
}
