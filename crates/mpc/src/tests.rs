//! End-to-end tests of the MPC: correctness against the clear evaluation, and cheating parties.

use crate::blake2s_circuit::{Word, add2, add3, split_prefixes, th_circuit};
use crate::circuit::{Builder, Program};
use crate::engine::{Cheat, Shares};
use crate::net::{Abort, Fault, Stats};
use crate::session::{parties, random_keys, run, share};

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

struct Run {
    outputs: [Result<Vec<Vec<u64>>, Abort>; 3],
    stats: [Stats; 3],
    fault_applied: bool,
}

/// Evaluates `prog` in MPC, verifies, opens; party `bad` cheats as told.
fn mpc(prog: &Program, n: usize, pub_in: &[Vec<u64>], sec_in: &[Vec<u64>], bad: Option<(usize, Option<Fault>, Cheat)>) -> Run {
    let shares: Vec<[Shares; 3]> = sec_in.iter().map(|v| share(v)).collect();
    let mut ps = parties(&random_keys(), [7; 16], n);
    if let Some((i, fault, cheat)) = bad {
        ps[i].link.fault = fault;
        ps[i].cheat = cheat;
    }
    let results = run(ps, |mut p| {
        let mine: Vec<Shares> = shares.iter().map(|s| s[p.id].clone()).collect();
        let mut go = || -> Result<Vec<Vec<u64>>, Abort> {
            let out = p.eval(prog, pub_in, &mine)?;
            p.verify()?;
            p.open(&out)
        };
        let out = go();
        Ok((out, p.link.stats, p.link.fault_applied))
    })
    .map(|r| r.unwrap());
    let fault_applied = results.iter().any(|r| r.2);
    let stats = std::array::from_fn(|i| results[i].1);
    Run { outputs: results.map(|r| r.0), stats, fault_applied }
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

#[test]
fn toy_circuit_matches_clear_evaluation() {
    let prog = toy();
    for n in [1usize, 5, 64, 100] {
        let (pub_in, sec_in) = random_inputs(&prog, n, n as u64);
        let want = clear(&prog, n, &pub_in, &sec_in);
        let run = mpc(&prog, n, &pub_in, &sec_in, None);
        for out in run.outputs {
            assert_eq!(out.unwrap(), want, "n = {n}");
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
    let run = mpc(&prog, n, &pub_in, &sec_in, None);
    let out = run.outputs[1].as_ref().unwrap();
    for k in 0..n {
        let mut input = prefixes[k].to_vec();
        input.extend_from_slice(&secrets[k]);
        let want = blake2s::hash(&input);
        for bit in 0..128 {
            assert_eq!((out[bit][k / 64] >> (k % 64)) & 1, u64::from((want[bit / 8] >> (bit % 8)) & 1));
        }
    }
    // About one bit per AND per party, plus the opening and a proof of a few KB; rounds: the depth
    // plus the proof.
    let s = run.stats[0];
    let and_bytes = (prog.n_and * words * 8) as u64;
    let open_bytes = (128 * words * 8 + 32) as u64;
    assert!(s.bytes_sent >= and_bytes + open_bytes && s.bytes_sent < and_bytes + open_bytes + 4096, "{s:?}, {and_bytes}");
    assert!(s.rounds as usize > prog.depth && (s.rounds as usize) < prog.depth + 64, "{s:?}");
}

/// Every honest party aborts or outputs the right value; never a wrong one.
fn check_no_wrong_output(run: &Run, want: &[Vec<u64>], bad: usize) -> bool {
    let mut aborted = false;
    for (i, out) in run.outputs.iter().enumerate() {
        if i == bad {
            continue;
        }
        match out {
            Ok(v) => assert_eq!(v, want, "an honest party accepted a wrong output"),
            Err(_) => aborted = true,
        }
    }
    aborted
}

#[test]
fn any_flipped_bit_is_caught() {
    let prog = toy();
    let n = 70;
    let (pub_in, sec_in) = random_inputs(&prog, n, 11);
    let want = clear(&prog, n, &pub_in, &sec_in);
    let rounds = mpc(&prog, n, &pub_in, &sec_in, None).stats[0].rounds;
    let mut caught = 0;
    for bad in 0..3 {
        for round in 0..rounds {
            for to_next in [false, true] {
                // Bits in the first 64 instances (AND messages mask the bits past `n`).
                for bit in [0usize, 37, 63] {
                    let fault = Fault { round, to_next, bit };
                    let run = mpc(&prog, n, &pub_in, &sec_in, Some((bad, Some(fault), Cheat::Honest)));
                    let aborted = check_no_wrong_output(&run, &want, bad);
                    assert_eq!(aborted, run.fault_applied, "party {bad}, round {round}, to_next {to_next}, bit {bit}");
                    caught += aborted as usize;
                }
            }
        }
    }
    // Empty messages cannot be flipped; every flipped nonempty message is caught.
    assert!(caught > 100);
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
                    let run = mpc(&prog, n, &pub_in, &sec_in, Some((bad, None, cheat)));
                    assert!(check_no_wrong_output(&run, &want, bad), "undetected: party {bad}, AND {and}, consistent {consistent}");
                    // Both honest parties abort.
                    for (i, out) in run.outputs.iter().enumerate() {
                        if i != bad {
                            assert!(out.is_err(), "honest party {i} accepted");
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
    let prefixes: Vec<[u8; 32]> = (0..n as u32)
        .map(|k| {
            let mut p = [3u8; 32];
            p[12..16].copy_from_slice(&k.to_le_bytes());
            p
        })
        .collect();
    let (layout, pub_in) = split_prefixes(&prefixes);
    let prog = th_circuit(&layout).compile();
    let (_, sec_in) = random_inputs(&prog, n, 13);
    let want = clear(&prog, n, &pub_in, &sec_in);
    let rounds = mpc(&prog, n, &pub_in, &sec_in, None).stats[0].rounds;
    let mut r = rng(14);
    for _ in 0..24 {
        let bad = (r() % 3) as usize;
        let fault = Fault { round: r() % rounds, to_next: r().is_multiple_of(2), bit: r() as usize };
        let run = mpc(&prog, n, &pub_in, &sec_in, Some((bad, Some(fault), Cheat::Honest)));
        let aborted = check_no_wrong_output(&run, &want, bad);
        assert!(aborted || !run.fault_applied || fault.bit % 64 >= n - 64, "an applied flip went unnoticed");
    }
    for bad in 0..3 {
        let cheat = Cheat::FlipAnd { and: (r() as usize) % prog.n_and, bit: r() as usize, consistent: true };
        let run = mpc(&prog, n, &pub_in, &sec_in, Some((bad, None, cheat)));
        assert!(run.outputs.iter().enumerate().all(|(i, o)| i == bad || o.is_err()));
    }
}
