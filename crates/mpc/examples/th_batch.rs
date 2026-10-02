//! Times one batch of `Th` on secret inputs in MPC: evaluation, verification, opening.
//! `cargo run --release -p mpc --example th_batch -- <instances> <steps>`

use std::time::Instant;

use mpc::blake2s_circuit::{split_prefixes, th_circuit};
use mpc::engine::Shares;
use mpc::engine::Party;
use mpc::net::ring;
use mpc::session::{establish, random_keys, share};

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().unwrap()).collect();
    let n = args.first().copied().unwrap_or(1 << 14);
    let steps = args.get(1).copied().unwrap_or(1);
    let prefixes: Vec<[u8; 32]> = (0..n as u32)
        .map(|k| {
            let mut p = [0u8; 32];
            p[0] = 1;
            p[12..16].copy_from_slice(&k.to_le_bytes());
            p[16..].copy_from_slice(&[0x42; 16]);
            p
        })
        .collect();
    let (layout, pub_in) = split_prefixes(&prefixes);
    let prog = th_circuit(&layout).compile();
    println!("n = {n}, steps = {steps}: {} ANDs per hash, depth {}", prog.n_and, prog.depth);
    let words = n.div_ceil(64);
    let secrets: Vec<[Shares; 3]> = (0..128).map(|_| share(&vec![0x0123_4567_89ab_cdefu64; words])).collect();
    let t = Instant::now();
    let keys = random_keys();
    let out: Vec<_> = std::thread::scope(|scope| {
        let handles: Vec<_> = ring()
            .into_iter()
            .map(|mut link| {
                let (secrets, prog, pub_in) = (&secrets, &prog, &pub_in);
                scope.spawn(move || -> Result<_, mpc::net::Abort> {
                    let i = link.id;
                    let session = establish(&mut link)?;
                    let mut p = Party::new(link, keys[i], keys[(i + 2) % 3], session, n);
                    let mut x: Vec<Shares> = secrets.iter().map(|s| s[i].clone()).collect();
                    let t0 = Instant::now();
                    for _ in 0..steps {
                        x = p.eval(prog, pub_in, &x)?;
                    }
                    let t1 = Instant::now();
                    p.verify()?;
                    let t2 = Instant::now();
                    p.open(&x)?;
                    Ok((t1 - t0, t2 - t1, p.link.stats))
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let (e, v, s) = out[0].as_ref().unwrap();
    println!("eval {e:.2?}, verify {v:.2?}, total {:.2?}; party 0 sent {:.1} MB in {} rounds", t.elapsed(), s.bytes_sent as f64 / 1e6, s.rounds);
    let ands = (prog.n_and * n * steps) as f64;
    println!("{:.3} bits per AND per party", s.bytes_sent as f64 * 8.0 / ands);
}
