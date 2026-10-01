//! Benchmarks of the 3-of-4 protocol: traffic sent and rounds per operator (the busiest one), wall
//! time measured with all four operators on this machine, and the time on a LAN or a WAN (latency x
//! rounds + traffic / bandwidth, computation excluded).
//!
//! `cargo run --release -p threshold --bin bench -- [b]`: kept subtree of 2^b leaves (default 12, as in
//! the note: about 16 GB of memory and a minute; keygen traffic scales with 2^b, rounds don't).

use std::time::Instant;

use mpc::net::{LAN, Stats, WAN};
use sphincs::*;
use threshold::cluster::{Cluster, Report};
use threshold::protocol::{Mode, grind};

fn size(bytes: u64) -> String {
    match bytes {
        b if b >= 1_000_000_000 => format!("{:.2} GB", b as f64 / 1e9),
        b if b >= 1_000_000 => format!("{:.1} MB", b as f64 / 1e6),
        b if b >= 1_000 => format!("{:.1} KB", b as f64 / 1e3),
        b => format!("{b} B"),
    }
}

/// Prints the phases of the operator that sent the most; returns its total.
fn print(title: &str, secs: f64, report: &Report) -> Stats {
    println!("{title} ({secs:.1} s)");
    let busiest = report.iter().max_by_key(|p| p.iter().map(|x| x.stats.bytes_sent).sum::<u64>()).unwrap();
    let mut total = Stats::default();
    for p in busiest {
        println!("  {:<46} {:>9} {:>5} rounds {:>7.2} s", p.name, size(p.stats.bytes_sent), p.stats.rounds, p.time.as_secs_f64());
        total = total + p.stats;
    }
    total
}

fn main() {
    let b: usize = std::env::args().nth(1).map_or(12, |a| a.parse().unwrap());
    println!("leanSphincs 3-of-4 threshold prototype, kept subtree of 2^{b} leaves; per operator (the busiest)\n");

    let t = Instant::now();
    let (mut cluster, _, report) = Cluster::dkg(b, vec![]).unwrap();
    let dkg = print("DKG", t.elapsed().as_secs_f64(), &report);
    let pk = cluster.ops[0].key().pk;

    let m: Message = [7; 32];
    let t = Instant::now();
    let (sig, _, report) = cluster.sign(&m, Mode::Vanilla).unwrap();
    assert_eq!(verify(&pk, &m, &sig), Ok(()));
    let vanilla = print("\nvanilla signature", t.elapsed().as_secs_f64(), &report);

    let t = Instant::now();
    let (_, report) = cluster.preprocess().unwrap();
    let pre = print("\npreprocessing (the next instance)", t.elapsed().as_secs_f64(), &report);

    let m: Message = [9; 32];
    let t = Instant::now();
    let (sig, _, report) = cluster.sign(&m, Mode::Preprocessed).unwrap();
    assert_eq!(verify(&pk, &m, &sig), Ok(()));
    let online = print("\nonline signature (three operators grinding on one machine)", t.elapsed().as_secs_f64(), &report);

    // Grinding alone, as one operator on its own machine: 2^26 expected tries of 3 compressions.
    let (pp, root) = (pk.public_param, pk.root);
    let (mut tries, t) = (0u64, Instant::now());
    for k in 0..4u64 {
        let target = (k * 0x9e3779b9) % (1 << H);
        tries += u64::from(grind(&pp, &root, &[k as u8; 16], &m, &|idx| idx == target).0) + 1;
    }
    let grind_secs = (1u64 << 26) as f64 * t.elapsed().as_secs_f64() / tries as f64;

    let scale = (1u64 << (12 - b.min(12))) as f64;
    let at12 = |s: Stats| if b == 12 { size(s.bytes_sent) } else { format!("{} (x{scale} at b=12)", size(s.bytes_sent)) };
    let model = |s: Stats| format!("LAN {:.1} s, WAN {:.0} s", LAN.seconds(s), WAN.seconds(s));
    println!("\n{:<26} {:<34} {:<16} network time (no compute)", "", "traffic, rounds", "note");
    println!("{:<26} {:<34} {:<16} {}", "keygen (DKG)", format!("{}, {}", at12(dkg), dkg.rounds), "1.45 GB, 2,500", model(dkg));
    println!("{:<26} {:<34} {:<16} {}", "vanilla signature", format!("{}, {}", size(vanilla.bytes_sent), vanilla.rounds), "45 MB, 2,600", model(vanilla));
    println!("{:<26} {:<34} {:<16} {}", "preprocessing", format!("{}, {}", size(pre.bytes_sent), pre.rounds), "45 MB, 2,600", model(pre));
    println!("{:<26} {:<34} {:<16} {}", "online signature", format!("{}, {}", size(online.bytes_sent), online.rounds), "~1 KB, 2", model(online));
    println!("\ngrinding alone (all cores): {:.0} M compressions/s, {grind_secs:.2} s for the expected 2^26 tries (2.0e8 compressions)", 3.0 * tries as f64 / t.elapsed().as_secs_f64() / 1e6);
}
