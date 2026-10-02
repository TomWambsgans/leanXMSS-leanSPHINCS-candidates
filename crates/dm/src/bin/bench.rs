//! Benchmarks of the three tiers on all-secret BLAKE2s compressions (14,714 ANDs each).
//!
//! `cargo run --release -p dm --bin bench -- [scale] [threads]`: end-to-end runs per tier at paper
//! parameters (FOLEAGE `c = 5`, `t = 27`), `n = 11 + s` (plain) or `n = 10 + s` with `q = 3`
//! batches ((D)SSD), for `s = scale` and `scale + 1` (default 1), each on a fresh setup; then a
//! cost model calibrated on the larger runs (and checked by predicting them from the smaller ones)
//! for one FORS instance (24,696 compressions) and keygen (786,432), on the cheapest layout with
//! `n <= 16` and groups of at most 27 batches that fits the memory budget. Per party, the busiest;
//! CPU in single-core seconds, the simulated setup (dealer) excluded.

use std::sync::Arc;
use std::time::Instant;

use dm::aes::Stream;
use dm::dealer::{Config, Dealer, GROUP_MAX, Tier};
use dm::gf::F;
use dm::mdpf;
use dm::net::{LAN, Stats, WAN};
use dm::pcg::Params;
use dm::protocol::{Options, Phase, Report, session};
use mpc::blake2s_circuit::{Word, compress};
use mpc::circuit::{Builder, Program};

const AND_PER_COMPRESSION: f64 = 14_714.0;
/// The paper's assumed throughput of a 3-party maliciously secure F̂ multiplication.
const PAPER_FMUL_PER_S: f64 = 500.0;
/// The largest ring for `c = 5`, `t = 27` over F4 (ePrint 2025/892's folding attack).
const N_MAX: usize = 16;
/// Memory per party the layouts must fit in.
const BUDGET: f64 = 45e9;
/// Bytes of one `F_Mul` in flight: its two openings (sent, copied, received twice, summed) and MACs.
const FMUL_BYTES: f64 = 288.0;

fn circuit() -> Program {
    let mut b = Builder::new();
    let h: [Word; 8] = std::array::from_fn(|_| std::array::from_fn(|_| b.sec_input()));
    let m: [Word; 16] = std::array::from_fn(|_| std::array::from_fn(|_| b.sec_input()));
    for w in &compress(&mut b, &h, &m, 64, true) {
        for &bit in w {
            b.output(bit);
        }
    }
    b.compile()
}

fn size(bytes: f64) -> String {
    match bytes {
        b if b >= 1e12 => format!("{:.1} TB", b / 1e12),
        b if b >= 1e9 => format!("{:.1} GB", b / 1e9),
        b if b >= 1e6 => format!("{:.0} MB", b / 1e6),
        b if b >= 1e3 => format!("{:.0} KB", b / 1e3),
        b => format!("{b:.0} B"),
    }
}

fn hours(s: f64) -> String {
    if s >= 3600.0 { format!("{:.1} h", s / 3600.0) } else { format!("{:.0} s", s) }
}

/// The process's peak resident memory so far.
fn peak_rss() -> f64 {
    #[repr(C)]
    struct Rusage {
        times: [i64; 4],
        maxrss: i64,
        rest: [i64; 13],
    }
    unsafe extern "C" {
        fn getrusage(who: i32, usage: *mut Rusage) -> i32;
    }
    let mut r = Rusage { times: [0; 4], maxrss: 0, rest: [0; 13] };
    // SAFETY: `r` is a valid, writable rusage (18 64-bit fields on the supported targets).
    unsafe { getrusage(0, &mut r) };
    // Bytes on macOS, kilobytes on Linux.
    if cfg!(target_os = "macos") { r.maxrss as f64 } else { r.maxrss as f64 * 1024.0 }
}

/// The phases, merged by name, in order of first appearance.
fn phases(r: &Report) -> Vec<(&'static str, f64, f64, Stats)> {
    let mut out: Vec<(&'static str, f64, f64, Stats)> = vec![];
    for p in &r.phases {
        match out.iter_mut().find(|x| x.0 == p.name) {
            Some(x) => {
                x.1 += p.cpu;
                x.2 += p.setup;
                x.3 = x.3 + p.stats;
            }
            None => out.push((p.name, p.cpu, p.setup, p.stats)),
        }
    }
    out
}

fn cpu_of(r: &Report, names: &[&str]) -> f64 {
    r.phases.iter().filter(|p| names.contains(&p.name)).map(|p| p.cpu).sum()
}

/// A layout: ring `3^n`, batches, batches per group, and groups per `F_Mul` round.
#[derive(Clone, Copy, Debug)]
struct Shape {
    n: usize,
    batches: usize,
    group: usize,
    chunk: usize,
}

impl Shape {
    fn groups(&self) -> usize {
        self.batches.div_ceil(self.group)
    }

    fn chunks(&self) -> usize {
        self.groups().div_ceil(self.chunk)
    }
}

/// Operation counts of one party for a tier and layout.
struct Ops {
    ands: f64,
    triples: f64,
    pcg_lin: f64,
    pcg_fft: f64,
    db: f64,
    points: f64,
    width: f64,
    fmul: f64,
    streamed: f64,
    positions: f64,
    rounds: u64,
}

fn ops(tier: Tier, s: Shape, ands: f64) -> Ops {
    let p = Params::paper(s.n);
    let (nn, w, blk) = (p.slots() as f64, p.weight() as f64, p.blk() as f64);
    let (batches, groups, group) = (s.batches as f64, s.groups() as f64, s.group as f64);
    let len = (6 * p.slots()).next_power_of_two();
    let (db, points, width, fmul) = match tier {
        Tier::Plain => (batches * 60.0, batches * w * ((blk / 8.0).ceil() + 8.0), 16.0, batches * w * 18.0),
        Tier::Ssd => (batches * 60.0, groups * w * blk, 2.0 * group, batches * w * 2.0),
        Tier::Dssd => (groups * 60.0, groups * w * blk, 2.0, groups * w * 2.0),
    };
    let kb = s.batches.next_power_of_two().trailing_zeros() as u64;
    let rho = kb + len.trailing_zeros() as u64;
    // Verification rounds: coins, F_Mul (per chunk of groups), MAC checks, check and output
    // openings, the final agreement.
    let rounds = match tier {
        Tier::Plain => 13 + 4 * s.chunks() as u64,
        Tier::Ssd => 13 + 2 * s.chunks() as u64,
        Tier::Dssd => 15 + 2 * rho,
    };
    Ops {
        ands,
        triples: batches * 2.0 * nn,
        pcg_lin: batches * nn,
        pcg_fft: batches * nn * s.n as f64,
        db: db * nn * s.n as f64,
        points,
        width,
        fmul,
        streamed: if tier == Tier::Dssd { (kb + 1) as f64 * batches * len as f64 } else { 0.0 },
        positions: if tier == Tier::Dssd { len as f64 } else { 0.0 },
        rounds,
    }
}

/// Peak memory of one party (bytes), from the implementation's large buffers.
fn memory(tier: Tier, s: Shape, comps: f64, prog: &Program, threads: f64) -> f64 {
    let p = Params::paper(s.n);
    let (nn, t2, w) = (p.slots() as f64, p.triples() as f64, p.weight() as f64);
    let ands = comps * AND_PER_COMPRESSION;
    let words = (comps / 64.0).ceil();
    // Triple pool (3 bits per triple), the opened d and e, input and output words.
    let common = 3.0 * s.batches as f64 * t2 / 8.0 + 2.0 * ands / 8.0 + 6.0 * (768.0 + 256.0) * words * 8.0;
    let pcg = 2.0 * nn * 16.0 + threads * 50.0 * p.leaves() as f64 * 64.0;
    let eval = prog.n_sec_slots as f64 * words * 8.0 + 4.0 * prog.steps.iter().map(|st| st.ands.len()).max().unwrap_or(0) as f64 * words * 24.0;
    let chunk = s.chunk as f64;
    let verify = match tier {
        Tier::Plain => chunk * w * (24.0 * 32.0 + 16.0 * FMUL_BYTES) + nn * 48.0 + t2 * 16.0,
        Tier::Ssd => {
            let g = s.group as f64;
            chunk * w * 2.0 * g * (32.0 + FMUL_BYTES) + g * nn * 48.0 + t2 * 16.0
        }
        Tier::Dssd => {
            let len = (3 * p.triples()).next_power_of_two() as f64;
            let half = s.batches.next_power_of_two() as f64 / 2.0;
            4.0 * len * 16.0 + nn * 48.0 + s.groups() as f64 * w * 2.0 * (64.0 + FMUL_BYTES) + threads * 4.0 * half * 8192.0 * 16.0
        }
    };
    common + pcg.max(eval).max(verify)
}

/// The one-time setup material of one party: PCG keys, FUV keys, `F_Mul` triples, `F_Rand` masks.
fn setup_bytes(tier: Tier, s: Shape, comps: f64) -> f64 {
    let p = Params::paper(s.n);
    let pcg = s.batches as f64 * (8 * p.c * p.c * p.t() * p.t()) as f64 * (80 + 48 * p.depth()) as f64;
    let key = |n: usize| {
        let (rows, cols) = mdpf::grid(n);
        (rows * 33 + 4 * (cols * 16 + cols.div_ceil(8))) as f64
    };
    let (queries, bal) = if tier == Tier::Plain { (s.batches as f64 * p.weight() as f64, 8) } else { (s.groups() as f64 * p.weight() as f64, 1) };
    let fuv = queries * (key(p.blk().div_ceil(bal)) + if bal > 1 { key(bal) } else { 0.0 });
    let fmul = ops(tier, s, 0.0).fmul * 96.0;
    // Input masks of all three owners and output masks: a value bit and a MAC share per bit.
    let masks = comps * (3.0 * 768.0 + 256.0) * (16.0 + 1.0 / 8.0);
    pcg + fuv + fmul + masks
}

/// Single-core seconds per unit, from a measured run.
struct Units {
    pcg_lin: f64,
    pcg_fft: f64,
    eval: f64,
    coeff: f64,
    db: f64,
    /// Per point at the run's width, and the run's width.
    point: f64,
    width: f64,
    fmul: f64,
    stream: f64,
    position: f64,
    fixed: f64,
}

/// Per point of the fused FUV evaluation and PIR answer: `alpha + beta * width` (single core).
fn point_model() -> (f64, f64) {
    let mut rng = Stream::new(1);
    let n = 1 << 15;
    let time = |width: usize, rng: &mut Stream| {
        let db: Vec<u128> = (0..n * width).map(|_| rng.next_u128()).collect();
        let key = mdpf::keygen(n, 5, F(3), 9, 0);
        let mut sc = mdpf::Scratch::default();
        let reps = (40_000_000 / (n * (width + 4))).max(2);
        let t = Instant::now();
        for _ in 0..reps {
            std::hint::black_box(mdpf::answer(&key, n, width, &db, &mut sc));
        }
        t.elapsed().as_secs_f64() / (reps * n) as f64
    };
    let (t2, t16) = (time(2, &mut rng), time(16, &mut rng));
    let beta = (t16 - t2) / 14.0;
    (t2 - 2.0 * beta, beta)
}

struct Run {
    tier: Tier,
    n: usize,
    q: usize,
    instances: usize,
    wall: f64,
    rss: f64,
    report: Report,
}

fn tier_of(name: &str) -> Tier {
    match name {
        "Plain" => Tier::Plain,
        "Ssd" => Tier::Ssd,
        _ => Tier::Dssd,
    }
}

/// One measured run, in this process (`--run`): prints its report for the parent.
fn run_here(tier: Tier, n: usize, q: usize, threads: usize) {
    let prog = Arc::new(circuit());
    let pcg = Params::paper(n);
    let instances = (q * pcg.triples() / prog.n_and) / 64 * 64;
    let cfg = Config::new(pcg, tier, q, u128::from_le_bytes(mpc::prf::os_random::<16>()));
    let words = instances.div_ceil(64);
    let mut s = Stream::new(3);
    let inputs: [Vec<Vec<u64>>; 3] = std::array::from_fn(|_| (0..prog.n_sec_inputs).map(|_| (0..words).map(|_| s.next_u64()).collect()).collect());
    let t = Instant::now();
    let res = session(Arc::new(Dealer::new(cfg)), prog.clone(), instances, inputs, Options { threads, ..Default::default() });
    let wall = t.elapsed().as_secs_f64();
    let reports: Vec<Report> = res.into_iter().map(|r| r.expect("honest run").report).collect();
    let report = reports.into_iter().max_by_key(|r| r.total().stats.bytes_sent).unwrap();
    for p in &report.phases {
        println!("P\t{}\t{}\t{}\t{}\t{}", p.name, p.cpu, p.setup, p.stats.bytes_sent, p.stats.rounds);
    }
    let c = &report.counts;
    println!(
        "C\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        c.ands, c.triples, c.fmul, c.fuv, c.fuv_points, c.pcg_keys, c.pcg_key_bytes, c.fuv_key_bytes, c.sumcheck_rounds, c.sumcheck_streamed, c.sumcheck_stream_cpu, c.pcg_fft_cpu, c.db_transforms
    );
    println!("R\t{instances}\t{wall}\t{}", peak_rss());
}

/// A measured run in a child process, so that its peak memory is its own.
fn run(tier: Tier, n: usize, q: usize, threads: usize) -> Run {
    let exe = std::env::current_exe().unwrap();
    let out = std::process::Command::new(exe).args(["--run", &format!("{tier:?}"), &n.to_string(), &q.to_string(), &threads.to_string()]).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let (mut report, mut instances, mut wall, mut rss) = (Report::default(), 0, 0.0, 0.0);
    for line in String::from_utf8(out.stdout).unwrap().lines() {
        let f: Vec<&str> = line.split('\t').collect();
        let num = |i: usize| f[i].parse::<f64>().unwrap();
        match f[0] {
            "P" => report.phases.push(Phase { name: Box::leak(f[1].to_string().into_boxed_str()), cpu: num(2), setup: num(3), stats: Stats { bytes_sent: num(4) as u64, rounds: num(5) as u64 } }),
            "C" => {
                let c = &mut report.counts;
                let u = |i: usize| num(i) as u64;
                (c.ands, c.triples, c.fmul, c.fuv, c.fuv_points, c.pcg_keys, c.pcg_key_bytes, c.fuv_key_bytes) = (u(1), u(2), u(3), u(4), u(5), u(6), u(7), u(8));
                (c.sumcheck_rounds, c.sumcheck_streamed, c.sumcheck_stream_cpu, c.pcg_fft_cpu, c.db_transforms) = (u(9), u(10), num(11), num(12), u(13));
            }
            "R" => (instances, wall, rss) = (num(1) as usize, num(2), num(3)),
            _ => {}
        }
    }
    Run { tier, n, q, instances, wall, rss, report }
}

fn units(r: &Run) -> Units {
    let c = &r.report.counts;
    let p = Params::paper(r.n);
    let (nn, n) = (p.slots() as f64, r.n as f64);
    let q = r.q as f64;
    let pcg = cpu_of(&r.report, &["PCG expansion"]);
    let len = (6 * p.slots()).next_power_of_two() as f64;
    let sum = cpu_of(&r.report, &["verify: sumcheck"]);
    Units {
        pcg_lin: (pcg - c.pcg_fft_cpu) / (q * nn),
        pcg_fft: c.pcg_fft_cpu / (q * nn * n),
        eval: cpu_of(&r.report, &["inputs", "evaluation"]) / c.ands as f64,
        coeff: cpu_of(&r.report, &["verify: coefficients"]) / c.triples as f64,
        db: cpu_of(&r.report, &["verify: databases"]) / (c.db_transforms as f64 * nn * n),
        point: cpu_of(&r.report, &["verify: PIR answers"]) / c.fuv_points as f64,
        width: match r.tier {
            Tier::Plain => 16.0,
            Tier::Ssd => 2.0 * q,
            Tier::Dssd => 2.0,
        },
        fmul: cpu_of(&r.report, &["verify: FMul (balancing)", "verify: FMul (payloads)"]) / c.fmul.max(1) as f64,
        stream: if r.tier == Tier::Dssd { c.sumcheck_stream_cpu / c.sumcheck_streamed as f64 } else { 0.0 },
        position: if r.tier == Tier::Dssd { (sum - c.sumcheck_stream_cpu) / len } else { 0.0 },
        fixed: cpu_of(&r.report, &["verify: open and check", "outputs"]),
    }
}

/// The measured (semi-honest, authentication, verification) CPU of a run.
fn measured(r: &Run) -> [f64; 3] {
    [
        cpu_of(&r.report, &["PCG expansion", "inputs", "evaluation"]),
        cpu_of(&r.report, &["verify: databases", "verify: PIR answers", "verify: FMul (balancing)", "verify: FMul (payloads)"]),
        cpu_of(&r.report, &["verify: coefficients", "verify: sumcheck", "verify: open and check", "outputs"]),
    ]
}

/// The evaluation rounds of BGIN19 on the same circuits (one per AND level).
fn eval_rounds(compressions: f64) -> u64 {
    if compressions < 100_000.0 { 2_600 } else { 2_500 }
}

/// Predicted (semi-honest, authentication, verification) single-core seconds and traffic of one
/// party.
fn predict(u: &Units, model: (f64, f64), o: &Ops, compressions: f64) -> ([f64; 3], f64) {
    let semi = u.pcg_lin * o.pcg_lin + u.pcg_fft * o.pcg_fft + u.eval * o.ands;
    let point = u.point * (model.0 + model.1 * o.width) / (model.0 + model.1 * u.width);
    let auth = u.db * o.db + point * o.points + u.fmul * o.fmul;
    let verif = u.coeff * o.triples + u.stream * o.streamed + u.position * o.positions + u.fixed;
    // Bytes to both other parties: d and e per AND, masked inputs and outputs, output masks, F_Mul
    // openings, sumcheck messages and the constant-size coins and checks.
    let bytes = o.ands * 0.5 + compressions * 2.0 * (768.0 + 256.0 + 256.0) / 8.0 + o.fmul * 64.0 + o.rounds as f64 * 2.0 * 96.0;
    ([semi, auth, verif], bytes)
}

/// The cheapest layout of a workload that fits the memory budget (CPU plus `F_Mul` at 500/s).
fn layout(tier: Tier, u: &Units, model: (f64, f64), comps: f64, prog: &Program, threads: f64) -> Option<Shape> {
    let ands = comps * AND_PER_COMPRESSION;
    let mut best: Option<(f64, Shape)> = None;
    for n in 8..=N_MAX {
        let batches = (ands / Params::paper(n).triples() as f64).ceil() as usize;
        let group = if tier == Tier::Plain { 1 } else { batches.min(GROUP_MAX) };
        let groups = batches.div_ceil(group);
        // The most groups per F_Mul round that fit.
        let Some(chunk) = (1..=groups).rev().find(|&c| memory(tier, Shape { n, batches, group, chunk: c }, comps, prog, threads) <= BUDGET) else { continue };
        let s = Shape { n, batches, group, chunk };
        let o = ops(tier, s, ands);
        let (t, _) = predict(u, model, &o, comps);
        // CPU, with F_Mul at the paper's rate: the dealer's triples hide its real cost.
        let total: f64 = t.iter().sum::<f64>() + o.fmul / PAPER_FMUL_PER_S;
        if best.is_none_or(|(b, _)| total < b) {
            best = Some((total, s));
        }
    }
    best.map(|(_, s)| s)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(|s| s.as_str()) == Some("--run") {
        let num = |i: usize| args[i].parse::<usize>().unwrap();
        return run_here(tier_of(&args[2]), num(3), num(4), num(5));
    }
    let scale: usize = args.get(1).map_or(1, |a| a.parse().unwrap());
    let threads: usize = args.get(2).map_or(5, |a| a.parse().unwrap());
    let prog = Arc::new(circuit());
    println!("BGHIN26 prototype: 3 parties, up to 2 malicious; MACs and checks over GF(2^128); FOLEAGE PCG over F4, c = 5, t = 27");
    println!("hardware AES {}, carry-less multiply {}, {threads} threads per party\n", dm::aes::HW_AES, mpc::gf128::CLMUL);
    let model = point_model();
    println!("FUV + PIR answer per point: {:.2} ns + {:.2} ns per F̂ column (single core)\n", model.0 * 1e9, model.1 * 1e9);
    let at = |s: usize| -> Vec<Run> { [(Tier::Plain, 11 + s, 1), (Tier::Ssd, 10 + s, 3), (Tier::Dssd, 10 + s, 3)].into_iter().map(|(t, n, q)| run(t, n, q, threads)).collect() };
    let small = at(scale);
    let runs = at(scale + 1);
    for r in &runs {
        let c = &r.report.counts;
        println!(
            "{:?}: n = {}, q = {}, {} compressions ({} ANDs of {} triples), wall {:.1} s; {} FUV over {:.2e} points, {} FMul; per party FUV keys {}, PCG keys {}",
            r.tier, r.n, r.q, r.instances, c.ands, c.triples, r.wall, c.fuv, c.fuv_points as f64, c.fmul, size(c.fuv_key_bytes as f64), size(c.pcg_key_bytes as f64)
        );
        for (name, cpu, setup, st) in phases(&r.report) {
            println!("  {name:<26} {cpu:>8.2} s cpu {setup:>7.2} s dealer {:>10} {:>4} rounds", size(st.bytes_sent as f64), st.rounds);
        }
        let t = r.report.total();
        println!("  {:<26} {:>8.2} s cpu {:>7.2} s dealer {:>10} {:>4} rounds\n", "total", t.cpu, t.setup, size(t.stats.bytes_sent as f64), t.stats.rounds);
    }
    println!("Model check: the larger runs predicted from the smaller ones (semi-honest / authentication / verification CPU), and memory:");
    for (sm, big) in small.iter().zip(&runs) {
        let shape = Shape { n: big.n, batches: big.q, group: if big.tier == Tier::Plain { 1 } else { big.q }, chunk: usize::MAX };
        let ands = big.report.counts.ands as f64;
        let (pred, _) = predict(&units(sm), model, &ops(big.tier, shape, ands), big.instances as f64);
        let meas = measured(big);
        let mem = memory(big.tier, Shape { chunk: 1, ..shape }, big.instances as f64, &prog, threads as f64);
        println!(
            "  {:<5} n={}: predicted {:.2} / {:.2} / {:.2} s, measured {:.2} / {:.2} / {:.2} s; memory 3 x {} modelled, {} measured",
            format!("{:?}", big.tier),
            big.n,
            pred[0],
            pred[1],
            pred[2],
            meas[0],
            meas[1],
            meas[2],
            size(mem),
            size(big.rss)
        );
    }
    println!();

    // The paper's 3-party per-party totals at 3^20 ANDs (Table 3): semi-honest + authentication + verification.
    let paper = |t: Tier| match t {
        Tier::Plain => 3114.0 + 160_000.0 + 4.1,
        Tier::Ssd => 462.0 + 43_580.0 + 4.1,
        Tier::Dssd => 462.0 + 16_452.0 + 20.5,
    };
    let paper_ands = 3f64.powi(20);
    println!("Extrapolated, per party (single-core CPU; F_Mul with the dealer's triples, and at the paper's 500/s), on the cheapest layout within {}:", size(BUDGET));
    println!(
        "{:<11} {:<6} {:<19} {:>9} {:>9} {:>8} {:>9} {:>11} {:>9} {:>9} {:>9} {:>6} {:>8} {:>8} {:>8}",
        "workload", "tier", "layout", "semi-hon.", "auth/PIR", "verify", "total", "+FMul@500/s", "paper", "online", "setup", "rounds", "LAN", "WAN", "memory"
    );
    for (name, comps) in [("FORS inst.", 24_696.0), ("keygen", 786_432.0)] {
        let ands = comps * AND_PER_COMPRESSION;
        for r in &runs {
            let u = units(r);
            let Some(s) = layout(r.tier, &u, model, comps, &prog, 16.0) else {
                println!("{name:<11} {:?}: no layout fits {}", r.tier, size(BUDGET));
                continue;
            };
            let o = ops(r.tier, s, ands);
            let ([semi, auth, verif], bytes) = predict(&u, model, &o, comps);
            let total = semi + auth + verif;
            let st = Stats { rounds: o.rounds + eval_rounds(comps), bytes_sent: bytes as u64 };
            println!(
                "{:<11} {:<6} {:<19} {:>9} {:>9} {:>8} {:>9} {:>11} {:>9} {:>9} {:>9} {:>6} {:>8} {:>8} {:>8}",
                name,
                format!("{:?}", r.tier),
                format!("n={} {}x{} /{}", s.n, s.groups(), s.group, s.chunks()),
                hours(semi),
                hours(auth),
                hours(verif),
                hours(total),
                hours(total + o.fmul / PAPER_FMUL_PER_S),
                hours(paper(r.tier) * ands / paper_ands),
                size(bytes),
                size(setup_bytes(r.tier, s, comps)),
                format!("+{}", o.rounds),
                format!("{:.1} s", LAN.seconds(st)),
                format!("{:.0} s", WAN.seconds(st)),
                size(memory(r.tier, s, comps, &prog, 16.0)),
            );
        }
    }
    println!("\nlayout: ring 3^n, groups x batches per group (positions, and for DSSD the matrix, shared within a group; plain: 1), / F_Mul rounds.");
    println!("online: traffic sent by the party during the protocol. setup: its one-time material (PCG and FUV keys, F_Mul triples, F_Rand");
    println!("  masks), here from the simulated dealer; generating it without a dealer is not costed. memory: the party's peak, modelled.");
    println!("rounds: verification only; the evaluation adds one per AND level, as in BGIN19 (about 2,600 for a FORS instance, 2,500 for keygen).");
    println!("LAN/WAN: network time of the online traffic, all rounds included (latency x rounds + bytes / bandwidth), compute excluded.");
    println!("BGIN19 (3-of-4, honest majority), online traffic only, its own setup excluded too: 42 MB per FORS instance, 1.33 GB for keygen per operator.");
}
