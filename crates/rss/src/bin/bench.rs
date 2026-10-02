//! Benchmarks of the n-party MPC on the keygen ceremony's hashes, for n = 3, 5, 7: per operator
//! (busiest and average) traffic, bits per AND, rounds, CPU, memory; then the ceremony extrapolated
//! linearly from the measured batches: traffic, soundness (union bound over its batches), and LAN
//! and WAN times with the batches in flight that fit an operator's memory.
//!
//! Time model (computation excluded): batches run in waves of `q` at once, `q` as large as
//! [`MEMORY`] allows (every batch in flight holds its transcript and evaluation state; a few verify
//! at a time and hold their statement too); a wave costs its rounds' latency, and the whole
//! ceremony's traffic goes through the busiest operator's link: `waves x rounds x latency +
//! traffic / bandwidth` in lockstep (an upper bound), and `max` of the two terms with the batches
//! perfectly staggered (a lower bound).
//!
//! `cargo run --release -p rss --bin bench -- [fors instances] [chain instances] [n ...]`
//! (defaults 4096, 2048, and n = 3 5 7). All n parties run on this machine, each on its own thread.
//!
//! - FORS leaf: `Th(P, tw, x)` on a secret 16-byte `x` at bytes 32..47, `tw` and `P` public, the
//!   128-bit leaf opened.
//! - WOTS chain: three chained `Th` steps from a secret start, the chain end opened.
//! - Ceremony at lifetime `2^L`: `2^(L-4) * 24 * 1024` leaves and `2^(L-4) * 64` chains, i.e.
//!   `2^(L-4) * (24 * 1024 + 192)` MPC hashes.

use std::sync::{Arc, Barrier, Mutex};
use std::time::Instant;

use mpc::blake2s_circuit::{split_prefixes, th_circuit};
use mpc::circuit::Program;
use rss::engine::{Party, Shares};
use rss::net::{LAN, NetModel, Stats, WAN, network};
use rss::setup::{deal, establish, share};
use rss::structure::Structure;
use rss::verify::{plan, soundness_log2};

/// Memory per operator for the ceremony.
const MEMORY: f64 = 32e9;

#[repr(C)]
struct RUsage {
    utime: [i64; 2],
    stime: [i64; 2],
    rest: [i64; 14],
}

unsafe extern "C" {
    fn getrusage(who: i32, usage: *mut RUsage) -> i32;
}

/// Process CPU seconds (user + system) and peak resident memory in bytes.
fn usage() -> (f64, u64) {
    let mut u = RUsage { utime: [0; 2], stime: [0; 2], rest: [0; 14] };
    // SAFETY: `RUsage` matches `struct rusage` on 64-bit macOS and Linux (two 16-byte timevals,
    // then 14 longs); RUSAGE_SELF = 0.
    assert_eq!(unsafe { getrusage(0, &mut u) }, 0);
    let secs = |t: [i64; 2]| t[0] as f64 + (t[1] & 0xffff_ffff) as f64 * 1e-6;
    let rss = if cfg!(target_os = "macos") { u.rest[0] as u64 } else { u.rest[0] as u64 * 1024 };
    (secs(u.utime) + secs(u.stime), rss)
}

fn size(bytes: f64) -> String {
    match bytes {
        b if b >= 1e9 => format!("{:.1} GB", b / 1e9),
        b if b >= 1e6 => format!("{:.1} MB", b / 1e6),
        b if b >= 1e3 => format!("{:.1} KB", b / 1e3),
        b => format!("{b:.0} B"),
    }
}

/// Public `tw | P` prefixes of `count` instances at chain step (or leaf kind) `step`.
fn prefixes(count: usize, step: u8) -> Vec<[u8; 32]> {
    (0..count as u32)
        .map(|k| {
            let mut p = [0u8; 32];
            p[0] = 1 + step;
            p[12..16].copy_from_slice(&k.to_le_bytes());
            p[16..].copy_from_slice(&[0x42; 16]);
            p
        })
        .collect()
}

/// A circuit, its public inputs, and the `tw | P` prefixes behind them.
type Step = (Program, Vec<Vec<u64>>, Vec<[u8; 32]>);

/// One phase of one party: traffic and wall time.
#[derive(Clone, Copy, Default)]
struct Phase {
    stats: Stats,
    secs: f64,
}

/// A measured batch: per party and phase (eval, verify, open); process CPU per phase; peak memory.
struct Batch {
    instances: usize,
    hashes: usize,
    ands: usize,
    depth: usize,
    phases: Vec<[Phase; 3]>,
    session: Vec<Stats>,
    cpu: [f64; 3],
    peak: u64,
    /// Per party: the transcript, the evaluation state, the check's statement, in bytes.
    transcript: f64,
    state: f64,
    statement: f64,
    /// Dimension-reduction rounds of the check, and log2 of the padded batch.
    check_rounds: usize,
    c: usize,
}

impl Batch {
    fn total(&self, i: usize) -> Stats {
        self.phases[i].iter().fold(self.session[i], |acc, p| acc + p.stats)
    }

    fn busiest(&self) -> usize {
        (0..self.phases.len()).max_by_key(|&i| self.total(i).bytes_sent).unwrap()
    }

    /// Bytes of party `i`'s phase `k`.
    fn bytes(&self, i: usize, k: usize) -> u64 {
        self.phases[i][k].stats.bytes_sent
    }

    fn rounds(&self) -> u64 {
        self.total(0).rounds
    }

    /// Busiest operator's bytes per instance (without the session round).
    fn per_instance(&self) -> f64 {
        let i = self.busiest();
        (self.total(i).bytes_sent - self.session[i].bytes_sent) as f64 / self.instances as f64
    }

    /// Memory per operator with `q` batches in flight: each holds its transcript and state; the share
    /// of them verifying (by rounds), at least one, holds its statement.
    fn memory(&self, q: usize) -> f64 {
        let verifying = ((q as f64 * self.phases[0][1].stats.rounds as f64 / self.rounds() as f64).ceil() as usize + 1).min(q);
        q as f64 * (self.transcript + self.state) + verifying as f64 * self.statement
    }

    /// The batches in flight that fit [`MEMORY`] (at least one), out of `batches`.
    fn in_flight(&self, batches: u64) -> usize {
        let mut q = 1;
        while (q as u64) < batches && self.memory(q + 1) <= MEMORY {
            q += 1;
        }
        q
    }
}

/// Runs `steps` chained `Th` evaluations on `instances` random secrets among `parties` parties, then
/// verifies and opens the 128 outputs; checks them against BLAKE2s.
fn batch(parties: usize, instances: usize, steps: usize) -> Batch {
    let s = Arc::new(Structure::new(parties));
    let keys = deal(&s);
    let progs: Vec<Step> = (0..steps)
        .map(|step| {
            let pre = prefixes(instances, step as u8 + if steps == 1 { 0 } else { 8 });
            let (layout, pub_in) = split_prefixes(&pre);
            (th_circuit(&layout).compile(), pub_in, pre)
        })
        .collect();
    let words = instances.div_ceil(64);
    let secrets: Vec<[u8; 16]> = (0..instances).map(|k| std::array::from_fn(|b| (k * 31 + b * 7) as u8 ^ 0x5c)).collect();
    let sec_in: Vec<Vec<Shares>> = (0..128)
        .map(|bit| {
            let mut v = vec![0u64; words];
            for (k, x) in secrets.iter().enumerate() {
                v[k / 64] |= u64::from((x[bit / 8] >> (bit % 8)) & 1) << (k % 64);
            }
            share(&s, &v)
        })
        .collect();
    let barrier = Barrier::new(parties);
    let marks: Mutex<Vec<f64>> = Mutex::new(vec![]);
    // All parties wait; party 0 reads the process CPU; all wait again.
    let mark = |id: usize| {
        barrier.wait();
        if id == 0 {
            marks.lock().unwrap().push(usage().0);
        }
        barrier.wait();
    };
    let results: Vec<(Stats, [Phase; 3], Vec<Vec<u64>>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = network(parties)
            .into_iter()
            .map(|mut net| {
                let (s, keys, progs, sec_in, mark) = (&s, &keys, &progs, &sec_in, &mark);
                scope.spawn(move || {
                    let i = net.id;
                    let id = establish(&mut net).unwrap();
                    let session = net.stats;
                    let mut p = Party::new(net, s.clone(), keys[i].clone(), id, instances);
                    let mut x: Vec<Shares> = sec_in.iter().map(|v| v[i].clone()).collect();
                    let mut phases = [Phase::default(); 3];
                    let mut last = (p.net.stats, Instant::now());
                    let mut end = |p: &Party, k: usize, phases: &mut [Phase; 3]| {
                        let now = (p.net.stats, Instant::now());
                        phases[k] = Phase { stats: Stats { rounds: now.0.rounds - last.0.rounds, bytes_sent: now.0.bytes_sent - last.0.bytes_sent }, secs: (now.1 - last.1).as_secs_f64() };
                        last = now;
                    };
                    mark(i);
                    for (prog, pub_in, _) in progs {
                        x = p.eval(prog, pub_in, &x).unwrap();
                    }
                    end(&p, 0, &mut phases);
                    mark(i);
                    p.verify().unwrap();
                    end(&p, 1, &mut phases);
                    mark(i);
                    let out = p.open(&x).unwrap();
                    end(&p, 2, &mut phases);
                    mark(i);
                    (session, phases, out)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    // Check a few outputs against BLAKE2s.
    for k in [0, instances / 2, instances - 1] {
        let mut x = secrets[k].to_vec();
        for (_, _, pre) in &progs {
            let mut input = pre[k].to_vec();
            input.extend_from_slice(&x);
            x = blake2s::hash(&input)[..16].to_vec();
        }
        for bit in 0..128 {
            assert_eq!((results[1].2[bit][k / 64] >> (k % 64)) & 1, u64::from((x[bit / 8] >> (bit % 8)) & 1), "instance {k}");
        }
    }
    let m = marks.into_inner().unwrap();
    let (terms, words) = (s.m() as f64, words as f64);
    let ands: usize = progs.iter().map(|p| p.0.n_and).sum();
    let transcript = ands as f64 * words * 3.0 * terms * 8.0;
    let slots = progs.iter().map(|p| p.0.n_sec_slots as f64 * terms + p.0.n_pub_slots as f64).fold(0.0, f64::max);
    let check = plan(ands, instances, transcript as usize, None);
    Batch {
        transcript,
        state: (slots + 2.0 * 128.0 * terms) * words * 8.0,
        statement: check.bytes as f64,
        check_rounds: check.rounds,
        c: instances.next_power_of_two().trailing_zeros() as usize,
        instances,
        hashes: steps,
        ands: progs.iter().map(|p| p.0.n_and).sum(),
        depth: progs.iter().map(|p| p.0.depth).sum(),
        session: results.iter().map(|r| r.0).collect(),
        phases: results.iter().map(|r| r.1).collect(),
        cpu: [m[1] - m[0], m[2] - m[1], m[3] - m[2]],
        peak: usage().1,
    }
}

fn report(parties: usize, b: &Batch) {
    let f = (parties - 1) / 2;
    let n = parties as f64;
    let ands = (b.ands * b.instances) as f64;
    let busy = b.busiest();
    let avg = |k: usize| (0..parties).map(|i| b.bytes(i, k)).sum::<u64>() as f64 / n;
    let wall = |k: usize| b.phases[0][k].secs;
    println!(
        "  batch: {} instances x {} Th ({} ANDs, AND-depth {}): {} rounds",
        b.instances,
        b.hashes,
        b.ands,
        b.depth,
        b.rounds()
    );
    for (k, name) in ["evaluation", "verification", "opening"].iter().enumerate() {
        println!(
            "    {:<13} {:>9} avg, {:>9} busiest; {:>5} rounds; wall {:>6.2} s; CPU {:>6.2} s ({:.1} ns per AND per party)",
            name,
            size(avg(k)),
            size(b.bytes(busy, k) as f64),
            b.phases[0][k].stats.rounds,
            wall(k),
            b.cpu[k],
            b.cpu[k] / ands / n * 1e9
        );
    }
    println!(
        "    AND traffic: {:.4} bits per AND per operator on average ({:.4} = (n - 1) + f over n), {:.4} for the busiest",
        avg(0) * 8.0 / ands,
        (parties - 1 + f) as f64 / n,
        b.bytes(busy, 0) as f64 * 8.0 / ands
    );
    println!(
        "    per party: transcript {}, evaluation state {}, check statement {} ({} of {} rounds streamed); soundness 2^{:.1}",
        size(b.transcript),
        size(b.state),
        size(b.statement),
        plan(b.ands, b.instances, b.transcript as usize, None).streamed,
        b.check_rounds,
        soundness_log2(b.check_rounds, b.c)
    );
    println!("    peak memory of the process (all {parties} parties) so far: {}", size(b.peak as f64));
}

/// The ceremony at lifetime `2^l`, per operator (busiest): leaf and chain batches.
struct Ceremony {
    bytes: f64,
    batches: [u64; 2],
    in_flight: [usize; 2],
    memory: f64,
    /// log2 of the soundness error, union bound over every batch.
    soundness: f64,
}

impl Ceremony {
    fn new(l: u32, leaf: &Batch, chain: &Batch) -> Self {
        let units = 1u64 << (l - 4);
        let (leaves, chains) = (units * 24 * 1024, units * 64);
        let batches = [leaves.div_ceil(leaf.instances as u64), chains.div_ceil(chain.instances as u64)];
        let in_flight = [leaf.in_flight(batches[0]), chain.in_flight(batches[1])];
        let err = |b: &Batch, k: u64| k as f64 * 2f64.powf(soundness_log2(b.check_rounds, b.c));
        Self {
            bytes: leaves as f64 * leaf.per_instance() + chains as f64 * chain.per_instance(),
            batches,
            in_flight,
            memory: leaf.memory(in_flight[0]).max(chain.memory(in_flight[1])),
            soundness: (err(leaf, batches[0]) + err(chain, batches[1])).log2(),
        }
    }

    /// Waves of batches, each paying its rounds' latency, and the traffic: their sum (lockstep, an
    /// upper bound) and their maximum (perfectly staggered, a lower bound).
    fn seconds(&self, m: &NetModel, leaf: &Batch, chain: &Batch) -> (f64, f64) {
        let waves = |k: usize| self.batches[k].div_ceil(self.in_flight[k] as u64);
        let latency = (waves(0) * leaf.rounds() + waves(1) * chain.rounds()) as f64 * m.latency_s;
        let traffic = self.bytes * 8.0 / m.bandwidth_bit_s;
        (latency + traffic, latency.max(traffic))
    }
}

/// `lower-upper`, in one unit.
fn range((upper, lower): (f64, f64)) -> String {
    if upper >= 5400.0 {
        format!("{:.1}-{:.1} h", lower / 3600.0, upper / 3600.0)
    } else if upper >= 120.0 {
        format!("{:.0}-{:.0} min", lower / 60.0, upper / 60.0)
    } else {
        format!("{lower:.0}-{upper:.0} s")
    }
}


fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().unwrap()).collect();
    let leaves = args.first().copied().unwrap_or(4096);
    let chains = args.get(1).copied().unwrap_or(2048);
    let ns: Vec<usize> = if args.len() > 2 { args[2..].to_vec() } else { vec![3, 5, 7] };
    println!("n-party MPC (replicated sharing, collector resharing, sublinear checks), malicious with abort");
    println!(
        "this machine: {} cores; carry-less multiply {}, BLAKE2s batches {}\n",
        std::thread::available_parallelism().map_or(1, |p| p.get()),
        mpc::gf128::CLMUL,
        blake2s::BACKEND
    );
    let mut rows = vec![];
    for &parties in &ns {
        let t = parties.div_ceil(2);
        println!("{t}-of-{parties} (n = {parties}, f = {}): {} terms per party", parties / 2, Structure::new(parties).m());
        println!(" FORS leaves");
        let t0 = Instant::now();
        let leaf = batch(parties, leaves, 1);
        report(parties, &leaf);
        println!(" WOTS chains (3 steps)");
        let chain = batch(parties, chains, 3);
        report(parties, &chain);
        println!("  ({:.1} s)\n", t0.elapsed().as_secs_f64());
        rows.push((parties, leaf, chain));
    }

    println!("Measured, per operator:");
    println!("{:<8} {:>14} {:>14} {:>16} {:>16} {:>14} {:>14}", "", "bits/AND avg", "bits/AND max", "bytes/leaf max", "bytes/chain max", "rounds leaf", "rounds chain");
    for (parties, leaf, chain) in &rows {
        let ands = (leaf.ands * leaf.instances) as f64;
        let n = *parties as f64;
        let avg = (0..*parties).map(|i| leaf.bytes(i, 0)).sum::<u64>() as f64 / n;
        let per = |b: &Batch| {
            let i = b.busiest();
            (b.total(i).bytes_sent - b.session[i].bytes_sent) as f64 / b.instances as f64
        };
        println!(
            "{:<8} {:>14.4} {:>14.4} {:>16.0} {:>16.0} {:>14} {:>14}",
            format!("{}-of-{parties}", parties.div_ceil(2)),
            avg * 8.0 / ands,
            leaf.bytes(leaf.busiest(), 0) as f64 * 8.0 / ands,
            per(leaf),
            per(chain),
            leaf.rounds(),
            chain.rounds()
        );
    }
    println!("{:<8} {:>18} {:>18} {:>18}", "", "CPU eval ns/AND", "CPU verify ns/AND", "CPU open ns/AND");
    for (parties, leaf, _) in &rows {
        let per = |k: usize| leaf.cpu[k] / (leaf.ands * leaf.instances) as f64 / *parties as f64 * 1e9;
        println!("{:<8} {:>18.2} {:>18.2} {:>18.2}", format!("{}-of-{parties}", parties.div_ceil(2)), per(0), per(1), per(2));
    }

    println!("\nKeygen ceremony, per operator (busiest), extrapolated linearly from the batches above:");
    println!("{:<8} {:>12} {:>12} {:>12}   traffic", "", "2^12", "2^14", "2^16");
    for (parties, leaf, chain) in &rows {
        let c: Vec<Ceremony> = [12, 14, 16].iter().map(|&l| Ceremony::new(l, leaf, chain)).collect();
        println!("{:<8} {:>12} {:>12} {:>12}", format!("{}-of-{parties}", parties.div_ceil(2)), size(c[0].bytes), size(c[1].bytes), size(c[2].bytes));
    }
    println!("soundness (union bound over the batches, {leaves}-instance leaf and {chains}-instance chain batches):");
    for (parties, leaf, chain) in &rows {
        let c: Vec<Ceremony> = [12, 14, 16].iter().map(|&l| Ceremony::new(l, leaf, chain)).collect();
        println!(
            "{:<8} {:>12} {:>12} {:>12}   ({} + {} batches at 2^16)",
            format!("{}-of-{parties}", parties.div_ceil(2)),
            format!("2^{:.1}", c[0].soundness),
            format!("2^{:.1}", c[1].soundness),
            format!("2^{:.1}", c[2].soundness),
            c[2].batches[0],
            c[2].batches[1]
        );
    }
    println!("wall time with {:.0} GB per operator (batches in flight: leaf, chain; memory per operator; {} / {}):", MEMORY / 1e9, LAN.name, WAN.name);
    for (parties, leaf, chain) in &rows {
        let cells: Vec<String> = [12, 14, 16]
            .iter()
            .map(|&l| {
                let c = Ceremony::new(l, leaf, chain);
                format!("q {}+{}, {}: {} / {}", c.in_flight[0], c.in_flight[1], size(c.memory), range(c.seconds(&LAN, leaf, chain)), range(c.seconds(&WAN, leaf, chain)))
            })
            .collect();
        println!("{:<8} {}", format!("{}-of-{parties}", parties.div_ceil(2)), cells.join(" | "));
    }
    // The WAN link saturates when one wave's traffic takes as long as its rounds' latency.
    println!("WAN saturation (in-flight leaf batches needed, 50 ms x 100 Mbit/s over the bytes per round of one batch):");
    for (parties, leaf, _) in &rows {
        let per_round = leaf.per_instance() * leaf.instances as f64 / leaf.rounds() as f64;
        let need = WAN.latency_s * WAN.bandwidth_bit_s / 8.0 / per_round;
        let have = leaf.in_flight(u64::MAX);
        println!(
            "{:<8} need {:.0}, fit {} in {:.0} GB ({})",
            format!("{}-of-{parties}", parties.div_ceil(2)),
            need,
            have,
            MEMORY / 1e9,
            if have as f64 >= need { "bandwidth-bound" } else { "latency-bound" }
        );
    }
    println!("CPU per operator for the ceremony (all three phases, measured ns per AND x ANDs):");
    for (parties, leaf, chain) in &rows {
        let ns_per = |b: &Batch| b.cpu.iter().sum::<f64>() / (b.ands * b.instances) as f64 / *parties as f64;
        let cells: Vec<String> = [12u32, 14, 16]
            .iter()
            .map(|&l| {
                let units = 1u64 << (l - 4);
                let secs = (units * 24 * 1024) as f64 * (leaf.ands as f64) * ns_per(leaf) + (units * 64) as f64 * (chain.ands as f64) * ns_per(chain);
                format!("{:.1} core-hours", secs / 3600.0)
            })
            .collect();
        println!("{:<8} {:>20} {:>20} {:>20}", format!("{}-of-{parties}", parties.div_ceil(2)), cells[0], cells[1], cells[2]);
    }
}
