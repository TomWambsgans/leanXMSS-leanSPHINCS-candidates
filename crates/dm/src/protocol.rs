//! One party's run: PCG expansion, masked inputs, GMW evaluation level by level (secure up to
//! additive attacks), then `Π_Vrfy`, then the outputs.
//!
//! Every opened authenticated value joins a running MAC check (a random combination drawn after the
//! opening, from a coin committed alongside it), settled by a commit-then-reveal of the `σ` shares;
//! the same message carries each party's hash of every broadcast it has seen, so equivocation
//! aborts too. Nothing derived from secrets is opened before the MAC checks of everything it
//! depends on: the `F_Mul` openings are settled before the check values are opened, these before
//! the outputs, and a last round of view hashes lets the honest parties output together. Coins are
//! commit-reveal over BLAKE2s; commitments and coins are bound to the session.

use std::sync::Arc;

use mpc::circuit::{Op, Program};

use crate::aes::{Prf, Stream};
use crate::auth::Auth;
use crate::bits::BitVec;
use crate::dealer::{Dealer, Tier};
use crate::gf::{Acc, F, sel};
use crate::mdpf;
use crate::net::{Abort, Link, Reader, Recorder, Stats, Tamper, Writer, abort};
use crate::par;
use crate::pcg;
use crate::ring::Pair;
use crate::verify::{self, Opened, TripleCoeffs, WordSum};

pub const KIND_IN: u64 = 1;
pub const KIND_OUT: u64 = 2;
pub const KIND_PI: u64 = 3;

#[derive(Clone, Debug, Default)]
pub struct Phase {
    pub name: &'static str,
    /// CPU seconds of this party (all its threads), the dealer's work excluded.
    pub cpu: f64,
    /// CPU seconds spent drawing the simulated setup (dealer keys, triples, masks).
    pub setup: f64,
    pub stats: Stats,
}

#[derive(Clone, Debug, Default)]
pub struct Counts {
    pub ands: u64,
    pub triples: u64,
    pub fmul: u64,
    pub fuv: u64,
    /// Points of all FUV domains evaluated (fused with the PIR answers).
    pub fuv_points: u64,
    pub pcg_keys: u64,
    pub pcg_key_bytes: u64,
    pub fuv_key_bytes: u64,
    pub sumcheck_rounds: u64,
    /// Sumcheck positions streamed: batches times positions, per pass over the batches; and the
    /// CPU seconds of these passes.
    pub sumcheck_streamed: u64,
    pub sumcheck_stream_cpu: f64,
    /// CPU seconds of the PCG's transforms (the `N log N` part), and of the public matrices.
    pub pcg_fft_cpu: f64,
    /// Database transforms computed (each over `N` slots).
    pub db_transforms: u64,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub phases: Vec<Phase>,
    pub counts: Counts,
}

impl Report {
    pub fn total(&self) -> Phase {
        self.phases.iter().fold(Phase { name: "total", ..Default::default() }, |a, p| Phase {
            name: "total",
            cpu: a.cpu + p.cpu,
            setup: a.setup + p.setup,
            stats: a.stats + p.stats,
        })
    }
}

pub struct Output {
    pub out: Vec<Vec<u64>>,
    pub report: Report,
}

pub struct Party<'a> {
    pub me: usize,
    link: Link,
    dealer: &'a Dealer,
    delta: F,
    session: u128,
    rng: Stream,
    seen: [blake2s::Hasher; 3],
    acc_m: F,
    acc_y: F,
    ctr: u64,
    fmul_next: u64,
    report: Report,
    mark: (f64, f64, Stats),
    setup: f64,
}

fn diff(a: Stats, b: Stats) -> Stats {
    Stats { rounds: a.rounds - b.rounds, bytes_sent: a.bytes_sent - b.bytes_sent }
}

const CH: usize = 4096;

impl<'a> Party<'a> {
    pub fn new(dealer: &'a Dealer, me: usize, link: Link, seed: u128) -> Self {
        Self {
            me,
            link,
            dealer,
            delta: dealer.mac_key(me),
            session: dealer.cfg.session,
            rng: Stream::labeled(seed, &[me as u64]),
            seen: Default::default(),
            acc_m: F::ZERO,
            acc_y: F::ZERO,
            ctr: 0,
            fmul_next: 0,
            report: Report::default(),
            mark: (par::cpu_seconds(), 0.0, Stats::default()),
            setup: 0.0,
        }
    }

    fn phase(&mut self, name: &'static str) {
        let cpu = par::cpu_seconds();
        let (c0, s0, st0) = self.mark;
        let setup = self.setup - s0;
        self.report.phases.push(Phase { name, cpu: cpu - c0 - setup, setup, stats: diff(self.link.stats, st0) });
        self.mark = (cpu, self.setup, self.link.stats);
    }

    fn deal<R>(&mut self, f: impl FnOnce(&Dealer) -> R) -> R {
        let t = par::cpu_seconds();
        let r = f(self.dealer);
        self.setup += par::cpu_seconds() - t;
        r
    }

    fn commitment(&self, who: usize, ctr: u64, data: &[u8]) -> [u8; 32] {
        let mut h = blake2s::Hasher::new();
        h.update(b"dm commit").update(&self.session.to_le_bytes()).update(&(who as u64).to_le_bytes()).update(&ctr.to_le_bytes()).update(data);
        h.finalize()
    }

    fn bcast(&mut self, msg: Vec<u8>) -> Result<[Vec<u8>; 3], Abort> {
        let all = self.link.broadcast(msg)?;
        for j in 0..3 {
            self.seen[j].update(&(all[j].len() as u64).to_le_bytes()).update(&all[j]);
        }
        Ok(all)
    }

    fn snapshot(&self) -> Vec<u8> {
        self.seen.iter().flat_map(|h| h.finalize()).collect()
    }

    /// Broadcasts `extra` with a commitment to a fresh coin share, then opens the shares: returns
    /// everyone's `extra` (all of the same length) and the coin. With `check_view`, the first
    /// message also carries this party's hash of all broadcasts so far, which must match everyone's.
    fn coin_with(&mut self, extra: Vec<u8>, check_view: bool) -> Result<([Vec<u8>; 3], u128), Abort> {
        self.ctr += 1;
        let ctr = self.ctr;
        let s = self.rng.next_u128().to_le_bytes();
        let snap = if check_view { self.snapshot() } else { vec![] };
        let header = 32 + snap.len();
        let len = header + extra.len();
        let mut msg = Vec::with_capacity(len);
        msg.extend_from_slice(&self.commitment(self.me, ctr, &s));
        msg.extend_from_slice(&snap);
        msg.extend_from_slice(&extra);
        drop(extra);
        let mut all = self.bcast(msg)?;
        let mut coms = [[0u8; 32]; 3];
        for j in 0..3 {
            if all[j].len() != len {
                return abort("malformed message");
            }
            coms[j] = all[j][..32].try_into().unwrap();
            if all[j][32..header] != snap[..] {
                return abort("inconsistent broadcasts");
            }
            all[j].drain(..header);
        }
        let reveal = self.bcast(s.to_vec())?;
        let mut h = blake2s::Hasher::new();
        h.update(b"dm coin").update(&self.session.to_le_bytes()).update(&ctr.to_le_bytes());
        for j in 0..3 {
            if reveal[j].len() != 16 || self.commitment(j, ctr, &reveal[j]) != coms[j] {
                return abort("bad coin opening");
            }
            h.update(&reveal[j]);
        }
        Ok((all, u128::from_le_bytes(h.finalize()[..16].try_into().unwrap())))
    }

    fn coin(&mut self, check_view: bool) -> Result<u128, Abort> {
        Ok(self.coin_with(vec![], check_view)?.1)
    }

    /// Adds `sum chi_k (m_k, y_k)` to the MAC check, `chi` from `seed`.
    fn absorb(&mut self, seed: u128, opened: impl Iterator<Item = F>, macs: impl Iterator<Item = F>) {
        let mut chi = Stream::new(seed);
        let (mut am, mut ay) = (Acc::default(), Acc::default());
        for (y, m) in opened.zip(macs) {
            let c = chi.next_u128();
            am.add_mul(c, m.0);
            ay.add_mul(c, y.0);
        }
        self.acc_m += am.reduce();
        self.acc_y += ay.reduce();
    }

    /// Opens authenticated values (value shares `vals`, MAC shares `macs`), their MACs checked by the
    /// next [`Party::mac_check`]: 2 rounds.
    fn open(&mut self, what: &'static str, vals: &[F], macs: &[F]) -> Result<Vec<F>, Abort> {
        let mut msg = Vec::with_capacity(16 * vals.len());
        for v in vals {
            msg.extend_from_slice(&v.0.to_le_bytes());
        }
        self.open_raw(what, msg, macs)
    }

    /// [`Party::open`] of value shares already serialized.
    fn open_raw(&mut self, what: &'static str, msg: Vec<u8>, macs: &[F]) -> Result<Vec<F>, Abort> {
        let n = macs.len();
        assert_eq!(msg.len(), 16 * n);
        let (all, seed) = self.coin_with(msg, false)?;
        let mut opened = vec![F::ZERO; n];
        for m in &all {
            let mut r = Reader::new(m);
            for (o, x) in opened.iter_mut().zip(r.u128s(n)?) {
                *o += F(x);
            }
            r.end()?;
        }
        drop(all);
        self.link.note_opened(what, opened.iter().map(|x| x.0));
        self.absorb(seed, opened.iter().copied(), macs.iter().copied());
        Ok(opened)
    }

    /// Opens authenticated bits, packed in words, their MAC shares (per lane; inactive lanes
    /// ignored) fetched from the setup word by word.
    fn open_bits(&mut self, what: &'static str, words: &[u64], lanes: &[u64], macs: &(dyn Fn(&Dealer, usize) -> [F; 64] + Sync)) -> Result<Vec<u64>, Abort> {
        let n = words.len();
        let (all, seed) = self.coin_with(Writer::default().u64s(words).done(), false)?;
        let mut opened = vec![0u64; n];
        for m in &all {
            let mut r = Reader::new(m);
            for (k, x) in r.u64s(n)?.into_iter().enumerate() {
                opened[k] ^= x & lanes[k];
            }
            r.end()?;
        }
        self.link.note_opened(what, opened.iter().map(|&x| u128::from(x)));
        let mut chi = Stream::new(seed);
        let (mut am, mut ay) = (Acc::default(), Acc::default());
        for k in 0..n {
            let m = self.deal(|d| macs(d, k));
            for l in (0..64).filter(|l| (lanes[k] >> l) & 1 == 1) {
                let c = chi.next_u128();
                am.add_mul(c, m[l].0);
                ay.add_mul(c, u128::from((opened[k] >> l) & 1));
            }
        }
        self.acc_m += am.reduce();
        self.acc_y += ay.reduce();
        Ok(opened)
    }

    /// Settles the MAC check of everything opened so far, and compares the views: 2 rounds.
    fn mac_check(&mut self) -> Result<(), Abort> {
        self.ctr += 1;
        let ctr = self.ctr;
        let sigma = self.acc_m + self.delta * self.acc_y;
        let snap = self.snapshot();
        let mut data = sigma.0.to_le_bytes().to_vec();
        data.extend_from_slice(&self.rng.next_u128().to_le_bytes());
        let coms = self.bcast(self.commitment(self.me, ctr, &data).to_vec())?;
        let all = self.bcast([data.clone(), snap.clone()].concat())?;
        let mut sum = F::ZERO;
        for j in 0..3 {
            let mut r = Reader::new(&all[j]);
            let d = r.bytes(32)?;
            if coms[j].len() != 32 || self.commitment(j, ctr, d) != coms[j].as_slice() {
                return abort("bad MAC-check opening");
            }
            if r.bytes(snap.len())? != snap.as_slice() {
                return abort("inconsistent broadcasts");
            }
            r.end()?;
            sum += F(u128::from_le_bytes(d[..16].try_into().unwrap()));
        }
        if sum != F::ZERO {
            return abort("MAC check failed");
        }
        self.acc_m = F::ZERO;
        self.acc_y = F::ZERO;
        Ok(())
    }

    /// The last round: everyone's hash of the whole transcript, which must match. A party that
    /// aborted earlier sends nothing, so the others abort too.
    fn agree(&mut self) -> Result<(), Abort> {
        let snap = self.snapshot();
        let all = self.bcast(snap.clone())?;
        if all.iter().any(|m| *m != snap) {
            return abort("no agreement to output");
        }
        Ok(())
    }

    /// Authenticated products `x_k y_k` (`pair(k)`, `k < n`) with the dealer's triples (Beaver),
    /// summed over consecutive groups of `group`: 2 rounds, MACs checked later.
    fn fmul_sums(&mut self, n: usize, group: usize, pair: impl Fn(usize) -> (Auth, Auth) + Sync) -> Result<Vec<Auth>, Abort> {
        assert!(n.is_multiple_of(group) && CH.is_multiple_of(group));
        let (base, me, dealer, delta) = (self.fmul_next, self.me, self.dealer, self.delta);
        self.fmul_next += n as u64;
        self.report.counts.fmul += n as u64;
        let range = |ci: usize| ci * CH..((ci + 1) * CH).min(n);
        let triples = |ci: usize| -> (Vec<[Auth; 3]>, f64) {
            let t0 = par::thread_cpu();
            let t = range(ci).map(|k| dealer.fmul(base + k as u64, me)).collect();
            (t, par::thread_cpu() - t0)
        };
        // ε = x + A and δ = y + B, opened.
        let parts = par::map(n.div_ceil(CH), |ci| {
            let (t, s) = triples(ci);
            let mut msg = Vec::with_capacity(32 * t.len());
            let mut macs = Vec::with_capacity(2 * t.len());
            for (k, [a, b, _]) in range(ci).zip(&t) {
                let (x, y) = pair(k);
                msg.extend_from_slice(&(x.v + a.v).0.to_le_bytes());
                msg.extend_from_slice(&(y.v + b.v).0.to_le_bytes());
                macs.extend([x.m + a.m, y.m + b.m]);
            }
            (msg, macs, s)
        });
        let (mut msg, mut macs) = (Vec::with_capacity(32 * n), Vec::with_capacity(2 * n));
        for (v, m, s) in parts {
            msg.extend(v);
            macs.extend(m);
            self.setup += s;
        }
        let opened = self.open_raw("F_Mul", msg, &macs)?;
        drop(macs);
        // xy = C + ε B + δ A + εδ.
        let parts = par::map(n.div_ceil(CH), |ci| {
            let (t, s) = triples(ci);
            let mut sums = vec![Auth::default(); range(ci).len() / group];
            for (k, [a, b, c]) in range(ci).zip(&t) {
                let (eps, del) = (opened[2 * k], opened[2 * k + 1]);
                sums[(k - ci * CH) / group] += (*c + b.scale(eps) + a.scale(del)).add_const(eps * del, me, delta);
            }
            (sums, s)
        });
        let mut out = Vec::with_capacity(n / group);
        for (z, s) in parts {
            out.extend(z);
            self.setup += s;
        }
        Ok(out)
    }

    /// GMW over the triple pool: one round per AND level. Returns the opened `d`, `e` of every
    /// gate (`[gate][word]`) and the output shares.
    fn eval(&mut self, prog: &Program, pool: &[BitVec; 3], instances: usize, lanes: &[u64], inputs: &[Vec<u64>]) -> Result<Evaluated, Abort> {
        let words = lanes.len();
        let me = self.me;
        let mut secs = vec![0u64; prog.n_sec_slots * words];
        let (mut dv, mut ev) = (vec![0u64; prog.n_and * words], vec![0u64; prog.n_and * words]);
        let mut g0 = 0;
        for step in &prog.steps {
            for op in &step.local {
                for w in 0..words {
                    match *op {
                        Op::SecIn { dst, input } => secs[dst as usize * words + w] = inputs[input as usize][w],
                        Op::SecXor { dst, a, b } => secs[dst as usize * words + w] = secs[a as usize * words + w] ^ secs[b as usize * words + w],
                        Op::SecNot { dst, a } => secs[dst as usize * words + w] = secs[a as usize * words + w] ^ if me == 0 { lanes[w] } else { 0 },
                        _ => panic!("all-secret circuits only"),
                    }
                }
            }
            if step.ands.is_empty() {
                continue;
            }
            let n = step.ands.len();
            let mut msg = Vec::with_capacity(2 * n * words);
            let mut trip = Vec::with_capacity(n * words);
            for (k, g) in step.ands.iter().enumerate() {
                for w in 0..words {
                    let tau = (g0 + k) * instances + 64 * w;
                    let t = [0, 1, 2].map(|c| pool[c].get64(tau) & lanes[w]);
                    msg.push((secs[g.a as usize * words + w] ^ t[0]) & lanes[w]);
                    msg.push((secs[g.b as usize * words + w] ^ t[1]) & lanes[w]);
                    trip.push(t);
                }
            }
            let all = self.bcast(Writer::default().u64s(&msg).done())?;
            let mut opened = vec![0u64; 2 * n * words];
            for m in &all {
                let mut r = Reader::new(m);
                for (o, x) in opened.iter_mut().zip(r.u64s(2 * n * words)?) {
                    *o ^= x;
                }
                r.end()?;
            }
            let mut z = vec![0u64; n * words];
            for k in 0..n {
                for w in 0..words {
                    let i = k * words + w;
                    let (d, e) = (opened[2 * i] & lanes[w], opened[2 * i + 1] & lanes[w]);
                    let [a, b, c] = trip[i];
                    dv[(g0 + k) * words + w] = d;
                    ev[(g0 + k) * words + w] = e;
                    z[i] = c ^ (d & b) ^ (e & a) ^ if me == 0 { d & e } else { 0 };
                }
            }
            for (k, g) in step.ands.iter().enumerate() {
                secs[g.dst as usize * words..(g.dst as usize + 1) * words].copy_from_slice(&z[k * words..(k + 1) * words]);
            }
            g0 += n;
        }
        let outs = prog.outputs.iter().map(|&s| secs[s as usize * words..(s as usize + 1) * words].to_vec()).collect();
        Ok((dv, ev, outs))
    }
}

/// The opened `d`, `e` (`[gate][word]`) and the output shares.
type Evaluated = (Vec<u64>, Vec<u64>, Vec<Vec<u64>>);

/// A query of the PIR: (group, vector, block, entry).
#[derive(Clone, Copy)]
struct Query {
    g: usize,
    v: usize,
    b: usize,
    idx: usize,
}

/// A query's answers: per column (balancing column, batch of the group, coordinate), and the
/// balancing unit vector.
struct Answer {
    r: Vec<Auth>,
    u2: Vec<Auth>,
}

impl Party<'_> {
    /// Evaluates the FUVs of every query of `group` against the databases of one vector, fused
    /// with the answers.
    fn answer_vector(&mut self, group: usize, v: usize, dbs: &[&[Pair<u128>]]) -> Vec<Answer> {
        let (dealer, me) = (self.dealer, self.me);
        let cfg = &dealer.cfg;
        let p = &cfg.pcg;
        let (blk, bal) = (p.blk(), cfg.balance);
        let entries = p.entries(p.vector(v));
        let parts = par::map(p.t(), |b| {
            let (rows, width, flat) = verify::block_rows(dbs, b * blk, blk, bal);
            let mut sc = mdpf::Scratch::default();
            let (mut out, mut setup, mut key_bytes) = (Vec::with_capacity(entries), 0.0, 0u64);
            for idx in 0..entries {
                let t0 = par::thread_cpu();
                let (row, col) = dealer.fuv_keys(group, v, b, idx, me);
                setup += par::thread_cpu() - t0;
                key_bytes += (row.bytes() + col.as_ref().map_or(0, |c| c.bytes())) as u64;
                let (val, mac) = mdpf::answer(&row, rows, width, &flat, &mut sc);
                let r = val.iter().zip(&mac).map(|(&v, &m)| Auth { v: F(v), m }).collect();
                let u2 = col.map_or(vec![], |c| mdpf::eval_all(&c, bal, &mut sc).into_iter().map(|(u, m)| Auth { v: F(u128::from(u)), m }).collect());
                out.push(Answer { r, u2 });
            }
            (out, setup, key_bytes, rows as u64)
        });
        let mut out = Vec::with_capacity(entries * p.t());
        for (a, s, kb, rows) in parts {
            self.setup += s;
            self.report.counts.fuv += a.len() as u64 * if bal > 1 { 2 } else { 1 };
            self.report.counts.fuv_points += a.len() as u64 * (rows + if bal > 1 { bal as u64 } else { 0 });
            self.report.counts.fuv_key_bytes += kb;
            out.extend(a);
        }
        out
    }

    /// The payload shares of the queries, per batch of each query's group.
    fn payloads(&mut self, queries: &[Query]) -> Vec<[Auth; 2]> {
        let me = self.me;
        self.deal(|d| queries.iter().flat_map(|qr| d.cfg.group_batches(qr.g).map(move |bt| d.payload(bt, qr.v, qr.b, qr.idx, me))).collect())
    }

    /// `Π_Vrfy` with `DB = G^T a_T` (plain and SSD tiers): `⟪<a_T, G e>⟫` through the PIR, the
    /// groups' `F_Mul`s sharing rounds `chunk` groups at a time.
    fn pir_direct(&mut self, tc: &TripleCoeffs) -> Result<Auth, Abort> {
        let cfg = &self.dealer.cfg;
        let p = cfg.pcg;
        let (bal, t2) = (cfg.balance, p.triples());
        let mut total = Auth::default();
        let groups: Vec<usize> = (0..cfg.groups()).collect();
        for chunk in groups.chunks(cfg.chunk.min(groups.len())) {
            let (mut answers, mut queries) = (vec![], vec![]);
            for &g in chunk {
                let batches: Vec<usize> = cfg.group_batches(g).collect();
                let coefs: Vec<Vec<Pair<u64>>> = batches.iter().map(|&bt| pcg::matrix(&p, cfg.matrix_seed(bt))).collect();
                for v in 0..p.n_vectors() {
                    let vec = p.vector(v);
                    let comp = verify::component(vec);
                    let dbs: Vec<Vec<Pair<u128>>> = batches.iter().zip(&coefs).map(|(&bt, coef)| verify::db_vector(&p, coef, &tc.range(comp, bt * t2, t2), vec)).collect();
                    self.report.counts.db_transforms += dbs.len() as u64;
                    self.phase("verify: databases");
                    let refs: Vec<&[Pair<u128>]> = dbs.iter().map(|d| d.as_slice()).collect();
                    answers.extend(self.answer_vector(g, v, &refs));
                    self.phase("verify: PIR answers");
                    for b in 0..p.t() {
                        for idx in 0..p.entries(vec) {
                            queries.push(Query { g, v, b, idx });
                        }
                    }
                }
            }
            // Balancing (plain, one batch per group): `DB[alpha]_s = sum_c u2_c R_{c,s}`.
            let entry: Vec<Auth> = if bal > 1 {
                let per = 2 * bal;
                self.fmul_sums(answers.len() * per, bal, |k| {
                    let (a, s, c) = (&answers[k / per], (k % per) / bal, k % bal);
                    (a.u2[c], a.r[c * 2 + s])
                })?
            } else {
                answers.iter().flat_map(|a| a.r.iter().copied()).collect()
            };
            drop(answers);
            self.phase("verify: FMul (balancing)");
            // Payloads: `sum_batch sum_s beta_{batch,s} DB_batch[alpha]_s`.
            let pays = self.payloads(&queries);
            let prod = self.fmul_sums(entry.len(), 1, |k| (pays[k / 2][k % 2], entry[k]))?;
            total = prod.into_iter().fold(total, |s, x| s + x);
            self.phase("verify: FMul (payloads)");
        }
        Ok(total)
    }
}

/// The public part of the check and the masks' authenticated part.
struct Check {
    lambda: F,
    gl: Auth,
}

pub fn run(dealer: &Dealer, prog: &Program, instances: usize, me: usize, link: Link, input: &[Vec<u64>], seed: u128) -> Result<Output, Abort> {
    dealer.claim(me)?;
    let cfg = &dealer.cfg;
    let p = cfg.pcg;
    let q = cfg.batches;
    let words = instances.div_ceil(64);
    let lanes: Vec<u64> = (0..words).map(|w| if instances - 64 * w >= 64 { !0 } else { (1u64 << (instances - 64 * w)) - 1 }).collect();
    let mut party = Party::new(dealer, me, link, seed);

    // The ST-PCG expansion, batch by batch (the public matrices are recomputed when verifying).
    let mut pool: [BitVec; 3] = Default::default();
    for batch in 0..q {
        let noise = party.deal(|d| d.noise(batch, me));
        let t0 = par::cpu_seconds();
        let coef = pcg::matrix(&p, cfg.matrix_seed(batch));
        party.report.counts.pcg_fft_cpu += par::cpu_seconds() - t0;
        let key_bytes = std::sync::atomic::AtomicU64::new(0);
        let (tr, s, fft_cpu) = pcg::expand(&p, me, &noise, &coef, &|id| {
            let k = dealer.pcg_key(batch, me, id);
            key_bytes.fetch_add(k.bytes() as u64, std::sync::atomic::Ordering::Relaxed);
            k
        });
        party.setup += s;
        party.report.counts.pcg_fft_cpu += fft_cpu;
        party.report.counts.pcg_keys += (8 * p.c * p.c * p.t() * p.t()) as u64;
        party.report.counts.pcg_key_bytes += key_bytes.into_inner();
        pool[0].append(&tr.a, tr.len);
        pool[1].append(&tr.b, tr.len);
        pool[2].append(&tr.c, tr.len);
    }
    party.report.counts.triples = pool[0].len as u64;
    party.report.counts.ands = (prog.n_and * instances) as u64;
    assert!(prog.n_and * instances <= pool[0].len, "not enough triples: {} needed, {} made", prog.n_and * instances, pool[0].len);
    party.phase("PCG expansion");

    // Inputs: each party owns its share of every input bit, masked with an authenticated mask (the
    // masks' MAC shares stay with the setup until the check needs them).
    let n_in = prog.n_sec_inputs;
    let in_mask = |d: &Dealer, i: usize, o: usize, w: usize| d.mask_word(KIND_IN, ((i * 3 + o) * words + w) as u64, Some(o), me);
    let mut my_hat = vec![0u64; n_in * words];
    let mut rv = vec![0u64; n_in * words];
    party.deal(|d| {
        for i in 0..n_in {
            for w in 0..words {
                for o in 0..3 {
                    let mw = in_mask(d, i, o, w);
                    if let Some(x) = mw.clear {
                        my_hat[i * words + w] = (input[i][w] ^ x) & lanes[w];
                    }
                    rv[i * words + w] ^= mw.v;
                }
            }
        }
    });
    let all = party.bcast(Writer::default().u64s(&my_hat).done())?;
    let mut in_hat = vec![0u64; n_in * words];
    for m in &all {
        let mut r = Reader::new(m);
        for (o, x) in in_hat.iter_mut().zip(r.u64s(n_in * words)?) {
            *o ^= x;
        }
        r.end()?;
    }
    for (k, h) in in_hat.iter_mut().enumerate() {
        *h &= lanes[k % words];
    }
    let in_share: Vec<Vec<u64>> = (0..n_in).map(|i| (0..words).map(|w| (if me == 0 { in_hat[i * words + w] } else { 0 }) ^ rv[i * words + w]).collect()).collect();
    party.phase("inputs");

    // Evaluation, then the outputs, masked.
    let (dv, ev, outs) = party.eval(prog, &pool, instances, &lanes, &in_share)?;
    let n_out = prog.outputs.len();
    let out_mask = |d: &Dealer, k: usize| d.mask_word(KIND_OUT, k as u64, None, me);
    let out_v: Vec<u64> = party.deal(|d| (0..n_out * words).map(|k| out_mask(d, k).v).collect());
    let msg: Vec<u64> = (0..n_out * words).map(|k| (outs[k / words][k % words] ^ out_v[k]) & lanes[k % words]).collect();
    let all = party.bcast(Writer::default().u64s(&msg).done())?;
    let mut out_hat = vec![0u64; n_out * words];
    for m in &all {
        let mut r = Reader::new(m);
        for (k, x) in r.u64s(n_out * words)?.into_iter().enumerate() {
            out_hat[k] ^= x & lanes[k % words];
        }
        r.end()?;
    }
    party.phase("evaluation");

    // Π_Vrfy: random coefficients drawn once every view is fixed and consistent.
    let prf = Prf::new(party.coin(true)?);
    let coeffs = verify::coefficients(prog, &prf);
    let bcoef = verify::instance_coeffs(&prf, instances);
    let ws = WordSum::new(&bcoef);
    let opened = Opened { words, d: &dv, e: &ev, out_hat: &out_hat, in_hat: &in_hat, lanes: &lanes };
    let lambda = verify::lambda(&coeffs, &ws, &opened);
    // `Γ_local`: the masks' part of the check, from their value shares and MAC shares (fetched
    // from the setup a chunk of words at a time).
    let mut gl = Auth::default();
    let mut add_masks = |coef: F, w: usize, v: u64, m: &[F; 64]| {
        let mut acc = Acc::default();
        let mut val = 0u128;
        for l in (0..64).filter(|l| (lanes[w] >> l) & 1 == 1) {
            let k = coef * bcoef[64 * w + l];
            val ^= sel(v >> l, k.0);
            acc.add_mul(k.0, m[l].0);
        }
        gl += Auth { v: F(val), m: acc.reduce() };
    };
    for start in (0..n_in * words).step_by(CH) {
        let ks = start..(start + CH).min(n_in * words);
        let macs: Vec<[F; 64]> = party.deal(|d| ks.clone().map(|k| (0..3).fold([F::ZERO; 64], |acc, o| std::array::from_fn(|l| acc[l] + in_mask(d, k / words, o, k % words).m[l]))).collect());
        for (k, m) in ks.zip(&macs) {
            add_masks(coeffs.beta_in[k / words], k % words, rv[k], m);
        }
    }
    for start in (0..n_out * words).step_by(CH) {
        let ks = start..(start + CH).min(n_out * words);
        let macs: Vec<[F; 64]> = party.deal(|d| ks.clone().map(|k| out_mask(d, k).m).collect());
        for (k, m) in ks.zip(&macs) {
            add_masks(coeffs.a_out[k / words], k % words, out_v[k], m);
        }
    }
    let check = Check { lambda, gl };
    let tc = TripleCoeffs { c: &coeffs, b: &bcoef, o: &opened };
    party.phase("verify: coefficients");

    let delta = party.delta;
    let zero_checks: Vec<Auth> = match cfg.tier {
        Tier::Plain | Tier::Ssd => {
            let e = party.pir_direct(&tc)?;
            vec![(e + check.gl).add_const(check.lambda, me, delta)]
        }
        Tier::Dssd => sumcheck(&mut party, &check, &tc, &pool)?,
    };
    // The F_Mul openings' MACs are settled before any check value is opened: an error in them
    // would otherwise make a check value reveal secrets.
    party.mac_check()?;
    let vals: Vec<F> = zero_checks.iter().map(|a| a.v).collect();
    let macs: Vec<F> = zero_checks.iter().map(|a| a.m).collect();
    let opened_checks = party.open("checks", &vals, &macs)?;
    party.mac_check()?;
    if opened_checks.iter().any(|&u| u != F::ZERO) {
        return abort("verification failed: a party cheated in the evaluation");
    }
    party.phase("verify: open and check");

    // Outputs: the masks are revealed only now; then everyone confirms the whole transcript.
    let out_lanes: Vec<u64> = (0..n_out * words).map(|k| lanes[k % words]).collect();
    let r = party.open_bits("output masks", &out_v, &out_lanes, &|d: &Dealer, k: usize| out_mask(d, k).m)?;
    party.mac_check()?;
    party.agree()?;
    let out = (0..n_out).map(|o| (0..words).map(|w| out_hat[o * words + w] ^ r[o * words + w]).collect()).collect();
    party.phase("outputs");
    Ok(Output { out, report: party.report })
}

/// The DSSD tier (Appendix D): a sumcheck (FLIOP for inner products) with a distributed prover
/// whose round messages are masked by authenticated randomness. It folds the batches first, then
/// the positions, streaming the batches (memory: a few vectors of one batch's size), so the final
/// query `Q`, the tensor of the position challenges, is shared by all batches: `DB_g = G_g^T Q`
/// per group. Returns the checks, all 0.
fn sumcheck(party: &mut Party, check: &Check, tc: &TripleCoeffs, pool: &[BitVec; 3]) -> Result<Vec<Auth>, Abort> {
    let (dealer, me, delta) = (party.dealer, party.me, party.delta);
    let cfg = &dealer.cfg;
    let p = cfg.pcg;
    let (q, t2) = (cfg.batches, p.triples());
    let q2 = q.next_power_of_two();
    let len = (3 * t2).next_power_of_two();
    let (kb, ki) = (q2.trailing_zeros() as usize, len.trailing_zeros() as usize);
    // Batch `rho`, positions `i0..`: the coefficients and this party's triple shares.
    let fetch = |rho: usize, i0: usize, ta: &mut [F], tb: &mut [F]| {
        let mut k = 0;
        while k < ta.len() {
            let i = i0 + k;
            if i >= 3 * t2 {
                ta[k..].fill(F::ZERO);
                tb[k..].fill(F::ZERO);
                break;
            }
            let (comp, off) = (i / t2, i % t2);
            let run = (t2 - off).min(ta.len() - k);
            let tau = rho * t2 + off;
            tc.fill(comp, tau, &mut ta[k..k + run]);
            for x in 0..run {
                tb[k + x] = F(u128::from(pool[comp].bit(tau + x)));
            }
            k += run;
        }
    };
    let (mut a, mut b) = (vec![], vec![]);
    let (mut rb, mut ri) = (vec![], vec![]);
    let mut checks = vec![];
    let mut prev: Option<([Auth; 3], F)> = None;
    for j in 0..kb + ki {
        let t0 = par::cpu_seconds();
        let h = if j < kb {
            party.report.counts.sumcheck_streamed += (q * len) as u64;
            let h = verify::batch_round(q, q2, len, &rb, &fetch);
            party.report.counts.sumcheck_stream_cpu += par::cpu_seconds() - t0;
            h
        } else {
            if j == kb {
                party.report.counts.sumcheck_streamed += (q * len) as u64;
                let (fa, fb) = verify::batch_fold(q, len, &rb, &fetch);
                party.report.counts.sumcheck_stream_cpu += par::cpu_seconds() - t0;
                (a, b) = (vec![fa], vec![fb]);
            }
            verify::round_poly(&a, &b)
        };
        let mask: [Auth; 3] = party.deal(|d| [0, 1, 2].map(|k| d.rand(KIND_PI, (3 * j + k) as u64, me)));
        let mine: Vec<u128> = (0..3).map(|k| (h[k] + mask[k].v).0).collect();
        let (all, coin) = party.coin_with(Writer::default().u128s(&mine).done(), false)?;
        let mut hat = [F::ZERO; 3];
        for m in &all {
            let mut r = Reader::new(m);
            for (k, x) in r.u128s(3)?.into_iter().enumerate() {
                hat[k] += F(x);
            }
            r.end()?;
        }
        let r = F(coin);
        // ⟪h_j⟫ = π̂_j - ⟪π̃_j⟫.
        let hj: [Auth; 3] = [0, 1, 2].map(|k| mask[k].add_const(hat[k], me, delta));
        let sum01 = hj[1] + hj[2];
        checks.push(match prev {
            None => (sum01 + check.gl).add_const(check.lambda, me, delta),
            Some((hp, rp)) => sum01 + hp[0] + hp[1].scale(rp) + hp[2].scale(rp * rp),
        });
        prev = Some((hj, r));
        if j < kb {
            rb.push(r);
        } else {
            ri.push(r);
            a = a.iter().map(|v| verify::fold(v, r)).collect();
            b = b.iter().map(|v| verify::fold(v, r)).collect();
        }
    }
    party.report.counts.sumcheck_rounds += (kb + ki) as u64;
    party.phase("verify: sumcheck");
    let a_final = a[0][0];
    drop((a, b));
    let (weights, qv) = (verify::tensor(&rb), verify::tensor(&ri));
    // Per group, one database per vector for all its batches; the payloads combined first.
    let mut pairs = vec![];
    for g in 0..cfg.groups() {
        let coef = pcg::matrix(&p, cfg.matrix_seed(g * cfg.group));
        for v in 0..p.n_vectors() {
            let vec = p.vector(v);
            let comp = verify::component(vec);
            let db = verify::db_vector(&p, &coef, &qv[comp * t2..(comp + 1) * t2], vec);
            party.report.counts.db_transforms += 1;
            party.phase("verify: databases");
            let ans = party.answer_vector(g, v, &[&db]);
            party.phase("verify: PIR answers");
            let queries: Vec<Query> = (0..p.t()).flat_map(|b| (0..p.entries(vec)).map(move |idx| Query { g, v, b, idx })).collect();
            let pays = party.payloads(&queries);
            let nb = cfg.group_batches(g).len();
            for (k, an) in ans.iter().enumerate() {
                for s in 0..2 {
                    let omega = cfg.group_batches(g).enumerate().fold(Auth::default(), |acc, (j, bt)| acc + pays[k * nb + j][s].scale(weights[bt]));
                    pairs.push((omega, an.r[s]));
                }
            }
        }
    }
    let prod = party.fmul_sums(pairs.len(), 1, |k| pairs[k])?;
    party.phase("verify: FMul (payloads)");
    // The claim `a* b*`, `b* = sum_rho W(rho) <Q, G e_rho>` read through the PIR.
    let b_star = prod.into_iter().fold(Auth::default(), |s, x| s + x);
    let (hp, rp) = prev.unwrap();
    checks.push(b_star.scale(a_final) + hp[0] + hp[1].scale(rp) + hp[2].scale(rp * rp));
    Ok(checks)
}

/// How a session runs: worker threads per party, and the test hooks that play corrupt parties.
pub struct Options {
    pub threads: usize,
    pub tamper: [Option<Tamper>; 3],
    /// Rushing parties (at most one) read each round's messages before sending theirs.
    pub rush: [bool; 3],
    pub record: [Option<Recorder>; 3],
    /// Each party's own coins (default: from the operating system).
    pub coins: Option<[u128; 3]>,
}

impl Default for Options {
    fn default() -> Self {
        Self { threads: 1, tamper: [None, None, None], rush: [false; 3], record: [None, None, None], coins: None }
    }
}

/// Runs the three parties on threads.
pub fn session(dealer: Arc<Dealer>, prog: Arc<Program>, instances: usize, inputs: [Vec<Vec<u64>>; 3], mut opts: Options) -> [Result<Output, Abort>; 3] {
    assert!(opts.rush.iter().filter(|&&r| r).count() <= 1, "at most one rushing party");
    let links = crate::net::ring();
    let handles: Vec<_> = links
        .into_iter()
        .zip(inputs)
        .enumerate()
        .map(|(me, (mut link, input))| {
            link.tamper = opts.tamper[me].take();
            link.rush = opts.rush[me];
            link.record = opts.record[me].take();
            let (dealer, prog, threads) = (dealer.clone(), prog.clone(), opts.threads);
            let seed = opts.coins.map_or_else(|| u128::from_le_bytes(mpc::prf::os_random::<16>()), |c| c[me]);
            std::thread::spawn(move || {
                par::set_threads(threads);
                run(&dealer, &prog, instances, me, link, &input, seed)
            })
        })
        .collect();
    let mut out = handles.into_iter().map(|h| h.join().unwrap());
    std::array::from_fn(|_| out.next().unwrap())
}
