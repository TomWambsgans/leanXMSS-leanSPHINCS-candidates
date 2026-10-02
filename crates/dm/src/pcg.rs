//! The sparse-tensored PCG: FOLEAGE's ring-LPN over `F4[Z_3^n]` with regular noise (Bombar et al.,
//! Asiacrypt 2024), turned into Boolean triples by the trace (Li–Xing–Yao–Yuan, Trace-F2-OLE).
//!
//! Each party `i` holds `c` sparse `e_i^j` and `c` sparse `f_i^j`, each with one point in every one
//! of the `t` blocks (the top `tau` trits of the index). With `a_0 = 1` and public random `a_j`,
//! `X = sum_ij a_j e_i^j` and `Y = sum_ij a_j f_i^j` are pseudorandom; in the Fourier domain every
//! slot holds two Boolean triples:
//!   `Tr(X) Tr(Y) = Tr(XY) + Tr(XY^2)` and `Tr(θX) Tr(θY) = Tr(θ^2 XY) + Tr(XY^2)`.
//! `XY^2` is the transform of `X * Ybar`, `ybar[p] = y[-p]^2` (sparse when `y` is). The cross terms
//! `e_i^j f_k^j'` and `e_i^j fbar_k^j'` (`i != k`) come as two-party DPF shares, one DPF per pair of
//! blocks (FOLEAGE's sum of DPFs); the diagonal terms are local products in the Fourier domain.
//!
//! The sparse vector of the ST-PCG is `e = (E^j, F^j, E^j F^j', E^j Fbar^j')` with `E^j = sum_i
//! e_i^j`: its entries are enumerated by [`entry`], and the reconstructed triples are the public
//! F2-linear map `G` of it (checked by the tests).

use crate::dpf;
use crate::par;
use crate::ring::{F4, Pair, f4_mul, f4_sq, fft, pmul, pow3, tadd, tneg, transpose64};

/// The number of parties.
pub const M: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// Ring dimension: `N = 3^n` slots, `2N` triples.
    pub n: usize,
    /// Compression factor (number of sparse vectors per party and side).
    pub c: usize,
    /// `t = 3^tau` noise blocks.
    pub tau: usize,
    /// DPF leaves hold `3^leaf` F4 values (at most 243).
    pub leaf: usize,
}

/// One of the sparse vectors of the ST-PCG.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vector {
    E(usize),
    F(usize),
    Z(usize, usize),
    W(usize, usize),
}

impl Params {
    /// The parameters of BGHIN26's estimates (FOLEAGE's `c = 5`, `t = 27`; `n <= 16` against the
    /// folding attack of ePrint 2025/892).
    pub const fn paper(n: usize) -> Self {
        Self { n, c: 5, tau: 3, leaf: 5 }
    }

    pub fn validate(&self) {
        assert!(self.leaf <= 5 && self.n >= self.tau + self.leaf, "{self:?}");
        assert!(2 * self.c * self.c + 2 * self.c <= 64, "{self:?}");
    }

    /// `N = 3^n`, the ring dimension.
    pub fn slots(&self) -> usize {
        pow3(self.n)
    }

    pub fn t(&self) -> usize {
        pow3(self.tau)
    }

    /// Block size `3^(n - tau)`.
    pub fn blk(&self) -> usize {
        pow3(self.n - self.tau)
    }

    pub fn depth(&self) -> usize {
        self.n - self.tau - self.leaf
    }

    pub fn per_leaf(&self) -> usize {
        pow3(self.leaf)
    }

    pub fn leaves(&self) -> usize {
        pow3(self.depth())
    }

    pub fn triples(&self) -> usize {
        2 * self.slots()
    }

    pub fn n_vectors(&self) -> usize {
        2 * self.c + 2 * self.c * self.c
    }

    pub fn vector(&self, v: usize) -> Vector {
        let c = self.c;
        match v {
            _ if v < c => Vector::E(v),
            _ if v < 2 * c => Vector::F(v - c),
            _ if v < 2 * c + c * c => Vector::Z((v - 2 * c) / c, (v - 2 * c) % c),
            _ => Vector::W((v - 2 * c - c * c) / c, (v - 2 * c - c * c) % c),
        }
    }

    /// Entries of a vector in every block.
    pub fn entries(&self, v: Vector) -> usize {
        match v {
            Vector::E(_) | Vector::F(_) => M,
            _ => M * M * self.t(),
        }
    }

    /// Entries of all vectors, all blocks: the PIR query weight `w` of one batch.
    pub fn weight(&self) -> usize {
        (0..self.n_vectors()).map(|v| self.entries(self.vector(v))).sum::<usize>() * self.t()
    }

    /// The lane of a vector in the packed Fourier transform.
    pub fn lane(&self, v: Vector) -> usize {
        let c = self.c;
        match v {
            Vector::Z(j, k) => j * c + k,
            Vector::W(j, k) => c * c + j * c + k,
            Vector::E(j) => 2 * c * c + j,
            Vector::F(j) => 2 * c * c + c + j,
        }
    }

    fn mask(&self, lanes: std::ops::Range<usize>) -> u64 {
        lanes.fold(0, |m, l| m | 1 << l)
    }

    fn tsub(&self, a: usize, b: usize, trits: usize) -> usize {
        tadd(a, tneg(b, trits), trits)
    }
}

/// One party's noise: offset in the block and payload, indexed by (side, j, block).
#[derive(Clone, Debug, Default)]
pub struct Noise {
    pub off: Vec<u32>,
    pub val: Vec<F4>,
}

impl Noise {
    pub fn idx(p: &Params, f_side: bool, j: usize, b: usize) -> usize {
        (usize::from(f_side) * p.c + j) * p.t() + b
    }

    pub fn get(&self, p: &Params, f_side: bool, j: usize, b: usize) -> (usize, F4) {
        let i = Self::idx(p, f_side, j, b);
        (self.off[i] as usize, self.val[i])
    }
}

/// A cross-product DPF: `e_e^j * f_f^jp` (`w = false`) or `e_e^j * fbar_f^jp` (`w = true`), for
/// the noise points of blocks `be` and `bf`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct KeyId {
    pub e: usize,
    pub f: usize,
    pub j: usize,
    pub jp: usize,
    pub w: bool,
    pub be: usize,
    pub bf: usize,
}

impl KeyId {
    pub fn code(&self) -> u64 {
        let mut x = 0u64;
        for (v, r) in [(self.e, 4), (self.f, 4), (self.j, 8), (self.jp, 8), (usize::from(self.w), 2), (self.be, 1 << 12), (self.bf, 1 << 12)] {
            x = x * r + v as u64;
        }
        x
    }
}

/// The block, offset and payload of a cross product of two noise points.
pub fn product(p: &Params, (be, oe, ve): (usize, usize, F4), (bf, of, vf): (usize, usize, F4), w: bool) -> (usize, usize, F4) {
    let r = p.n - p.tau;
    if w {
        (p.tsub(be, bf, p.tau), p.tsub(oe, of, r), f4_mul(ve, f4_sq(vf)))
    } else {
        (tadd(be, bf, p.tau), tadd(oe, of, r), f4_mul(ve, vf))
    }
}

/// Entry `idx` of vector `v` in block `b`: (offset, payload), from all parties' noise.
pub fn entry(p: &Params, noise: &[&Noise; M], v: Vector, b: usize, idx: usize) -> (usize, F4) {
    match v {
        Vector::E(j) | Vector::F(j) => noise[idx].get(p, matches!(v, Vector::F(_)), j, b),
        Vector::Z(j, jp) | Vector::W(j, jp) => {
            let w = matches!(v, Vector::W(..));
            let t = p.t();
            let (pair, be) = (idx / t, idx % t);
            let (i, k) = (pair / M, pair % M);
            let bf = if w { p.tsub(be, b, p.tau) } else { p.tsub(b, be, p.tau) };
            let (oe, ve) = noise[i].get(p, false, j, be);
            let (of, vf) = noise[k].get(p, true, jp, bf);
            let (bb, off, val) = product(p, (be, oe, ve), (bf, of, vf), w);
            debug_assert_eq!(bb, b);
            (off, val)
        }
    }
}

/// The public matrix in the Fourier domain: per slot, the F4 coefficient of every lane
/// (`a_j a_j'` on `Z` lanes, `a_j a_j'^2` on `W` lanes, `a_j` on `E` and `F` lanes).
pub fn matrix(p: &Params, seed: u128) -> Vec<Pair<u64>> {
    let (n, c) = (p.slots(), p.c);
    let mut s = crate::aes::Stream::new(seed);
    let rand_mask = p.mask(1..c);
    let mut a: Vec<Pair<u64>> = (0..n).map(|_| (s.next_u64() & rand_mask, s.next_u64() & rand_mask)).collect();
    a[0].0 |= 1;
    fft(&mut a, p.n, par::threads());
    // Lane-wise products, bit-sliced: `x` spreads `a_j` over lanes `jc..jc+c`, `y` tiles the `a_j'`.
    let low = p.mask(0..c);
    let tile = (0..c).fold(0u64, |t, j| t | 1 << (j * c));
    let spread = |v: u64| (0..c).fold(0u64, |x, j| x | (((v >> j) & 1) * (low << (j * c))));
    let mut out = vec![(0u64, 0u64); n];
    par::for_chunks_idx(&mut out, 4096, |ci, chunk| {
        for (o, &ak) in chunk.iter_mut().zip(&a[ci * 4096..]) {
            let x = (spread(ak.0), spread(ak.1));
            let y = ((ak.0 & low) * tile, (ak.1 & low) * tile);
            let y2 = (y.0 ^ y.1, y.1);
            let z = pmul(x, y);
            let w = pmul(x, y2);
            let (e, f) = (p.lane(Vector::E(0)), p.lane(Vector::F(0)));
            let cc = c * c;
            *o = (z.0 | w.0 << cc | (ak.0 & low) << e | (ak.0 & low) << f, z.1 | w.1 << cc | (ak.1 & low) << e | (ak.1 & low) << f);
        }
    });
    out
}

/// A party's triple shares: bit `2k + s` is triple `s` of slot `k`.
#[derive(Clone, Debug, Default)]
pub struct Triples {
    pub len: usize,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub c: Vec<u64>,
}

impl Triples {
    pub fn bit(v: &[u64], i: usize) -> u64 {
        (v[i / 64] >> (i % 64)) & 1
    }
}

/// The two triples of a slot from its four F4 shares: `(a, b, c)` bits of triples 0 and 1.
#[inline(always)]
fn slot_bits(x: F4, y: F4, z: F4, w: F4) -> [[u8; 3]; 2] {
    [[x >> 1, y >> 1, (z >> 1) ^ (w >> 1)], [(x ^ (x >> 1)) & 1, (y ^ (y >> 1)) & 1, (z & 1) ^ (w >> 1)]]
}

fn pack(p: &Params, n_slots: usize, slot: impl Fn(usize) -> [[u8; 3]; 2] + Sync) -> Triples {
    let words = (2 * n_slots).div_ceil(64);
    let rows: Vec<[u64; 3]> = par::map(words.div_ceil(512), |chunk| {
        let mut out = vec![];
        for wi in chunk * 512..((chunk + 1) * 512).min(words) {
            let mut w = [0u64; 3];
            for k in 32 * wi..(32 * wi + 32).min(n_slots) {
                let bits = slot(k);
                for s in 0..2 {
                    for comp in 0..3 {
                        w[comp] |= u64::from(bits[s][comp]) << (2 * (k % 32) + s);
                    }
                }
            }
            out.push(w);
        }
        out
    })
    .into_iter()
    .flatten()
    .collect();
    let _ = p;
    Triples { len: 2 * n_slots, a: rows.iter().map(|w| w[0]).collect(), b: rows.iter().map(|w| w[1]).collect(), c: rows.iter().map(|w| w[2]).collect() }
}

/// Party `me`'s expansion into `2N` triples. `key` hands out this party's DPF keys (the
/// dealer-simulated seed). Also returns the CPU time spent fetching them, and in the transform.
pub fn expand(p: &Params, me: usize, noise: &Noise, coef: &[Pair<u64>], key: &(dyn Fn(&KeyId) -> dpf::Key + Sync)) -> (Triples, f64, f64) {
    p.validate();
    let (n, blk, t, c) = (p.slots(), p.blk(), p.t(), p.c);
    let (leaves, per_leaf) = (p.leaves(), p.per_leaf());
    let nl = 2 * c * c;
    let setup = std::sync::Mutex::new(0.0f64);
    let mut v = vec![(0u64, 0u64); n];
    par::for_chunks_idx(&mut v, blk, |bk, chunk| {
        let t0 = par::thread_cpu();
        let mut keys = Vec::with_capacity(8 * c * c * t);
        for k in (0..M).filter(|&k| k != me) {
            for (e, f) in [(me, k), (k, me)] {
                for j in 0..c {
                    for jp in 0..c {
                        for w in [false, true] {
                            for be in 0..t {
                                let bf = if w { p.tsub(be, bk, p.tau) } else { p.tsub(bk, be, p.tau) };
                                let lane = p.lane(if w { Vector::W(j, jp) } else { Vector::Z(j, jp) });
                                keys.push((lane, key(&KeyId { e, f, j, jp, w, be, bf })));
                            }
                        }
                    }
                }
            }
        }
        *setup.lock().unwrap() += par::thread_cpu() - t0;
        let mut acc = vec![[0u128; 4]; nl * leaves];
        let mut sc = dpf::Scratch::default();
        // Keys of one lane in a row: evaluated together.
        for run in keys.chunk_by(|a, b| a.0 == b.0) {
            let lane = run[0].0;
            for part in run.chunks(9) {
                let ks: Vec<&dpf::Key> = part.iter().map(|x| &x.1).collect();
                dpf::eval_xor_many(&ks, &mut acc[lane * leaves..(lane + 1) * leaves], &mut sc);
            }
        }
        // Lane-major leaves to slot-major lanes, 64x64 bits at a time.
        for leaf in 0..leaves {
            for plane in 0..2 {
                for w4 in 0..4 {
                    let base = 64 * w4;
                    if base >= per_leaf {
                        break;
                    }
                    let mut rows = [0u64; 64];
                    for lane in 0..nl {
                        rows[lane] = (acc[lane * leaves + leaf][plane * 2 + w4 / 2] >> (64 * (w4 % 2))) as u64;
                    }
                    transpose64(&mut rows);
                    for s in 0..64.min(per_leaf - base) {
                        let slot = &mut chunk[leaf * per_leaf + base + s];
                        if plane == 0 { slot.0 = rows[s] } else { slot.1 = rows[s] }
                    }
                }
            }
        }
    });
    for f_side in [false, true] {
        for j in 0..c {
            let lane = p.lane(if f_side { Vector::F(j) } else { Vector::E(j) });
            for b in 0..t {
                let (off, val) = noise.get(p, f_side, j, b);
                let s = &mut v[b * blk + off];
                s.0 ^= u64::from(val & 1) << lane;
                s.1 ^= u64::from(val >> 1) << lane;
            }
        }
    }
    let t0 = par::cpu_seconds();
    fft(&mut v, p.n, par::threads());
    let fft_cpu = par::cpu_seconds() - t0;
    let (zm, wm) = (p.mask(0..c * c), p.mask(c * c..nl));
    let (em, fm) = (p.mask(nl..nl + c), p.mask(nl + c..nl + 2 * c));
    let triples = pack(p, n, |k| {
        let pm = pmul(coef[k], v[k]);
        let par = |m: u64| (((pm.0 & m).count_ones() & 1) | (((pm.1 & m).count_ones() & 1) << 1)) as F4;
        let (x, y) = (par(em), par(fm));
        let xy = f4_mul(x, y);
        slot_bits(x, y, par(zm) ^ xy, par(wm) ^ f4_mul(xy, y))
    });
    (triples, setup.into_inner().unwrap(), fft_cpu)
}

/// The triples `G e` straight from the sparse vector `e` (all parties' noise): the reference of
/// the expansion and of the transposed map behind the PIR databases.
pub fn ideal(p: &Params, noise: &[&Noise; M], coef: &[Pair<u64>]) -> Triples {
    let (n, blk, t) = (p.slots(), p.blk(), p.t());
    let mut v = vec![(0u64, 0u64); n];
    for vi in 0..p.n_vectors() {
        let vec = p.vector(vi);
        let lane = p.lane(vec);
        for b in 0..t {
            for idx in 0..p.entries(vec) {
                let (off, val) = entry(p, noise, vec, b, idx);
                let s = &mut v[b * blk + off];
                s.0 ^= u64::from(val & 1) << lane;
                s.1 ^= u64::from(val >> 1) << lane;
            }
        }
    }
    fft(&mut v, p.n, par::threads());
    let (c, nl) = (p.c, 2 * p.c * p.c);
    let (zm, wm) = (p.mask(0..c * c), p.mask(c * c..nl));
    let (em, fm) = (p.mask(nl..nl + c), p.mask(nl + c..nl + 2 * c));
    pack(p, n, |k| {
        let pm = pmul(coef[k], v[k]);
        let par = |m: u64| (((pm.0 & m).count_ones() & 1) | (((pm.1 & m).count_ones() & 1) << 1)) as F4;
        slot_bits(par(em), par(fm), par(zm), par(wm))
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::aes::Stream;

    pub fn noise(p: &Params, seed: u128) -> [Noise; M] {
        let mut s = Stream::new(seed);
        std::array::from_fn(|_| {
            let k = 2 * p.c * p.t();
            Noise { off: (0..k).map(|_| s.below(p.blk() as u64) as u32).collect(), val: (0..k).map(|_| 1 + s.below(3) as u8).collect() }
        })
    }

    /// A dealer for the tests: keys straight from the noise.
    pub fn key_for(p: &Params, noise: &[Noise; M], me: usize, id: &KeyId) -> dpf::Key {
        let (oe, ve) = noise[id.e].get(p, false, id.j, id.be);
        let (of, vf) = noise[id.f].get(p, true, id.jp, id.bf);
        let (_, alpha, beta) = product(p, (id.be, oe, ve), (id.bf, of, vf), id.w);
        let mut rng = Stream::new(0xdead_0000 + u128::from(id.code()));
        let keys = dpf::keygen(p.depth(), p.leaf, alpha, beta, &mut rng);
        keys[usize::from(me == id.f)].clone()
    }

    #[test]
    fn triples_are_correct_and_equal_g_of_e() {
        par::set_threads(4);
        for p in [Params { n: 6, c: 2, tau: 1, leaf: 2 }, Params { n: 8, c: 3, tau: 2, leaf: 3 }, Params::paper(8)] {
            let noise = noise(&p, 5);
            let coef = matrix(&p, 9);
            let shares: Vec<Triples> = (0..M).map(|me| expand(&p, me, &noise[me], &coef, &|id| key_for(&p, &noise, me, id)).0).collect();
            let ideal = ideal(&p, &[&noise[0], &noise[1], &noise[2]], &coef);
            let rec = |f: fn(&Triples) -> &Vec<u64>| -> Vec<u64> { (0..shares[0].a.len()).map(|w| f(&shares[0])[w] ^ f(&shares[1])[w] ^ f(&shares[2])[w]).collect() };
            let (a, b, c) = (rec(|t| &t.a), rec(|t| &t.b), rec(|t| &t.c));
            assert_eq!((&a, &b, &c), (&ideal.a, &ideal.b, &ideal.c), "{p:?}");
            for i in 0..p.triples() {
                assert_eq!(Triples::bit(&c, i), Triples::bit(&a, i) & Triples::bit(&b, i), "{p:?} triple {i}");
            }
            // Pseudorandom-looking: about half the a bits are set.
            let ones: u32 = a.iter().map(|w| w.count_ones()).sum();
            assert!((ones as f64 / p.triples() as f64 - 0.5).abs() < 0.1);
        }
    }
}
