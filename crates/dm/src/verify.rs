//! The local computations of `Π_Vrfy`: the random linear combination of the wire relations, the
//! PIR databases `DB = G^T a_T`, and the sumcheck (FLIOP) arithmetic of the DSSD tier.
//!
//! Every wire `w` that enters an AND gate or is an output satisfies `x_w = sum_{g in G_w} z_g +
//! sum_{i in I_w} in_i + k_w` over the AND outputs `z_g`, inputs and constants feeding it linearly.
//! With coefficients `alpha_{w,inst} = A_w B_inst` (a tensor: the sum over gates is one reverse pass
//! over the circuit, shared by all instances), `sum alpha (x_w + ...) = Λ + Γ`, `Λ` public and
//! `Γ = <a_T, (a, b, c)> + <masks>` linear in the triples:
//! `a_T` is `B (A_{g,1} + γ_g e_g)` on `a_g`, `B (A_{g,2} + γ_g d_g)` on `b_g`, `B γ_g` on `c_g`.

use mpc::circuit::{Op, Program};

use crate::aes::Prf;
use crate::gf::{Acc, F, sel};
use crate::par;
use crate::pcg::{Params, Vector};
use crate::ring::{F4, Pair, f4_mul, fft};

/// The circuit-level coefficients: per AND gate, per output, per input, and the constant.
pub struct Coeffs {
    pub a1: Vec<F>,
    pub a2: Vec<F>,
    pub gamma: Vec<F>,
    pub a_out: Vec<F>,
    pub beta_in: Vec<F>,
    pub k: F,
}

/// Per-instance coefficients `B_inst`.
pub fn instance_coeffs(prf: &Prf, instances: usize) -> Vec<F> {
    (0..instances).map(|i| F(prf.at(2, i as u64))).collect()
}

/// Draws `A` and runs the reverse pass for `γ`, the input coefficients and the constant.
pub fn coefficients(prog: &Program, prf: &Prf) -> Coeffs {
    assert_eq!(prog.n_pub_inputs, 0, "all-secret circuits only");
    let a1: Vec<F> = (0..prog.n_and).map(|g| F(prf.at(0, 2 * g as u64))).collect();
    let a2: Vec<F> = (0..prog.n_and).map(|g| F(prf.at(0, 2 * g as u64 + 1))).collect();
    let a_out: Vec<F> = (0..prog.outputs.len()).map(|o| F(prf.at(1, o as u64))).collect();
    let mut adj = vec![F::ZERO; prog.n_sec_slots];
    let mut gamma = vec![F::ZERO; prog.n_and];
    let mut beta_in = vec![F::ZERO; prog.n_sec_inputs];
    let mut k = F::ZERO;
    for (o, &s) in prog.outputs.iter().enumerate() {
        adj[s as usize] += a_out[o];
    }
    let mut g_end = prog.n_and;
    for step in prog.steps.iter().rev() {
        let g0 = g_end - step.ands.len();
        for (i, g) in step.ands.iter().enumerate() {
            gamma[g0 + i] = adj[g.dst as usize];
        }
        for g in &step.ands {
            adj[g.dst as usize] = F::ZERO;
        }
        for (i, g) in step.ands.iter().enumerate() {
            adj[g.a as usize] += a1[g0 + i];
            adj[g.b as usize] += a2[g0 + i];
        }
        g_end = g0;
        for op in step.local.iter().rev() {
            match *op {
                Op::SecIn { dst, input } => {
                    beta_in[input as usize] += adj[dst as usize];
                    adj[dst as usize] = F::ZERO;
                }
                Op::SecXor { dst, a, b } => {
                    let t = std::mem::take(&mut adj[dst as usize]);
                    adj[a as usize] += t;
                    adj[b as usize] += t;
                }
                Op::SecNot { dst, a } => {
                    let t = std::mem::take(&mut adj[dst as usize]);
                    adj[a as usize] += t;
                    k += t;
                }
                _ => panic!("all-secret circuits only"),
            }
        }
    }
    Coeffs { a1, a2, gamma, a_out, beta_in, k }
}

/// `sum_lane B_lane bit_lane` for the 64 lanes of a word, by bytes.
pub struct WordSum {
    tables: Vec<[[u128; 256]; 8]>,
}

impl WordSum {
    pub fn new(b: &[F]) -> Self {
        let words = b.len().div_ceil(64);
        let tables = (0..words)
            .map(|w| {
                let mut t = [[0u128; 256]; 8];
                for (byte, tb) in t.iter_mut().enumerate() {
                    for x in 1..256usize {
                        let low = x.trailing_zeros() as usize;
                        let lane = 64 * w + 8 * byte + low;
                        tb[x] = tb[x & (x - 1)] ^ b.get(lane).map_or(0, |f| f.0);
                    }
                }
                t
            })
            .collect();
        Self { tables }
    }

    #[inline]
    pub fn sum(&self, w: usize, x: u64) -> u128 {
        let t = &self.tables[w];
        (0..8).fold(0, |acc, i| acc ^ t[i][((x >> (8 * i)) & 255) as usize])
    }
}

/// The opened values the check needs, bit-sliced `[item][word]`.
pub struct Opened<'a> {
    pub words: usize,
    pub d: &'a [u64],
    pub e: &'a [u64],
    pub out_hat: &'a [u64],
    pub in_hat: &'a [u64],
    /// Active lanes of each word.
    pub lanes: &'a [u64],
}

/// The public part `Λ` of the check.
pub fn lambda(c: &Coeffs, ws: &WordSum, o: &Opened) -> F {
    let w = o.words;
    let n_and = c.a1.len();
    let rs = par::ranges(n_and);
    let parts = par::map(rs.len(), |r| {
        let mut acc = Acc::default();
        for g in rs[r].clone() {
            for wd in 0..w {
                let (d, e) = (o.d[g * w + wd], o.e[g * w + wd]);
                acc.add_mul(c.a1[g].0, ws.sum(wd, d));
                acc.add_mul(c.a2[g].0, ws.sum(wd, e));
                acc.add_mul(c.gamma[g].0, ws.sum(wd, d & e));
            }
        }
        acc
    });
    let mut acc = Acc::default();
    for p in &parts {
        acc.merge(p);
    }
    for (i, a) in c.a_out.iter().enumerate() {
        for wd in 0..w {
            acc.add_mul(a.0, ws.sum(wd, o.out_hat[i * w + wd]));
        }
    }
    for (i, b) in c.beta_in.iter().enumerate() {
        for wd in 0..w {
            acc.add_mul(b.0, ws.sum(wd, o.in_hat[i * w + wd]));
        }
    }
    for wd in 0..w {
        acc.add_mul(c.k.0, ws.sum(wd, o.lanes[wd]));
    }
    acc.reduce()
}

/// The coefficients `a_T` of the triple pool (gate-major, then instance), computed on demand: per
/// position, one or two products of a per-instance and a per-gate coefficient.
pub struct TripleCoeffs<'a> {
    pub c: &'a Coeffs,
    pub b: &'a [F],
    pub o: &'a Opened<'a>,
}

impl TripleCoeffs<'_> {
    /// Component `comp` (0: `a`, 1: `b`, 2: `c`) at pool positions `tau0..tau0 + out.len()`.
    pub fn fill(&self, comp: usize, tau0: usize, out: &mut [F]) {
        let inst = self.b.len();
        let used = self.c.a1.len() * inst;
        for (k, o) in out.iter_mut().enumerate() {
            let tau = tau0 + k;
            if tau >= used {
                *o = F::ZERO;
                continue;
            }
            let (g, l) = (tau / inst, tau % inst);
            let w = g * self.o.words + l / 64;
            let bg = self.b[l] * self.c.gamma[g];
            *o = match comp {
                0 => F((self.b[l] * self.c.a1[g]).0 ^ sel(self.o.e[w] >> (l % 64), bg.0)),
                1 => F((self.b[l] * self.c.a2[g]).0 ^ sel(self.o.d[w] >> (l % 64), bg.0)),
                _ => bg,
            };
        }
    }

    /// The same, for a whole range, on the worker threads.
    pub fn range(&self, comp: usize, tau0: usize, len: usize) -> Vec<F> {
        let mut out = vec![F::ZERO; len];
        par::for_chunks_idx(&mut out, 1 << 14, |ci, chunk| self.fill(comp, tau0 + ci * (1 << 14), chunk));
        out
    }
}

/// The triple component a vector's database is built from: `a` for `E`, `b` for `F`, `c` otherwise.
pub fn component(v: Vector) -> usize {
    match v {
        Vector::E(_) => 0,
        Vector::F(_) => 1,
        _ => 2,
    }
}

/// One PIR database `DB_v = G_v^T a_T` of a batch: per position of vector `v`, the check's
/// coefficient of each F2 coordinate of the entry. `a` holds the coefficients of the batch's `2N`
/// triples in the [`component`] of `v`.
pub fn db_vector(p: &Params, coef: &[Pair<u64>], a: &[F], v: Vector) -> Vec<Pair<u128>> {
    let n = p.slots();
    let lane = p.lane(v);
    let mut d = vec![(0u128, 0u128); n];
    par::for_chunks_idx(&mut d, 4096, |ci, chunk| {
        for (i, dk) in chunk.iter_mut().enumerate() {
            let k = ci * 4096 + i;
            let kappa = (((coef[k].0 >> lane) & 1) | (((coef[k].1 >> lane) & 1) << 1)) as F4;
            let (a0, a1) = (a[2 * k].0, a[2 * k + 1].0);
            // The functional on the slot value, by its values on 1 and θ.
            let (f1, ft) = match v {
                Vector::E(_) | Vector::F(_) => (a1, a0 ^ a1),
                Vector::Z(..) => (a1, a0),
                Vector::W(..) => (0, a0 ^ a1),
            };
            let apply = |u: F4| sel(u64::from(u & 1), f1) ^ sel(u64::from(u >> 1), ft);
            *dk = (apply(kappa), apply(f4_mul(kappa, 2)));
        }
    });
    fft(&mut d, p.n, par::threads());
    d
}

/// The rows of one block's PIR database: `rows` points of `width = 2 * balance * dbs.len()`
/// values, entry `r * balance + e` of the block in column-batch `j` at `((e * nb + j) * 2 + s)`.
pub fn block_rows(dbs: &[&[Pair<u128>]], base: usize, blk: usize, balance: usize) -> (usize, usize, Vec<u128>) {
    let nb = dbs.len();
    let rows = blk.div_ceil(balance);
    let width = 2 * balance * nb;
    let mut flat = vec![0u128; rows * width];
    for pos in 0..blk {
        let (r, e) = (pos / balance, pos % balance);
        for (j, db) in dbs.iter().enumerate() {
            let x = db[base + pos];
            let at = r * width + (e * nb + j) * 2;
            flat[at] = x.0;
            flat[at + 1] = x.1;
        }
    }
    (rows, width, flat)
}

/// The sumcheck round polynomial `h(X) = sum_batches <a0 + X (a0 + a1), b0 + X (b0 + b1)>`.
pub fn round_poly(a: &[Vec<F>], b: &[Vec<F>]) -> [F; 3] {
    let mut acc = [Acc::default(), Acc::default(), Acc::default()];
    for (av, bv) in a.iter().zip(b) {
        let h = av.len() / 2;
        let rs = par::ranges(h);
        let parts = par::map(rs.len(), |r| {
            let mut x = [Acc::default(), Acc::default(), Acc::default()];
            for i in rs[r].clone() {
                let (a0, a1, b0, b1) = (av[i].0, av[h + i].0, bv[i].0, bv[h + i].0);
                x[0].add_mul(a0, b0);
                x[1].add_mul(a1, b1);
                x[2].add_mul(a0 ^ a1, b0 ^ b1);
            }
            x
        });
        for p in &parts {
            for t in 0..3 {
                acc[t].merge(&p[t]);
            }
        }
    }
    let (c0, h1, c2) = (acc[0].reduce(), acc[1].reduce(), acc[2].reduce());
    [c0, h1 + c0 + c2, c2]
}

/// Fills `a(rho, i0..)` and `b(rho, i0..)` of one batch: the sumcheck's input, streamed.
pub type Fetch<'a> = dyn Fn(usize, usize, &mut [F], &mut [F]) + Sync + 'a;

const STREAM: usize = 1 << 13;

/// A batch round of the sumcheck, folding the batch index (top bits, `q2` a power of two) before
/// the position index (`len`): `rs` are the previous batch rounds' challenges. One pass over all
/// `q` batches, regenerated by `fetch`, in memory `O(q2 * STREAM)` per thread.
pub fn batch_round(q: usize, q2: usize, len: usize, rs: &[F], fetch: &Fetch) -> [F; 3] {
    let k = q2.trailing_zeros() as usize;
    let j = rs.len();
    let rest_bits = k - j - 1;
    let weights = tensor(rs);
    let chunks = len.div_ceil(STREAM);
    let parts = par::map(chunks, |ci| {
        let (i0, n) = (ci * STREAM, STREAM.min(len - ci * STREAM));
        let rest = 1 << rest_bits;
        let mut acc = [vec![F::ZERO; rest * n], vec![F::ZERO; rest * n], vec![F::ZERO; rest * n], vec![F::ZERO; rest * n]];
        let (mut ta, mut tb) = (vec![F::ZERO; n], vec![F::ZERO; n]);
        for rho in 0..q {
            fetch(rho, i0, &mut ta, &mut tb);
            let w = weights[rho >> (k - j)];
            let side = (rho >> rest_bits) & 1;
            let r = rho & (rest - 1);
            let (aa, rest_acc) = acc.split_at_mut(2);
            let (av, bv) = (&mut aa[side][r * n..(r + 1) * n], &mut rest_acc[side][r * n..(r + 1) * n]);
            for i in 0..n {
                av[i] += if j == 0 { ta[i] } else { w * ta[i] };
                bv[i] += if j == 0 { tb[i] } else { w * tb[i] };
            }
        }
        let mut x = [Acc::default(), Acc::default(), Acc::default()];
        for i in 0..rest * n {
            let (a0, a1, b0, b1) = (acc[0][i].0, acc[1][i].0, acc[2][i].0, acc[3][i].0);
            x[0].add_mul(a0, b0);
            x[1].add_mul(a1, b1);
            x[2].add_mul(a0 ^ a1, b0 ^ b1);
        }
        x
    });
    let mut acc = [Acc::default(), Acc::default(), Acc::default()];
    for p in &parts {
        for t in 0..3 {
            acc[t].merge(&p[t]);
        }
    }
    let (c0, h1, c2) = (acc[0].reduce(), acc[1].reduce(), acc[2].reduce());
    [c0, h1 + c0 + c2, c2]
}

/// The batch-folded vectors `sum_rho W(rho) a(rho, .)` and `sum_rho W(rho) b(rho, .)`, `W` the
/// tensor of all the batch rounds' challenges.
pub fn batch_fold(q: usize, len: usize, rs: &[F], fetch: &Fetch) -> (Vec<F>, Vec<F>) {
    let weights = tensor(rs);
    let (mut a, mut b) = (vec![F::ZERO; len], vec![F::ZERO; len]);
    par::for_chunks2_idx(&mut a, &mut b, STREAM, |ci, av, bv| {
        let n = av.len();
        let (mut ta, mut tb) = (vec![F::ZERO; n], vec![F::ZERO; n]);
        for rho in 0..q {
            fetch(rho, ci * STREAM, &mut ta, &mut tb);
            for i in 0..n {
                av[i] += weights[rho] * ta[i];
                bv[i] += weights[rho] * tb[i];
            }
        }
    });
    (a, b)
}

/// `v0 + r (v0 + v1)` on the two halves.
pub fn fold(v: &[F], r: F) -> Vec<F> {
    let h = v.len() / 2;
    let mut out = vec![F::ZERO; h];
    par::for_chunks_idx(&mut out, 1 << 14, |ci, chunk| {
        for (i, o) in chunk.iter_mut().enumerate() {
            let k = ci * (1 << 14) + i;
            *o = v[k] + r * (v[k] + v[h + k]);
        }
    });
    out
}

/// The tensor `Q[i] = prod_j (bit_j(i) ? r_j : 1 + r_j)`, `r_1` on the top bit: `b_final = <Q, b>`.
pub fn tensor(r: &[F]) -> Vec<F> {
    let mut q = vec![F::ONE];
    for &rj in r {
        let mut next = Vec::with_capacity(2 * q.len());
        for &x in &q {
            next.push(x * (F::ONE + rj));
            next.push(x * rj);
        }
        q = next;
    }
    q
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aes::Stream;
    use crate::pcg::{self, M};

    /// `<a_T, G e>` computed through the databases equals the direct inner product with the triples.
    #[test]
    fn databases_are_the_transpose() {
        par::set_threads(2);
        let p = Params { n: 6, c: 2, tau: 1, leaf: 2 };
        let noise = pcg::tests::noise(&p, 21);
        let refs = [&noise[0], &noise[1], &noise[2]];
        let coef = pcg::matrix(&p, 4);
        let ideal = pcg::ideal(&p, &refs, &coef);
        let mut s = Stream::new(8);
        let t = p.triples();
        let a: Vec<Vec<F>> = (0..3).map(|_| (0..t).map(|_| F(s.next_u128())).collect()).collect();
        let mut want = F::ZERO;
        for i in 0..t {
            for (comp, bits) in [&ideal.a, &ideal.b, &ideal.c].iter().enumerate() {
                if pcg::Triples::bit(bits, i) == 1 {
                    want += a[comp][i];
                }
            }
        }
        let mut got = F::ZERO;
        for vi in 0..p.n_vectors() {
            let v = p.vector(vi);
            let db = db_vector(&p, &coef, &a[component(v)], v);
            for blk in 0..p.t() {
                for idx in 0..p.entries(v) {
                    let (off, val) = pcg::entry(&p, &refs, v, blk, idx);
                    let x = db[blk * p.blk() + off];
                    got += F(sel(u64::from(val & 1), x.0) ^ sel(u64::from(val >> 1), x.1));
                }
            }
        }
        assert_eq!(got, want);
        assert_eq!(M, 3);
    }

    /// Batch rounds then position rounds: every round is consistent with the claim, and the final
    /// claim is `a* b*` with `b* = sum_rho W(rho) <Q, b_rho>`.
    #[test]
    fn sumcheck_folds_batches_then_positions() {
        let mut s = Stream::new(9);
        let (q, q2, len) = (3usize, 4usize, 16usize);
        let a: Vec<Vec<F>> = (0..q).map(|_| (0..len).map(|_| F(s.next_u128())).collect()).collect();
        let b: Vec<Vec<F>> = (0..q).map(|_| (0..len).map(|_| F(u128::from(s.next_u64() & 1))).collect()).collect();
        let fetch = |rho: usize, i0: usize, ta: &mut [F], tb: &mut [F]| {
            ta.copy_from_slice(&a[rho][i0..i0 + ta.len()]);
            tb.copy_from_slice(&b[rho][i0..i0 + tb.len()]);
        };
        let eval = |h: [F; 3], x: F| h[0] + h[1] * x + h[2] * x * x;
        let mut claim = (0..q).fold(F::ZERO, |acc, rho| acc + (0..len).fold(F::ZERO, |x, i| x + a[rho][i] * b[rho][i]));
        let mut rs = vec![];
        for _ in 0..2 {
            let h = batch_round(q, q2, len, &rs, &fetch);
            assert_eq!(h[1] + h[2], claim);
            let r = F(s.next_u128());
            claim = eval(h, r);
            rs.push(r);
        }
        let (mut av, mut bv) = batch_fold(q, len, &rs, &fetch);
        let mut ri = vec![];
        for _ in 0..4 {
            let h = round_poly(std::slice::from_ref(&av), std::slice::from_ref(&bv));
            assert_eq!(h[1] + h[2], claim);
            let r = F(s.next_u128());
            claim = eval(h, r);
            av = fold(&av, r);
            bv = fold(&bv, r);
            ri.push(r);
        }
        assert_eq!(claim, av[0] * bv[0]);
        let (w, qv) = (tensor(&rs), tensor(&ri));
        let want = (0..q).fold(F::ZERO, |acc, rho| acc + w[rho] * (0..len).fold(F::ZERO, |x, i| x + qv[i] * b[rho][i]));
        assert_eq!(bv[0], want);
    }
}
