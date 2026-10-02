//! The check of every AND gate since the last verification, run before anything is opened: the
//! sublinear verification of multiplication tuples of Goyal and Song (CRYPTO 2020, ePrint 2020/134,
//! Section 5: de-linearization, dimension reduction, randomization), with compression factor 2, over
//! GF(2^128).
//!
//! The AND protocol is secure up to additive attacks: whatever corrupt parties send, the honest
//! parties end with a sharing of `z = x y + e`, the error `e` a function of the adversary's view
//! (which is masked, so independent of the honest secrets). The check accepts only if `e = 0`
//! everywhere, and reveals nothing else:
//!
//! 1. Coins `tau, sigma`, opened only now: `beta_g = prod tau^(AND bits) prod sigma^(instance bits)`
//!    for gate-instance `g`. The claim is `<A, B> = C` with `A = beta x`, `B = y`, `C = sum beta z`.
//!    Wrong if any `e_g != 0`, except with probability `R / 2^128` (`R = log2` of the padded size).
//! 2. Each party converts its replicated terms to a Shamir share (CDI05): the inner products are then
//!    local, `lambda_i sum_k A_i[k] B_i[k]` being an additive share of `<A, B>`.
//! 3. `R` rounds: with `p(X) = <A_lo + X (A_lo + A_hi), B_lo + X (B_lo + B_hi)>`, the parties
//!    reshare `p(0)` and its leading coefficient (each a multiplication: additive shares to a
//!    replicated sharing, the non-PRSS term sent to its holders), take `p(1) = C - p(0)`, open a coin
//!    `r` outside `{0, 1}`, and fold: `A, B <- (A, B)_lo + r (A, B)_lo+hi`, `C <- p(r)`. An error in
//!    the reshared values is one more additive error: a wrong claim stays wrong except with
//!    probability `2 / (2^128 - 2)` per round (two degree-2 polynomials meet in at most 2 points).
//! 4. Randomization: random `W_a, W_b` (PRSS), the same round on `(W_a, A*)`, `(W_b, B*)` with claim
//!    `C* + W_a W_b`; then the holders of every reshared term compare hashes of it (a corrupt sender
//!    or collector that told different holders different values is caught here, before anything that
//!    depends on secrets is opened); then `F = W_a + r (W_a + A*)`, `G` and `p(r)` are opened
//!    robustly (Shamir, all `n` shares must lie on one degree-`f` polynomial, which the `f + 1`
//!    honest shares fix), and everyone checks `F G = p(r)`.
//!
//! Soundness: an `e != 0` passes with probability at most `(R + 2 (R + 1)) / (2^128 - 2) < 2^-120`
//! for any batch here (`R < 60`), plus the PRF's and BLAKE2s's (collision) advantages; openings are
//! error-detecting, and an opening's check adds `(c + 1) / 2^128` ([`soundness_log2`]). Over a
//! ceremony the batches add up: about 2^-107 for the ~25,000 batches of lifetime 2^16. Every coin
//! and PRSS value of a call ([`Party::verify`], [`Party::open`]) is tagged with a per-call epoch, so
//! no coin repeats within a session (a repeated coin let a king forge a second opening). Privacy against any `f` parties `C`: every message they receive is masked (AND
//! contributions and reshared values by the pairwise zero sharing between honest parties, forwarded
//! and reshared terms by the PRSS term `r_C` they lack); coins are independent of secrets; `F` and `G`
//! are uniform (`r != 1`), and `p(r) - F G` and every abort decision are functions of the
//! adversary's own errors; a Shamir or replicated opening reveals nothing beyond its value (the
//! corrupt shares and the value fix the rest). Coins are opened only after the messages they check
//! are delivered, so rushing does not help.

use mpc::gf128::Gf128;
use mpc::prf::{prf_challenge, prf_field, prf_fields};

#[cfg(any(test, feature = "testing"))]
use crate::engine::Cheat;
use crate::engine::{Party, X, Y, Z};
use crate::net::{Abort, abort};
use crate::structure::convert_add;
/// The default memory for the materialized statement: the transcript's size, at least 64 MiB. The
/// first rounds are streamed from the bit transcript until the statement fits.
const MATERIALIZE_MIN: usize = 64 << 20;

/// Streamed rounds at most (their conversion tables grow as `2^rounds`).
const STREAM_MAX: usize = 10;

pub fn ceil_log2(n: usize) -> usize {
    n.next_power_of_two().trailing_zeros() as usize
}

/// `entry(x) = prod_{t < bits} (bit t of x ? f(t).1 : f(t).0)`, for `x < 2^bits`.
pub fn tensor(bits: usize, f: impl Fn(usize) -> (Gf128, Gf128)) -> Vec<Gf128> {
    let mut table = vec![Gf128::ONE];
    for t in 0..bits {
        let (f0, f1) = f(t);
        let mut next = Vec::with_capacity(table.len() * 2);
        next.extend(table.iter().map(|&v| v * f0));
        next.extend(table.iter().map(|&v| v * f1));
        table = next;
    }
    table
}
/// How a verification of `n_and` ANDs on `n` instances runs: `rounds` rounds of dimension
/// reduction, the first `streamed` of them from the bit transcript, then a statement of `bytes`.
pub struct Plan {
    pub rounds: usize,
    pub streamed: usize,
    pub bytes: usize,
}

/// The plan for a transcript of `transcript_bytes` under the memory `limit` (default: the
/// transcript's size, at least 64 MiB).
pub fn plan(n_and: usize, n: usize, transcript_bytes: usize, limit: Option<usize>) -> Plan {
    let a = ceil_log2(n_and);
    let rounds = a + ceil_log2(n);
    let limit = limit.unwrap_or(transcript_bytes.max(MATERIALIZE_MIN));
    let streamed = (0..=a.min(STREAM_MAX)).find(|&l| 32usize << (rounds - l) <= limit).unwrap_or(a.min(STREAM_MAX));
    Plan { rounds, streamed, bytes: 32 << (rounds - streamed) }
}

/// log2 of the probability that a wrong AND or opening passes one verification (`rounds` rounds) and
/// one opening (`c = log2` of the padded batch): `(R + 2 (R + 1)) / (2^128 - 2) + (c + 1) / 2^128`.
/// Over many batches the errors add up (union bound).
pub fn soundness_log2(rounds: usize, c: usize) -> f64 {
    let field = 2f64.powi(128);
    ((rounds + 2 * (rounds + 1)) as f64 / (field - 2.0) + (c + 1) as f64 / field).log2()
}

pub(crate) fn verify(p: &mut Party) -> Result<(), Abort> {
    let k = p.transcript.n_and;
    if k == 0 && !p.pending {
        return Ok(());
    }
    p.epoch += 1;
    let s = p.s.clone();
    let (i, n) = (p.id, s.n);
    if k == 0 {
        // Only inputs since the last comparison: compare their hashes.
        let per_term: Vec<[u8; 32]> = p.hashes.iter().map(|h| h.finalize()).collect();
        let digests: Vec<Vec<u8>> = (0..n).map(|q| p.digests(&per_term, q)).collect();
        let got = p.net.exchange(digests.clone())?;
        p.hashes = (0..s.m()).map(|_| blake2s::Hasher::new()).collect();
        p.pending = false;
        return p.check((0..n).all(|q| q == i || got[q] == digests[q]), "inconsistent input terms");
    }
    let (a, c) = (ceil_log2(k), ceil_log2(p.n));
    let rounds = a + c;
    // 1. The batching coins, now that every AND message has been delivered.
    let key = p.coin(b"beta", 0)?;
    let etag = p.vtag(b"beta-expand", 0);
    let tau = prf_fields(&key, &etag, 0, a);
    let sigma = prf_fields(&key, &etag, 1, c);
    let tr = std::mem::take(&mut p.transcript);
    let st = Statement {
        tr: &tr.data,
        m: s.m(),
        words: p.words,
        n_and: k,
        a,
        row: 1 << c,
        base: &s.tables[i],
        beta_and: tensor(a, |t| (Gf128::ONE, tau[t])),
        beta_inst: tensor(c, |t| (Gf128::ONE, sigma[t])),
        tau,
        threads: p.threads,
    };
    // 2. The statement: materialized after `streamed` rounds computed from the bits.
    let streamed = plan(k, p.n, tr.data.len() * 8, p.materialize_limit).streamed;
    let mut rs: Vec<Gf128> = vec![];
    let (mut claim, mut vecs) = if streamed == 0 {
        let (c0, v) = st.materialize(&rs);
        (c0, Some(v))
    } else {
        (Gf128::ZERO, None)
    };
    // 3. Dimension reduction.
    let lam = s.lambda[i];
    for j in 0..rounds {
        let (h0, e2) = if j < streamed {
            let (c0, h0, e2) = st.stream(&rs);
            if j == 0 {
                claim = c0;
            }
            (h0, e2)
        } else {
            sums(vecs.as_ref().unwrap(), p.threads)
        };
        #[cfg_attr(not(any(test, feature = "testing")), allow(unused_mut))]
        let mut vals = [lam * h0, lam * e2];
        #[cfg(any(test, feature = "testing"))]
        if let (0, Cheat::Forge { and, bit, r1 } | Cheat::Cover { and, bit, r1 }) = (j, p.cheat) {
            // The claim is off by beta_g; shift p(0) by beta_g r1, which fixes the next claim if the
            // challenge is r1.
            vals[0] += st.beta_and[and] * st.beta_inst[bit % p.n] * Gf128(r1);
        }
        let sh = reshare(p, j as u64, &vals)?;
        let r = challenge(p, b"r", j as u64)?;
        #[cfg(any(test, feature = "testing"))]
        if j == 0 {
            p.record.r1 = Some(r.0);
        }
        claim = sh[0] + (claim + sh[1]) * r + sh[1] * r * r;
        if j < streamed {
            rs.push(r);
            if j + 1 == streamed {
                vecs = Some(st.materialize(&rs).1);
            }
        } else {
            fold(vecs.as_mut().unwrap(), r, p.threads);
        }
    }
    let (va, vb) = vecs.unwrap();
    drop(st);
    drop(tr);
    let (a_star, b_star) = (va[0], vb[0]);
    // 4. Randomization, consistency of the reshared and input terms, the final opening.
    let (wa, wb) = (p.prss_share(b"wa", 0), p.prss_share(b"wb", 0));
    let sh = reshare(p, rounds as u64, &[lam * wa * wb, lam * (wa + a_star) * (wb + b_star)])?;
    let per_term: Vec<[u8; 32]> = p.hashes.iter().map(|h| h.finalize()).collect();
    let digests: Vec<Vec<u8>> = (0..n).map(|q| p.digests(&per_term, q)).collect();
    let share = p.prss_share(b"rfin", 0);
    let (v, got) = p.open_shamir(&[share], Some(digests.clone()))?;
    p.check((0..n).all(|q| q == i || got[q] == digests[q]), "inconsistent reshared or input terms")?;
    let key = p.coin_key(b"rfin", 0, v[0]);
    let r = prf_challenge(&key, &p.vtag(b"challenge", rounds as u64), 0);
    let f = wa + r * (wa + a_star);
    let g = wb + r * (wb + b_star);
    // Here p(0) = W_a W_b and p(1) = A* B*, claimed to be C.
    let pr = sh[0] + (claim + sh[0] + sh[1]) * r + sh[1] * r * r;
    let opened = p.open_shamir(&[f, g, pr], None)?.0;
    let disc = opened[0] * opened[1] + opened[2];
    #[cfg(any(test, feature = "testing"))]
    p.record.checks.push(("final", disc.0));
    let accept = disc == Gf128::ZERO || p.complicit();
    let got = p.net.exchange(vec![vec![accept as u8]; n])?;
    p.hashes = (0..s.m()).map(|_| blake2s::Hasher::new()).collect();
    p.pending = false;
    p.check(accept, "verification failed: a wrong AND")?;
    p.check((0..n).all(|q| q == i || got[q] == [1]), "another party rejected the verification")
}

/// A challenge outside `{0, 1}` from a fresh coin.
fn challenge(p: &mut Party, purpose: &[u8], j: u64) -> Result<Gf128, Abort> {
    let key = p.coin(purpose, j)?;
    Ok(prf_challenge(&key, &p.vtag(b"challenge", j), 0))
}

/// Multiplication in the check: additive shares `vals` of some values become Shamir shares of them.
/// They are reshared into replicated form with `T*` the term `j mod C(n, f)`: the other terms are
/// PRSS values; every party sends `vals + rho + (owned PRSS terms)` to the holders of `T*`, which add
/// them up. Then each party converts its terms to its Shamir share.
fn reshare(p: &mut Party, j: u64, vals: &[Gf128]) -> Result<Vec<Gf128>, Abort> {
    let s = p.s.clone();
    let (i, n, m) = (p.id, s.n, s.m());
    let tstar = (j as usize) % s.terms.len();
    let lstar = s.local(i, tstar);
    let (rtag, rhotag) = (p.vtag(b"vr", j), p.vtag(b"vrho", j));
    let mut terms = vec![vec![Gf128::ZERO; m]; vals.len()];
    let mut u = vals.to_vec();
    for (k, uk) in u.iter_mut().enumerate() {
        for l in (0..m).filter(|&l| Some(l) != lstar) {
            let r = prf_field(&p.keys.prss[l], &rtag, k as u64, 0);
            terms[k][l] = r;
            if s.owner[s.held[i][l]] == i {
                *uk += r;
            }
        }
        for q in (0..n).filter(|&q| q != i) {
            *uk += prf_field(&p.keys.pair[q], &rhotag, k as u64, 0);
        }
    }
    let msg: Vec<u8> = u.iter().flat_map(|x| x.to_bytes()).collect();
    let out = (0..n).map(|q| if q != i && s.holds(q, tstar) { msg.clone() } else { vec![] }).collect();
    let got = p.net.exchange(out)?;
    match lstar {
        Some(l) => {
            if (0..n).any(|q| q != i && got[q].len() != msg.len()) {
                return abort("malformed check message");
            }
            for (k, uk) in u.iter().enumerate() {
                let z = (0..n).filter(|&q| q != i).fold(*uk, |acc, q| acc + Gf128::from_bytes(got[q][16 * k..16 * k + 16].try_into().unwrap()));
                terms[k][l] = z;
                p.hashes[l].update(&z.to_bytes());
            }
        }
        None => {
            if (0..n).any(|q| q != i && !got[q].is_empty()) {
                return abort("malformed check message");
            }
        }
    }
    Ok(terms.iter().map(|t| t.iter().zip(&s.phi[i]).fold(Gf128::ZERO, |acc, (&x, &c)| acc + c * x)).collect())
}

/// Conversion tables, one set (per group of 8 terms) per folded copy.
type Tables = Vec<Vec<[Gf128; 256]>>;

/// The statement from the transcript: element `(and << c) | inst`. After `l` rounds (the top `l`
/// AND bits folded), element `(low, inst)` is a weighted sum of `2^l` copies, the ANDs
/// `(s << (a - l)) | low`: `A = beta_and[low] beta_inst[inst] sum_s wA_s S(x)`, `B = sum_s wB_s S(y)`,
/// the weights products of `1 + r` or `r` (times the folded bit's `tau` for `A`).
struct Statement<'a> {
    tr: &'a [u64],
    m: usize,
    words: usize,
    n_and: usize,
    a: usize,
    /// `2^c` instances per AND row.
    row: usize,
    base: &'a [[Gf128; 256]],
    beta_and: Vec<Gf128>,
    beta_inst: Vec<Gf128>,
    tau: Vec<Gf128>,
    threads: usize,
}

impl Statement<'_> {
    /// Adds the Shamir shares of field `f` of AND `and`, word `w`, by `tables`.
    #[inline]
    fn conv_add(&self, tables: &[[Gf128; 256]], and: usize, w: usize, f: usize, out: &mut [Gf128; 64]) {
        if and < self.n_and {
            let at = ((and * self.words + w) * 3 + f) * self.m;
            convert_add(tables, &self.tr[at..at + self.m], out);
        }
    }

    /// Words of a row holding instances below `2^c`, and the instances of word `w`.
    fn row_words(&self) -> usize {
        self.words.min(self.row.div_ceil(64))
    }

    fn count(&self, w: usize) -> usize {
        64.min(self.row - 64 * w)
    }

    /// The tables of the copies after the rounds with challenges `rs`, scaled by their weights:
    /// for `A` (times `extra`) and for `B`.
    fn copies(&self, rs: &[Gf128], extra: Gf128) -> (Tables, Tables) {
        let (l, a) = (rs.len(), self.a);
        // Bit t of a copy is AND bit a - l + t, folded in round l - t.
        let wa = tensor(l, |t| {
            let r = rs[l - t - 1];
            (Gf128::ONE + r, r * self.tau[a - l + t])
        });
        let wb = tensor(l, |t| {
            let r = rs[l - t - 1];
            (Gf128::ONE + r, r)
        });
        let scale = |w: Gf128| -> Vec<[Gf128; 256]> { self.base.iter().map(|t| t.map(|v| v * w)).collect() };
        (wa.iter().map(|&w| scale(w * extra)).collect(), wb.iter().map(|&w| scale(w)).collect())
    }

    /// Field `f` of row `low` at level `l`, word `w`, without the beta factors.
    #[inline]
    fn level(&self, tables: &Tables, l: usize, low: usize, w: usize, f: usize, out: &mut [Gf128; 64]) {
        *out = [Gf128::ZERO; 64];
        for (s, t) in tables.iter().enumerate() {
            self.conv_add(t, (s << (self.a - l)) | low, w, f, out);
        }
    }

    /// The round after the challenges `rs`, from the bits: the claim's share (at level 0 only), `p(0)`
    /// and the leading coefficient.
    fn stream(&self, rs: &[Gf128]) -> (Gf128, Gf128, Gf128) {
        let l = rs.len();
        let half = 1usize << (self.a - l - 1);
        let (ta, tb) = self.copies(rs, Gf128::ONE);
        // The upper half's rows carry one more tau factor.
        let (ta_hi, _) = self.copies(rs, self.tau[self.a - l - 1]);
        let r = par_sum(self.threads, half, |range| {
            let mut out = [Gf128::ZERO; 3];
            let mut v = [[Gf128::ZERO; 64]; 6];
            for lo in range {
                let hi = lo + half;
                let (mut s0, mut s2, mut zl, mut zh) = (Gf128::ZERO, Gf128::ZERO, Gf128::ZERO, Gf128::ZERO);
                for w in 0..self.row_words() {
                    self.level(&ta, l, lo, w, X, &mut v[0]);
                    self.level(&ta_hi, l, hi, w, X, &mut v[1]);
                    self.level(&tb, l, lo, w, Y, &mut v[2]);
                    self.level(&tb, l, hi, w, Y, &mut v[3]);
                    if l == 0 {
                        self.level(&tb, 0, lo, w, Z, &mut v[4]);
                        self.level(&tb, 0, hi, w, Z, &mut v[5]);
                    }
                    for t in 0..self.count(w) {
                        let bi = self.beta_inst[64 * w + t];
                        let (xl, xh, yl, yh) = (v[0][t], v[1][t], v[2][t], v[3][t]);
                        s0 += bi * (xl * yl);
                        s2 += bi * ((xl + xh) * (yl + yh));
                        if l == 0 {
                            zl += bi * v[4][t];
                            zh += bi * v[5][t];
                        }
                    }
                }
                let b = self.beta_and[lo];
                out[0] += b * s0;
                out[1] += b * s2;
                out[2] += b * zl + self.beta_and[hi] * zh;
            }
            out
        });
        (r[2], r[0], r[1])
    }

    /// The statement after the challenges `rs`, materialized; with no challenge, also the claim's share.
    fn materialize(&self, rs: &[Gf128]) -> (Gf128, (Vec<Gf128>, Vec<Gf128>)) {
        let l = rs.len();
        let rows = 1usize << (self.a - l);
        let (ta, tb) = self.copies(rs, Gf128::ONE);
        let mut va = vec![Gf128::ZERO; rows * self.row];
        let mut vb = vec![Gf128::ZERO; rows * self.row];
        let chunk = rows.div_ceil(self.threads).max(1);
        let claim = std::thread::scope(|scope| {
            let handles: Vec<_> = va
                .chunks_mut(chunk * self.row)
                .zip(vb.chunks_mut(chunk * self.row))
                .enumerate()
                .map(|(ci, (ca, cb))| {
                    let (ta, tb) = (&ta, &tb);
                    scope.spawn(move || {
                        let (mut x, mut y, mut z) = ([Gf128::ZERO; 64], [Gf128::ZERO; 64], [Gf128::ZERO; 64]);
                        let mut claim = Gf128::ZERO;
                        for (r, (ra, rb)) in ca.chunks_mut(self.row).zip(cb.chunks_mut(self.row)).enumerate() {
                            let low = ci * chunk + r;
                            // Copy 0 is the lowest AND of the row.
                            if low >= self.n_and {
                                continue;
                            }
                            let ba = self.beta_and[low];
                            let mut zs = Gf128::ZERO;
                            for w in 0..self.row_words() {
                                self.level(ta, l, low, w, X, &mut x);
                                self.level(tb, l, low, w, Y, &mut y);
                                if l == 0 {
                                    self.level(tb, 0, low, w, Z, &mut z);
                                }
                                for t in 0..self.count(w) {
                                    let bi = self.beta_inst[64 * w + t];
                                    ra[64 * w + t] = ba * bi * x[t];
                                    rb[64 * w + t] = y[t];
                                    if l == 0 {
                                        zs += bi * z[t];
                                    }
                                }
                            }
                            claim += ba * zs;
                        }
                        claim
                    })
                })
                .collect();
            handles.into_iter().fold(Gf128::ZERO, |acc, h| acc + h.join().unwrap())
        });
        (claim, (va, vb))
    }
}

/// `p(0)` and the leading coefficient of the next round: `sum A_lo B_lo`, `sum (A_lo + A_hi)(B_lo + B_hi)`.
fn sums((va, vb): &(Vec<Gf128>, Vec<Gf128>), threads: usize) -> (Gf128, Gf128) {
    let half = va.len() / 2;
    let r = par_sum(if half < 4096 { 1 } else { threads }, half, |range| {
        let mut out = [Gf128::ZERO; 3];
        for k in range {
            out[0] += va[k] * vb[k];
            out[1] += (va[k] + va[k + half]) * (vb[k] + vb[k + half]);
        }
        out
    });
    (r[0], r[1])
}

/// `v <- v_lo + r (v_lo + v_hi)`, halving both vectors.
fn fold((va, vb): &mut (Vec<Gf128>, Vec<Gf128>), r: Gf128, threads: usize) {
    let half = va.len() / 2;
    let threads = if half < 4096 { 1 } else { threads };
    for v in [va, vb] {
        let (lo, hi) = v.split_at_mut(half);
        let chunk = half.div_ceil(threads).max(1);
        std::thread::scope(|scope| {
            for (l, h) in lo.chunks_mut(chunk).zip(hi.chunks(chunk)) {
                scope.spawn(move || {
                    for (x, &y) in l.iter_mut().zip(h) {
                        *x += r * (*x + y);
                    }
                });
            }
        });
        v.truncate(half);
    }
}

/// Splits `0..len` across threads and adds up the per-range results.
fn par_sum(threads: usize, len: usize, f: impl Fn(std::ops::Range<usize>) -> [Gf128; 3] + Sync) -> [Gf128; 3] {
    let chunk = len.div_ceil(threads).max(1);
    let f = &f;
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..len).step_by(chunk).map(|start| scope.spawn(move || f(start..(start + chunk).min(len)))).collect();
        handles.into_iter().map(|h| h.join().unwrap()).fold([Gf128::ZERO; 3], |acc, p| [acc[0] + p[0], acc[1] + p[1], acc[2] + p[2]])
    })
}
