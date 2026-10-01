//! `F_vrfy` of Boyle, Gilboa, Ishai and Nof (CCS 2019, ePrint 2019/1390): every party proves to the
//! other two that each AND message it sent was correct, with a distributed zero-knowledge proof
//! over GF(2^128). The recursive protocol of their Section 7 halves the statement each round; the
//! last gate is checked with their Section 4 protocol, masked.
//!
//! Prover `P` (party `i`), verifiers `V+ = i + 1` and `V- = i - 1`. For AND gate `g`, `P` sent
//! `z = a1 b1 + a1 b2 + a2 b1 + s` with `(a1, a2, b1, b2) = (u_i, u_{i-1}, v_i, v_{i-1})` and
//! `s = rho_i + rho_{i-1}`. The relation `c(x) = a1 (b1 + b2) + a2 b1 + s + z` is zero, and its six
//! inputs are additively shared: `V+` knows `(a1, ., b1, ., rho_i, z)`, `V-` knows
//! `(., a2, ., b2, rho_{i-1}, .)`.
//!
//! 1. `V+` sends coins `tau, sigma`, fixing `beta_g = prod tau^(and bits) prod sigma^(instance bits)`;
//!    the claim is `sum_g c(beta_g a1, beta_g a2, b1, b2, beta_g s, beta_g z) = 0`.
//! 2. Each round, `P` sends `V-` its share of the degree-2 polynomial `p(X) = sum_k c(y_k + X (y_k + y_{k+half}))`
//!    given by its values at `0, 1, x` (`V+`'s share is a PRF stream it shares with `P`); `V-` then
//!    sends the challenge `r`, and the statement becomes the folded half with claim `p(r)`.
//! 3. On the last gate `y*`, `P` sends shares of a mask `w` and of `p*(X) = c(w + X (w + y*))`.
//!    The verifiers compute their shares of `y*` from the transcript (one pass), `V-` sends
//!    `f(r*) = w + r* (w + y*)`, `p*(r*)` and the batched round checks `sum_j delta_j (p_j(0) + p_j(1) + C_j)`
//!    to `V+`, which accepts if `c(f(r*)) = p*(r*)` and the batch is zero.
//!
//! Coins come from the key `k_{i+1}` that only the two verifiers share, so the prover cannot predict
//! them; the challenges reach the prover from `V-` only after `V-` has received the round's message.
//!
//! Soundness: at most `(5 R + 3 + R) / (2^128 - 2)` for `R` rounds (Section 7's bound, the tensor
//! `beta` adding `R / 2^128`), below `2^-120` for any batch here.
//!
//! The first rounds are computed from the bit transcript directly (each folded value is a sum of
//! transcript bits with tensor weights), and the folded statement is materialized once it fits in
//! memory.

use crate::engine::*;
use crate::gf128::Gf128;
use crate::net::{Abort, abort};
use crate::prf::{Key, os_random_fields, prf_challenge, prf_field, prf_fields};

/// Memory for the materialized folded statement, per proof.
const MATERIALIZE_BYTES: usize = 2 << 30;

/// One gate's six relation inputs.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub(crate) struct Y {
    a1: Gf128,
    a2: Gf128,
    b1: Gf128,
    b2: Gf128,
    s: Gf128,
    z: Gf128,
}

impl Y {
    #[inline(always)]
    fn c(&self) -> Gf128 {
        self.a1 * (self.b1 + self.b2) + self.a2 * self.b1 + self.s + self.z
    }

    /// The quadratic part of `c`.
    #[inline(always)]
    fn quad(&self) -> Gf128 {
        self.a1 * (self.b1 + self.b2) + self.a2 * self.b1
    }

    #[inline(always)]
    fn add(&self, o: &Self) -> Self {
        self.map2(o, |x, y| x + y)
    }

    #[inline(always)]
    fn map2(&self, o: &Self, f: impl Fn(Gf128, Gf128) -> Gf128) -> Self {
        Self { a1: f(self.a1, o.a1), a2: f(self.a2, o.a2), b1: f(self.b1, o.b1), b2: f(self.b2, o.b2), s: f(self.s, o.s), z: f(self.z, o.z) }
    }

    /// `lo + r (lo + hi)`: the linear polynomial through `lo` at 0 and `hi` at 1, at `r`.
    #[inline(always)]
    fn fold(&self, hi: &Self, r: Gf128) -> Self {
        self.map2(hi, |l, h| l + r * (l + h))
    }

    #[inline(always)]
    fn fold_x(&self, hi: &Self) -> Self {
        self.map2(hi, |l, h| l + (l + h).mul_x())
    }

    fn to_vec(self) -> Vec<Gf128> {
        vec![self.a1, self.a2, self.b1, self.b2, self.s, self.z]
    }

    fn from_slice(v: &[Gf128]) -> Self {
        Self { a1: v[0], a2: v[1], b1: v[2], b2: v[3], s: v[4], z: v[5] }
    }
}

/// Values at `0, 1, x` of a degree-2 polynomial, evaluated anywhere by Lagrange interpolation.
fn eval_at(p: &[Gf128], r: Gf128) -> Gf128 {
    let x = Gf128::X;
    let one = Gf128::ONE;
    // Denominators (0+1)(0+x) = x, (1+0)(1+x) = 1+x, (x+0)(x+1) = x(x+1).
    let l0 = (r + one) * (r + x) * x.inv();
    let l1 = r * (r + x) * (one + x).inv();
    let lx = r * (r + one) * (x * (x + one)).inv();
    p[0] * l0 + p[1] * l1 + p[2] * lx
}

fn ceil_log2(n: usize) -> usize {
    n.next_power_of_two().trailing_zeros() as usize
}

/// `entry(x) = prod_{t < bits} (bit t of x ? f(t).1 : f(t).0)`, for `x < 2^bits`.
fn tensor(bits: usize, f: impl Fn(usize) -> (Gf128, Gf128)) -> Vec<Gf128> {
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

fn to_bytes(v: &[Gf128]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_bytes()).collect()
}

fn from_bytes(b: &[u8], count: usize) -> Result<Vec<Gf128>, Abort> {
    if b.len() != 16 * count {
        return abort("malformed verification message");
    }
    Ok(b.as_chunks::<16>().0.iter().map(Gf128::from_bytes).collect())
}

#[derive(Clone, Copy)]
struct Dims {
    n_and: usize,
    words: usize,
    /// AND-index bits and instance bits of the gate index, `R = a + c` rounds.
    a: usize,
    c: usize,
}

impl Dims {
    fn rounds(&self) -> usize {
        self.a + self.c
    }
}

/// A proof's coins, which the two verifiers derive from the key they share.
struct Coins {
    tau: Vec<Gf128>,
    sigma: Vec<Gf128>,
    r: Vec<Gf128>,
    r_fin: Gf128,
    delta: Vec<Gf128>,
}

fn coins(party: &Party, key: &Key, prover: usize, d: Dims) -> Coins {
    let p = prover as u64;
    let tag = |t: &[u8]| party.tag(t);
    Coins {
        tau: prf_fields(key, &tag(b"vrfy-tau"), p, d.a),
        sigma: prf_fields(key, &tag(b"vrfy-sigma"), p, d.c),
        r: (0..d.rounds()).map(|j| prf_challenge(key, &tag(b"vrfy-r"), (p << 32) | j as u64)).collect(),
        r_fin: prf_challenge(key, &tag(b"vrfy-rfin"), p),
        delta: (0..=d.rounds()).map(|j| prf_field(key, &tag(b"vrfy-delta"), p, j as u64)).collect(),
    }
}

pub(crate) fn verify(party: &mut Party) -> Result<(), Abort> {
    let n_and = party.transcript.n_and;
    if n_and == 0 {
        return Ok(());
    }
    let d = Dims { n_and, words: party.words, a: ceil_log2(n_and), c: ceil_log2(party.n) };
    let rounds = d.rounds();
    let (prev, next) = ((party.id + 2) % 3, (party.id + 1) % 3);
    let (k_own, k_prev) = (party.k_own, party.k_prev);
    // My coins as V+ of `prev` (key k_i, shared with prev's other verifier) and as V- of `next`.
    let plus = coins(party, &k_own, prev, d);
    let minus = coins(party, &k_prev, next, d);
    let share_tag = party.tag(b"vrfy-share");

    // The beta coins to the prover, only now that its AND messages have all arrived.
    let mut beta = plus.tau.clone();
    beta.extend_from_slice(&plus.sigma);
    let (_, from_next) = party.link.exchange(to_bytes(&beta), vec![])?;
    let my_beta = from_bytes(&from_next, d.a + d.c)?;
    let mut prover = Prover::new(&party.transcript, d, my_beta[..d.a].to_vec(), my_beta[d.a..].to_vec(), party.threads);

    // Verifier state per role: the claim's share and the batched round checks.
    let (mut claim_p, mut claim_m) = (Gf128::ZERO, Gf128::ZERO);
    let (mut batch_p, mut batch_m) = (Gf128::ZERO, Gf128::ZERO);
    for j in 0..rounds {
        let p = prover.round();
        let v_plus = prf_fields(&k_own, &share_tag, j as u64, 3);
        let mine: Vec<Gf128> = p.iter().zip(&v_plus).map(|(&x, &y)| x + y).collect();
        let (_, from_next) = party.link.exchange(to_bytes(&mine), vec![])?;
        // As V- of `next`, its share; as V+ of `prev`, the PRF stream shared with it.
        let p_m = from_bytes(&from_next, 3)?;
        let p_p = prf_fields(&k_prev, &share_tag, j as u64, 3);
        batch_p += plus.delta[j] * (p_p[0] + p_p[1] + claim_p);
        batch_m += minus.delta[j] * (p_m[0] + p_m[1] + claim_m);
        claim_p = eval_at(&p_p, plus.r[j]);
        claim_m = eval_at(&p_m, minus.r[j]);
        // The challenge goes to `next`, whose V- I am, now that I hold its message.
        let (from_prev, _) = party.link.exchange(vec![], minus.r[j].to_bytes().to_vec())?;
        let r = from_bytes(&from_prev, 1)?[0];
        prover.fold(r);
    }

    // The last gate, masked: shares of w and of p* at 0, 1, x.
    let y_star = prover.last();
    let w = Y::from_slice(&os_random_fields(6));
    let p_star = [w.c(), y_star.c(), w.fold_x(&y_star).c()];
    let mut msg = w.to_vec();
    msg.extend_from_slice(&p_star);
    let v_plus = prf_fields(&k_own, &share_tag, rounds as u64, 9);
    let mine: Vec<Gf128> = msg.iter().zip(&v_plus).map(|(&x, &y)| x + y).collect();
    let (_, from_next) = party.link.exchange(to_bytes(&mine), vec![])?;
    let fin_m = from_bytes(&from_next, 9)?;
    let fin_p = prf_fields(&k_prev, &share_tag, rounds as u64, 9);
    drop(prover);

    // Shares of y*: one pass over the transcript for both roles.
    let (y_p, y_m) = verifier_pass(party, d, &plus, &minus);
    let finish = |fin: &[Gf128], y: &Y, coins: &Coins, claim: Gf128, batch: Gf128| {
        let w = Y::from_slice(&fin[..6]);
        let f = w.fold(y, coins.r_fin);
        let p_r = eval_at(&fin[6..9], coins.r_fin);
        let batch = batch + coins.delta[rounds] * (fin[7] + claim);
        (f, p_r, batch)
    };
    let (f_p, pr_p, b_p) = finish(&fin_p, &y_p, &plus, claim_p, batch_p);
    let (f_m, pr_m, b_m) = finish(&fin_m, &y_m, &minus, claim_m, batch_m);
    // As V- of `next`, my shares go to its V+, which is `prev`.
    let mut msg = f_m.to_vec();
    msg.extend_from_slice(&[pr_m, b_m]);
    let (_, from_next) = party.link.exchange(to_bytes(&msg), vec![])?;
    let other = from_bytes(&from_next, 8)?;
    let f = f_p.map2(&Y::from_slice(&other[..6]), |x, y| x + y);
    let accept = f.c() == pr_p + other[6] && b_p + other[7] == Gf128::ZERO;

    let verdict = vec![accept as u8];
    let (from_prev, from_next) = party.link.exchange(verdict.clone(), verdict)?;
    party.transcript = Transcript::default();
    party.verifications += 1;
    if !accept {
        return abort(format!("party {prev}'s AND messages are wrong"));
    }
    if from_prev != [1] || from_next != [1] {
        return abort("another party rejected a proof");
    }
    Ok(())
}

/// The prover's side: the statement folded round by round.
///
/// The `beta`-scaled inputs `(a1, a2, s, z)` of a folded gate share one factor
/// `beta_low(low) beta_inst(inst)`, and `c` is linear in them, so streamed rounds sum `c` and its
/// quadratic part on unscaled sums and apply the factor once per instance. Each round needs only
/// `p(0)` and the leading coefficient: `p(1) = p(0) + C` for the claim `C` the prover itself made.
struct Prover<'a> {
    tr: &'a [[u64; 8]],
    d: Dims,
    tau: Vec<Gf128>,
    beta_inst: Vec<Gf128>,
    rs: Vec<Gf128>,
    claim: Gf128,
    last_p: [Gf128; 3],
    /// Rounds computed from the bit transcript before materializing.
    streamed: usize,
    mat: Option<Vec<Y>>,
    threads: usize,
}

/// The prover's six transcript inputs of word `w` of a gate record.
#[inline(always)]
fn prover_words(rec: &[u64; 8]) -> [u64; 6] {
    [rec[U_OWN], rec[U_PREV], rec[V_OWN], rec[V_PREV], rec[RHO_OWN] ^ rec[RHO_PREV], rec[Z_OWN]]
}

/// Fields scaled by beta: a1, a2, s, z (indices into the six inputs).
const SCALED: [bool; 6] = [true, true, false, false, true, true];

/// Rounds computed on bit-words: with `C = 2^(j-1)` copies, a folded input is an F2-combination of
/// `C` constants, a product of two is one of `C^2` products of constants, and each round sum is
/// `sum (constant product) * (sum of beta_inst over the instances whose bits are set)`.
const BIT_ROUNDS: usize = 3;

/// `sum of beta[64 w + t]` over the set bits `t` of `bits`.
#[inline(always)]
fn select_sum(beta: &[Gf128], w: usize, mut bits: u64) -> Gf128 {
    let mut acc = Gf128::ZERO;
    while bits != 0 {
        acc += beta[64 * w + bits.trailing_zeros() as usize];
        bits &= bits - 1;
    }
    acc
}

/// `p(0), p(1), p(x)` from `p(0)`, the claim `p(0) + p(1)`, and the leading coefficient.
fn values_from(p0: Gf128, claim: Gf128, lead: Gf128) -> [Gf128; 3] {
    let p1 = p0 + claim;
    let e1 = p1 + p0 + lead;
    let x = Gf128::X;
    [p0, p1, p0 + e1 * x + lead * x * x]
}

impl<'a> Prover<'a> {
    fn new(transcript: &'a Transcript, d: Dims, tau: Vec<Gf128>, sigma: Vec<Gf128>, threads: usize) -> Self {
        let n_pad = 1usize << d.c;
        let streamed = (0..=d.a).find(|&j| (1usize << (d.a - j)) * n_pad * std::mem::size_of::<Y>() <= MATERIALIZE_BYTES).unwrap_or(d.a);
        Self {
            tr: &transcript.data,
            d,
            beta_inst: tensor(d.c, |t| (Gf128::ONE, sigma[t])),
            tau,
            rs: vec![],
            claim: Gf128::ZERO,
            last_p: [Gf128::ZERO; 3],
            streamed,
            mat: None,
            threads,
        }
    }

    /// Weights of the `2^(j-1)` copies folded before round `j` (1-based): `(scaled, plain)`.
    fn copy_tables(&self, j: usize) -> (Vec<Gf128>, Vec<Gf128>) {
        let a = self.d.a;
        // Copy bit q is AND bit a - j + 1 + q, folded in round j - 1 - q (challenge rs[j - 2 - q]).
        let scaled = tensor(j - 1, |q| {
            let r = self.rs[j - 2 - q];
            (Gf128::ONE + r, r * self.tau[a - j + 1 + q])
        });
        let plain = tensor(j - 1, |q| {
            let r = self.rs[j - 2 - q];
            (Gf128::ONE + r, r)
        });
        (scaled, plain)
    }

    fn beta_low(&self, j: usize, low: usize) -> Gf128 {
        (0..self.d.a + 1 - j).filter(|t| (low >> t) & 1 == 1).fold(Gf128::ONE, |acc, t| acc * self.tau[t])
    }

    /// Unscaled sums at level `j` of the low AND index `low`, for the 64 instances of word `w`:
    /// `sum_s table(s) x_f[s : low][inst]`.
    #[inline(always)]
    fn gather(&self, j: usize, tables: (&[Gf128], &[Gf128]), low: usize, w: usize, acc: &mut [[Gf128; 64]; 6]) {
        let d = self.d;
        let shift = d.a + 1 - j;
        *acc = [[Gf128::ZERO; 64]; 6];
        for s in 0..1usize << (j - 1) {
            let and = (s << shift) | low;
            if and >= d.n_and {
                continue;
            }
            let x = prover_words(&self.tr[and * d.words + w]);
            for f in 0..6 {
                let weight = if SCALED[f] { tables.0[s] } else { tables.1[s] };
                let mut bits = x[f];
                while bits != 0 {
                    let t = bits.trailing_zeros() as usize;
                    acc[f][t] += weight;
                    bits &= bits - 1;
                }
            }
        }
    }

    /// The next round's polynomial values at `0, 1, x`.
    fn round(&mut self) -> [Gf128; 3] {
        let j = self.rs.len() + 1;
        let (p0, lead) = if j <= self.streamed && j <= BIT_ROUNDS {
            self.bit_round(j)
        } else if j <= self.streamed {
            self.streamed_round(j)
        } else {
            if self.mat.is_none() {
                self.materialize(j);
            }
            let mat = self.mat.as_ref().unwrap();
            let half = mat.len() / 2;
            let p = parallel_sum(self.threads, half, |range| {
                let mut p = [Gf128::ZERO; 3];
                for k in range {
                    let (lo, hi) = (&mat[k], &mat[k + half]);
                    p[0] += lo.c();
                    p[1] += lo.add(hi).quad();
                }
                p
            });
            (p[0], p[1])
        };
        self.last_p = values_from(p0, self.claim, lead);
        self.last_p
    }

    /// [`Self::streamed_round`] on bit-words, for few copies (see [`BIT_ROUNDS`]).
    fn bit_round(&self, j: usize) -> (Gf128, Gf128) {
        let d = self.d;
        let (ut, wt) = self.copy_tables(j);
        let c = ut.len();
        let t_up = self.tau[d.a - j];
        // A-side constants of the lower copies, then the upper copies (one more tau factor).
        let ua: Vec<Gf128> = ut.iter().copied().chain(ut.iter().map(|&v| v * t_up)).collect();
        let half = 1usize << (d.a - j);
        let shift = d.a + 1 - j;
        let n_pad = 1usize << d.c;
        let beta = &self.beta_inst[..];
        let p = parallel_sum(self.threads, half, |range| {
            let mut p = [Gf128::ZERO; 3];
            let mut tc = vec![Gf128::ZERO; c * c];
            let mut tl = vec![Gf128::ZERO; c];
            let mut tq = vec![Gf128::ZERO; 2 * c * c];
            let mut lo = vec![[0u64; 6]; c];
            let mut hi = vec![[0u64; 6]; c];
            for low in range {
                tc.fill(Gf128::ZERO);
                tl.fill(Gf128::ZERO);
                tq.fill(Gf128::ZERO);
                for w in 0..d.words.min(n_pad.div_ceil(64)) {
                    for s in 0..c {
                        let load = |l: usize| {
                            let and = (s << shift) | l;
                            if and < d.n_and { prover_words(&self.tr[and * d.words + w]) } else { [0; 6] }
                        };
                        lo[s] = load(low);
                        hi[s] = load(low + half);
                    }
                    // c(lo): A1 (B1 + B2) + A2 B1 + S + Z.
                    for s in 0..c {
                        let x = &lo[s];
                        tl[s] += select_sum(beta, w, x[4] ^ x[5]);
                        for t in 0..c {
                            let y = &lo[t];
                            tc[s * c + t] += select_sum(beta, w, (x[0] & (y[2] ^ y[3])) ^ (x[1] & y[2]));
                        }
                    }
                    // quad(lo + hi): B sums combine bitwise, A sums keep 2c copies.
                    for t in 0..c {
                        let db1 = lo[t][2] ^ hi[t][2];
                        let db12 = db1 ^ lo[t][3] ^ hi[t][3];
                        for s2 in 0..2 * c {
                            let x = if s2 < c { &lo[s2] } else { &hi[s2 - c] };
                            tq[s2 * c + t] += select_sum(beta, w, (x[0] & db12) ^ (x[1] & db1));
                        }
                    }
                }
                let b = self.beta_low(j, low);
                let mut c0 = Gf128::ZERO;
                for s in 0..c {
                    c0 += ut[s] * tl[s];
                    for t in 0..c {
                        c0 += ut[s] * wt[t] * tc[s * c + t];
                    }
                }
                let mut q = Gf128::ZERO;
                for s2 in 0..2 * c {
                    for t in 0..c {
                        q += ua[s2] * wt[t] * tq[s2 * c + t];
                    }
                }
                p[0] += b * c0;
                p[1] += b * q;
            }
            p
        });
        (p[0], p[1])
    }

    /// `p(0)` and the leading coefficient of round `j`, from the bit transcript.
    fn streamed_round(&self, j: usize) -> (Gf128, Gf128) {
        let d = self.d;
        let tables = self.copy_tables(j);
        // The upper half's low index carries one more tau factor (bit a - j), folded into its table.
        let t_up = self.tau[d.a - j];
        let up_scaled: Vec<Gf128> = tables.0.iter().map(|&v| v * t_up).collect();
        let half = 1usize << (d.a - j);
        let n_pad = 1usize << d.c;
        let p = parallel_sum(self.threads, half, |range| {
            let mut p = [Gf128::ZERO; 3];
            let (mut lo, mut hi) = ([[Gf128::ZERO; 64]; 6], [[Gf128::ZERO; 64]; 6]);
            for low in range {
                let (mut s0, mut s2) = (Gf128::ZERO, Gf128::ZERO);
                for w in 0..d.words {
                    self.gather(j, (&tables.0, &tables.1), low, w, &mut lo);
                    self.gather(j, (&up_scaled, &tables.1), low + half, w, &mut hi);
                    for t in 0..64.min(n_pad - 64 * w) {
                        let l = Y { a1: lo[0][t], a2: lo[1][t], b1: lo[2][t], b2: lo[3][t], s: lo[4][t], z: lo[5][t] };
                        let h = Y { a1: hi[0][t], a2: hi[1][t], b1: hi[2][t], b2: hi[3][t], s: hi[4][t], z: hi[5][t] };
                        let beta = self.beta_inst[64 * w + t];
                        s0 += beta * l.c();
                        s2 += beta * l.add(&h).quad();
                    }
                }
                let b = self.beta_low(j, low);
                p[0] += b * s0;
                p[1] += b * s2;
            }
            p
        });
        (p[0], p[1])
    }

    /// Materializes the statement at level `j`: `2^(a - j + 1)` low AND indices by `2^c` instances.
    fn materialize(&mut self, j: usize) {
        let d = self.d;
        let n_pad = 1usize << d.c;
        let lows = 1usize << (d.a + 1 - j);
        let tables = self.copy_tables(j);
        let mut mat = vec![Y::default(); lows * n_pad];
        let this = &*self;
        let chunk = lows.div_ceil(this.threads).max(1);
        std::thread::scope(|scope| {
            for (c, part) in mat.chunks_mut(chunk * n_pad).enumerate() {
                let tables = &tables;
                scope.spawn(move || {
                    let mut acc = [[Gf128::ZERO; 64]; 6];
                    for (i, row) in part.chunks_mut(n_pad).enumerate() {
                        let low = c * chunk + i;
                        let b = this.beta_low(j, low);
                        for w in 0..d.words {
                            this.gather(j, (&tables.0, &tables.1), low, w, &mut acc);
                            for t in 0..64.min(n_pad - 64 * w) {
                                let f = b * this.beta_inst[64 * w + t];
                                row[64 * w + t] = Y {
                                    a1: f * acc[0][t],
                                    a2: f * acc[1][t],
                                    b1: acc[2][t],
                                    b2: acc[3][t],
                                    s: f * acc[4][t],
                                    z: f * acc[5][t],
                                };
                            }
                        }
                    }
                });
            }
        });
        self.mat = Some(mat);
    }

    fn fold(&mut self, r: Gf128) {
        self.claim = eval_at(&self.last_p, r);
        self.rs.push(r);
        if let Some(mat) = self.mat.as_mut() {
            let half = mat.len() / 2;
            let (lo, hi) = mat.split_at_mut(half);
            let chunk = half.div_ceil(self.threads).max(1);
            std::thread::scope(|scope| {
                for (l, h) in lo.chunks_mut(chunk).zip(hi.chunks(chunk)) {
                    scope.spawn(move || {
                        for (x, y) in l.iter_mut().zip(h) {
                            *x = x.fold(y, r);
                        }
                    });
                }
            });
            mat.truncate(half);
        }
    }

    /// The single gate left after every round.
    fn last(&mut self) -> Y {
        if self.mat.is_none() {
            self.materialize(self.rs.len() + 1);
        }
        let mat = self.mat.as_ref().unwrap();
        assert_eq!(mat.len(), 1);
        mat[0]
    }
}

/// Splits `0..len` across threads and adds up the per-range results.
fn parallel_sum(threads: usize, len: usize, f: impl Fn(std::ops::Range<usize>) -> [Gf128; 3] + Sync) -> [Gf128; 3] {
    let chunk = len.div_ceil(threads).max(1);
    let f = &f;
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..len).step_by(chunk).map(|start| scope.spawn(move || f(start..(start + chunk).min(len)))).collect();
        handles.into_iter().map(|h| h.join().unwrap()).fold([Gf128::ZERO; 3], |acc, p| [acc[0] + p[0], acc[1] + p[1], acc[2] + p[2]])
    })
}

/// Both verifier roles' shares of the last gate: as `V+` of `prev` (inputs a1, b1, s, z from its
/// messages and my `prev` components) and as `V-` of `next` (a2, b2, s from my `own` components).
fn verifier_pass(party: &Party, d: Dims, plus: &Coins, minus: &Coins) -> (Y, Y) {
    let n_pad = 1usize << d.c;
    // Weight of AND bit t: round a - t; of instance bit t: round a + c - t.
    let and_w = |c: &Coins, scaled: bool| tensor(d.a, |t| {
        let r = c.r[d.a - t - 1];
        (Gf128::ONE + r, if scaled { r * c.tau[t] } else { r })
    });
    let inst_w = |c: &Coins, scaled: bool| tensor(d.c, |t| {
        let r = c.r[d.a + d.c - t - 1];
        (Gf128::ONE + r, if scaled { r * c.sigma[t] } else { r })
    });
    let (pa, pa_w, pi, pi_w) = (and_w(plus, true), and_w(plus, false), inst_w(plus, true), inst_w(plus, false));
    let (ma, ma_w, mi, mi_w) = (and_w(minus, true), and_w(minus, false), inst_w(minus, true), inst_w(minus, false));
    let tr = &party.transcript.data;
    // (field, AND weights, instance weights) for the seven inputs: four as V+, three as V-.
    let inputs: [(usize, &[Gf128], &[Gf128]); 7] = [
        (U_PREV, &pa, &pi),
        (V_PREV, &pa_w, &pi_w),
        (RHO_PREV, &pa, &pi),
        (Z_PREV, &pa, &pi),
        (U_OWN, &ma, &mi),
        (V_OWN, &ma_w, &mi_w),
        (RHO_OWN, &ma, &mi),
    ];
    let chunk = d.n_and.div_ceil(party.threads).max(1);
    let sums = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..d.n_and)
            .step_by(chunk)
            .map(|start| {
                let inputs = &inputs;
                scope.spawn(move || {
                    let mut total = [Gf128::ZERO; 7];
                    for and in start..(start + chunk).min(d.n_and) {
                        let mut inner = [Gf128::ZERO; 7];
                        for w in 0..d.words {
                            let rec = &tr[and * d.words + w];
                            for (i, &(field, _, inst)) in inputs.iter().enumerate() {
                                let mut bits = rec[field];
                                while bits != 0 {
                                    let t = bits.trailing_zeros() as usize;
                                    if 64 * w + t < n_pad {
                                        inner[i] += inst[64 * w + t];
                                    }
                                    bits &= bits - 1;
                                }
                            }
                        }
                        for (i, &(_, aw, _)) in inputs.iter().enumerate() {
                            total[i] += aw[and] * inner[i];
                        }
                    }
                    total
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).fold([Gf128::ZERO; 7], |mut acc, t| {
            for i in 0..7 {
                acc[i] += t[i];
            }
            acc
        })
    });
    let z = Gf128::ZERO;
    (
        Y { a1: sums[0], a2: z, b1: sums[1], b2: z, s: sums[2], z: sums[3] },
        Y { a1: z, a2: sums[4], b1: z, b2: sums[5], s: sums[6], z },
    )
}
