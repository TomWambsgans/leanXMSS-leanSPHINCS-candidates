//! Replicated secret sharing among `n = 2f + 1` parties (Cramer, Damgard, Ishai, TCC 2005), and the
//! fixed public choices of the protocol: who computes which cross product, the collectors, the PRSS
//! owners, the openers' helpers, and the local conversion to Shamir shares over GF(2^128).
//!
//! The terms are the `f`-subsets `T` of parties (bitmasks, in increasing order); `x_T` is held by
//! the `f + 1` parties outside `T`. A party holds `C(n - 1, f)` terms: 2, 6, 20 for n = 3, 5, 7.
//! Shamir conversion: with `f_T` the degree-`f` polynomial that is 1 at 0 and vanishes on the points
//! `alpha_j` of the parties `j` in `T`, party `i`'s Shamir share of `x` is
//! `sum_{T held} f_T(alpha_i) x_T`: the shares lie on `sum_T x_T f_T`, of degree `f`, with value `x`
//! at 0 (CDI05, share conversion).

use mpc::gf128::Gf128;

const NONE: usize = usize::MAX;

pub struct Structure {
    pub n: usize,
    pub f: usize,
    /// The terms, as bitmasks of the parties in `T`, in increasing order.
    pub terms: Vec<u32>,
    /// Per party, the terms it holds (global indices, increasing): the local indices.
    pub held: Vec<Vec<usize>>,
    /// Per party and global term: the local index, or `NONE`.
    local: Vec<Vec<usize>>,
    /// Per party, its cross products `x_A y_B`, grouped by `A`: `(A, [B, ...])` in local indices.
    pub cross: Vec<Vec<(usize, Vec<usize>)>>,
    /// Per term, the holder that adds its PRSS value into the collected sum (the lowest holder).
    pub owner: Vec<usize>,
    /// The rotation of `(T*, collector)` pairs over the AND gates.
    collectors: Vec<(usize, usize)>,
    /// Per party and local term, the Shamir coefficient `f_T(alpha_i)`.
    pub phi: Vec<Vec<Gf128>>,
    /// Per party, subset sums of its coefficients, 8 local terms per table.
    pub tables: Vec<Vec<[Gf128; 256]>>,
    /// Lagrange coefficients at 0 for degree `2f` from all `n` points: `sum_i lambda_i p(alpha_i) = p(0)`.
    pub lambda: Vec<Gf128>,
    /// Interpolation from the shares of parties `0..=f`: rows for `alpha_j`, `j > f`, then for 0.
    interp: Vec<Vec<Gf128>>,
    /// Per king (opener), its helpers and the helper's local terms whose sum it sends.
    helpers: Vec<Vec<(usize, Vec<usize>)>>,
}

pub fn alpha(i: usize) -> Gf128 {
    Gf128(i as u128 + 1)
}

impl Structure {
    pub fn new(n: usize) -> Self {
        assert!(n >= 3 && n % 2 == 1 && n <= 15, "n = 2f + 1 parties, 3 <= n <= 15");
        let f = (n - 1) / 2;
        let terms: Vec<u32> = (0u32..1 << n).filter(|m| m.count_ones() as usize == f).collect();
        let holds = |i: usize, t: usize| terms[t] >> i & 1 == 0;
        let held: Vec<Vec<usize>> = (0..n).map(|i| (0..terms.len()).filter(|&t| holds(i, t)).collect()).collect();
        let mut local = vec![vec![NONE; terms.len()]; n];
        for i in 0..n {
            for (l, &t) in held[i].iter().enumerate() {
                local[i][t] = l;
            }
        }
        // Each cross product goes to the least loaded party outside A and B (|A u B| <= 2f < n).
        let mut load = vec![0usize; n];
        let mut pairs: Vec<Vec<(usize, usize)>> = vec![vec![]; n];
        for a in 0..terms.len() {
            for b in 0..terms.len() {
                let i = (0..n).filter(|&i| holds(i, a) && holds(i, b)).min_by_key(|&i| (load[i], i)).unwrap();
                load[i] += 1;
                pairs[i].push((local[i][a], local[i][b]));
            }
        }
        let cross = pairs
            .iter()
            .map(|ps| {
                let mut by_a: Vec<(usize, Vec<usize>)> = vec![];
                for &(a, b) in ps {
                    match by_a.iter_mut().find(|(x, _)| *x == a) {
                        Some((_, bs)) => bs.push(b),
                        None => by_a.push((a, vec![b])),
                    }
                }
                by_a
            })
            .collect();
        let owner = (0..terms.len()).map(|t| (0..n).find(|&i| holds(i, t)).unwrap()).collect();
        let mut collectors = vec![];
        for r in 0..=f {
            for t in 0..terms.len() {
                let hs: Vec<usize> = (0..n).filter(|&i| holds(i, t)).collect();
                collectors.push((t, hs[(r + t) % hs.len()]));
            }
        }
        let phi: Vec<Vec<Gf128>> = (0..n)
            .map(|i| {
                held[i]
                    .iter()
                    .map(|&t| (0..n).filter(|&j| terms[t] >> j & 1 == 1).fold(Gf128::ONE, |acc, j| acc * (alpha(i) + alpha(j)) * alpha(j).inv()))
                    .collect()
            })
            .collect();
        let tables = phi
            .iter()
            .map(|ph| {
                ph.chunks(8)
                    .map(|g| {
                        let mut table = [Gf128::ZERO; 256];
                        for v in 1..256usize {
                            let k = v.trailing_zeros() as usize;
                            table[v] = table[v & (v - 1)] + g.get(k).copied().unwrap_or(Gf128::ZERO);
                        }
                        table
                    })
                    .collect()
            })
            .collect();
        let lambda = (0..n).map(|i| (0..n).filter(|&j| j != i).fold(Gf128::ONE, |acc, j| acc * alpha(j) * (alpha(j) + alpha(i)).inv())).collect();
        let lagrange = |x: Gf128| -> Vec<Gf128> {
            (0..=f).map(|k| (0..=f).filter(|&m| m != k).fold(Gf128::ONE, |acc, m| acc * (x + alpha(m)) * (alpha(k) + alpha(m)).inv())).collect()
        };
        let mut interp: Vec<Vec<Gf128>> = (f + 1..n).map(|j| lagrange(alpha(j))).collect();
        interp.push(lagrange(Gf128::ZERO));
        // A king misses the terms that contain it; each goes to the first of the next f parties
        // outside it (a term has f - 1 other members, so one of them is outside).
        let helpers = (0..n)
            .map(|king| {
                let mut hs: Vec<(usize, Vec<usize>)> = vec![];
                for t in (0..terms.len()).filter(|&t| !holds(king, t)) {
                    let h = (1..=f).map(|d| (king + d) % n).find(|&h| holds(h, t)).unwrap();
                    match hs.iter_mut().find(|(x, _)| *x == h) {
                        Some((_, ls)) => ls.push(local[h][t]),
                        None => hs.push((h, vec![local[h][t]])),
                    }
                }
                hs.sort_by_key(|(h, _)| *h);
                hs
            })
            .collect();
        Self { n, f, terms, held, local, cross, owner, collectors, phi, tables, lambda, interp, helpers }
    }

    /// Terms per party.
    pub fn m(&self) -> usize {
        self.held[0].len()
    }

    pub fn holds(&self, i: usize, t: usize) -> bool {
        self.terms[t] >> i & 1 == 0
    }

    pub fn holders(&self, t: usize) -> impl Iterator<Item = usize> + '_ {
        (0..self.n).filter(move |&i| self.holds(i, t))
    }

    /// Party `i`'s local index of term `t`, if it holds it.
    pub fn local(&self, i: usize, t: usize) -> Option<usize> {
        Some(self.local[i][t]).filter(|&l| l != NONE)
    }

    /// The non-PRSS term `T*` of the `g`-th AND gate of a session, and its collector.
    pub fn collector(&self, g: u64) -> (usize, usize) {
        self.collectors[(g % self.collectors.len() as u64) as usize]
    }

    /// The opener of output `k`.
    pub fn king(&self, k: usize) -> usize {
        k % self.n
    }

    /// The helpers of `king`, and the local terms each sums for it.
    pub fn helpers(&self, king: usize) -> &[(usize, Vec<usize>)] {
        &self.helpers[king]
    }

    /// The value at 0 of the polynomial through the shares of `parties` (`f + 1` of them).
    pub fn interpolate(&self, parties: &[usize], shares: &[Gf128]) -> Gf128 {
        parties.iter().fold(Gf128::ZERO, |acc, &k| {
            let l = parties.iter().filter(|&&m| m != k).fold(Gf128::ONE, |a, &m| a * alpha(m) * (alpha(k) + alpha(m)).inv());
            acc + l * shares[k]
        })
    }

    /// The value of a Shamir sharing of degree `f` given all `n` shares, or `None` if they do not lie
    /// on one such polynomial: the `f + 1` honest shares fix it, so a wrong corrupt share is caught.
    pub fn reconstruct(&self, shares: &[Gf128]) -> Option<Gf128> {
        let f = self.f;
        let at = |row: &[Gf128]| row.iter().zip(&shares[..=f]).fold(Gf128::ZERO, |acc, (&c, &s)| acc + c * s);
        if (f + 1..self.n).any(|j| at(&self.interp[j - f - 1]) != shares[j]) {
            return None;
        }
        Some(at(&self.interp[self.n - f - 1]))
    }
}

/// Transposes an 8x8 bit matrix: bit `j` of byte `i` becomes bit `i` of byte `j`.
#[inline(always)]
fn transpose8(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^ t ^ (t << 28)
}

/// Shamir shares of 64 instances from a party's term words `terms` (one bit-word per local term):
/// `out[t] = sum_l phi_l bit_t(terms[l])`, by the subset-sum `tables` (8 terms per byte lookup).
#[inline]
pub fn convert(tables: &[[Gf128; 256]], terms: &[u64], out: &mut [Gf128; 64]) {
    *out = [Gf128::ZERO; 64];
    convert_add(tables, terms, out);
}

/// [`convert`], added to `out`.
#[inline]
pub fn convert_add(tables: &[[Gf128; 256]], terms: &[u64], out: &mut [Gf128; 64]) {
    for (g, table) in tables.iter().enumerate() {
        let xs = &terms[8 * g..terms.len().min(8 * g + 8)];
        for b in 0..8 {
            let rows = xs.iter().enumerate().fold(0u64, |m, (k, &x)| m | ((x >> (8 * b)) & 0xff) << (8 * k));
            if rows == 0 {
                continue;
            }
            let cols = transpose8(rows);
            for k in 0..8 {
                let v = (cols >> (8 * k)) & 0xff;
                if v != 0 {
                    out[8 * b + k] += table[v as usize];
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_and_coverage() {
        for (n, m) in [(3, 2), (5, 6), (7, 20)] {
            let s = Structure::new(n);
            assert_eq!(s.m(), m);
            // Every cross product exactly once, by a party holding both terms.
            let total: usize = s.cross.iter().flat_map(|c| c.iter().map(|(_, bs)| bs.len())).sum();
            assert_eq!(total, s.terms.len() * s.terms.len());
            // Collectors hold T*; each party collects equally often.
            let mut count = vec![0; n];
            for g in 0..s.collectors.len() as u64 {
                let (t, c) = s.collector(g);
                assert!(s.holds(c, t));
                count[c] += 1;
            }
            assert!(count.iter().all(|&c| c == count[0]));
            // A king's helpers cover its missing terms, with f of them.
            for king in 0..n {
                let covered: usize = s.helpers(king).iter().map(|(_, ls)| ls.len()).sum();
                assert_eq!(covered, s.terms.len() - m);
                assert_eq!(s.helpers(king).len(), s.f);
            }
        }
    }

    #[test]
    fn shamir_conversion_and_products() {
        for n in [3, 5, 7] {
            let s = Structure::new(n);
            let mut seed = 0x1234_5678_9abc_def0u128 * n as u128;
            let mut rnd = || {
                seed = seed.wrapping_mul(0x2545_f491_4f6c_dd1d_9e37_79b9_7f4a_7c15).wrapping_add(1);
                Gf128(seed)
            };
            let (x, y): (Vec<Gf128>, Vec<Gf128>) = s.terms.iter().map(|_| (rnd(), rnd())).unzip();
            let sum = |v: &[Gf128]| v.iter().fold(Gf128::ZERO, |a, &b| a + b);
            let share = |v: &[Gf128], i: usize| s.held[i].iter().zip(&s.phi[i]).fold(Gf128::ZERO, |a, (&t, &c)| a + c * v[t]);
            let sx: Vec<Gf128> = (0..n).map(|i| share(&x, i)).collect();
            assert_eq!(s.reconstruct(&sx), Some(sum(&x)));
            let mut bad = sx.clone();
            bad[n - 1] += Gf128::ONE;
            assert_eq!(s.reconstruct(&bad), None);
            let prod = (0..n).fold(Gf128::ZERO, |a, i| a + s.lambda[i] * sx[i] * share(&y, i));
            assert_eq!(prod, sum(&x) * sum(&y));
            // The bit conversion agrees with the field one.
            let i = n - 1;
            let words: Vec<u64> = (0..s.m()).map(|l| 0x9e37_79b9_7f4a_7c15u64.rotate_left(l as u32 * 7) ^ l as u64).collect();
            let mut out = [Gf128::ZERO; 64];
            convert(&s.tables[i], &words, &mut out);
            for t in 0..64 {
                let want = (0..s.m()).filter(|&l| words[l] >> t & 1 == 1).fold(Gf128::ZERO, |a, l| a + s.phi[i][l]);
                assert_eq!(out[t], want);
            }
        }
    }
}
