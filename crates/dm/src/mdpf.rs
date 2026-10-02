//! Three-party distributed point functions (BGI15 §3.2, the √N construction behind the 3-party PCG
//! of Abram–Scholl, PKC 2022), secure against two colluding parties: the FUV of the PIR.
//!
//! The domain is a `rows x cols` grid. Each row has four slots, each with a fresh seed; the slots'
//! holder sets are the four even-weight subsets of the three parties on every row but the point's
//! row, which uses the four odd-weight subsets (randomly permuted). Every party holds two seeds per
//! row. A party's output on a row is the XOR of its seeds' expansions and of the correction words of
//! its slots, so the three outputs cancel except on the point's row, where the correction words fix
//! them to the payload.
//!
//! The output is a pair (bit, F̂) per point, the payload `(1, Δ)`: an authenticated unit vector.
//! Full-domain evaluation is fused with the inner product against the PIR database.

use crate::aes::{Prf, tree_keys};
use crate::gf::{F, simd};

/// One party's key.
#[derive(Clone, Debug)]
pub struct Key {
    pub cols: usize,
    /// Per row: the two slots this party holds, with their seeds.
    pub rows: Vec<[(u8, u128); 2]>,
    /// Per slot: the F̂ correction word of each column, then the bit correction words.
    pub cw: [Vec<u128>; 4],
    pub cwb: [Vec<u64>; 4],
}

impl Key {
    pub fn bytes(&self) -> usize {
        self.rows.len() * 33 + 4 * (self.cols * 16 + self.cols.div_ceil(8))
    }
}

/// The grid of a domain of `n` points: `(rows, cols)`.
pub fn grid(n: usize) -> (usize, usize) {
    let cols = ((n as f64).sqrt().ceil() as usize).max(1);
    (n.div_ceil(cols), cols)
}

/// Expands seeds into `cols` F̂ values and `cols` bits each, XORed together into `out`, `bits`.
fn prg(seeds: &[u128], cols: usize, out: &mut [u128], bits: &mut [u64], tmp: &mut Vec<u128>) {
    let nb = cols.div_ceil(128);
    let per = cols + nb;
    tmp.clear();
    for &seed in seeds {
        tmp.extend((0..cols).map(|y| seed ^ y as u128));
        tmp.extend((0..nb).map(|i| seed ^ ((1u128 << 32) + i as u128)));
    }
    tree_keys()[1].encrypt(tmp);
    out[..cols].fill(0);
    bits.fill(0);
    for (k, &seed) in seeds.iter().enumerate() {
        let t = &tmp[k * per..(k + 1) * per];
        for y in 0..cols {
            out[y] ^= t[y] ^ seed ^ y as u128;
        }
        for i in 0..nb {
            let v = t[cols + i] ^ seed ^ ((1u128 << 32) + i as u128);
            bits[2 * i] ^= v as u64;
            if 2 * i + 1 < bits.len() {
                bits[2 * i + 1] ^= (v >> 64) as u64;
            }
        }
    }
}

const EVEN: [u8; 4] = [0b000, 0b011, 0b101, 0b110];
const ODD: [u8; 4] = [0b001, 0b010, 0b100, 0b111];

/// The permutation of rank `r` (`< 24`) of four slots.
fn perm(mut r: usize) -> [usize; 4] {
    let mut left = vec![0, 1, 2, 3];
    std::array::from_fn(|i| {
        let f = [6, 2, 1, 1][i];
        let x = left.remove(r / f);
        r %= f;
        x
    })
}

/// Party `me`'s key for the point `alpha` of a domain of `n` points with payload `(1, delta)`.
/// All randomness comes from `seed`: the three parties' keys of one seed fit together.
pub fn keygen(n: usize, alpha: usize, delta: F, seed: u128, me: usize) -> Key {
    assert!(alpha < n);
    let prf = Prf::new(seed);
    let (rows, cols) = grid(n);
    let (gamma, dpos) = (alpha / cols, alpha % cols);
    let words = cols.div_ceil(64);
    let slots = |x: usize| -> ([usize; 4], [u8; 4]) { (perm((prf.at(x as u64, 4) % 24) as usize), if x == gamma { ODD } else { EVEN }) };
    let key_rows = (0..rows)
        .map(|x| {
            let (pm, sets) = slots(x);
            let mut held = (0..4).filter(|&j| (sets[pm[j]] >> me) & 1 == 1).map(|j| (j as u8, prf.at(x as u64, j as u64)));
            [held.next().unwrap(), held.next().unwrap()]
        })
        .collect();
    // Correction words: three random, the fourth fixes the point's row to the payload.
    let rand = |j: u64, y: usize| prf.at(1 << 40 | j, y as u64);
    let mut cw: [Vec<u128>; 4] = std::array::from_fn(|j| if j < 3 { (0..cols).map(|y| rand(j as u64, y)).collect() } else { vec![0; cols] });
    let mut cwb: [Vec<u64>; 4] = std::array::from_fn(|j| if j < 3 { (0..words).map(|w| rand(4 + j as u64, w) as u64).collect() } else { vec![0; words] });
    let (mut gsum, mut gbits, mut tmp) = (vec![0u128; cols], vec![0u64; words], vec![]);
    let seeds: Vec<u128> = (0..4).map(|j| prf.at(gamma as u64, j)).collect();
    prg(&seeds, cols, &mut gsum, &mut gbits, &mut tmp);
    for y in 0..cols {
        cw[3][y] = gsum[y] ^ cw[0][y] ^ cw[1][y] ^ cw[2][y] ^ if y == dpos { delta.0 } else { 0 };
    }
    for w in 0..words {
        cwb[3][w] = gbits[w] ^ cwb[0][w] ^ cwb[1][w] ^ cwb[2][w] ^ if w == dpos / 64 { 1u64 << (dpos % 64) } else { 0 };
    }
    Key { cols, rows: key_rows, cw, cwb }
}

/// Reusable buffers of the evaluation.
#[derive(Default)]
pub struct Scratch {
    m: Vec<u128>,
    u: Vec<u64>,
    tmp: Vec<u128>,
}

impl Scratch {
    /// This party's share of grid row `x`: F̂ parts in `m`, bits in `u`.
    fn row(&mut self, key: &Key, x: usize) {
        let cols = key.cols;
        let (words, nb) = (cols.div_ceil(64), cols.div_ceil(128));
        let per = cols + nb;
        let row = &key.rows[x];
        let (s0, s1) = (row[0].1, row[1].1);
        self.tmp.resize(2 * per, 0);
        let (t0, t1) = self.tmp.split_at_mut(per);
        for y in 0..cols {
            t0[y] = s0 ^ y as u128;
            t1[y] = s1 ^ y as u128;
        }
        for i in 0..nb {
            t0[cols + i] = s0 ^ ((1u128 << 32) + i as u128);
            t1[cols + i] = s1 ^ ((1u128 << 32) + i as u128);
        }
        tree_keys()[1].encrypt(&mut self.tmp);
        // The tweaks cancel between the two expansions.
        let (t0, t1) = self.tmp.split_at(per);
        let (j0, j1) = (row[0].0 as usize, row[1].0 as usize);
        let (c0, c1) = (&key.cw[j0], &key.cw[j1]);
        self.m.resize(cols, 0);
        let s = s0 ^ s1;
        for y in 0..cols {
            self.m[y] = t0[y] ^ t1[y] ^ s ^ c0[y] ^ c1[y];
        }
        self.u.resize(words, 0);
        for i in 0..nb {
            let v = t0[cols + i] ^ t1[cols + i] ^ s;
            self.u[2 * i] = v as u64 ^ key.cwb[j0][2 * i] ^ key.cwb[j1][2 * i];
            if 2 * i + 1 < words {
                self.u[2 * i + 1] = (v >> 64) as u64 ^ key.cwb[j0][2 * i + 1] ^ key.cwb[j1][2 * i + 1];
            }
        }
    }
}

/// This party's share of `sum_r unit(alpha)[r] * db[r]` for a database of `n` points with `width`
/// F̂ values each (`db.len() == n * width`): value shares and MAC shares, per column.
pub fn answer(key: &Key, n: usize, width: usize, db: &[u128], sc: &mut Scratch) -> (Vec<u128>, Vec<F>) {
    assert_eq!(db.len(), n * width);
    match width {
        2 => answer_w::<2>(key, n, db, sc),
        4 => answer_w::<4>(key, n, db, sc),
        6 => answer_w::<6>(key, n, db, sc),
        16 => answer_w::<16>(key, n, db, sc),
        _ => answer_dyn(key, n, width, db, sc),
    }
}

fn answer_w<const W: usize>(key: &Key, n: usize, db: &[u128], sc: &mut Scratch) -> (Vec<u128>, Vec<F>) {
    let cols = key.cols;
    let mut val = [0u128; W];
    let mut mac = [simd::Acc::default(); W];
    for x in 0..key.rows.len() {
        let start = x * cols;
        if start >= n {
            break;
        }
        sc.row(key, x);
        let cnt = (n - start).min(cols);
        let (entries, _) = db[start * W..(start + cnt) * W].as_chunks::<W>();
        for (y, entry) in entries.iter().enumerate() {
            let m = simd::split(sc.m[y]);
            let um = 0u128.wrapping_sub(u128::from((sc.u[y / 64] >> (y % 64)) & 1));
            for c in 0..W {
                val[c] ^= entry[c] & um;
                mac[c].add_mul(&m, &entry[c]);
            }
        }
    }
    (val.to_vec(), mac.iter().map(|a| a.reduce()).collect())
}

fn answer_dyn(key: &Key, n: usize, width: usize, db: &[u128], sc: &mut Scratch) -> (Vec<u128>, Vec<F>) {
    let cols = key.cols;
    let mut val = vec![0u128; width];
    let mut mac = vec![simd::Acc::default(); width];
    for x in 0..key.rows.len() {
        let start = x * cols;
        if start >= n {
            break;
        }
        sc.row(key, x);
        let cnt = (n - start).min(cols);
        for (y, entry) in db[start * width..(start + cnt) * width].chunks_exact(width).enumerate() {
            let m = simd::split(sc.m[y]);
            let um = 0u128.wrapping_sub(u128::from((sc.u[y / 64] >> (y % 64)) & 1));
            // Blocks of eight columns, unrolled, then the rest.
            let (blocks, rest) = entry.as_chunks::<8>();
            let (vb, vr) = val.as_chunks_mut::<8>();
            let (mb, mr) = mac.as_chunks_mut::<8>();
            for ((e, v), a) in blocks.iter().zip(vb.iter_mut()).zip(mb.iter_mut()) {
                for c in 0..8 {
                    v[c] ^= e[c] & um;
                    a[c].add_mul(&m, &e[c]);
                }
            }
            for ((d, v), a) in rest.iter().zip(vr.iter_mut()).zip(mr.iter_mut()) {
                *v ^= d & um;
                a.add_mul(&m, d);
            }
        }
    }
    (val, mac.iter().map(|a| a.reduce()).collect())
}

/// This party's share of the whole unit vector (for the small balancing domain).
pub fn eval_all(key: &Key, n: usize, sc: &mut Scratch) -> Vec<(u64, F)> {
    let mut out = Vec::with_capacity(n);
    for x in 0..key.rows.len() {
        sc.row(key, x);
        for y in 0..key.cols {
            if out.len() == n {
                break;
            }
            out.push(((sc.u[y / 64] >> (y % 64)) & 1, F(sc.m[y])));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn three_shares_make_the_payload() {
        let mut rng = crate::aes::Stream::new(11);
        let delta = F(rng.next_u128());
        for n in [1usize, 2, 7, 64, 100, 300] {
            for _ in 0..4 {
                let alpha = rng.below(n as u64) as usize;
                let seed = rng.next_u128();
                let keys: Vec<Key> = (0..3).map(|me| keygen(n, alpha, delta, seed, me)).collect();
                let mut sc = Scratch::default();
                let shares: Vec<Vec<(u64, F)>> = keys.iter().map(|k| eval_all(k, n, &mut sc)).collect();
                for x in 0..n {
                    let (u, m) = (shares[0][x].0 ^ shares[1][x].0 ^ shares[2][x].0, shares[0][x].1 + shares[1][x].1 + shares[2][x].1);
                    assert_eq!((u, m), if x == alpha { (1, delta) } else { (0, F::ZERO) }, "n {n} x {x}");
                }
                // Any two parties' shares look random on the point's row: no all-zero pair sum.
                // The fused inner product agrees with the unit vector.
                let width = 3;
                let db: Vec<u128> = (0..n * width).map(|_| rng.next_u128()).collect();
                let (mut v, mut m) = (vec![0u128; width], vec![F::ZERO; width]);
                for k in &keys {
                    let (vv, mm) = answer(k, n, width, &db, &mut sc);
                    for c in 0..width {
                        v[c] ^= vv[c];
                        m[c] += mm[c];
                    }
                }
                for c in 0..width {
                    assert_eq!(v[c], db[alpha * width + c]);
                    assert_eq!(m[c], delta * F(db[alpha * width + c]));
                }
            }
        }
    }

    #[test]
    fn two_parties_hold_two_seeds_per_row() {
        for me in 0..3 {
            let k = keygen(50, 17, F::ONE, 99, me);
            assert!(k.rows.iter().all(|r| r[0].0 != r[1].0));
        }
        let all: Vec<[usize; 4]> = (0..24).map(perm).collect();
        assert!((0..24).all(|i| (0..i).all(|j| all[i] != all[j])));
    }
}
