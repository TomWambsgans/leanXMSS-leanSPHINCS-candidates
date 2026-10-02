//! Two-party distributed point functions over a ternary tree (BGI16 with arity 3, as in
//! FOLEAGE's tri-dpf), with F4 leaves: the cross products of the PCG.
//!
//! The domain `3^(depth + leaf)` is a tree of `depth` ternary levels whose leaves each pack `3^leaf`
//! F4 values (at most 243) as two 256-bit planes. A seed's low bit is its control bit; a correction
//! word per child carries both the seed and the control-bit correction. The PRG is fixed-key AES in
//! tweaked Matyas–Meyer–Oseas mode. The keys come from the (simulated) dealer; only full-domain
//! evaluation is needed.

use crate::aes::{Stream, tree_keys};
use crate::ring::F4;

/// One leaf: the low plane in blocks 0 and 1, the high plane in blocks 2 and 3.
pub type Leaf = [u128; 4];

#[derive(Clone, Debug)]
pub struct Key {
    pub root: u128,
    pub cw: Vec<[u128; 3]>,
    pub leaf: [u128; 4],
}

impl Key {
    pub fn bytes(&self) -> usize {
        16 + 48 * self.cw.len() + 64
    }
}

/// The tweak of child `c`: one fixed key, children told apart by tweaks (tweaked MMO), so a
/// level of many nodes is one pipelined AES pass.
#[inline(always)]
fn tweak(c: usize) -> u128 {
    (c as u128) << 64
}

fn expand(seeds: &[u128], c: usize, out: &mut [u128]) {
    for (o, s) in out.iter_mut().zip(seeds) {
        *o = s ^ tweak(c);
    }
    tree_keys()[0].encrypt(out);
    for (o, s) in out.iter_mut().zip(seeds) {
        *o ^= s ^ tweak(c);
    }
}

fn convert(s: u128) -> [u128; 4] {
    let mut b: [u128; 4] = std::array::from_fn(|i| s ^ i as u128);
    let x = b;
    tree_keys()[2].encrypt(&mut b);
    std::array::from_fn(|i| b[i] ^ x[i])
}

/// Keys for the point `alpha` (in `0..3^(depth + leaf)`) with value `beta`.
pub fn keygen(depth: usize, leaf: usize, alpha: usize, beta: F4, rng: &mut Stream) -> [Key; 2] {
    let per_leaf = crate::ring::pow3(leaf);
    let (mut path, low) = (alpha / per_leaf, alpha % per_leaf);
    let mut digits = vec![0usize; depth];
    for d in (0..depth).rev() {
        digits[d] = path % 3;
        path /= 3;
    }
    let mut s = [rng.next_u128() & !1, rng.next_u128() | 1];
    let roots = s;
    let mut cws = Vec::with_capacity(depth);
    for &keep in &digits {
        let mut x = [[0u128; 3]; 2];
        for b in 0..2 {
            for c in 0..3 {
                let mut o = [0u128];
                expand(&[s[b]], c, &mut o);
                x[b][c] = o[0];
            }
        }
        let mut cw = [0u128; 3];
        for c in 0..3 {
            let d = x[0][c] ^ x[1][c];
            cw[c] = if c == keep { (rng.next_u128() & !1) | ((d & 1) ^ 1) } else { d };
        }
        for b in 0..2 {
            s[b] = x[b][keep] ^ (cw[keep] & 0u128.wrapping_sub(s[b] & 1));
        }
        cws.push(cw);
    }
    let (c0, c1) = (convert(s[0]), convert(s[1]));
    let mut payload = [0u128; 4];
    payload[low / 128] |= u128::from(beta & 1) << (low % 128);
    payload[2 + low / 128] |= u128::from(beta >> 1) << (low % 128);
    let leaf_cw: [u128; 4] = std::array::from_fn(|i| c0[i] ^ c1[i] ^ payload[i]);
    [0, 1].map(|b| Key { root: roots[b], cw: cws.clone(), leaf: leaf_cw })
}

/// Reusable buffers of the full-domain evaluation.
#[derive(Default)]
pub struct Scratch {
    cur: Vec<u128>,
    next: Vec<u128>,
    tmp: Vec<u128>,
}

/// XORs this key's share of the whole domain into `acc` (`3^depth` leaves).
pub fn eval_xor(key: &Key, acc: &mut [Leaf], sc: &mut Scratch) {
    eval_xor_many(&[key], acc, sc);
}

/// The XOR of several keys' shares (of the same depth), at once: their levels share AES passes.
pub fn eval_xor_many(keys: &[&Key], acc: &mut [Leaf], sc: &mut Scratch) {
    let k = keys.len();
    let n_leaves = acc.len();
    sc.cur.clear();
    sc.cur.extend(keys.iter().map(|key| key.root));
    for d in 0..keys[0].cw.len() {
        let m = sc.cur.len();
        let per = m / k;
        sc.tmp.resize(3 * m, 0);
        for u in 0..m {
            for c in 0..3 {
                sc.tmp[3 * u + c] = sc.cur[u] ^ tweak(c);
            }
        }
        tree_keys()[0].encrypt(&mut sc.tmp);
        sc.next.resize(3 * m, 0);
        for u in 0..m {
            let (cw, t) = (&keys[u / per].cw[d], 0u128.wrapping_sub(sc.cur[u] & 1));
            for c in 0..3 {
                sc.next[3 * u + c] = sc.tmp[3 * u + c] ^ sc.cur[u] ^ tweak(c) ^ (cw[c] & t);
            }
        }
        std::mem::swap(&mut sc.cur, &mut sc.next);
    }
    assert_eq!(sc.cur.len(), k * n_leaves);
    // Leaf expansion: four blocks per leaf, encrypted in one pass.
    sc.tmp.resize(4 * k * n_leaves, 0);
    for (u, &s) in sc.cur.iter().enumerate() {
        for i in 0..4 {
            sc.tmp[4 * u + i] = s ^ i as u128;
        }
    }
    tree_keys()[2].encrypt(&mut sc.tmp);
    for (ki, key) in keys.iter().enumerate() {
        let leaf_cw = &key.leaf;
        for (l, a) in acc.iter_mut().enumerate() {
            let u = ki * n_leaves + l;
            let s = sc.cur[u];
            let t = 0u128.wrapping_sub(s & 1);
            for i in 0..4 {
                a[i] ^= sc.tmp[4 * u + i] ^ s ^ i as u128 ^ (leaf_cw[i] & t);
            }
        }
    }
}

/// The F4 value at `pos` of a leaf.
pub fn leaf_get(l: &Leaf, pos: usize) -> F4 {
    (((l[pos / 128] >> (pos % 128)) & 1) | (((l[2 + pos / 128] >> (pos % 128)) & 1) << 1)) as F4
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shares_xor_to_the_point() {
        let mut rng = Stream::new(7);
        for (depth, leaf) in [(0, 2), (1, 3), (3, 5), (4, 1)] {
            let size = crate::ring::pow3(depth + leaf);
            for trial in 0..6 {
                let alpha = rng.below(size as u64) as usize;
                let beta = 1 + (trial % 3) as u8;
                let keys = keygen(depth, leaf, alpha, beta, &mut rng);
                let nl = crate::ring::pow3(depth);
                let mut acc = vec![[0u128; 4]; nl];
                let mut sc = Scratch::default();
                let mut one = vec![[0u128; 4]; nl];
                eval_xor(&keys[0], &mut one, &mut sc);
                eval_xor(&keys[0], &mut acc, &mut sc);
                eval_xor(&keys[1], &mut acc, &mut sc);
                // Each share alone looks random; the XOR is the point function.
                assert!(one.iter().any(|l| l.iter().any(|&w| w != 0)));
                let per = crate::ring::pow3(leaf);
                for x in 0..size {
                    let v = leaf_get(&acc[x / per], x % per);
                    assert_eq!(v, if x == alpha { beta } else { 0 }, "depth {depth} leaf {leaf} x {x}");
                }
                for l in &acc {
                    // Padding beyond 3^leaf values cancels too.
                    for pos in per..256 {
                        assert_eq!(leaf_get(l, pos), 0);
                    }
                }
            }
        }
    }
}
