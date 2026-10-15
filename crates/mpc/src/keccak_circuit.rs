//! Keccak-f[1600] as a Boolean circuit, and `Th` on a secret 16-byte value.
//!
//! The same model as scripts/keccak_circuit.py: theta, rho, pi and iota are XORs, rotations and
//! constants, free in the MPC; chi, `a ^ (!b & c)`, is the only non-linear step, one AND per bit:
//! 1,600 ANDs per round, 38,400 and AND-depth 24 when every input is secret. Constant and public
//! inputs fold part of the first round away, and the last round keeps only the output lanes: one
//! `Th` on a secret value is 36,288 ANDs.

use crate::circuit::{Builder, Wire, ZERO};

/// A 64-bit lane, least significant bit first.
pub type Lane = [Wire; 64];

pub fn const_lane(b: &Builder, v: u64) -> Lane {
    std::array::from_fn(|i| b.constant((v >> i) & 1 == 1))
}

fn xor_l(b: &mut Builder, x: &Lane, y: &Lane) -> Lane {
    std::array::from_fn(|i| b.xor(x[i], y[i]))
}

/// Rotation left by `r`: bit `i` of the result is bit `i - r` of the input.
fn rotl_l(x: &Lane, r: u32) -> Lane {
    std::array::from_fn(|i| x[(i + 64 - r as usize) % 64])
}

/// Keccak-f[1600] on 25 lanes, lane `x + 5 y` being `A[x][y]`, as in [`sha3::keccak_f`].
pub fn keccak_f(b: &mut Builder, a: &mut [Lane; 25]) {
    for rc in sha3::RC {
        // theta
        let mut c = [[ZERO; 64]; 5];
        for x in 0..5 {
            c[x] = a[x];
            for y in 1..5 {
                c[x] = xor_l(b, &c[x], &a[x + 5 * y]);
            }
        }
        for x in 0..5 {
            let d = xor_l(b, &c[(x + 4) % 5], &rotl_l(&c[(x + 1) % 5], 1));
            for y in 0..5 {
                a[x + 5 * y] = xor_l(b, &a[x + 5 * y], &d);
            }
        }
        // rho and pi
        let mut carried = a[1];
        for i in 0..24 {
            let next = a[sha3::PI[i]];
            a[sha3::PI[i]] = rotl_l(&carried, sha3::RHO[i]);
            carried = next;
        }
        // chi
        for y in 0..5 {
            let row: [Lane; 5] = std::array::from_fn(|x| a[x + 5 * y]);
            for x in 0..5 {
                a[x + 5 * y] = std::array::from_fn(|i| {
                    let not_next = b.not(row[(x + 1) % 5][i]);
                    let t = b.and(not_next, row[(x + 2) % 5][i]);
                    b.xor(row[x][i], t)
                });
            }
        }
        // iota
        a[0] = xor_l(b, &a[0], &const_lane(b, rc));
    }
}

/// How each of the 256 bits of `P | tw` enters a batch: a constant shared by every instance, or a
/// public input whose per-instance values the caller supplies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PubBit {
    Const(bool),
    Input,
}

/// The circuit of `Th(P, tw, x) = SHA3-256(P | tw | x)[..16]` on a secret 16-byte `x`: one
/// permutation of a 48-byte input. `prefix[i]` describes bit `i` of `P | tw` (little endian);
/// public inputs come in that order, then the 128 secret bits of `x`, and the outputs are the 128
/// bits of the truncated digest.
pub fn th_circuit(prefix: &[PubBit; 256]) -> Builder {
    let mut b = Builder::new();
    let prefix_wires: Vec<Wire> = prefix
        .iter()
        .map(|p| match *p {
            PubBit::Const(v) => b.constant(v),
            PubBit::Input => b.pub_input(),
        })
        .collect();
    let secret: Vec<Wire> = (0..128).map(|_| b.sec_input()).collect();
    // The padded block: `P | tw | x`, then 0x06 at byte 48 and 0x80 at byte 135.
    let mut padding = [0u8; sha3::RATE];
    padding[48] = 0x06;
    padding[sha3::RATE - 1] = 0x80;
    let mut a: [Lane; 25] = std::array::from_fn(|lane| {
        std::array::from_fn(|i| {
            let bit = 64 * lane + i;
            match bit {
                0..256 => prefix_wires[bit],
                256..384 => secret[bit - 256],
                _ if bit < 8 * sha3::RATE => b.constant((padding[bit / 8] >> (bit % 8)) & 1 == 1),
                _ => ZERO,
            }
        })
    });
    keccak_f(&mut b, &mut a);
    for lane in &a[..2] {
        for &bit in lane {
            b.output(bit);
        }
    }
    b
}

/// Splits per-instance 32-byte `P | tw` prefixes into constant bits and public inputs (bit-sliced:
/// one bit-vector over instances per public input), the layout [`th_circuit`] expects.
pub fn split_prefixes(prefixes: &[[u8; 32]]) -> ([PubBit; 256], Vec<Vec<u64>>) {
    let words = prefixes.len().div_ceil(64);
    let bit = |p: &[u8; 32], i: usize| (p[i / 8] >> (i % 8)) & 1 == 1;
    let mut layout = [PubBit::Const(false); 256];
    let mut inputs = vec![];
    for i in 0..256 {
        let first = bit(&prefixes[0], i);
        if prefixes.iter().all(|p| bit(p, i) == first) {
            layout[i] = PubBit::Const(first);
        } else {
            layout[i] = PubBit::Input;
            let mut v = vec![0u64; words];
            for (k, p) in prefixes.iter().enumerate() {
                v[k / 64] |= u64::from(bit(p, i)) << (k % 64);
            }
            inputs.push(v);
        }
    }
    (layout, inputs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rng(seed: u64) -> impl FnMut() -> u64 {
        let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
        move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        }
    }

    #[test]
    fn all_secret_permutation_counts_and_matches() {
        let mut b = Builder::new();
        let mut a: [Lane; 25] = std::array::from_fn(|_| std::array::from_fn(|_| b.sec_input()));
        keccak_f(&mut b, &mut a);
        for lane in &a {
            for &bit in lane {
                b.output(bit);
            }
        }
        let p = b.compile();
        assert_eq!(p.n_and, 24 * 1600);
        assert_eq!(p.depth, 24);
        let mut r = rng(1);
        let states: Vec<[u64; 25]> = (0..64).map(|_| std::array::from_fn(|_| r())).collect();
        // Bit-sliced: input `64 * lane + i` holds bit `i` of `lane` in every instance.
        let sec_in: Vec<Vec<u64>> = (0..1600)
            .map(|bit| vec![states.iter().enumerate().fold(0u64, |acc, (k, s)| acc | ((s[bit / 64] >> (bit % 64)) & 1) << k)])
            .collect();
        let got = p.eval_plain(1, &[], &sec_in);
        for (k, state) in states.iter().enumerate() {
            let mut want = *state;
            sha3::keccak_f(&mut want);
            for bit in 0..1600 {
                assert_eq!((got[bit][0] >> k) & 1, (want[bit / 64] >> (bit % 64)) & 1, "instance {k} bit {bit}");
            }
        }
    }

    #[test]
    fn th_circuit_matches_sha3() {
        let mut r = rng(2);
        let pp: [u8; 16] = std::array::from_fn(|_| r() as u8);
        // A batch whose addresses differ only in a few bytes, as in the protocol.
        let prefixes: Vec<[u8; 32]> = (0..100u32)
            .map(|k| {
                let mut p = [0u8; 32];
                p[..16].copy_from_slice(&pp);
                p[16..20].copy_from_slice(&(k * 37).to_le_bytes());
                p[20] = 9;
                p[23] = 1;
                p
            })
            .collect();
        let secrets: Vec<[u8; 16]> = (0..100).map(|_| std::array::from_fn(|_| r() as u8)).collect();
        let (layout, pub_in) = split_prefixes(&prefixes);
        let p = th_circuit(&layout).compile();
        assert!(p.n_and < 38_400 && p.depth <= 24, "public inputs fold: {} ANDs, depth {}", p.n_and, p.depth);
        let words = 2;
        let sec_in: Vec<Vec<u64>> = (0..128)
            .map(|bit| {
                let mut v = vec![0u64; words];
                for (k, s) in secrets.iter().enumerate() {
                    v[k / 64] |= u64::from((s[bit / 8] >> (bit % 8)) & 1) << (k % 64);
                }
                v
            })
            .collect();
        let out = p.eval_plain(words, &pub_in, &sec_in);
        for k in 0..100 {
            let mut input = prefixes[k].to_vec();
            input.extend_from_slice(&secrets[k]);
            let want = sha3::hash(&input);
            for bit in 0..128 {
                assert_eq!((out[bit][k / 64] >> (k % 64)) & 1, u64::from((want[bit / 8] >> (bit % 8)) & 1));
            }
        }
    }

    /// The counts of one `Th` with a public prefix: theta spreads the two secret lanes over 4 of
    /// the 5 columns, so the first round's chi has 15 secret-secret ANDs per row bit (960); rounds 2
    /// to 23 are all secret (22 * 1600); the last round computes the two output lanes only (128).
    #[test]
    fn th_circuit_counts() {
        for prefixes in [[[0x5a; 32], [0x5a; 32]], [[0x5a; 32], [0xa5; 32]]] {
            let (layout, _) = split_prefixes(&prefixes);
            let p = th_circuit(&layout).compile();
            assert_eq!((p.n_and, p.depth), (960 + 22 * 1600 + 128, 24));
        }
    }
}
