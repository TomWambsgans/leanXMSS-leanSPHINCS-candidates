//! The BLAKE2s compression as a Boolean circuit, and `Th` on a secret 16-byte value.
//!
//! The same model as scripts/blake2s_circuit.py: a two-operand addition is a ripple-carry adder
//! with one AND per carry (`maj(x, y, c) = x ^ ((x ^ y) & (x ^ c))`, 31 ANDs), a three-operand one
//! a carry-save layer then a ripple (61 ANDs): 14,720 ANDs and AND-depth 884 when every input is
//! secret. Constant and public inputs fold most of the first round away.

use crate::circuit::{Builder, Wire, ZERO};

/// A 32-bit word, least significant bit first.
pub type Word = [Wire; 32];

pub fn const_word(b: &Builder, v: u32) -> Word {
    std::array::from_fn(|i| b.constant((v >> i) & 1 == 1))
}

fn xor_w(b: &mut Builder, x: &Word, y: &Word) -> Word {
    std::array::from_fn(|i| b.xor(x[i], y[i]))
}

/// Rotation right by `r`: bit `i` of the result is bit `i + r` of the input.
fn rotr_w(x: &Word, r: usize) -> Word {
    std::array::from_fn(|i| x[(i + r) % 32])
}

fn maj(b: &mut Builder, x: Wire, y: Wire, z: Wire) -> Wire {
    let (xy, xz) = (b.xor(x, y), b.xor(x, z));
    let t = b.and(xy, xz);
    b.xor(x, t)
}

/// `x + y mod 2^32`, ripple carry.
pub fn add2(b: &mut Builder, x: &Word, y: &Word) -> Word {
    let mut carry = ZERO;
    std::array::from_fn(|i| {
        let xy = b.xor(x[i], y[i]);
        let sum = b.xor(xy, carry);
        if i < 31 {
            carry = maj(b, x[i], y[i], carry);
        }
        sum
    })
}

/// `x + y + z mod 2^32`: carry-save, then ripple (its carry out of bit 0 folds to zero).
pub fn add3(b: &mut Builder, x: &Word, y: &Word, z: &Word) -> Word {
    let mut sum = [ZERO; 32];
    let mut carries = [ZERO; 32];
    for i in 0..32 {
        let xy = b.xor(x[i], y[i]);
        sum[i] = b.xor(xy, z[i]);
        if i < 31 {
            carries[i + 1] = maj(b, x[i], y[i], z[i]);
        }
    }
    add2(b, &sum, &carries)
}

/// The BLAKE2s compression of block `m` into chaining value `h`, at byte counter `t`.
pub fn compress(b: &mut Builder, h: &[Word; 8], m: &[Word; 16], t: u64, last: bool) -> [Word; 8] {
    let mut v: [Word; 16] = std::array::from_fn(|i| if i < 8 { h[i] } else { const_word(b, blake2s::IV[i - 8]) });
    v[12] = const_word(b, blake2s::IV[4] ^ t as u32);
    v[13] = const_word(b, blake2s::IV[5] ^ (t >> 32) as u32);
    if last {
        v[14] = const_word(b, !blake2s::IV[6]);
    }
    for round in &blake2s::SIGMA {
        for (g, &[a, bb, c, d]) in blake2s::G_LANES.iter().enumerate() {
            let (mx, my) = (m[round[2 * g]], m[round[2 * g + 1]]);
            v[a] = add3(b, &v[a], &v[bb], &mx);
            v[d] = rotr_w(&xor_w(b, &v[d], &v[a]), 16);
            v[c] = add2(b, &v[c], &v[d]);
            v[bb] = rotr_w(&xor_w(b, &v[bb], &v[c]), 12);
            v[a] = add3(b, &v[a], &v[bb], &my);
            v[d] = rotr_w(&xor_w(b, &v[d], &v[a]), 8);
            v[c] = add2(b, &v[c], &v[d]);
            v[bb] = rotr_w(&xor_w(b, &v[bb], &v[c]), 7);
        }
    }
    std::array::from_fn(|i| {
        let x = xor_w(b, &h[i], &v[i]);
        xor_w(b, &x, &v[i + 8])
    })
}

/// How each of the 256 bits of `tw | P` enters a batch: a constant shared by every instance, or a
/// public input whose per-instance values the caller supplies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PubBit {
    Const(bool),
    Input,
}

/// The circuit of `Th(P, tw, x) = BLAKE2s(tw | P | x)[..16]` on a secret 16-byte `x`: one
/// compression of a 48-byte input. `prefix[i]` describes bit `i` of `tw | P` (little endian);
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
    let m: [Word; 16] = std::array::from_fn(|w| {
        std::array::from_fn(|i| match w {
            0..8 => prefix_wires[32 * w + i],
            8..12 => secret[32 * (w - 8) + i],
            _ => ZERO,
        })
    });
    let h: [Word; 8] = std::array::from_fn(|i| const_word(&b, blake2s::PARAM_IV[i]));
    let out = compress(&mut b, &h, &m, 48, true);
    for w in out.iter().take(4) {
        for &bit in w {
            b.output(bit);
        }
    }
    b
}

/// Splits per-instance 32-byte `tw | P` prefixes into constant bits and public inputs (bit-sliced:
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

    /// Bit-slices 64 instances of `count` words into `32 * count` bit-vectors of one word.
    fn slice(values: &[Vec<u32>]) -> Vec<Vec<u64>> {
        let count = values[0].len();
        (0..32 * count)
            .map(|bit| vec![(0..values.len()).fold(0u64, |acc, k| acc | (u64::from((values[k][bit / 32] >> (bit % 32)) & 1) << k))])
            .collect()
    }

    #[test]
    fn all_secret_compression_counts_and_matches() {
        let mut b = Builder::new();
        let h: [Word; 8] = std::array::from_fn(|_| std::array::from_fn(|_| b.sec_input()));
        let m: [Word; 16] = std::array::from_fn(|_| std::array::from_fn(|_| b.sec_input()));
        let out = compress(&mut b, &h, &m, 1234, true);
        for w in &out {
            for &bit in w {
                b.output(bit);
            }
        }
        let p = b.compile();
        // 80 G functions of 184 ANDs, minus the 6 that the constant IV half of the state folds away
        // in the first round; depth as in scripts/blake2s_circuit.py.
        assert_eq!(p.n_and, 14_714);
        assert_eq!(p.depth, 884);
        let mut r = rng(1);
        let inputs: Vec<Vec<u32>> = (0..64).map(|_| (0..24).map(|_| r() as u32).collect()).collect();
        let got = p.eval_plain(1, &[], &slice(&inputs));
        for (k, input) in inputs.iter().enumerate() {
            let mut hh: [u32; 8] = input[..8].try_into().unwrap();
            blake2s::compress(&mut hh, &input[8..].try_into().unwrap(), 1234, true);
            for i in 0..256 {
                assert_eq!((got[i][0] >> k) & 1, u64::from((hh[i / 32] >> (i % 32)) & 1), "instance {k} bit {i}");
            }
        }
    }

    #[test]
    fn th_circuit_matches_blake2s() {
        let mut r = rng(2);
        let pp: [u8; 16] = std::array::from_fn(|_| r() as u8);
        // A batch whose tweaks differ only in a few bytes, as in the protocol.
        let prefixes: Vec<[u8; 32]> = (0..100u32)
            .map(|k| {
                let mut p = [0u8; 32];
                p[0] = 1;
                p[1] = 9;
                p[12..16].copy_from_slice(&(k * 37).to_le_bytes());
                p[16..].copy_from_slice(&pp);
                p
            })
            .collect();
        let secrets: Vec<[u8; 16]> = (0..100).map(|_| std::array::from_fn(|_| r() as u8)).collect();
        let (layout, pub_in) = split_prefixes(&prefixes);
        let p = th_circuit(&layout).compile();
        assert!(p.n_and < 14_720 && p.depth <= 884, "public inputs fold: {} ANDs, depth {}", p.n_and, p.depth);
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
            let want = blake2s::hash(&input);
            for bit in 0..128 {
                assert_eq!((out[bit][k / 64] >> (k % 64)) & 1, u64::from((want[bit / 8] >> (bit % 8)) & 1));
            }
        }
    }
}
