//! SHA-256 (FIPS 180-4).
//!
//! - The compression function over a 64-byte block.
//! - SHA-256 over bytes, one-shot or streaming. Costs are counted in compressions.
//!
//! Hashing `len` bytes costs `(len + 9).div_ceil(64)` compressions: the padding is a `0x80` byte
//! and the 8-byte bit length, at least 9 bytes.

/// Digest length in bytes.
pub const OUT_LEN: usize = 32;
/// Block length in bytes.
pub const BLOCK: usize = 64;

pub const IV: [u32; 8] =
    [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// The compression function.
pub fn compress(state: &mut [u32; 8], block: &[u8; BLOCK]) {
    let mut w = [0u32; 64];
    for i in 0..16 {
        w[i] = u32::from_be_bytes(block[4 * i..4 * i + 4].try_into().unwrap());
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for i in 0..64 {
        let t1 = h
            .wrapping_add(e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25))
            .wrapping_add((e & f) ^ (!e & g))
            .wrapping_add(K[i])
            .wrapping_add(w[i]);
        let t2 = (a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22)).wrapping_add((a & b) ^ (a & c) ^ (b & c));
        (h, g, f, e, d, c, b, a) = (g, f, e, d.wrapping_add(t1), c, b, a, t1.wrapping_add(t2));
    }
    for (s, x) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *s = s.wrapping_add(x);
    }
}

/// Compressions SHA-256 spends on `len` bytes.
pub const fn compressions(len: usize) -> u64 {
    (len + 9).div_ceil(BLOCK) as u64
}

/// Streaming SHA-256. A full block is compressed as soon as it is complete: the padding always
/// follows.
#[derive(Clone)]
pub struct Hasher {
    state: [u32; 8],
    buf: [u8; BLOCK],
    /// Bytes currently in `buf`, less than `BLOCK`.
    buf_len: usize,
    /// Bytes hashed so far.
    len: u64,
}

impl Hasher {
    pub fn new() -> Self {
        Self { state: IV, buf: [0; BLOCK], buf_len: 0, len: 0 }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        self.len += data.len() as u64;
        while !data.is_empty() {
            let take = (BLOCK - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == BLOCK {
                compress(&mut self.state, &self.buf);
                self.buf_len = 0;
            }
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut state = self.state;
        let mut block = self.buf;
        block[self.buf_len..].fill(0);
        block[self.buf_len] = 0x80;
        if self.buf_len + 9 > BLOCK {
            compress(&mut state, &block);
            block = [0; BLOCK];
        }
        block[BLOCK - 8..].copy_from_slice(&(8 * self.len).to_be_bytes());
        compress(&mut state, &block);
        let mut out = [0u8; OUT_LEN];
        for (chunk, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(&state) {
            *chunk = word.to_be_bytes();
        }
        out
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// One-shot SHA-256.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    Hasher::new().update(data).finalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|j| j as u8).collect()
    }

    fn hex(d: [u8; 32]) -> String {
        d.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// `test_vectors.txt`, line `n`: SHA-256 of the bytes `0, 1, .., n - 1`, for `n` up to 3 blocks,
    /// from Python's `hashlib.sha256`.
    #[test]
    fn matches_reference_vectors() {
        let lines: Vec<&str> = include_str!("test_vectors.txt").lines().collect();
        assert_eq!(lines.len(), 3 * BLOCK + 1);
        for (n, line) in lines.iter().enumerate() {
            assert_eq!(&hex(hash(&pattern(n))), line, "length {n}");
        }
    }

    #[test]
    fn known_answer() {
        assert_eq!(hex(hash(b"abc")), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    }

    #[test]
    fn streaming_matches_one_shot() {
        let data = pattern(3 * BLOCK + 7);
        for split in [0, 1, 55, 56, BLOCK, BLOCK + 1, 2 * BLOCK, data.len()] {
            let mut h = Hasher::new();
            h.update(&data[..split]).update(&data[split..]);
            assert_eq!(h.finalize(), hash(&data), "split at {split}");
        }
    }

    #[test]
    fn compression_count() {
        assert_eq!(compressions(0), 1);
        assert_eq!(compressions(55), 1);
        assert_eq!(compressions(56), 2, "the 9 padding bytes no longer fit");
        assert_eq!(compressions(119), 2);
    }
}
