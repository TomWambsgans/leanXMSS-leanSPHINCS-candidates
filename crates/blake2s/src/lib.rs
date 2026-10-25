//! BLAKE2s-256 (RFC 7693), unkeyed, with a 32-byte output.
//!
//! - The compression function `F` over a 64-byte block, with the byte counter and the final flag.
//! - BLAKE2s-256 over bytes, one-shot or streaming. Costs are counted in compressions.
//!
//! Hashing `len` bytes costs `max(1, ceil(len / 64))` compressions: the last block is zero-padded and
//! flagged final, and no padding byte is added, so an input that fills its last block exactly pays
//! nothing more.

/// Digest length in bytes.
pub const OUT_LEN: usize = 32;
/// Block length in bytes.
pub const BLOCK: usize = 64;

pub const IV: [u32; 8] =
    [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];

const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

#[inline]
fn g(v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(12);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(8);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(7);
}

/// The compression function `F(h, m, t, f)`: `t` counts the bytes hashed so far, this block included.
pub fn compress(h: &mut [u32; 8], block: &[u8; BLOCK], t: u64, last: bool) {
    let m: [u32; 16] = std::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    if last {
        v[14] = !v[14];
    }
    for s in &SIGMA {
        g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// Compressions BLAKE2s spends on `len` bytes.
pub const fn compressions(len: usize) -> u64 {
    if len == 0 { 1 } else { len.div_ceil(BLOCK) as u64 }
}

/// Streaming BLAKE2s-256. A full block is compressed only once more input arrives: the last block
/// must carry the final flag.
#[derive(Clone)]
pub struct Hasher {
    h: [u32; 8],
    buf: [u8; BLOCK],
    /// Bytes currently in `buf`, at most `BLOCK`.
    buf_len: usize,
    /// Bytes compressed so far.
    t: u64,
}

impl Hasher {
    pub fn new() -> Self {
        let mut h = IV;
        h[0] ^= 0x0101_0000 ^ OUT_LEN as u32;
        Self { h, buf: [0; BLOCK], buf_len: 0, t: 0 }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.buf_len == BLOCK {
                self.t += BLOCK as u64;
                compress(&mut self.h, &self.buf, self.t, false);
                self.buf_len = 0;
            }
            let take = (BLOCK - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut h = self.h;
        let mut block = self.buf;
        block[self.buf_len..].fill(0);
        compress(&mut h, &block, self.t + self.buf_len as u64, true);
        let mut out = [0u8; OUT_LEN];
        for (chunk, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(&h) {
            *chunk = word.to_le_bytes();
        }
        out
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// One-shot BLAKE2s-256.
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

    /// `test_vectors.txt`, line `n`: BLAKE2s-256 of the bytes `0, 1, .., n - 1`, for `n` up to 3
    /// blocks, from Python's `hashlib.blake2s`.
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
        assert_eq!(hex(hash(b"abc")), "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982");
    }

    #[test]
    fn streaming_matches_one_shot() {
        let data = pattern(3 * BLOCK + 7);
        for split in [0, 1, 63, BLOCK, BLOCK + 1, 2 * BLOCK, data.len()] {
            let mut h = Hasher::new();
            h.update(&data[..split]).update(&data[split..]);
            assert_eq!(h.finalize(), hash(&data), "split at {split}");
        }
    }

    #[test]
    fn compression_count() {
        assert_eq!(compressions(0), 1);
        assert_eq!(compressions(BLOCK), 1, "a full last block needs no padding");
        assert_eq!(compressions(BLOCK + 1), 2);
    }
}
