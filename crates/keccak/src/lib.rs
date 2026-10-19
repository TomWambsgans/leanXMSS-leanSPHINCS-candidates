//! Keccak-256, the repo's one hash function: Ethereum's `keccak256`, the original Keccak padding (not FIPS 202's SHA3-256).
//!
//! - Keccak-f[1600]: every hash here is a chain of permutations, and costs are counted in permutations.
//! - Keccak-256 over bytes, one-shot or streaming: a sponge of rate 136 bytes, padding `0x01 .. 0x80`
//!   (SHA3-256 differs only in its first padding byte, `0x06`).
//!
//! Hashing `len` bytes costs `len / 136 + 1` permutations: the padding takes at least one byte, so an
//! input that fills its last block exactly pays one more permutation for the padding alone.

/// Digest length in bytes.
pub const OUT_LEN: usize = 32;
/// Sponge rate of Keccak-256 in bytes: `1600 - 2 * 256` bits.
pub const RATE: usize = 136;
/// Rounds per permutation.
pub const ROUNDS: usize = 24;

/// The round constants, added (XOR) to lane 0 at the end of each round.
pub const RC: [u64; ROUNDS] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// `rho` and `pi` as one walk over the 24 lanes other than lane 0: step `i` moves the lane it
/// carries, rotated left by `RHO[i]`, into lane `PI[i]`, and picks up the lane that was there. The
/// walk starts carrying lane 1. Lane `x + 5 y` is `A[x][y]`.
pub const RHO: [u32; 24] = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44];
pub const PI: [usize; 24] = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1];

/// Keccak-f[1600] on 25 lanes, lane `x + 5 y` being `A[x][y]`.
#[inline]
pub fn keccak_f(a: &mut [u64; 25]) {
    for rc in RC {
        // theta
        let c: [u64; 5] = std::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                a[x + 5 * y] ^= d;
            }
        }
        // rho and pi
        let mut carried = a[1];
        for i in 0..24 {
            let next = a[PI[i]];
            a[PI[i]] = carried.rotate_left(RHO[i]);
            carried = next;
        }
        // chi
        for y in 0..5 {
            let row: [u64; 5] = std::array::from_fn(|x| a[x + 5 * y]);
            for x in 0..5 {
                a[x + 5 * y] = row[x] ^ (!row[(x + 1) % 5] & row[(x + 2) % 5]);
            }
        }
        // iota
        a[0] ^= rc;
    }
}

/// Permutations Keccak-256 spends on `len` bytes.
pub const fn permutations(len: usize) -> u64 {
    (len / RATE + 1) as u64
}

/// XOR a whole block into the first 17 lanes.
#[inline]
fn absorb_block(state: &mut [u64; 25], block: &[u8; RATE]) {
    for (lane, chunk) in state.iter_mut().zip(block.as_chunks::<8>().0) {
        *lane ^= u64::from_le_bytes(*chunk);
    }
}

/// Streaming Keccak-256. A full block is permuted as soon as it is complete: the padding always
/// follows, so it is never the last.
#[derive(Clone)]
pub struct Hasher {
    state: [u64; 25],
    buf: [u8; RATE],
    /// Bytes currently in `buf`, less than `RATE`.
    buf_len: usize,
}

impl Hasher {
    pub fn new() -> Self {
        Self { state: [0; 25], buf: [0; RATE], buf_len: 0 }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            let take = (RATE - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == RATE {
                absorb_block(&mut self.state, &self.buf);
                keccak_f(&mut self.state);
                self.buf_len = 0;
            }
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut state = self.state;
        let mut block = self.buf;
        block[self.buf_len..].fill(0);
        block[self.buf_len] ^= 0x01;
        block[RATE - 1] ^= 0x80;
        absorb_block(&mut state, &block);
        keccak_f(&mut state);
        let mut out = [0u8; OUT_LEN];
        for (chunk, lane) in out.as_chunks_mut::<8>().0.iter_mut().zip(&state) {
            *chunk = lane.to_le_bytes();
        }
        out
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// One-shot Keccak-256.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    Hasher::new().update(data).finalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|j| j as u8).collect()
    }

    /// `test_vectors.txt`, line `n`: Keccak-256 of the bytes `0, 1, .., n - 1` (mod 256), for `n` up
    /// to 3 blocks, from a Python Keccak checked against `hashlib.sha3_256` (with SHA3's padding) and
    /// Ethereum's `keccak256("")` and `keccak256("abc")`.
    #[test]
    fn matches_reference_vectors() {
        let lines: Vec<&str> = include_str!("test_vectors.txt").lines().collect();
        assert_eq!(lines.len(), 3 * RATE + 1);
        for (n, line) in lines.iter().enumerate() {
            let got: String = hash(&pattern(n)).iter().map(|b| format!("{b:02x}")).collect();
            assert_eq!(&got, line, "length {n}");
        }
    }

    #[test]
    fn known_answers() {
        let hex = |d: [u8; 32]| d.iter().map(|b| format!("{b:02x}")).collect::<String>();
        assert_eq!(hex(hash(b"")), "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
        assert_eq!(hex(hash(b"abc")), "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45");
    }

    #[test]
    fn streaming_matches_one_shot() {
        let data = pattern(3 * RATE + 7);
        for split in [0, 1, 63, RATE - 1, RATE, RATE + 1, 2 * RATE, data.len()] {
            let mut h = Hasher::new();
            h.update(&data[..split]).update(&data[split..]);
            assert_eq!(h.finalize(), hash(&data), "split at {split}");
        }
        let mut h = Hasher::new();
        for byte in &data {
            h.update(std::slice::from_ref(byte));
        }
        assert_eq!(h.finalize(), hash(&data));
    }

    #[test]
    fn permutation_count() {
        assert_eq!(permutations(0), 1);
        assert_eq!(permutations(RATE - 1), 1);
        assert_eq!(permutations(RATE), 2, "a full last block pays for the padding");
        assert_eq!(permutations(2 * RATE + 5), 3);
    }
}
