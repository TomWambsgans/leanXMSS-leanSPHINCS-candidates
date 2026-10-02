//! A packed bit-vector with unaligned appends and 64-bit reads: the triple pool.

#[derive(Clone, Debug, Default)]
pub struct BitVec {
    pub words: Vec<u64>,
    pub len: usize,
}

impl BitVec {
    /// Appends the first `n` bits of `src`.
    pub fn append(&mut self, src: &[u64], n: usize) {
        let sh = self.len % 64;
        self.words.resize((self.len + n).div_ceil(64), 0);
        let base = self.len / 64;
        for (i, &w) in src.iter().enumerate().take(n.div_ceil(64)) {
            let w = if 64 * (i + 1) > n { w & ((1u64 << (n - 64 * i)) - 1) } else { w };
            self.words[base + i] |= w << sh;
            if sh != 0 && base + i + 1 < self.words.len() {
                self.words[base + i + 1] |= w >> (64 - sh);
            }
        }
        self.len += n;
    }

    /// Bits `pos..pos + 64` (zeros past the end).
    #[inline]
    pub fn get64(&self, pos: usize) -> u64 {
        let (i, sh) = (pos / 64, pos % 64);
        let lo = self.words.get(i).copied().unwrap_or(0) >> sh;
        if sh == 0 { lo } else { lo | self.words.get(i + 1).copied().unwrap_or(0) << (64 - sh) }
    }

    #[inline]
    pub fn bit(&self, pos: usize) -> u64 {
        (self.words[pos / 64] >> (pos % 64)) & 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn append_and_read() {
        let mut s = crate::aes::Stream::new(4);
        let mut bv = BitVec::default();
        let mut bits = vec![];
        for n in [5usize, 64, 70, 1, 130, 63] {
            let src: Vec<u64> = (0..n.div_ceil(64)).map(|_| s.next_u64()).collect();
            bv.append(&src, n);
            bits.extend((0..n).map(|i| (src[i / 64] >> (i % 64)) & 1));
        }
        assert_eq!(bv.len, bits.len());
        for pos in 0..bits.len() {
            assert_eq!(bv.bit(pos), bits[pos]);
            let w = bv.get64(pos);
            for k in 0..64 {
                assert_eq!((w >> k) & 1, bits.get(pos + k).copied().unwrap_or(0));
            }
        }
    }
}
