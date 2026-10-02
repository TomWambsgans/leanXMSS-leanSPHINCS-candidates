//! AES-128 with fixed public keys: the PRG of the DPFs (Matyas-Meyer-Oseas, `AES_k(x) ^ x`) and the
//! counter-mode streams of the dealer and of the protocol's public coins.
//!
//! Hardware AES (ARMv8 AESE/AESMC, x86 AES-NI) when the build enables it, a slow table-free
//! software fallback otherwise.

/// An expanded AES-128 key.
#[derive(Clone)]
pub struct Aes128 {
    rk: [[u8; 16]; 11],
}

const SBOX: [u8; 256] = {
    // The AES S-box, computed at compile time from the inverse in GF(2^8) and the affine map.
    let mut s = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        let x = i as u8;
        // x^254 is the inverse (0 maps to 0).
        let mut inv = 1u8;
        let mut base = x;
        let mut e = 254u32;
        while e > 0 {
            if e & 1 == 1 {
                inv = gmul(inv, base);
            }
            base = gmul(base, base);
            e >>= 1;
        }
        if x == 0 {
            inv = 0;
        }
        let b = inv;
        s[i] = b ^ b.rotate_left(1) ^ b.rotate_left(2) ^ b.rotate_left(3) ^ b.rotate_left(4) ^ 0x63;
        i += 1;
    }
    s
};

const fn gmul(mut a: u8, mut b: u8) -> u8 {
    let mut p = 0u8;
    while b != 0 {
        if b & 1 == 1 {
            p ^= a;
        }
        let hi = a & 0x80;
        a <<= 1;
        if hi != 0 {
            a ^= 0x1b;
        }
        b >>= 1;
    }
    p
}

impl Aes128 {
    pub fn new(key: [u8; 16]) -> Self {
        let mut rk = [[0u8; 16]; 11];
        rk[0] = key;
        let mut rcon = 1u8;
        for r in 1..11 {
            let p = rk[r - 1];
            let mut t = [SBOX[p[13] as usize] ^ rcon, SBOX[p[14] as usize], SBOX[p[15] as usize], SBOX[p[12] as usize]];
            rcon = gmul(rcon, 2);
            let mut k = [0u8; 16];
            for w in 0..4 {
                for j in 0..4 {
                    k[4 * w + j] = p[4 * w + j] ^ t[j];
                }
                t = [k[4 * w], k[4 * w + 1], k[4 * w + 2], k[4 * w + 3]];
            }
            rk[r] = k;
        }
        Self { rk }
    }

    /// A key from a 128-bit value.
    pub fn from_u128(key: u128) -> Self {
        Self::new(key.to_le_bytes())
    }

    /// Encrypts every block in place.
    #[inline]
    pub fn encrypt(&self, blocks: &mut [u128]) {
        backend::encrypt(&self.rk, blocks)
    }

    pub fn encrypt1(&self, x: u128) -> u128 {
        let mut b = [x];
        self.encrypt(&mut b);
        b[0]
    }

    /// Software encryption of one block, the reference of the hardware paths.
    pub fn encrypt_soft(&self, x: u128) -> u128 {
        let mut s = x.to_le_bytes();
        xor16(&mut s, &self.rk[0]);
        for r in 1..11 {
            for b in s.iter_mut() {
                *b = SBOX[*b as usize];
            }
            // ShiftRows: byte (row, col) at index 4 col + row moves to column col - row.
            let t = s;
            for col in 0..4 {
                for row in 0..4 {
                    s[4 * col + row] = t[4 * ((col + row) % 4) + row];
                }
            }
            if r < 10 {
                for col in 0..4 {
                    let a: [u8; 4] = [s[4 * col], s[4 * col + 1], s[4 * col + 2], s[4 * col + 3]];
                    for row in 0..4 {
                        s[4 * col + row] = gmul(a[row], 2) ^ gmul(a[(row + 1) % 4], 3) ^ a[(row + 2) % 4] ^ a[(row + 3) % 4];
                    }
                }
            }
            xor16(&mut s, &self.rk[r]);
        }
        u128::from_le_bytes(s)
    }
}

fn xor16(a: &mut [u8; 16], b: &[u8; 16]) {
    for i in 0..16 {
        a[i] ^= b[i];
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
mod backend {
    use core::arch::aarch64::*;

    #[inline]
    pub fn encrypt(rk: &[[u8; 16]; 11], blocks: &mut [u128]) {
        // SAFETY: the `aes` and `neon` target features are enabled at compile time; loads and stores
        // are of whole u128 values.
        unsafe {
            let k: [uint8x16_t; 11] = std::array::from_fn(|r| vld1q_u8(rk[r].as_ptr()));
            let (chunks, rest) = blocks.as_chunks_mut::<8>();
            for c in chunks {
                let mut s: [uint8x16_t; 8] = std::array::from_fn(|i| vreinterpretq_u8_u128(c[i]));
                for r in 0..9 {
                    for x in s.iter_mut() {
                        *x = vaesmcq_u8(vaeseq_u8(*x, k[r]));
                    }
                }
                for (i, x) in s.iter().enumerate() {
                    c[i] = vreinterpretq_u128_u8(veorq_u8(vaeseq_u8(*x, k[9]), k[10]));
                }
            }
            for b in rest {
                let mut x = vreinterpretq_u8_u128(*b);
                for r in 0..9 {
                    x = vaesmcq_u8(vaeseq_u8(x, k[r]));
                }
                *b = vreinterpretq_u128_u8(veorq_u8(vaeseq_u8(x, k[9]), k[10]));
            }
        }
    }

    #[inline(always)]
    unsafe fn vreinterpretq_u8_u128(x: u128) -> uint8x16_t {
        // SAFETY: a u128 and a uint8x16_t are both 16 plain bytes.
        unsafe { core::mem::transmute(x) }
    }

    #[inline(always)]
    unsafe fn vreinterpretq_u128_u8(x: uint8x16_t) -> u128 {
        // SAFETY: as above.
        unsafe { core::mem::transmute(x) }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "aes", target_feature = "sse2"))]
mod backend {
    use core::arch::x86_64::*;

    #[inline]
    pub fn encrypt(rk: &[[u8; 16]; 11], blocks: &mut [u128]) {
        // SAFETY: the `aes` and `sse2` target features are enabled at compile time.
        unsafe {
            let k: [__m128i; 11] = std::array::from_fn(|r| _mm_loadu_si128(rk[r].as_ptr() as *const __m128i));
            for b in blocks.iter_mut() {
                let mut x = _mm_xor_si128(_mm_loadu_si128(b as *const u128 as *const __m128i), k[0]);
                for r in 1..10 {
                    x = _mm_aesenc_si128(x, k[r]);
                }
                x = _mm_aesenclast_si128(x, k[10]);
                _mm_storeu_si128(b as *mut u128 as *mut __m128i, x);
            }
        }
    }
}

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "aes", target_feature = "sse2")
)))]
mod backend {
    pub fn encrypt(rk: &[[u8; 16]; 11], blocks: &mut [u128]) {
        let aes = super::Aes128 { rk: *rk };
        for b in blocks.iter_mut() {
            *b = aes.encrypt_soft(*b);
        }
    }
}

/// Whether this build encrypts with hardware AES.
pub const HW_AES: bool = cfg!(any(all(target_arch = "aarch64", target_feature = "aes"), all(target_arch = "x86_64", target_feature = "aes")));

/// A counter-mode stream: block `i` is `AES_seed(nonce ^ i)` under a key derived from the seed.
pub struct Stream {
    aes: Aes128,
    ctr: u128,
    buf: [u128; 8],
    pos: usize,
}

impl Stream {
    pub fn new(seed: u128) -> Self {
        Self { aes: Aes128::from_u128(seed), ctr: 0, buf: [0; 8], pos: 8 }
    }

    /// A stream keyed by a seed and a domain-separation label.
    pub fn labeled(seed: u128, label: &[u64]) -> Self {
        let mut h = blake2s::Hasher::new();
        h.update(&seed.to_le_bytes());
        for l in label {
            h.update(&l.to_le_bytes());
        }
        Self::new(u128::from_le_bytes(h.finalize()[..16].try_into().unwrap()))
    }

    #[inline]
    pub fn next_u128(&mut self) -> u128 {
        if self.pos == 8 {
            for (i, b) in self.buf.iter_mut().enumerate() {
                *b = self.ctr + i as u128;
            }
            self.ctr += 8;
            self.aes.encrypt(&mut self.buf);
            self.pos = 0;
        }
        self.pos += 1;
        self.buf[self.pos - 1]
    }

    pub fn next_u64(&mut self) -> u64 {
        self.next_u128() as u64
    }

    /// Uniform in `0..n`, by rejection.
    pub fn below(&mut self, n: u64) -> u64 {
        assert!(n > 0);
        let zone = u64::MAX - (u64::MAX % n);
        loop {
            let x = self.next_u64();
            if x < zone {
                return x % n;
            }
        }
    }

}

/// A random-access PRF `(a, b) -> AES_key(a || b)`: the dealer's randomness, addressed by index.
#[derive(Clone)]
pub struct Prf(Aes128);

impl Prf {
    pub fn new(key: u128) -> Self {
        Self(Aes128::from_u128(key))
    }

    /// A PRF keyed by a seed and a domain-separation label.
    pub fn labeled(seed: u128, label: &[u64]) -> Self {
        let mut h = blake2s::Hasher::new();
        h.update(b"dm prf");
        h.update(&seed.to_le_bytes());
        for l in label {
            h.update(&l.to_le_bytes());
        }
        Self::new(u128::from_le_bytes(h.finalize()[..16].try_into().unwrap()))
    }

    #[inline]
    pub fn at(&self, a: u64, b: u64) -> u128 {
        self.0.encrypt1(u128::from(a) << 64 | u128::from(b))
    }
}

/// The fixed keys of the DPF PRGs: the 2-party trees, the 3-party rows, the 2-party leaves.
pub fn tree_keys() -> &'static [Aes128; 3] {
    use std::sync::OnceLock;
    static K: OnceLock<[Aes128; 3]> = OnceLock::new();
    K.get_or_init(|| std::array::from_fn(|i| Aes128::from_u128(0x6c65_616e_5370_6869_6e63_7364_6d00_0000 + i as u128)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fips197_vector() {
        // FIPS-197 Appendix C.1.
        let key: [u8; 16] = std::array::from_fn(|i| i as u8);
        let pt: [u8; 16] = std::array::from_fn(|i| (i as u8) * 0x11);
        let want: [u8; 16] = [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a];
        let aes = Aes128::new(key);
        assert_eq!(aes.encrypt_soft(u128::from_le_bytes(pt)).to_le_bytes(), want);
        assert_eq!(aes.encrypt1(u128::from_le_bytes(pt)).to_le_bytes(), want);
        let mut many: Vec<u128> = (0..21).map(|i| u128::from_le_bytes(pt) ^ (i as u128) << 64).collect();
        let want_many: Vec<u128> = many.iter().map(|&x| aes.encrypt_soft(x)).collect();
        aes.encrypt(&mut many);
        assert_eq!(many, want_many);
    }
}
