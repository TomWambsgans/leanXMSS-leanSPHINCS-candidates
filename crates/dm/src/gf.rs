//! GF(2^128), the MAC and check field F̂: [`mpc::gf128::Gf128`] (modulus `x^128 + x^7 + x^2 + x + 1`),
//! plus a lazily reduced multiply-accumulate for the long inner products of the PIR answers.

pub use mpc::gf128::Gf128 as F;

/// Carry-less 64x64 -> 128 product.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
pub fn clmul64(a: u64, b: u64) -> u128 {
    // SAFETY: the `aes` target feature (PMULL) is enabled at compile time.
    unsafe { core::arch::aarch64::vmull_p64(a, b) }
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
#[inline(always)]
pub fn clmul64(a: u64, b: u64) -> u128 {
    use core::arch::x86_64::*;
    // SAFETY: the `pclmulqdq` and SSE2 target features are enabled at compile time.
    unsafe {
        let r = _mm_clmulepi64_si128(_mm_set_epi64x(0, a as i64), _mm_set_epi64x(0, b as i64), 0);
        let lo = _mm_cvtsi128_si64(r) as u64;
        let hi = _mm_cvtsi128_si64(_mm_unpackhi_epi64(r, r)) as u64;
        (u128::from(hi) << 64) | u128::from(lo)
    }
}

#[cfg(not(any(all(target_arch = "aarch64", target_feature = "aes"), all(target_arch = "x86_64", target_feature = "pclmulqdq"))))]
#[inline(always)]
pub fn clmul64(a: u64, b: u64) -> u128 {
    (0..64).fold(0u128, |acc, i| acc ^ ((u128::from(a) << i) & 0u128.wrapping_sub(u128::from((b >> i) & 1))))
}

/// An unreduced sum of products: Karatsuba terms kept apart, combined and reduced once.
#[derive(Clone, Copy, Default)]
pub struct Acc {
    lo: u128,
    hi: u128,
    mid: u128,
}

impl Acc {
    #[inline(always)]
    pub fn add_mul(&mut self, a: u128, b: u128) {
        let (a0, a1, b0, b1) = (a as u64, (a >> 64) as u64, b as u64, (b >> 64) as u64);
        self.lo ^= clmul64(a0, b0);
        self.hi ^= clmul64(a1, b1);
        self.mid ^= clmul64(a0 ^ a1, b0 ^ b1);
    }

    /// The halves of a multiplier and their XOR, for repeated products with it.
    #[inline(always)]
    pub fn split(a: u128) -> (u64, u64, u64) {
        (a as u64, (a >> 64) as u64, (a as u64) ^ ((a >> 64) as u64))
    }

    #[inline(always)]
    pub fn add_mul_split(&mut self, a: (u64, u64, u64), b: u128) {
        let (b0, b1) = (b as u64, (b >> 64) as u64);
        self.lo ^= clmul64(a.0, b0);
        self.hi ^= clmul64(a.1, b1);
        self.mid ^= clmul64(a.2, b0 ^ b1);
    }

    #[inline(always)]
    pub fn merge(&mut self, o: &Acc) {
        self.lo ^= o.lo;
        self.hi ^= o.hi;
        self.mid ^= o.mid;
    }

    pub fn reduce(&self) -> F {
        let mid = self.mid ^ self.lo ^ self.hi;
        let p0 = self.lo as u64;
        let p1 = (self.lo >> 64) as u64 ^ mid as u64;
        let p2 = self.hi as u64 ^ (mid >> 64) as u64;
        let p3 = (self.hi >> 64) as u64;
        let t = clmul64(p3, 0x87);
        let p2 = p2 ^ (t >> 64) as u64;
        let p1 = p1 ^ t as u64;
        let u = clmul64(p2, 0x87);
        let p1 = p1 ^ (u >> 64) as u64;
        let p0 = p0 ^ u as u64;
        F((u128::from(p1) << 64) | u128::from(p0))
    }
}

/// The accumulator of the PIR answers: one multiplier `a` against many `b` from memory. On
/// aarch64 the partial products stay in vector registers.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod simd {
    use core::arch::aarch64::*;

    #[derive(Clone, Copy)]
    pub struct Acc {
        lo: uint64x2_t,
        hi: uint64x2_t,
        mid: uint64x2_t,
    }

    #[derive(Clone, Copy)]
    pub struct Split {
        a: uint64x2_t,
    }

    #[inline(always)]
    pub fn split(a: u128) -> Split {
        // SAFETY: plain 16-byte reinterpretation.
        Split { a: unsafe { core::mem::transmute::<u128, uint64x2_t>(a) } }
    }

    impl Default for Acc {
        fn default() -> Self {
            // SAFETY: NEON is enabled at compile time.
            let z = unsafe { vdupq_n_u64(0) };
            Self { lo: z, hi: z, mid: z }
        }
    }

    impl Acc {
        /// Schoolbook: four PMULLs on vector registers, the cross terms summed apart.
        #[inline(always)]
        pub fn add_mul(&mut self, a: &Split, b: &u128) {
            // SAFETY: NEON and PMULL are enabled at compile time; `b` points to 16 readable bytes.
            unsafe {
                let bv = vld1q_u64(b as *const u128 as *const u64);
                let bs = vextq_u64(bv, bv, 1);
                let pa = vreinterpretq_p64_u64(a.a);
                let lo = vmull_p64(vgetq_lane_u64(a.a, 0), vgetq_lane_u64(bv, 0));
                let hi = vmull_high_p64(pa, vreinterpretq_p64_u64(bv));
                let m1 = vmull_p64(vgetq_lane_u64(a.a, 0), vgetq_lane_u64(bs, 0));
                let m2 = vmull_high_p64(pa, vreinterpretq_p64_u64(bs));
                self.lo = veorq_u64(self.lo, vreinterpretq_u64_p128(lo));
                self.hi = veorq_u64(self.hi, vreinterpretq_u64_p128(hi));
                self.mid = veorq_u64(self.mid, veorq_u64(vreinterpretq_u64_p128(m1), vreinterpretq_u64_p128(m2)));
            }
        }

        pub fn reduce(&self) -> super::F {
            // SAFETY: plain 16-byte reinterpretations.
            let t = |v: uint64x2_t| unsafe { core::mem::transmute::<uint64x2_t, u128>(v) };
            // The schoolbook middle term is the Karatsuba one minus the outer terms.
            let (lo, hi) = (t(self.lo), t(self.hi));
            super::Acc { lo, hi, mid: t(self.mid) ^ lo ^ hi }.reduce()
        }
    }
}

/// The portable accumulator of the PIR answers.
#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
pub mod simd {
    #[derive(Clone, Copy, Default)]
    pub struct Acc(super::Acc);

    pub type Split = (u64, u64, u64);

    #[inline(always)]
    pub fn split(a: u128) -> Split {
        super::Acc::split(a)
    }

    impl Acc {
        #[inline(always)]
        pub fn add_mul(&mut self, a: &Split, b: &u128) {
            self.0.add_mul_split(*a, *b)
        }

        pub fn reduce(&self) -> super::F {
            self.0.reduce()
        }
    }
}

/// `bit ? x : 0`.
#[inline(always)]
pub fn sel(bit: u64, x: u128) -> u128 {
    x & 0u128.wrapping_sub(u128::from(bit & 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lazy_matches_field() {
        let mut s = crate::aes::Stream::new(1);
        let (mut acc, mut want) = (Acc::default(), F::ZERO);
        for _ in 0..500 {
            let (a, b) = (s.next_u128(), s.next_u128());
            acc.add_mul(a, b);
            want += F(a) * F(b);
        }
        assert_eq!(acc.reduce(), want);
    }
}
