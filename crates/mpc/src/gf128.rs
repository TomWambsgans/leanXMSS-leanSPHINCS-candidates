//! GF(2^128) = GF(2)[x] / (x^128 + x^7 + x^2 + x + 1), the field of the BGIN19 checks.

/// A field element, bit `i` being the coefficient of `x^i`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Gf128(pub u128);

impl std::fmt::Debug for Gf128 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Gf128({:#034x})", self.0)
    }
}

impl Gf128 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    /// The element `x`, the third evaluation point of the round polynomials.
    pub const X: Self = Self(2);

    #[inline(always)]
    pub fn from_bit(bit: bool) -> Self {
        Self(bit as u128)
    }

    pub fn from_bytes(bytes: &[u8; 16]) -> Self {
        Self(u128::from_le_bytes(*bytes))
    }

    pub fn to_bytes(self) -> [u8; 16] {
        self.0.to_le_bytes()
    }

    /// Multiplication by `x`.
    #[inline(always)]
    pub fn mul_x(self) -> Self {
        let carry = self.0 >> 127;
        Self((self.0 << 1) ^ (carry * 0x87))
    }

    pub fn square(self) -> Self {
        self * self
    }

    pub fn pow(self, mut e: u128) -> Self {
        let (mut base, mut acc) = (self, Self::ONE);
        while e != 0 {
            if e & 1 == 1 {
                acc = acc * base;
            }
            base = base.square();
            e >>= 1;
        }
        acc
    }

    /// The inverse of a nonzero element, `a^(2^128 - 2)`.
    pub fn inv(self) -> Self {
        assert_ne!(self, Self::ZERO, "zero has no inverse");
        self.pow(u128::MAX - 1)
    }
}

// Addition in characteristic 2 is XOR.
#[allow(clippy::suspicious_arithmetic_impl)]
impl std::ops::Add for Gf128 {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self(self.0 ^ o.0)
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl std::ops::AddAssign for Gf128 {
    #[inline(always)]
    fn add_assign(&mut self, o: Self) {
        self.0 ^= o.0;
    }
}

impl std::ops::Mul for Gf128 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        Self(mul128(self.0, o.0))
    }
}

/// The product modulo `x^128 + x^7 + x^2 + x + 1`: a Karatsuba carry-less product in 64-bit limbs
/// `p3 p2 p1 p0`, then two folds by `x^128 = 0x87`.
#[inline(always)]
fn mul128(a: u128, b: u128) -> u128 {
    let (a0, a1, b0, b1) = (a as u64, (a >> 64) as u64, b as u64, (b >> 64) as u64);
    let lo = clmul64(a0, b0);
    let hi = clmul64(a1, b1);
    let mid = clmul64(a0 ^ a1, b0 ^ b1) ^ lo ^ hi;
    let p0 = lo as u64;
    let p1 = (lo >> 64) as u64 ^ mid as u64;
    let p2 = hi as u64 ^ (mid >> 64) as u64;
    let p3 = (hi >> 64) as u64;
    // p3 x^192 = p3 * 0x87 * x^64, at most 71 bits: into limbs 2 and 1.
    let t = clmul64(p3, 0x87);
    let p2 = p2 ^ (t >> 64) as u64;
    let p1 = p1 ^ t as u64;
    // p2 x^128 = p2 * 0x87: into limbs 1 and 0.
    let u = clmul64(p2, 0x87);
    let p1 = p1 ^ (u >> 64) as u64;
    let p0 = p0 ^ u as u64;
    (u128::from(p1) << 64) | u128::from(p0)
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
fn clmul64(a: u64, b: u64) -> u128 {
    // SAFETY: the `aes` target feature (PMULL) is enabled at compile time.
    unsafe { core::arch::aarch64::vmull_p64(a, b) }
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
#[inline(always)]
fn clmul64(a: u64, b: u64) -> u128 {
    use core::arch::x86_64::*;
    // SAFETY: the `pclmulqdq` and SSE2 target features are enabled at compile time.
    unsafe {
        let r = _mm_clmulepi64_si128(_mm_set_epi64x(0, a as i64), _mm_set_epi64x(0, b as i64), 0);
        let lo = _mm_cvtsi128_si64(r) as u64;
        let hi = _mm_cvtsi128_si64(_mm_unpackhi_epi64(r, r)) as u64;
        (u128::from(hi) << 64) | u128::from(lo)
    }
}

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "pclmulqdq")
)))]
#[inline(always)]
fn clmul64(a: u64, b: u64) -> u128 {
    clmul64_soft(a, b)
}

/// The portable carry-less product, also the tests' reference.
#[allow(dead_code)]
fn clmul64_soft(a: u64, b: u64) -> u128 {
    (0..64).fold(0u128, |acc, i| acc ^ ((u128::from(a) << i) & 0u128.wrapping_sub(u128::from((b >> i) & 1))))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Bit-by-bit multiplication modulo the field polynomial.
    fn reference_mul(a: u128, b: u128) -> u128 {
        let (mut acc, mut a) = (0u128, a);
        for i in 0..128 {
            if (b >> i) & 1 == 1 {
                acc ^= a;
            }
            a = (a << 1) ^ ((a >> 127) * 0x87);
        }
        acc
    }

    fn sample(i: u64) -> u128 {
        let mut x = (u128::from(i) << 64 | 0x9e37_79b9_7f4a_7c15) ^ 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;
        for _ in 0..3 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
        }
        x
    }

    #[test]
    fn multiplication_matches_reference() {
        for i in 0..2000u64 {
            let (a, b) = (sample(i), sample(i + 7919));
            assert_eq!((Gf128(a) * Gf128(b)).0, reference_mul(a, b));
            assert_eq!(clmul64(a as u64, b as u64), clmul64_soft(a as u64, b as u64));
        }
        assert_eq!((Gf128(u128::MAX) * Gf128(u128::MAX)).0, reference_mul(u128::MAX, u128::MAX));
    }

    #[test]
    fn inverse_and_mul_x() {
        for i in 1..50u64 {
            let a = Gf128(sample(i));
            assert_eq!(a * a.inv(), Gf128::ONE);
            assert_eq!(a.mul_x(), a * Gf128::X);
        }
    }
}
