//! F4 and the group algebra `F4[Z_3^n]`, the ring of the FOLEAGE-style PCG.
//!
//! An F4 element `u0 + u1 θ` (`θ^2 = θ + 1`) is the byte `u0 | u1 << 1`. A vector over `Z_3^n` is
//! indexed by `p = Σ p_d 3^d`; the product of two monomials adds their exponents trit by trit, and
//! the Fourier transform evaluates at every `(θ^{k_0}, …, θ^{k_{n-1}})`, a tensor product of 3-point
//! DFTs with no twiddles.
//!
//! The transforms run on "planes": a pair `(lo, hi)` of words holds one F4 value per bit (64 or 128
//! independent lanes). Multiplication by an F4 constant is then an F2-linear map of the pair, the
//! 2x2 matrix `M(κ)` in the basis `(1, θ)`; every `M(κ)` is symmetric, so transposing the PCG's
//! F2-linear map (to build the PIR databases) is running the same transform on pairs of GF(2^128)
//! values (see [`Plane`]).

use crate::par;

pub type F4 = u8;

#[inline(always)]
pub fn f4_mul(a: F4, b: F4) -> F4 {
    let (a0, a1, b0, b1) = (a & 1, a >> 1, b & 1, b >> 1);
    ((a0 & b0) ^ (a1 & b1)) | (((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1)
}

#[inline(always)]
pub fn f4_sq(a: F4) -> F4 {
    f4_mul(a, a)
}

/// The trace `F4 -> F2`: `Tr(u0 + u1 θ) = u1`.
#[inline(always)]
pub fn f4_tr(a: F4) -> u8 {
    a >> 1
}

/// A pair of bit-planes: lane `i` of `(lo, hi)` is the F4 value `lo_i + hi_i θ`.
pub trait Plane: Copy + Send + Sync + Default + std::ops::BitXor<Output = Self> + std::ops::BitAnd<Output = Self> + PartialEq {}
impl Plane for u64 {}
impl Plane for u128 {}

pub type Pair<T> = (T, T);

#[inline(always)]
pub fn padd<T: Plane>(a: Pair<T>, b: Pair<T>) -> Pair<T> {
    (a.0 ^ b.0, a.1 ^ b.1)
}

/// Multiplication by θ, `M(θ) = [[0, 1], [1, 1]]`.
#[inline(always)]
pub fn ptheta<T: Plane>(a: Pair<T>) -> Pair<T> {
    (a.1, a.0 ^ a.1)
}

/// Multiplication by the F4 constant `k` (the same in every lane).
#[inline(always)]
pub fn pscale<T: Plane>(a: Pair<T>, k: F4) -> Pair<T> {
    match k & 3 {
        0 => (T::default(), T::default()),
        1 => a,
        2 => ptheta(a),
        _ => (a.0 ^ a.1, a.0),
    }
}

/// Lane-wise product of two packed F4 vectors.
#[inline(always)]
pub fn pmul(a: Pair<u64>, b: Pair<u64>) -> Pair<u64> {
    ((a.0 & b.0) ^ (a.1 & b.1), (a.0 & b.1) ^ (a.1 & b.0) ^ (a.1 & b.1))
}

/// `3^n`.
pub const fn pow3(n: usize) -> usize {
    let mut r = 1;
    let mut i = 0;
    while i < n {
        r *= 3;
        i += 1;
    }
    r
}

/// Trit-wise sum of two indices in `Z_3^n`.
pub fn tadd(mut a: usize, mut b: usize, n: usize) -> usize {
    let (mut r, mut place) = (0, 1);
    for _ in 0..n {
        r += ((a % 3 + b % 3) % 3) * place;
        a /= 3;
        b /= 3;
        place *= 3;
    }
    r
}

/// Trit-wise negation in `Z_3^n`.
pub fn tneg(mut a: usize, n: usize) -> usize {
    let (mut r, mut place) = (0, 1);
    for _ in 0..n {
        r += ((3 - a % 3) % 3) * place;
        a /= 3;
        place *= 3;
    }
    r
}

/// The radix-3 butterfly: `(x0, x1, x2) -> (Σ x, x0 + θ x1 + θ^2 x2, x0 + θ^2 x1 + θ x2)`.
#[inline(always)]
fn butterfly<T: Plane>(x0: Pair<T>, x1: Pair<T>, x2: Pair<T>) -> [Pair<T>; 3] {
    let u = padd(x1, x2);
    let v = padd(x0, ptheta(u));
    [padd(x0, u), padd(v, x2), padd(v, x1)]
}

/// In-place transform over `Z_3^n` of `data` (length `3^n`), on `threads` threads.
pub fn fft<T: Plane>(data: &mut [Pair<T>], n: usize, threads: usize) {
    assert_eq!(data.len(), pow3(n));
    for d in 0..n {
        let s = pow3(d);
        let chunk = 3 * s;
        let groups = data.len() / chunk;
        if groups >= threads || s < 256 {
            // Many independent chunks: split them between threads.
            let per = groups.div_ceil(threads.max(1)) * chunk;
            par::for_chunks(data, per, |part| {
                for c in part.chunks_exact_mut(chunk) {
                    let (a, rest) = c.split_at_mut(s);
                    let (b, cc) = rest.split_at_mut(s);
                    for i in 0..s {
                        let [y0, y1, y2] = butterfly(a[i], b[i], cc[i]);
                        a[i] = y0;
                        b[i] = y1;
                        cc[i] = y2;
                    }
                }
            });
        } else {
            // Few wide chunks: split each chunk's columns between threads.
            for c in data.chunks_exact_mut(chunk) {
                let (a, rest) = c.split_at_mut(s);
                let (b, cc) = rest.split_at_mut(s);
                let per = s.div_ceil(threads);
                par::for_chunks3(a, b, cc, per, |a, b, cc| {
                    for i in 0..a.len() {
                        let [y0, y1, y2] = butterfly(a[i], b[i], cc[i]);
                        a[i] = y0;
                        b[i] = y1;
                        cc[i] = y2;
                    }
                });
            }
        }
    }
}

/// Transposes the 64x64 bit matrix `m` (row `i`, bit `j`) in place.
pub fn transpose64(m: &mut [u64; 64]) {
    let mut j = 32;
    let mut mask: u64 = 0x0000_0000_ffff_ffff;
    while j != 0 {
        let mut k = 0;
        while k < 64 {
            let t = ((m[k] >> j) ^ m[k + j]) & mask;
            m[k] ^= t << j;
            m[k + j] ^= t;
            k = (k + j + 1) & !j;
        }
        j >>= 1;
        mask ^= mask << j;
    }
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
    fn f4_field() {
        // θ^2 = θ + 1, θ^3 = 1, and multiplication is a field.
        assert_eq!(f4_mul(2, 2), 3);
        assert_eq!(f4_mul(f4_mul(2, 2), 2), 1);
        for a in 1..4 {
            assert!((1..4).any(|b| f4_mul(a, b) == 1));
        }
        // M(κ) agrees with f4_mul on every lane.
        for k in 0..4u8 {
            for u in 0..4u8 {
                let (lo, hi) = pscale::<u64>((u64::from(u & 1), u64::from(u >> 1)), k);
                assert_eq!((lo | hi << 1) as u8, f4_mul(k, u));
            }
        }
    }

    #[test]
    fn trace_triples() {
        // Two Boolean triples per slot from Z = XY and W = XY^2:
        // Tr(X) Tr(Y) = Tr(Z) + Tr(W) and Tr(θX) Tr(θY) = Tr(θ^2 Z) + Tr(W).
        for x in 0..4u8 {
            for y in 0..4u8 {
                let (z, w) = (f4_mul(x, y), f4_mul(x, f4_sq(y)));
                assert_eq!((x >> 1) & (y >> 1), (z >> 1) ^ (w >> 1));
                assert_eq!(((x ^ (x >> 1)) & 1) & ((y ^ (y >> 1)) & 1), (z & 1) ^ (w >> 1));
            }
        }
    }

    /// The transform of a product is the product of the transforms.
    #[test]
    fn convolution_theorem() {
        let n = 4;
        let len = pow3(n);
        let mut r = rng(3);
        let a: Vec<F4> = (0..len).map(|_| (r() & 3) as u8).collect();
        let b: Vec<F4> = (0..len).map(|_| (r() & 3) as u8).collect();
        let mut c = vec![0u8; len];
        for i in 0..len {
            for j in 0..len {
                c[tadd(i, j, n)] ^= f4_mul(a[i], b[j]);
            }
        }
        let lift = |v: &[F4]| -> Vec<Pair<u64>> { v.iter().map(|&x| (u64::from(x & 1), u64::from(x >> 1))).collect() };
        let (mut fa, mut fb, mut fc) = (lift(&a), lift(&b), lift(&c));
        for (f, t) in [(&mut fa, 1), (&mut fb, 4), (&mut fc, 3)] {
            fft(f, n, t);
        }
        for k in 0..len {
            assert_eq!(pmul(fa[k], fb[k]), fc[k]);
        }
        // Squaring the transform is the transform of the negated, squared coefficients.
        let abar: Vec<F4> = (0..len).map(|p| f4_sq(a[tneg(p, n)])).collect();
        let mut fabar = lift(&abar);
        fft(&mut fabar, n, 2);
        for k in 0..len {
            assert_eq!(pmul(fa[k], fa[k]), fabar[k]);
        }
    }

    /// The transform is symmetric under the trace pairing: <d, F e> = <F d, e> on F2 coordinates.
    #[test]
    fn transpose_is_the_same_transform() {
        let n = 3;
        let len = pow3(n);
        let mut r = rng(5);
        let e: Vec<Pair<u64>> = (0..len).map(|_| (r() & 1, r() & 1)).collect();
        let d: Vec<Pair<u128>> = (0..len).map(|_| (u128::from(r()) | u128::from(r()) << 64, u128::from(r()))).collect();
        let (mut fe, mut fd) = (e.clone(), d.clone());
        fft(&mut fe, n, 1);
        fft(&mut fd, n, 1);
        let dot = |d: &[Pair<u128>], e: &[Pair<u64>]| d.iter().zip(e).fold(0u128, |acc, (x, y)| acc ^ (x.0 & 0u128.wrapping_sub(u128::from(y.0 & 1))) ^ (x.1 & 0u128.wrapping_sub(u128::from(y.1 & 1))));
        assert_eq!(dot(&d, &fe), dot(&fd, &e));
    }

    #[test]
    fn transpose_bits() {
        let mut r = rng(9);
        let m: [u64; 64] = std::array::from_fn(|_| r());
        let mut t = m;
        transpose64(&mut t);
        for i in 0..64 {
            for j in 0..64 {
                assert_eq!((t[i] >> j) & 1, (m[j] >> i) & 1);
            }
        }
    }
}
