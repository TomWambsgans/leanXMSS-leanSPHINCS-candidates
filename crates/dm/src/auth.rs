//! SPDZ-style authenticated additive shares over F̂ = GF(2^128): party `i` holds `v_i` and `m_i`
//! with `sum v_i = x` and `sum m_i = Δ x`, `Δ = sum Δ_i` (bits are shared as 0/1 elements of F̂).

use crate::gf::F;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Auth {
    pub v: F,
    pub m: F,
}

impl std::ops::Add for Auth {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self { v: self.v + o.v, m: self.m + o.m }
    }
}

impl std::ops::AddAssign for Auth {
    #[inline(always)]
    fn add_assign(&mut self, o: Self) {
        self.v += o.v;
        self.m += o.m;
    }
}

impl Auth {
    /// Times a public constant.
    #[inline(always)]
    pub fn scale(self, k: F) -> Self {
        Self { v: self.v * k, m: self.m * k }
    }

    /// Plus a public constant: party 0 adds it to its value share, everyone `Δ_i k` to its MAC.
    #[inline(always)]
    pub fn add_const(self, k: F, me: usize, delta_i: F) -> Self {
        Self { v: if me == 0 { self.v + k } else { self.v }, m: self.m + delta_i * k }
    }
}

/// Splits `x` (with MAC key `delta`) into three authenticated shares, from four random elements.
pub fn share(x: F, delta: F, r: [u128; 4], me: usize) -> Auth {
    match me {
        0 => Auth { v: F(r[0]), m: F(r[2]) },
        1 => Auth { v: F(r[1]), m: F(r[3]) },
        _ => Auth { v: x + F(r[0]) + F(r[1]), m: delta * x + F(r[2]) + F(r[3]) },
    }
}

/// Splits a bit: value shares are bits.
pub fn share_bit(x: u64, delta: F, r: [u128; 4], me: usize) -> Auth {
    let r = [r[0] & 1, r[1] & 1, r[2], r[3]];
    share(F(u128::from(x & 1)), delta, r, me)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_ops_keep_the_mac() {
        let mut s = crate::aes::Stream::new(3);
        let ds = [F(s.next_u128()), F(s.next_u128()), F(s.next_u128())];
        let delta = ds[0] + ds[1] + ds[2];
        let (x, y, k) = (F(s.next_u128()), F(s.next_u128()), F(s.next_u128()));
        let (rx, ry) = ([0; 4].map(|_| s.next_u128()), [0; 4].map(|_| s.next_u128()));
        let z: Vec<Auth> = (0..3).map(|i| (share(x, delta, rx, i) + share_bit(1, delta, ry, i)).scale(k).add_const(y, i, ds[i])).collect();
        let (v, m) = z.iter().fold((F::ZERO, F::ZERO), |(v, m), a| (v + a.v, m + a.m));
        let want = (x + F::ONE) * k + y;
        assert_eq!((v, m), (want, delta * want));
    }
}
