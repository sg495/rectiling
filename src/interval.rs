// SPDX-License-Identifier: LGPL-3.0-or-later

//! Rigorous floating-point interval evaluation of polynomials.

use crate::int::Int;
use crate::poly::Poly;

/// Sign of a polynomial over an interval of positive floats, if interval evaluation determines it.
pub fn sign_on_interval<C: Int>(q: &Poly<C>, lo: f64, hi: f64) -> Option<i32> {
    let (mut a, mut b) = (0.0f64, 0.0f64);
    for c in q.coeffs().iter().rev() {
        let c = c.to_f64_exact()?;
        let (pa, pb) = if a >= 0.0 {
            (a * lo, b * hi)
        } else if b <= 0.0 {
            (a * hi, b * lo)
        } else {
            (a * hi, b * hi)
        };
        a = (pa.next_down() + c).next_down();
        b = (pb.next_up() + c).next_up();
    }
    if a > 0.0 {
        Some(1)
    } else if b < 0.0 {
        Some(-1)
    } else {
        None
    }
}

/// Closed interval of floats, with arithmetic rounded outwards.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Iv {
    pub(crate) lo: f64,
    pub(crate) hi: f64,
}

impl Iv {
    /// The interval containing a single float.
    #[inline]
    pub(crate) fn point(v: f64) -> Self {
        Iv { lo: v, hi: v }
    }

    #[inline]
    fn widen(lo: f64, hi: f64) -> Self {
        Iv {
            lo: lo.next_down(),
            hi: hi.next_up(),
        }
    }

    /// Sum.
    #[inline]
    pub(crate) fn add(self, o: Iv) -> Iv {
        Iv::widen(self.lo + o.lo, self.hi + o.hi)
    }

    /// Difference.
    #[inline]
    pub(crate) fn sub(self, o: Iv) -> Iv {
        Iv::widen(self.lo - o.hi, self.hi - o.lo)
    }

    /// Product.
    #[inline]
    pub(crate) fn mul(self, o: Iv) -> Iv {
        let c = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi];
        let lo = c[0].min(c[1]).min(c[2]).min(c[3]);
        let hi = c[0].max(c[1]).max(c[2]).max(c[3]);
        Iv::widen(lo, hi)
    }

    /// Whether the interval contains zero or is not finite.
    #[inline]
    pub(crate) fn straddles_zero(self) -> bool {
        !(self.lo > 0.0 || self.hi < 0.0) || !self.lo.is_finite() || !self.hi.is_finite()
    }

    /// Quotient, for a divisor that does not contain zero.
    #[inline]
    pub(crate) fn div(self, o: Iv) -> Iv {
        let c = [self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi];
        let lo = c[0].min(c[1]).min(c[2]).min(c[3]);
        let hi = c[0].max(c[1]).max(c[2]).max(c[3]);
        Iv::widen(lo, hi)
    }

    /// Negation.
    #[inline]
    pub(crate) fn neg(self) -> Iv {
        Iv { lo: -self.hi, hi: -self.lo }
    }

    /// Integer power of a positive interval.
    pub(crate) fn powi(self, k: i32) -> Iv {
        let mut r = Iv::point(1.0);
        for _ in 0..k.unsigned_abs() {
            r = r.mul(self);
        }
        if k < 0 { Iv::point(1.0).div(r) } else { r }
    }
}
