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
