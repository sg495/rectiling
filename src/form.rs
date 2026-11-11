// SPDX-License-Identifier: LGPL-3.0-or-later

//! Linear forms in the unknown lengths of a tiling, with coefficients polynomial in the tile proportion.

use crate::int::Int;
use crate::poly::Poly;
use smallvec::SmallVec;

/// Linear form in the unknown lengths, divided by a power of the tile proportion.
///
/// Coefficient zero is the constant term, coefficient one multiplies the width of the main rectangle, and the remaining coefficients multiply the free tile sides.
#[derive(Clone, Debug)]
pub struct Form<C: Int> {
    den: u32,
    c: SmallVec<[Poly<C>; 6]>,
}

impl<C: Int> Form<C> {
    /// The form consisting of the unknown with the given index alone.
    pub fn unknown(index: usize) -> Self {
        let mut c: SmallVec<[Poly<C>; 6]> = SmallVec::new();
        c.resize(index, Poly::zero());
        c.push(Poly::one());
        Form { den: 0, c }
    }

    /// The coefficient of the unknown with the given index.
    pub fn coeff(&self, index: usize) -> Poly<C> {
        self.c.get(index).cloned().unwrap_or_else(Poly::zero)
    }

    /// The power of the tile proportion by which the form is divided.
    pub fn den(&self) -> u32 {
        self.den
    }

    /// The coefficients, by index of unknown.
    pub fn coeffs(&self) -> &[Poly<C>] {
        &self.c
    }

    fn raised(&self, den: u32) -> SmallVec<[Poly<C>; 6]> {
        let k = (den - self.den) as usize;
        self.c.iter().map(|p| p.shift(k)).collect()
    }

    fn combine(&self, o: &Self, sub: bool) -> Self {
        let den = self.den.max(o.den);
        let mut c = self.raised(den);
        let oc = o.raised(den);
        if c.len() < oc.len() {
            c.resize(oc.len(), Poly::zero());
        }
        for (x, y) in c.iter_mut().zip(oc.iter()) {
            *x = if sub { x.sub(y) } else { x.add(y) };
        }
        Form { den, c }
    }

    /// Sum.
    pub fn add(&self, o: &Self) -> Self {
        self.combine(o, false)
    }

    /// Difference.
    pub fn sub(&self, o: &Self) -> Self {
        self.combine(o, true)
    }

    /// Product with the tile proportion.
    pub fn mul_x(&self) -> Self {
        if self.den > 0 {
            Form {
                den: self.den - 1,
                c: self.c.clone(),
            }
        } else {
            Form {
                den: 0,
                c: self.c.iter().map(|p| p.shift(1)).collect(),
            }
        }
    }

    /// Quotient by the tile proportion.
    pub fn div_x(&self) -> Self {
        Form {
            den: self.den + 1,
            c: self.c.clone(),
        }
    }
}
