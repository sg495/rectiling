// SPDX-License-Identifier: LGPL-3.0-or-later

//! Dense univariate polynomials with integer coefficients.

use crate::int::Int;
use num_bigint::BigInt;
use smallvec::SmallVec;
use std::fmt;

/// Dense univariate polynomial, with coefficients stored from the constant term upwards.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Poly<C: Int> {
    c: SmallVec<[C; 12]>,
}

impl<C: Int> Poly<C> {
    /// The zero polynomial.
    #[inline]
    pub fn zero() -> Self {
        Poly { c: SmallVec::new() }
    }

    /// The constant polynomial with the given value.
    pub fn constant(v: C) -> Self {
        let mut p = Poly { c: SmallVec::new() };
        if !v.is_zero() {
            p.c.push(v);
        }
        p
    }

    /// The constant polynomial one.
    pub fn one() -> Self {
        Self::constant(C::from_i64(1))
    }

    /// The monomial of the given degree with unit coefficient.
    pub fn monomial(deg: usize) -> Self {
        let mut c: SmallVec<[C; 12]> = SmallVec::new();
        c.resize(deg, C::from_i64(0));
        c.push(C::from_i64(1));
        Poly { c }
    }

    /// The polynomial with the given coefficients, listed from the constant term upwards.
    pub fn from_coeffs<I: IntoIterator<Item = C>>(coeffs: I) -> Self {
        let mut p = Poly {
            c: coeffs.into_iter().collect(),
        };
        p.trim();
        p
    }

    /// The polynomial with the given machine-integer coefficients, listed from the constant term upwards.
    pub fn from_i64s(coeffs: &[i64]) -> Self {
        Self::from_coeffs(coeffs.iter().map(|&v| C::from_i64(v)))
    }

    #[inline]
    fn trim(&mut self) {
        while self.c.last().is_some_and(|v| v.is_zero()) {
            self.c.pop();
        }
    }

    /// The coefficients, from the constant term upwards, without trailing zeros.
    #[inline]
    pub fn coeffs(&self) -> &[C] {
        &self.c
    }

    /// Whether the polynomial is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.c.is_empty()
    }

    /// The degree, or `None` for the zero polynomial.
    #[inline]
    pub fn degree(&self) -> Option<usize> {
        self.c.len().checked_sub(1)
    }

    /// The leading coefficient, or `None` for the zero polynomial.
    pub fn leading(&self) -> Option<&C> {
        self.c.last()
    }

    /// Sum.
    pub fn add(&self, o: &Self) -> Self {
        let (a, b) = if self.c.len() >= o.c.len() { (self, o) } else { (o, self) };
        let mut c = a.c.clone();
        for (x, y) in c.iter_mut().zip(b.c.iter()) {
            *x = x.add(y);
        }
        let mut p = Poly { c };
        p.trim();
        p
    }

    /// Difference.
    pub fn sub(&self, o: &Self) -> Self {
        let n = self.c.len().max(o.c.len());
        let zero = C::from_i64(0);
        let mut c: SmallVec<[C; 12]> = SmallVec::with_capacity(n);
        for i in 0..n {
            let x = self.c.get(i).unwrap_or(&zero);
            let y = o.c.get(i).unwrap_or(&zero);
            c.push(x.sub(y));
        }
        let mut p = Poly { c };
        p.trim();
        p
    }

    /// Negation.
    pub fn neg(&self) -> Self {
        Poly {
            c: self.c.iter().map(|v| v.neg()).collect(),
        }
    }

    /// Product.
    pub fn mul(&self, o: &Self) -> Self {
        if self.is_zero() || o.is_zero() {
            return Self::zero();
        }
        let mut c: SmallVec<[C; 12]> = SmallVec::new();
        c.resize(self.c.len() + o.c.len() - 1, C::from_i64(0));
        for (i, x) in self.c.iter().enumerate() {
            if x.is_zero() {
                continue;
            }
            for (j, y) in o.c.iter().enumerate() {
                c[i + j] = c[i + j].add(&x.mul(y));
            }
        }
        let mut p = Poly { c };
        p.trim();
        p
    }

    /// Product with a scalar.
    pub fn scale(&self, k: &C) -> Self {
        let mut p = Poly {
            c: self.c.iter().map(|v| v.mul(k)).collect(),
        };
        p.trim();
        p
    }

    /// Product with the monomial of the given degree.
    pub fn shift(&self, deg: usize) -> Self {
        if self.is_zero() || deg == 0 {
            return self.clone();
        }
        let mut c: SmallVec<[C; 12]> = SmallVec::with_capacity(self.c.len() + deg);
        c.resize(deg, C::from_i64(0));
        c.extend(self.c.iter().cloned());
        Poly { c }
    }

    /// Quotient and remainder of the pseudo-division `lc(o)^k * self = q * o + r`, together with the exponent `k`.
    pub fn pseudo_div_rem(&self, o: &Self) -> (Self, Self, usize) {
        let dn = o.c.len();
        assert!(dn > 0, "division by the zero polynomial");
        let lc = &o.c[dn - 1];
        let mut r = self.clone();
        let mut q = Self::zero();
        let mut k = 0;
        while r.c.len() >= dn {
            let shift = r.c.len() - dn;
            let lr = r.c[r.c.len() - 1].clone();
            q = q.scale(lc).add(&Self::constant(lr.clone()).shift(shift));
            r = r.scale(lc).sub(&o.scale(&lr).shift(shift));
            k += 1;
        }
        (q, r, k)
    }

    /// Quotient of an exact division.
    pub fn div_exact(&self, o: &Self) -> Self {
        let dn = o.c.len();
        assert!(dn > 0, "division by the zero polynomial");
        if self.c.len() < dn {
            return Self::zero();
        }
        let lc = &o.c[dn - 1];
        let mut r = self.c.clone();
        let qn = self.c.len() - dn + 1;
        let mut q: SmallVec<[C; 12]> = SmallVec::new();
        q.resize(qn, C::from_i64(0));
        for i in (0..qn).rev() {
            let t = r[i + dn - 1].div_exact(lc);
            if !t.is_zero() {
                for j in 0..dn {
                    r[i + j] = r[i + j].sub(&t.mul(&o.c[j]));
                }
            }
            q[i] = t;
        }
        let mut p = Poly { c: q };
        p.trim();
        p
    }

    /// Whether the polynomial is an exact multiple of the other, over the integers.
    pub fn is_multiple_of(&self, o: &Self) -> bool {
        let dn = o.c.len();
        assert!(dn > 0, "division by the zero polynomial");
        let lc = &o.c[dn - 1];
        let mut r = self.c.clone();
        while r.len() >= dn {
            let top = r[r.len() - 1].clone();
            let t = top.div_exact(lc);
            if t.mul(lc) != top {
                return false;
            }
            let base = r.len() - dn;
            for j in 0..dn {
                r[base + j] = r[base + j].sub(&t.mul(&o.c[j]));
            }
            r.pop();
            while r.last().is_some_and(|v| v.is_zero()) {
                r.pop();
            }
        }
        r.is_empty()
    }

    /// The non-negative greatest common divisor of the coefficients.
    pub fn content(&self) -> C {
        let mut g = C::from_i64(0);
        for v in self.c.iter() {
            g = g.gcd(v);
        }
        g
    }

    /// The polynomial divided by its content, with positive leading coefficient.
    pub fn primitive(&self) -> Self {
        if self.is_zero() {
            return self.clone();
        }
        let mut g = self.content();
        if self.c[self.c.len() - 1].signum() < 0 {
            g = g.neg();
        }
        Poly {
            c: self.c.iter().map(|v| v.div_exact(&g)).collect(),
        }
    }

    /// The derivative.
    pub fn derivative(&self) -> Self {
        let mut p = Poly {
            c: self
                .c
                .iter()
                .enumerate()
                .skip(1)
                .map(|(i, v)| v.mul(&C::from_i64(i as i64)))
                .collect(),
        };
        p.trim();
        p
    }

    /// A primitive greatest common divisor, with positive leading coefficient.
    pub fn gcd(&self, o: &Self) -> Self {
        if self.is_zero() {
            return o.primitive();
        }
        if o.is_zero() {
            return self.primitive();
        }
        let (mut a, mut b) = (self.primitive(), o.primitive());
        if a.c.len() < b.c.len() {
            std::mem::swap(&mut a, &mut b);
        }
        while !b.is_zero() {
            let (_, r, _) = a.pseudo_div_rem(&b);
            a = b;
            b = r.primitive();
        }
        a
    }

    /// The primitive square-free part, with positive leading coefficient.
    pub fn squarefree_part(&self) -> Self {
        let p = self.primitive();
        if p.c.len() <= 2 {
            return p;
        }
        let g = p.gcd(&p.derivative());
        if g.c.len() <= 1 {
            p
        } else {
            p.div_exact(&g).primitive()
        }
    }

    /// The composition with `x + 1`.
    pub fn taylor_shift_one(&self) -> Self {
        let mut c = self.c.clone();
        let n = c.len();
        for i in 0..n {
            for j in (i..n.saturating_sub(1)).rev() {
                c[j] = c[j].add(&c[j + 1]);
            }
        }
        Poly { c }
    }

    /// The value at one.
    pub fn eval_one(&self) -> C {
        let mut s = C::from_i64(0);
        for v in self.c.iter() {
            s = s.add(v);
        }
        s
    }

    /// The number of sign changes in the coefficient sequence, ignoring zeros.
    pub fn sign_variations(&self) -> usize {
        let mut last = 0;
        let mut n = 0;
        for v in self.c.iter() {
            let s = v.signum();
            if s != 0 {
                if last != 0 && s != last {
                    n += 1;
                }
                last = s;
            }
        }
        n
    }

    /// The same polynomial with arbitrary-precision coefficients.
    pub fn to_big(&self) -> Poly<BigInt> {
        Poly {
            c: self.c.iter().map(|v| v.to_big()).collect(),
        }
    }
}

impl<C: Int + fmt::Display> fmt::Display for Poly<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        let mut first = true;
        for (i, v) in self.c.iter().enumerate().rev() {
            if v.is_zero() {
                continue;
            }
            let neg = v.signum() < 0;
            let mag = if neg { v.neg() } else { v.clone() };
            let sign = match (first, neg) {
                (true, true) => "-",
                (true, false) => "",
                (false, true) => " - ",
                (false, false) => " + ",
            };
            let unit = mag == C::from_i64(1);
            match i {
                0 => write!(f, "{sign}{mag}")?,
                1 if unit => write!(f, "{sign}x")?,
                1 => write!(f, "{sign}{mag}*x")?,
                _ if unit => write!(f, "{sign}x^{i}")?,
                _ => write!(f, "{sign}{mag}*x^{i}")?,
            }
            first = false;
        }
        Ok(())
    }
}
