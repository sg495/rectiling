// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exact isolation and refinement of real polynomial roots in the half-line from one.

use crate::poly::Poly;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::sync::Arc;

/// Dyadic rational number, of the form `m * 2^e`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dyadic {
    m: BigInt,
    e: i64,
}

impl Dyadic {
    /// The dyadic rational `m * 2^e`.
    pub fn new(m: BigInt, e: i64) -> Self {
        Dyadic { m, e }
    }

    fn aligned(&self, o: &Self) -> (BigInt, BigInt, i64) {
        let e = self.e.min(o.e);
        (&self.m << (self.e - e) as usize, &o.m << (o.e - e) as usize, e)
    }

    /// Sum.
    pub fn add(&self, o: &Self) -> Self {
        let (a, b, e) = self.aligned(o);
        Dyadic { m: a + b, e }
    }

    /// Product.
    pub fn mul(&self, o: &Self) -> Self {
        Dyadic {
            m: &self.m * &o.m,
            e: self.e + o.e,
        }
    }

    /// Half of the value.
    pub fn half(&self) -> Self {
        Dyadic {
            m: self.m.clone(),
            e: self.e - 1,
        }
    }

    /// Sign of the value, as -1, 0 or 1.
    pub fn signum(&self) -> i32 {
        self.m.signum().to_i32().unwrap_or(0)
    }

    /// Comparison by value.
    pub fn cmp_value(&self, o: &Self) -> Ordering {
        let (a, b, _) = self.aligned(o);
        a.cmp(&b)
    }

    fn to_f64_dir(&self, up: bool) -> f64 {
        if self.m.is_zero() {
            return 0.0;
        }
        let bits = self.m.bits() as i64;
        let drop = (bits - 64).max(0);
        let top = (&self.m >> drop as usize).to_f64().unwrap_or(f64::NAN);
        let top = if up { top.next_up().next_up() } else { top.next_down().next_down() };
        top * 2f64.powi((self.e + drop) as i32)
    }

    /// A float not greater than the value.
    pub fn to_f64_down(&self) -> f64 {
        self.to_f64_dir(false)
    }

    /// A float not smaller than the value.
    pub fn to_f64_up(&self) -> f64 {
        self.to_f64_dir(true)
    }
}

/// Sign of a polynomial at a dyadic rational.
pub fn sign_at_dyadic(p: &Poly<BigInt>, x: &Dyadic) -> i32 {
    let c = p.coeffs();
    if c.is_empty() {
        return 0;
    }
    let n = c.len() - 1;
    let mut acc = c[n].clone();
    if x.e >= 0 {
        let v = &x.m << x.e as usize;
        for a in c[..n].iter().rev() {
            acc = acc * &v + a;
        }
    } else {
        let s = (-x.e) as usize;
        for (k, a) in c[..n].iter().rev().enumerate() {
            acc = acc * &x.m + (a << (s * (k + 1)));
        }
    }
    acc.signum().to_i32().unwrap_or(0)
}

/// Sign of a polynomial at the rational `num / den`, with positive denominator.
pub fn sign_at_rational(p: &Poly<BigInt>, num: &BigInt, den: &BigInt) -> i32 {
    let c = p.coeffs();
    if c.is_empty() {
        return 0;
    }
    let n = c.len() - 1;
    let mut acc = c[n].clone();
    let mut dpow = BigInt::one();
    for a in c[..n].iter().rev() {
        dpow *= den;
        acc = acc * num + a * &dpow;
    }
    acc.signum().to_i32().unwrap_or(0)
}

fn interval_eval(p: &Poly<BigInt>, lo: &Dyadic, hi: &Dyadic) -> (Dyadic, Dyadic) {
    let zero = Dyadic::new(BigInt::zero(), 0);
    let (mut a, mut b) = (zero.clone(), zero);
    for c in p.coeffs().iter().rev() {
        let cands = [a.mul(lo), a.mul(hi), b.mul(lo), b.mul(hi)];
        let mut mn = cands[0].clone();
        let mut mx = cands[0].clone();
        for v in &cands[1..] {
            if v.cmp_value(&mn) == Ordering::Less {
                mn = v.clone();
            }
            if v.cmp_value(&mx) == Ordering::Greater {
                mx = v.clone();
            }
        }
        let cd = Dyadic::new(c.clone(), 0);
        a = mn.add(&cd);
        b = mx.add(&cd);
    }
    (a, b)
}

/// Real root of a polynomial, located exactly or within an isolating interval with dyadic endpoints.
#[derive(Clone, Debug)]
pub struct RealRoot {
    poly: Arc<Poly<BigInt>>,
    lo: Dyadic,
    hi: Dyadic,
    sign_lo: i32,
}

impl RealRoot {
    /// The polynomial of which this is a root.
    pub fn poly(&self) -> &Poly<BigInt> {
        &self.poly
    }

    /// Whether the root is known exactly.
    pub fn is_exact(&self) -> bool {
        self.lo == self.hi
    }

    /// Halves the isolating interval.
    pub fn refine(&mut self) {
        if self.is_exact() {
            return;
        }
        let mid = self.lo.add(&self.hi).half();
        let s = sign_at_dyadic(&self.poly, &mid);
        if s == 0 {
            self.lo = mid.clone();
            self.hi = mid;
        } else if s == self.sign_lo {
            self.lo = mid;
        } else {
            self.hi = mid;
        }
    }

    /// Refines the isolating interval until its width is at most `2^-bits` times its lower endpoint.
    pub fn refine_to(&mut self, bits: i64) {
        loop {
            if self.is_exact() {
                return;
            }
            let width = self.hi.add(&Dyadic::new(-&self.lo.m, self.lo.e));
            let bound = Dyadic::new(self.lo.m.clone(), self.lo.e - bits);
            if width.cmp_value(&bound) != Ordering::Greater {
                return;
            }
            self.refine();
        }
    }

    /// Floats enclosing the root.
    pub fn enclosure(&self) -> (f64, f64) {
        (self.lo.to_f64_down(), self.hi.to_f64_up())
    }

    /// Sign of the given polynomial at the root, for a root of an irreducible polynomial of degree at least two.
    pub fn sign_of(&mut self, q: &Poly<BigInt>) -> i32 {
        if q.is_zero() {
            return 0;
        }
        if q.degree() >= self.poly.degree() && q.pseudo_div_rem(&self.poly).1.is_zero() {
            return 0;
        }
        loop {
            if self.is_exact() {
                return sign_at_dyadic(q, &self.lo);
            }
            let (a, b) = interval_eval(q, &self.lo, &self.hi);
            if a.signum() > 0 {
                return 1;
            }
            if b.signum() < 0 {
                return -1;
            }
            self.refine();
        }
    }
}

fn descartes_bound(a: &Poly<BigInt>) -> usize {
    let mut rev: Vec<BigInt> = a.coeffs().to_vec();
    rev.reverse();
    Poly::from_coeffs(rev).taylor_shift_one().sign_variations()
}

/// Isolates the real roots greater than one of a square-free polynomial that does not vanish at one, in increasing order.
pub fn isolate_roots_above_one(p: &Poly<BigInt>) -> Vec<RealRoot> {
    let poly = Arc::new(p.clone());
    let q = p.taylor_shift_one();
    let Some(n) = q.degree() else {
        return Vec::new();
    };
    if n == 0 {
        return Vec::new();
    }
    let lead = q.coeffs()[n].abs();
    let maxc = q.coeffs()[..n].iter().map(|v| v.abs()).max().unwrap_or_default();
    let ratio: BigInt = maxc / &lead + 2;
    let k = ratio.bits() as usize + 1;
    let start = Poly::from_coeffs(q.coeffs().iter().enumerate().map(|(i, a)| a << (k * i)));
    let mut out = Vec::new();
    let mut stack = vec![(start, BigInt::zero(), k as i64)];
    let one = Dyadic::new(BigInt::one(), 0);
    while let Some((a, c, e)) = stack.pop() {
        let v = descartes_bound(&a);
        if v == 0 {
            continue;
        }
        if v == 1 {
            let lo = one.add(&Dyadic::new(c.clone(), e));
            let hi = one.add(&Dyadic::new(&c + 1, e));
            let mut sign_lo = sign_at_dyadic(&poly, &lo);
            if sign_lo == 0 {
                sign_lo = -sign_at_dyadic(&poly, &hi);
            }
            out.push(RealRoot {
                poly: poly.clone(),
                lo,
                hi,
                sign_lo,
            });
            continue;
        }
        let left = Poly::from_coeffs(a.coeffs().iter().enumerate().map(|(i, x)| x << (n - i)));
        let mut right = left.taylor_shift_one();
        if right.coeffs().first().is_some_and(|x| x.is_zero()) {
            let mid = one.add(&Dyadic::new(2 * &c + 1, e - 1));
            out.push(RealRoot {
                poly: poly.clone(),
                lo: mid.clone(),
                hi: mid,
                sign_lo: 0,
            });
            right = Poly::from_coeffs(right.coeffs()[1..].iter().cloned());
        }
        stack.push((left, 2 * &c, e - 1));
        stack.push((right, 2 * &c + 1, e - 1));
    }
    out.sort_by(|x, y| x.lo.cmp_value(&y.lo));
    out
}
