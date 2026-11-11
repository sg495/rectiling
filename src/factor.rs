// SPDX-License-Identifier: LGPL-3.0-or-later

//! Factorisation of integer polynomials into irreducible factors.

use crate::poly::Poly;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

trait Field {
    type E: Clone + PartialEq;
    fn modulus(&self) -> BigInt;
    fn zero(&self) -> Self::E;
    fn one(&self) -> Self::E;
    fn is_zero(&self, a: &Self::E) -> bool;
    fn add(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn sub(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn mul(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn inv(&self, a: &Self::E) -> Self::E;
    fn from_big(&self, a: &BigInt) -> Self::E;
    fn to_big(&self, a: &Self::E) -> BigInt;
    fn from_u64(&self, a: u64) -> Self::E {
        self.from_big(&BigInt::from(a))
    }
    /// The exponent k, if the modulus is the Mersenne number 2^k - 1.
    fn mersenne_exponent(&self) -> Option<u32> {
        None
    }
}

struct WordField {
    p: u64,
}

impl Field for WordField {
    type E = u64;
    fn modulus(&self) -> BigInt {
        BigInt::from(self.p)
    }
    fn zero(&self) -> u64 {
        0
    }
    fn one(&self) -> u64 {
        1
    }
    fn is_zero(&self, a: &u64) -> bool {
        *a == 0
    }
    fn add(&self, a: &u64, b: &u64) -> u64 {
        ((*a as u128 + *b as u128) % self.p as u128) as u64
    }
    fn sub(&self, a: &u64, b: &u64) -> u64 {
        if a >= b { a - b } else { self.p - (b - a) }
    }
    fn mul(&self, a: &u64, b: &u64) -> u64 {
        ((*a as u128 * *b as u128) % self.p as u128) as u64
    }
    fn inv(&self, a: &u64) -> u64 {
        let mut result = 1u64;
        let mut base = *a;
        let mut e = self.p - 2;
        while e > 0 {
            if e & 1 == 1 {
                result = self.mul(&result, &base);
            }
            base = self.mul(&base, &base);
            e >>= 1;
        }
        result
    }
    fn from_big(&self, a: &BigInt) -> u64 {
        a.mod_floor(&BigInt::from(self.p)).to_u64().unwrap_or(0)
    }
    fn to_big(&self, a: &u64) -> BigInt {
        BigInt::from(*a)
    }
}

const MERSENNE: u64 = (1 << 61) - 1;

struct MersenneField;

impl MersenneField {
    #[inline]
    fn reduce(t: u128) -> u64 {
        let folded = (t & MERSENNE as u128) + (t >> 61);
        let folded = (folded & MERSENNE as u128) as u64 + (folded >> 61) as u64;
        if folded >= MERSENNE { folded - MERSENNE } else { folded }
    }
}

impl Field for MersenneField {
    type E = u64;
    fn modulus(&self) -> BigInt {
        BigInt::from(MERSENNE)
    }
    fn zero(&self) -> u64 {
        0
    }
    fn one(&self) -> u64 {
        1
    }
    #[inline]
    fn is_zero(&self, a: &u64) -> bool {
        *a == 0
    }
    #[inline]
    fn add(&self, a: &u64, b: &u64) -> u64 {
        let s = a + b;
        if s >= MERSENNE { s - MERSENNE } else { s }
    }
    #[inline]
    fn sub(&self, a: &u64, b: &u64) -> u64 {
        if a >= b { a - b } else { MERSENNE - (b - a) }
    }
    #[inline]
    fn mul(&self, a: &u64, b: &u64) -> u64 {
        Self::reduce(*a as u128 * *b as u128)
    }
    fn inv(&self, a: &u64) -> u64 {
        let mut result = 1u64;
        let mut base = *a;
        let mut e = MERSENNE - 2;
        while e > 0 {
            if e & 1 == 1 {
                result = self.mul(&result, &base);
            }
            base = self.mul(&base, &base);
            e >>= 1;
        }
        result
    }
    fn from_big(&self, a: &BigInt) -> u64 {
        a.mod_floor(&BigInt::from(MERSENNE)).to_u64().unwrap_or(0)
    }
    fn to_big(&self, a: &u64) -> BigInt {
        BigInt::from(*a)
    }
    fn from_u64(&self, a: u64) -> u64 {
        a % MERSENNE
    }
    fn mersenne_exponent(&self) -> Option<u32> {
        Some(61)
    }
}

const SMALL_MERSENNE: u64 = (1 << 31) - 1;

struct SmallField;

impl Field for SmallField {
    type E = u64;
    fn modulus(&self) -> BigInt {
        BigInt::from(SMALL_MERSENNE)
    }
    fn zero(&self) -> u64 {
        0
    }
    fn one(&self) -> u64 {
        1
    }
    #[inline]
    fn is_zero(&self, a: &u64) -> bool {
        *a == 0
    }
    #[inline]
    fn add(&self, a: &u64, b: &u64) -> u64 {
        let s = a + b;
        if s >= SMALL_MERSENNE { s - SMALL_MERSENNE } else { s }
    }
    #[inline]
    fn sub(&self, a: &u64, b: &u64) -> u64 {
        if a >= b { a - b } else { SMALL_MERSENNE - (b - a) }
    }
    #[inline]
    fn mul(&self, a: &u64, b: &u64) -> u64 {
        let t = a * b;
        let folded = (t & SMALL_MERSENNE) + (t >> 31);
        let folded = (folded & SMALL_MERSENNE) + (folded >> 31);
        if folded >= SMALL_MERSENNE { folded - SMALL_MERSENNE } else { folded }
    }
    fn inv(&self, a: &u64) -> u64 {
        let mut result = 1u64;
        let mut base = *a;
        let mut e = SMALL_MERSENNE - 2;
        while e > 0 {
            if e & 1 == 1 {
                result = self.mul(&result, &base);
            }
            base = self.mul(&base, &base);
            e >>= 1;
        }
        result
    }
    fn from_big(&self, a: &BigInt) -> u64 {
        a.mod_floor(&BigInt::from(SMALL_MERSENNE)).to_u64().unwrap_or(0)
    }
    fn to_big(&self, a: &u64) -> BigInt {
        BigInt::from(*a)
    }
    fn from_u64(&self, a: u64) -> u64 {
        a % SMALL_MERSENNE
    }
    fn mersenne_exponent(&self) -> Option<u32> {
        Some(31)
    }
}

/// Whether a polynomial with machine-integer coefficients is certified irreducible over the rationals by its reduction modulo a small prime.
pub(crate) fn certified_irreducible(coeffs: &[i64]) -> bool {
    let f = SmallField;
    let image: Vec<u64> = coeffs.iter().map(|&c| c.rem_euclid(SMALL_MERSENNE as i64) as u64).collect();
    let d = image.len() - 1;
    if d < 2 || image[d] == 0 {
        return d == 1 && image[d] != 0;
    }
    let deriv: Vec<u64> = (1..=d).map(|i| f.mul(&image[i], &(i as u64))).collect();
    let mut deriv = deriv;
    trim(&f, &mut deriv);
    if fgcd(&f, &image, &deriv).len() != 1 {
        return false;
    }
    let g = fmonic(&f, &image);
    let frobenius = frobenius_of_x(&f, &g);
    nullity_of_frobenius(&f, &frobenius, &g) == 1
}

/// The power of the indeterminate by the modulus of the field, reduced by a monic polynomial.
fn frobenius_of_x<F: Field>(f: &F, g: &FPoly<F>) -> FPoly<F> {
    let x: FPoly<F> = vec![f.zero(), f.one()];
    let Some(k) = f.mersenne_exponent() else {
        return fpowmod(f, &x, &f.modulus(), g);
    };
    let mut r = fdivrem(f, &x, g).1;
    for _ in 1..k {
        let mut sq = fmul(f, &r, &r);
        sq.insert(0, f.zero());
        r = fdivrem(f, &sq, g).1;
    }
    r
}


struct BigField {
    p: BigInt,
}

impl Field for BigField {
    type E = BigInt;
    fn modulus(&self) -> BigInt {
        self.p.clone()
    }
    fn zero(&self) -> BigInt {
        BigInt::zero()
    }
    fn one(&self) -> BigInt {
        BigInt::one()
    }
    fn is_zero(&self, a: &BigInt) -> bool {
        a.is_zero()
    }
    fn add(&self, a: &BigInt, b: &BigInt) -> BigInt {
        (a + b).mod_floor(&self.p)
    }
    fn sub(&self, a: &BigInt, b: &BigInt) -> BigInt {
        (a - b).mod_floor(&self.p)
    }
    fn mul(&self, a: &BigInt, b: &BigInt) -> BigInt {
        (a * b).mod_floor(&self.p)
    }
    fn inv(&self, a: &BigInt) -> BigInt {
        a.modpow(&(&self.p - 2), &self.p)
    }
    fn from_big(&self, a: &BigInt) -> BigInt {
        a.mod_floor(&self.p)
    }
    fn to_big(&self, a: &BigInt) -> BigInt {
        a.clone()
    }
}

type FPoly<F> = Vec<<F as Field>::E>;

fn trim<F: Field>(f: &F, a: &mut FPoly<F>) {
    while a.last().is_some_and(|v| f.is_zero(v)) {
        a.pop();
    }
}

fn fsub<F: Field>(f: &F, a: &FPoly<F>, b: &FPoly<F>) -> FPoly<F> {
    let n = a.len().max(b.len());
    let z = f.zero();
    let mut r: FPoly<F> = (0..n).map(|i| f.sub(a.get(i).unwrap_or(&z), b.get(i).unwrap_or(&z))).collect();
    trim(f, &mut r);
    r
}

fn fmul<F: Field>(f: &F, a: &FPoly<F>, b: &FPoly<F>) -> FPoly<F> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut r = vec![f.zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            r[i + j] = f.add(&r[i + j], &f.mul(x, y));
        }
    }
    r
}

fn fdivrem<F: Field>(f: &F, a: &FPoly<F>, b: &FPoly<F>) -> (FPoly<F>, FPoly<F>) {
    let mut r = a.clone();
    if r.len() < b.len() {
        return (Vec::new(), r);
    }
    let lead = &b[b.len() - 1];
    let inv = if *lead == f.one() { f.one() } else { f.inv(lead) };
    let qn = r.len() - b.len() + 1;
    let mut q = vec![f.zero(); qn];
    for i in (0..qn).rev() {
        let t = f.mul(&r[i + b.len() - 1], &inv);
        if !f.is_zero(&t) {
            for (j, y) in b.iter().enumerate() {
                r[i + j] = f.sub(&r[i + j], &f.mul(&t, y));
            }
        }
        q[i] = t;
    }
    r.truncate(b.len() - 1);
    trim(f, &mut r);
    (q, r)
}

fn fmonic<F: Field>(f: &F, a: &FPoly<F>) -> FPoly<F> {
    match a.last() {
        None => Vec::new(),
        Some(l) => {
            let inv = f.inv(l);
            a.iter().map(|v| f.mul(v, &inv)).collect()
        }
    }
}

fn fgcd<F: Field>(f: &F, a: &FPoly<F>, b: &FPoly<F>) -> FPoly<F> {
    let (mut a, mut b) = (a.clone(), b.clone());
    while !b.is_empty() {
        let (_, r) = fdivrem(f, &a, &b);
        a = b;
        b = r;
    }
    fmonic(f, &a)
}

fn fpowmod<F: Field>(f: &F, base: &FPoly<F>, exp: &BigInt, m: &FPoly<F>) -> FPoly<F> {
    let mut result: FPoly<F> = vec![f.one()];
    let (_, mut b) = fdivrem(f, base, m);
    for i in 0..exp.bits() {
        if exp.bit(i) {
            result = fdivrem(f, &fmul(f, &result, &b), m).1;
        }
        b = fdivrem(f, &fmul(f, &b, &b), m).1;
    }
    result
}

fn frobenius_matrix<F: Field>(f: &F, frobenius: &FPoly<F>, g: &FPoly<F>) -> Vec<FPoly<F>> {
    let d = g.len() - 1;
    let mut rows: Vec<FPoly<F>> = Vec::with_capacity(d);
    let mut power: FPoly<F> = vec![f.one()];
    for i in 0..d {
        let mut row = power.clone();
        row.resize(d, f.zero());
        row[i] = f.sub(&row[i], &f.one());
        rows.push(row);
        power = fdivrem(f, &fmul(f, &power, frobenius), g).1;
    }
    rows
}

/// A basis of the polynomials fixed by the Frobenius map modulo a monic square-free polynomial.
fn fixed_space<F: Field>(f: &F, frobenius: &FPoly<F>, g: &FPoly<F>) -> Vec<FPoly<F>> {
    let d = g.len() - 1;
    let rows = frobenius_matrix(f, frobenius, g);
    let mut m: Vec<FPoly<F>> = (0..d).map(|r| (0..d).map(|c| rows[c][r].clone()).collect()).collect();
    let mut pivots: Vec<Option<usize>> = vec![None; d];
    let mut rank = 0;
    for col in 0..d {
        let Some(pivot) = (rank..d).find(|&r| !f.is_zero(&m[r][col])) else {
            continue;
        };
        m.swap(rank, pivot);
        let inv = f.inv(&m[rank][col]);
        for c in col..d {
            m[rank][c] = f.mul(&m[rank][c], &inv);
        }
        for r in 0..d {
            if r == rank || f.is_zero(&m[r][col]) {
                continue;
            }
            let factor = m[r][col].clone();
            for c in col..d {
                let delta = f.mul(&factor, &m[rank][c]);
                m[r][c] = f.sub(&m[r][c], &delta);
            }
        }
        pivots[col] = Some(rank);
        rank += 1;
    }
    let mut basis = Vec::new();
    for free in 0..d {
        if pivots[free].is_some() {
            continue;
        }
        let mut v = vec![f.zero(); d];
        v[free] = f.one();
        for col in 0..d {
            if let Some(r) = pivots[col] {
                v[col] = f.sub(&f.zero(), &m[r][free]);
            }
        }
        trim(f, &mut v);
        basis.push(v);
    }
    basis
}

/// The power of a polynomial by half the order of the multiplicative group of the field, reduced by a monic polynomial.
fn half_power<F: Field>(f: &F, v: &FPoly<F>, u: &FPoly<F>) -> FPoly<F> {
    let base = fdivrem(f, v, u).1;
    let Some(k) = f.mersenne_exponent() else {
        let exp: BigInt = (f.modulus() - 1) / 2;
        return fpowmod(f, &base, &exp, u);
    };
    let mut r = base.clone();
    for _ in 2..k {
        let sq = fdivrem(f, &fmul(f, &r, &r), u).1;
        r = fdivrem(f, &fmul(f, &sq, &base), u).1;
    }
    r
}

fn modular_factors<F: Field>(f: &F, p: &Poly<BigInt>) -> Option<Vec<FPoly<F>>> {
    let image: FPoly<F> = p.coeffs().iter().map(|c| f.from_big(c)).collect();
    if image.last().is_none_or(|l| f.is_zero(l)) {
        return None;
    }
    let deriv: FPoly<F> = p.derivative().coeffs().iter().map(|c| f.from_big(c)).collect();
    if fgcd(f, &image, &deriv).len() != 1 {
        return None;
    }
    let g = fmonic(f, &image);
    let frobenius = frobenius_of_x(f, &g);
    let basis = fixed_space(f, &frobenius, &g);
    let count = basis.len();
    let mut factors = vec![g];
    let mut seed = 0x9E3779B97F4A7C15u64;
    while factors.len() < count {
        let mut v: FPoly<F> = Vec::new();
        for b in &basis {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let c = f.from_u64(seed >> 11);
            if v.len() < b.len() {
                v.resize(b.len(), f.zero());
            }
            for (i, x) in b.iter().enumerate() {
                v[i] = f.add(&v[i], &f.mul(&c, x));
            }
        }
        trim(f, &mut v);
        let mut next = Vec::with_capacity(count);
        for u in factors {
            if u.len() <= 2 || next.len() + 1 >= count {
                next.push(u);
                continue;
            }
            let w = fsub(f, &half_power(f, &v, &u), &vec![f.one()]);
            let t = fgcd(f, &w, &u);
            if t.len() > 1 && t.len() < u.len() {
                let q = fmonic(f, &fdivrem(f, &u, &t).0);
                next.push(t);
                next.push(q);
            } else {
                next.push(u);
            }
        }
        factors = next;
    }
    Some(factors)
}

/// The number of irreducible factors of a monic square-free polynomial, as the dimension of the fixed space of the Frobenius map.
fn nullity_of_frobenius<F: Field>(f: &F, frobenius: &FPoly<F>, g: &FPoly<F>) -> usize {
    let d = g.len() - 1;
    let mut rows = frobenius_matrix(f, frobenius, g);
    let mut rank = 0;
    for col in 0..d {
        let Some(pivot) = (rank..d).find(|&r| !f.is_zero(&rows[r][col])) else {
            continue;
        };
        rows.swap(rank, pivot);
        let inv = f.inv(&rows[rank][col]);
        for r in rank + 1..d {
            if f.is_zero(&rows[r][col]) {
                continue;
            }
            let factor = f.mul(&rows[r][col], &inv);
            for c in col..d {
                let delta = f.mul(&factor, &rows[rank][c]);
                rows[r][c] = f.sub(&rows[r][c], &delta);
            }
        }
        rank += 1;
    }
    d - rank
}

fn symmetric_lift<F: Field>(f: &F, a: &FPoly<F>, scale: &BigInt) -> Poly<BigInt> {
    let m = f.modulus();
    let half: BigInt = &m / 2;
    Poly::from_coeffs(a.iter().map(|c| {
        let v = (f.to_big(c) * scale).mod_floor(&m);
        if v > half { v - &m } else { v }
    }))
}

fn recombine<F: Field>(f: &F, p: &Poly<BigInt>, mut mods: Vec<FPoly<F>>) -> Vec<Poly<BigInt>> {
    let mut rest = p.clone();
    let mut out = Vec::new();
    let mut size = 1;
    while 2 * size <= mods.len() {
        let mut idx: Vec<usize> = (0..size).collect();
        let mut found = false;
        loop {
            let mut prod: FPoly<F> = vec![f.one()];
            for &i in &idx {
                prod = fmul(f, &prod, &mods[i]);
            }
            let lead = rest.leading().cloned().unwrap_or_default();
            let cand = symmetric_lift(f, &prod, &lead).primitive();
            if rest.is_multiple_of(&cand) {
                rest = rest.div_exact(&cand);
                out.push(cand);
                for &i in idx.iter().rev() {
                    mods.remove(i);
                }
                found = true;
                break;
            }
            let mut k = size;
            while k > 0 && idx[k - 1] == mods.len() - size + k - 1 {
                k -= 1;
            }
            if k == 0 {
                break;
            }
            idx[k - 1] += 1;
            for j in k..size {
                idx[j] = idx[j - 1] + 1;
            }
        }
        if !found {
            size += 1;
        }
    }
    if rest.degree().is_some_and(|d| d > 0) {
        out.push(rest.primitive());
    }
    out
}

fn factor_squarefree(p: &Poly<BigInt>) -> Vec<Poly<BigInt>> {
    let d = p.degree().unwrap_or(0);
    if d <= 1 {
        return if d == 1 { vec![p.clone()] } else { Vec::new() };
    }
    let norm2: BigInt = p.coeffs().iter().map(|c| c * c).sum();
    let lead = p.leading().cloned().unwrap_or_default().abs();
    let bound: BigInt = ((norm2.sqrt() + 1) * &lead << (d + 1)) + 1;
    if bound < BigInt::from(MERSENNE) {
        if let Some(mods) = modular_factors(&MersenneField, p) {
            return recombine(&MersenneField, p, mods);
        }
    }
    for &w in &[(1u64 << 62) - 57, (1u64 << 63) - 25] {
        if bound < BigInt::from(w) {
            let f = WordField { p: w };
            if let Some(mods) = modular_factors(&f, p) {
                return recombine(&f, p, mods);
            }
        }
    }
    for &e in &[127u32, 521, 1279, 2203] {
        let m: BigInt = (BigInt::one() << e) - 1;
        if bound < m {
            let f = BigField { p: m };
            if let Some(mods) = modular_factors(&f, p) {
                return recombine(&f, p, mods);
            }
        }
    }
    panic!("coefficient bound exceeds the supported moduli");
}

/// Factorises a non-zero integer polynomial into primitive irreducible factors with positive leading coefficients, with multiplicities.
pub fn factor(p: &Poly<BigInt>) -> Vec<(Poly<BigInt>, usize)> {
    let mut out: Vec<(Poly<BigInt>, usize)> = Vec::new();
    let words: Option<Vec<i64>> = p.coeffs().iter().map(|c| c.to_i64()).collect();
    if let Some(mut w) = words {
        let content = w.iter().fold(0u64, |g, &c| {
            let (mut a, mut b) = (g, c.unsigned_abs());
            while b != 0 {
                (a, b) = (b, a % b);
            }
            a
        });
        if content > 1 && content <= i64::MAX as u64 {
            for c in w.iter_mut() {
                *c /= content as i64;
            }
        }
        if w.last().is_some_and(|&l| l < 0) && w.iter().all(|&c| c != i64::MIN) {
            for c in w.iter_mut() {
                *c = -*c;
            }
        }
        if w.len() >= 2 && certified_irreducible(&w) {
            return vec![(Poly::from_i64s(&w), 1)];
        }
    }
    let mut rest = p.primitive();
    let mut mult = 1;
    while rest.degree().is_some_and(|d| d > 0) {
        let g = rest.gcd(&rest.derivative());
        let sqf = rest.div_exact(&g).primitive();
        let next = g.gcd(&sqf);
        let layer = sqf.div_exact(&next).primitive();
        for f in factor_squarefree(&layer) {
            out.push((f, mult));
        }
        rest = g;
        mult += 1;
    }
    out.sort_by(|a, b| (a.0.degree(), a.0.coeffs()).cmp(&(b.0.degree(), b.0.coeffs())));
    out
}
