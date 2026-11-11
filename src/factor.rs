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

fn equal_degree_split<F: Field>(f: &F, g: FPoly<F>, d: usize, seed: &mut u64, out: &mut Vec<FPoly<F>>) {
    if g.len() - 1 == d {
        out.push(g);
        return;
    }
    let exp: BigInt = (f.modulus().pow(d as u32) - 1) / 2;
    loop {
        let mut r: FPoly<F> = (0..g.len() - 1)
            .map(|_| {
                *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                f.from_u64(*seed >> 11)
            })
            .collect();
        trim(f, &mut r);
        if r.len() < 2 {
            continue;
        }
        let t = fsub(f, &fpowmod(f, &r, &exp, &g), &vec![f.one()]);
        let s = fgcd(f, &t, &g);
        if s.len() > 1 && s.len() < g.len() {
            let (q, _) = fdivrem(f, &g, &s);
            equal_degree_split(f, s, d, seed, out);
            equal_degree_split(f, fmonic(f, &q), d, seed, out);
            return;
        }
    }
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
    let mut g = fmonic(f, &image);
    let x: FPoly<F> = vec![f.zero(), f.one()];
    let modulus = f.modulus();
    let frobenius = fpowmod(f, &x, &modulus, &g);
    if nullity_of_frobenius(f, &frobenius, &g) == 1 {
        return Some(vec![g]);
    }
    let mut h = x.clone();
    let mut out = Vec::new();
    let mut seed = 0x9E3779B97F4A7C15u64;
    let mut d = 0;
    while g.len() > 1 {
        d += 1;
        if 2 * d > g.len() - 1 {
            out.push(g);
            break;
        }
        h = fpowmod(f, &h, &modulus, &g);
        let s = fgcd(f, &fsub(f, &h, &x), &g);
        if s.len() > 1 {
            g = fmonic(f, &fdivrem(f, &g, &s).0);
            equal_degree_split(f, s, d, &mut seed, &mut out);
            h = fdivrem(f, &h, &g).1;
        }
    }
    Some(out)
}

/// The number of irreducible factors of a monic square-free polynomial, as the dimension of the fixed space of the Frobenius map.
fn nullity_of_frobenius<F: Field>(f: &F, frobenius: &FPoly<F>, g: &FPoly<F>) -> usize {
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
