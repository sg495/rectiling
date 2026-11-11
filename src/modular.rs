// SPDX-License-Identifier: LGPL-3.0-or-later

//! Arithmetic modulo word-sized primes, and roots of integer polynomials modulo such primes.

use std::sync::OnceLock;

/// Product modulo a modulus below 2^63.
#[inline]
pub(crate) fn mul_mod(a: u64, b: u64, p: u64) -> u64 {
    ((a as u128 * b as u128) % p as u128) as u64
}

/// Power modulo a modulus below 2^63.
pub(crate) fn pow_mod(mut a: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1 % p;
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod(r, a, p);
        }
        a = mul_mod(a, a, p);
        e >>= 1;
    }
    r
}

/// Inverse of a non-zero residue modulo a prime.
pub(crate) fn inv_mod(a: u64, p: u64) -> u64 {
    pow_mod(a, p - 2, p)
}

/// Residue of a machine integer modulo a modulus below 2^63.
#[inline]
pub(crate) fn residue(v: i64, p: u64) -> u64 {
    v.rem_euclid(p as i64) as u64
}

/// Whether a number is prime, by the test of Miller and Rabin with bases that decide every 64-bit number.
pub(crate) fn is_prime(n: u64) -> bool {
    const BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    if n < 2 {
        return false;
    }
    for q in BASES {
        if n % q == 0 {
            return n == q;
        }
    }
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    BASES.iter().all(|&a| {
        let mut x = pow_mod(a, d, n);
        if x == 1 || x == n - 1 {
            return true;
        }
        for _ in 1..s {
            x = mul_mod(x, x, n);
            if x == n - 1 {
                return true;
            }
        }
        false
    })
}

const PRIMES: usize = 256;

/// The largest primes below 2^62, in decreasing order.
pub(crate) fn primes() -> &'static [u64] {
    static LIST: OnceLock<Vec<u64>> = OnceLock::new();
    LIST.get_or_init(|| (0..1u64 << 61).map(|k| (1u64 << 62) - 1 - 2 * k).filter(|&n| is_prime(n)).take(PRIMES).collect())
}

/// Value at a residue of the polynomial with the given machine-integer coefficients, listed from the constant term upwards.
pub(crate) fn eval_mod(coeffs: &[i64], r: u64, p: u64) -> u64 {
    coeffs.iter().rev().fold(0, |acc, &c| (mul_mod(acc, r, p) + residue(c, p)) % p)
}

fn trim(a: &mut Vec<u64>) {
    while a.last() == Some(&0) {
        a.pop();
    }
}

/// Remainder of a polynomial modulo a monic polynomial, over a prime field.
fn rem(mut a: Vec<u64>, m: &[u64], p: u64) -> Vec<u64> {
    let dm = m.len() - 1;
    while a.len() > dm {
        let top = a.pop().unwrap_or(0);
        if top != 0 {
            let base = a.len() - dm;
            for (j, &c) in m[..dm].iter().enumerate() {
                a[base + j] = (a[base + j] + p - mul_mod(top, c, p)) % p;
            }
        }
    }
    trim(&mut a);
    a
}

fn mul_rem(a: &[u64], b: &[u64], m: &[u64], p: u64) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0u64; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            out[i + j] = (out[i + j] + mul_mod(x, y, p)) % p;
        }
    }
    rem(out, m, p)
}

fn pow_rem(base: &[u64], mut e: u64, m: &[u64], p: u64) -> Vec<u64> {
    let mut result = rem(vec![1], m, p);
    let mut base = rem(base.to_vec(), m, p);
    while e > 0 {
        if e & 1 == 1 {
            result = mul_rem(&result, &base, m, p);
        }
        base = mul_rem(&base, &base, m, p);
        e >>= 1;
    }
    result
}

fn monic(mut a: Vec<u64>, p: u64) -> Vec<u64> {
    trim(&mut a);
    if let Some(&lead) = a.last() {
        let inv = inv_mod(lead, p);
        for c in a.iter_mut() {
            *c = mul_mod(*c, inv, p);
        }
    }
    a
}

/// Monic greatest common divisor of two polynomials over a prime field.
fn gcd(a: Vec<u64>, b: Vec<u64>, p: u64) -> Vec<u64> {
    let (mut a, mut b) = (monic(a, p), monic(b, p));
    while !b.is_empty() {
        let r = monic(rem(a, &b, p), p);
        a = b;
        b = r;
    }
    a
}

fn sub_constant(mut a: Vec<u64>, c: u64, p: u64) -> Vec<u64> {
    if a.is_empty() {
        a.push(0);
    }
    a[0] = (a[0] + p - c % p) % p;
    trim(&mut a);
    a
}

/// A non-zero root modulo a prime of the polynomial with the given machine-integer coefficients, if the prime does not divide the leading coefficient and such a root exists.
pub(crate) fn root_mod(coeffs: &[i64], p: u64) -> Option<u64> {
    let f: Vec<u64> = coeffs.iter().map(|&c| residue(c, p)).collect();
    if f.len() < 2 || f[f.len() - 1] == 0 || f[0] == 0 {
        return None;
    }
    let f = monic(f, p);
    let mut g = if f.len() == 2 {
        f
    } else {
        let mut power = pow_rem(&[0, 1], p, &f, p);
        power.resize(power.len().max(2), 0);
        power[1] = (power[1] + p - 1) % p;
        trim(&mut power);
        if power.is_empty() { f } else { gcd(f, power, p) }
    };
    let mut shift = 0;
    while g.len() > 2 {
        shift += 1;
        let half = pow_rem(&[shift, 1], (p - 1) / 2, &g, p);
        let part = gcd(g.clone(), sub_constant(half, 1, p), p);
        if part.len() > 1 && part.len() < g.len() {
            g = part;
        }
        if shift > 1 << 16 {
            return None;
        }
    }
    (g.len() == 2).then(|| (p - g[0]) % p)
}
