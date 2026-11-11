// SPDX-License-Identifier: LGPL-3.0-or-later

//! Tests of the exact polynomial algebra.

use num_bigint::BigInt;
use rectiling::Poly;
use rectiling::algebraic::Registry;
use rectiling::factor::factor;
use rectiling::roots::isolate_roots_above_one;

fn poly(c: &[i64]) -> Poly<BigInt> {
    Poly::from_i64s(c)
}

fn product(factors: &[(Poly<BigInt>, usize)]) -> Poly<BigInt> {
    let mut p = Poly::one();
    for (f, m) in factors {
        for _ in 0..*m {
            p = p.mul(f);
        }
    }
    p
}

#[test]
fn arithmetic_identities() {
    let a = poly(&[1, -2, 0, 3]);
    let b = poly(&[-5, 1, 4]);
    assert_eq!(a.mul(&b).div_exact(&b), a);
    assert_eq!(a.add(&b).sub(&b), a);
    assert!(a.mul(&b).is_multiple_of(&a));
    assert!(!a.is_multiple_of(&b));
    assert_eq!(poly(&[1, 2, 1]).taylor_shift_one(), poly(&[4, 4, 1]));
    assert_eq!(poly(&[2, 4, 6]).primitive(), poly(&[1, 2, 3]));
    assert_eq!(a.mul(&b).gcd(&a.mul(&poly(&[7, 1]))), a.primitive());
    assert_eq!(format!("{}", poly(&[-1, 1, -2, 1])), "x^3 - 2*x^2 + x - 1");
}

#[test]
fn factorisation_of_known_products() {
    let cases: Vec<Vec<(Vec<i64>, usize)>> = vec![
        vec![(vec![-1, 1], 1)],
        vec![(vec![-1, 1], 3), (vec![1, 1], 2)],
        vec![(vec![-1, 1, -2, 1], 1), (vec![-2, 2, -2, 1], 1)],
        vec![(vec![1, 0, 1], 1), (vec![1, 1, 1], 2), (vec![-2, 0, 1], 1)],
        vec![(vec![-4, 3], 1), (vec![-1, 1, -3, 2], 1), (vec![-5, 2], 1)],
        vec![(vec![1, 1, 1, 1, 1], 1), (vec![1, -1, 1, -1, 1], 1)],
        vec![(vec![-1, 2, -7, 12, -10, 9, -3, 1], 1), (vec![-3, 2, -2, 1], 2)],
    ];
    for case in cases {
        let mut expected: Vec<(Poly<BigInt>, usize)> = case.iter().map(|(c, m)| (poly(c), *m)).collect();
        let p = product(&expected);
        let mut found = factor(&p);
        let key = |f: &(Poly<BigInt>, usize)| format!("{}^{}", f.0, f.1);
        expected.sort_by_key(key);
        found.sort_by_key(key);
        assert_eq!(found, expected, "factorisation of {p}");
    }
}

#[test]
fn irreducible_polynomials_stay_whole() {
    for c in [vec![1i64, 0, 0, 0, 1], vec![-2, 0, 0, 0, 0, 1], vec![1, 1, 0, 0, 0, 0, 0, 1], vec![-1, 2, -7, 12, -10, 9, -3, 1]] {
        let p = poly(&c);
        assert_eq!(factor(&p), vec![(p.clone(), 1)]);
    }
    let swinnerton_dyer = poly(&[1, 0, -10, 0, 1]);
    assert_eq!(factor(&swinnerton_dyer), vec![(swinnerton_dyer.clone(), 1)]);
}

#[test]
fn large_coefficients_use_larger_moduli() {
    let big = BigInt::from(10).pow(40);
    let a = Poly::from_coeffs([-&big - 1, BigInt::from(0), BigInt::from(3)]);
    let b = Poly::from_coeffs([big.clone() + 7, big.clone(), BigInt::from(1), BigInt::from(5)]);
    let found = factor(&a.mul(&b));
    assert_eq!(found.len(), 2);
    assert!(found.iter().any(|(f, m)| f == &a && *m == 1));
    assert!(found.iter().any(|(f, m)| f == &b && *m == 1));
}

#[test]
fn root_isolation_counts_and_locates_roots() {
    assert_eq!(isolate_roots_above_one(&poly(&[-2, 0, 1])).len(), 1);
    assert_eq!(isolate_roots_above_one(&poly(&[1, 0, 1])).len(), 0);
    assert_eq!(isolate_roots_above_one(&poly(&[-1, 1, -2, 1])).len(), 1);
    let wilkinson = product(&(2..=9).map(|k| (poly(&[-(2 * k + 1), 2]), 1)).collect::<Vec<_>>());
    let roots = isolate_roots_above_one(&wilkinson);
    assert_eq!(roots.len(), 8);
    for (k, mut r) in roots.into_iter().enumerate() {
        r.refine_to(40);
        let (lo, hi) = r.enclosure();
        let expected = k as f64 + 2.5;
        assert!(lo <= expected && expected <= hi && hi - lo < 1e-9);
    }
    let close = poly(&[2 * 1_000_001 * 1_000_001 - 1, -4 * 1_000_001, 2]);
    assert_eq!(isolate_roots_above_one(&close.to_big()).len(), 2);
}

#[test]
fn signs_at_algebraic_numbers() {
    let registry = Registry::new();
    let roots = registry.roots_from_one(&poly(&[-2, 0, 1]).mul(&poly(&[-3, 2])).mul(&poly(&[-1, 3])));
    assert_eq!(roots.len(), 2);
    let sqrt2 = roots.iter().find(|r| r.lo < 1.42).expect("root near 1.414");
    let half = roots.iter().find(|r| r.lo > 1.45).expect("root at 1.5");
    assert_eq!(registry.sign_at(sqrt2.id, &poly(&[-2, 0, 1])), 0);
    assert_eq!(registry.sign_at(sqrt2.id, &poly(&[-4, 0, 0, 0, 1])), 0);
    assert_eq!(registry.sign_at(sqrt2.id, &poly(&[-141421356237309505, 100000000000000000])), -1);
    assert_eq!(registry.sign_at(sqrt2.id, &poly(&[-141421356237309504, 100000000000000000])), 1);
    assert_eq!(registry.sign_at(half.id, &poly(&[-3, 2])), 0);
    assert_eq!(registry.sign_at(half.id, &poly(&[-9, 0, 4, 1])), 1);
    assert_eq!(registry.get(sqrt2.id).min_poly(), &poly(&[-2, 0, 1]));
    assert_eq!(registry.get(half.id).degree(), 1);
}
