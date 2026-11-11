// SPDX-License-Identifier: LGPL-3.0-or-later

//! Tests of the counts of tilings as sets of rectangles, and of their classes under symmetry.

use rectiling::{Census, Outcome, Search};

fn certified(outcome: &Outcome) -> &Census {
    let stats = outcome.stats();
    assert_eq!((stats.singular, stats.constant, stats.overflows), (0, 0, 0));
    let census = outcome.census().expect("tilings were counted");
    assert_eq!((census.inconsistent(), census.asymmetric()), (0, 0));
    census
}

const TILINGS: [u64; 8] = [1, 2, 14, 89, 830, 7278, 70410, 703606];
const CLASSES: [u64; 8] = [1, 1, 3, 16, 121, 976, 9051, 88982];

#[test]
fn tilings_of_the_square() {
    for n in 1..=8 {
        let outcome = Search::square(n).counting_tilings().run();
        let census = certified(&outcome);
        assert_eq!(census.tilings(), TILINGS[n - 1], "n = {n}");
        assert_eq!(census.classes(), CLASSES[n - 1], "n = {n}");
    }
}

#[test]
fn classes_agree_with_the_count_by_fixed_points() {
    for n in 1..=8 {
        let outcome = Search::square(n).counting_tilings().run();
        let census = certified(&outcome);
        assert_eq!(census.classes_by_fixed_points(), Some(census.classes()), "n = {n}");
        assert_eq!(census.fixed()[0], census.tilings());
    }
}

#[test]
fn fixed_tilings_with_four_and_seven_tiles() {
    let four = Search::square(4).counting_tilings().run();
    assert_eq!(certified(&four).fixed(), [89, 1, 15, 1, 15, 1, 5, 1]);
    let seven = Search::square(7).counting_tilings().run();
    assert_eq!(certified(&seven).fixed(), [70410, 2, 928, 0, 928, 0, 138, 2]);
}

#[test]
fn tilings_by_squares_and_by_crossings() {
    let squared: Vec<u64> = (1..=8).map(|n| certified(&Search::square(n).counting_tilings().run()).squared()).collect();
    assert_eq!(squared, [1, 0, 0, 1, 0, 4, 8, 36]);
    let seven = Search::square(7).counting_tilings().run();
    assert_eq!(certified(&seven).by_crossings(), [69010, 1356, 44]);
}

#[test]
fn each_tiling_is_found_once_for_each_resolution_of_its_crossings() {
    for n in 1..=8 {
        let outcome = Search::square(n).counting_tilings().run();
        let census = certified(&outcome);
        assert!(census.multiplicities_hold(), "n = {n}");
        let [records, squares] = census.records();
        let found: u64 = records.iter().chain(squares.iter()).sum::<u64>() + census.reoriented();
        assert_eq!(found, outcome.stats().tilings, "n = {n}");
        let repeats: u64 = squares.iter().sum::<u64>() * ((1 << (n - 1)) - 1);
        assert_eq!(census.reoriented(), repeats, "n = {n}");
    }
}

#[test]
fn exact_comparison_agrees_with_the_default_method() {
    for (n, w, h) in [(1, 1, 1), (4, 1, 1), (5, 1, 1), (6, 1, 1), (7, 1, 1), (5, 2, 1), (6, 3, 2)] {
        let fast = Search::new(n, w, h).counting_tilings().run();
        let exact = Search::new(n, w, h).counting_tilings().run_exact();
        let (a, b) = (certified(&fast), certified(&exact));
        assert_eq!(a.tilings(), b.tilings(), "n = {n}, w = {w}/{h}");
        assert_eq!(a.classes(), b.classes(), "n = {n}, w = {w}/{h}");
        assert_eq!(a.fixed(), b.fixed(), "n = {n}, w = {w}/{h}");
        assert_eq!(a.by_crossings(), b.by_crossings(), "n = {n}, w = {w}/{h}");
        assert_eq!(b.exact(), b.records().iter().flatten().sum::<u64>());
    }
}

#[test]
fn transposed_rectangles_have_as_many_tilings() {
    for (w, h) in [(2, 1), (3, 2), (5, 3)] {
        for n in 1..=6 {
            let a = Search::new(n, w, h).counting_tilings().run();
            let b = Search::new(n, h, w).counting_tilings().run();
            let (ca, cb) = (certified(&a), certified(&b));
            assert_eq!(ca.tilings(), cb.tilings(), "n = {n}, w = {w}/{h}");
            assert_eq!(ca.classes(), cb.classes(), "n = {n}, w = {w}/{h}");
            assert_eq!(ca.classes_by_fixed_points(), Some(ca.classes()), "n = {n}, w = {w}/{h}");
            let mut fixed = cb.fixed();
            fixed.swap(2, 4);
            assert_eq!(ca.fixed(), fixed, "n = {n}, w = {w}/{h}");
        }
    }
}

#[test]
fn a_scaled_square_has_the_tilings_of_the_square() {
    let unit = Search::square(6).counting_tilings().run();
    let scaled = Search::new(6, 3, 3).counting_tilings().run();
    assert_eq!(certified(&unit).tilings(), certified(&scaled).tilings());
    assert_eq!(certified(&unit).classes(), certified(&scaled).classes());
}

#[test]
fn classes_with_four_tiles() {
    let outcome = Search::square(4).listing_tilings().run();
    let classes = outcome.classes();
    assert_eq!(classes.len(), 16);
    assert_eq!(classes.iter().map(|t| t.orbit()).sum::<usize>(), 89);
    let orbits: Vec<usize> = classes.iter().map(|t| t.orbit()).collect();
    assert_eq!(orbits, [1, 4, 8, 4, 8, 4, 8, 8, 8, 8, 4, 2, 8, 8, 4, 2]);
    for tiling in &classes {
        let area: f64 = tiling.tiles().iter().map(|t| t[2] * t[3]).sum();
        assert!((area - 1.0).abs() < 1e-12);
        let x = tiling.proportion().approx();
        assert!(tiling.tiles().iter().all(|t| (t[2].max(t[3]) / t[2].min(t[3]) - x).abs() < 1e-9));
    }
    assert_eq!(classes[0].crossings(), 1);
    assert_eq!(classes[0].stabiliser().len(), 8);
}

#[test]
fn proportions_carry_their_numbers_of_tilings() {
    let outcome = Search::square(4).counting_tilings().run();
    let distinct: Vec<u64> = outcome.proportions().iter().map(|f| f.distinct).collect();
    assert_eq!(distinct, [1, 4, 12, 12, 8, 16, 8, 6, 8, 12, 2]);
    let classes: Vec<u64> = outcome.proportions().iter().map(|f| f.classes).collect();
    assert_eq!(classes, [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]);
}

#[test]
fn bags_of_the_square() {
    for (n, expected) in [1, 1, 3, 11, 51, 250, 1419, 8877].into_iter().enumerate() {
        let outcome = Search::square(n + 1).counting_bags().run();
        let census = certified(&outcome);
        assert_eq!(census.bags(), Some(expected), "n = {}", n + 1);
        assert_eq!(census.unresolved(), 0);
        let found = outcome.proportions();
        assert_eq!(found.iter().map(|f| f.bags).sum::<u64>(), expected);
        assert!(found.iter().all(|f| 1 <= f.bags && f.bags <= f.classes && f.classes <= f.distinct));
    }
}

#[test]
fn bags_agree_between_methods_and_between_transposed_rectangles() {
    for (n, w, h) in [(6, 1, 1), (7, 1, 1), (6, 2, 1), (6, 5, 3)] {
        let fast = Search::new(n, w, h).counting_bags().run();
        let exact = Search::new(n, w, h).counting_bags().run_exact();
        let transposed = Search::new(n, h, w).counting_bags().run();
        assert_eq!(certified(&fast).bags(), certified(&exact).bags(), "n = {n}, w = {w}/{h}");
        assert_eq!(certified(&fast).bags(), certified(&transposed).bags(), "n = {n}, w = {w}/{h}");
    }
}

#[test]
fn proportions_with_several_bags_for_six_tiles() {
    let outcome = Search::square(6).counting_bags().run();
    let several: Vec<(String, u64)> = outcome.proportions().iter().filter(|f| f.bags > 1).map(|f| (f.proportion.min_poly().to_string(), f.bags)).collect();
    let expected = [("2*x^3 - 3*x^2 + 2*x - 2", 2), ("2*x - 3", 2), ("x^3 - 2*x^2 + x - 1", 3), ("x - 2", 2)];
    assert_eq!(several, expected.map(|(p, b)| (p.to_string(), b)));
}

#[test]
#[ignore = "takes a quarter of a minute in release mode"]
fn tilings_with_nine_and_ten_tiles() {
    for (n, tilings, classes) in [(9, 7280599, 914261), (10, 77188146, 9666313)] {
        let outcome = Search::square(n).counting_tilings().run();
        let census = certified(&outcome);
        assert_eq!(census.tilings(), tilings);
        assert_eq!(census.classes(), classes);
        assert_eq!(census.classes_by_fixed_points(), Some(classes));
        assert!(census.multiplicities_hold());
    }
}
