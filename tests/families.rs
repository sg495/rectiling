// SPDX-License-Identifier: LGPL-3.0-or-later

//! Tests of the restricted families of tilings: guillotine tilings, and tilings with few tiles in one orientation.

use rectiling::{Outcome, Search, count_guillotine_ratios};

fn names(outcome: &Outcome) -> Vec<String> {
    outcome.proportions().iter().map(|f| format!("{} #{}", f.proportion.min_poly(), f.proportion.index())).collect()
}

#[test]
fn guillotine_ratio_counts() {
    let counts: Vec<usize> = (1..=8).map(count_guillotine_ratios).collect();
    assert_eq!(counts, [2, 6, 20, 76, 322, 1436, 6770, 33096]);
}

#[test]
fn guillotine_tilings_suffice_up_to_five_tiles() {
    for n in 1..=5 {
        assert_eq!(names(&Search::square(n).run_guillotine()), names(&Search::square(n).run()), "n = {n}");
    }
}

#[test]
fn guillotine_counts_for_the_square() {
    let counts: Vec<usize> = (6..=9).map(|n| Search::square(n).run_guillotine().count()).collect();
    assert_eq!(counts, [221, 1069, 5275, 26765]);
}

#[test]
fn guillotine_proportions_are_found_by_the_search() {
    for (n, w, h) in [(6, 1, 1), (7, 1, 1), (5, 2, 1), (6, 3, 2), (5, 1, 4)] {
        let all = names(&Search::new(n, w, h).run());
        let guillotine = names(&Search::new(n, w, h).run_guillotine());
        assert!(guillotine.len() < all.len(), "n = {n}, w = {w}/{h}");
        assert!(guillotine.iter().all(|g| all.contains(g)), "n = {n}, w = {w}/{h}");
    }
}

#[test]
fn guillotine_ratios_with_a_pole_at_infinity() {
    let counts: Vec<usize> = (1..=7).map(|n| Search::new(n, 1_000_003, 1).run_guillotine().count()).collect();
    assert_eq!(counts, [1, 3, 10, 38, 161, 718, 3385]);
}

#[test]
fn wide_rectangles_count_aspect_ratio_functions() {
    let counts: Vec<usize> = (1..=7).map(|n| Search::new(n, 1_000_003, 1).run().count()).collect();
    assert_eq!(counts, [1, 3, 10, 38, 164, 787, 4258]);
}

#[test]
fn counts_dip_where_two_aspect_ratio_functions_share_a_root() {
    let count = |n: usize, w: u32| Search::new(n, w, 1).run().count();
    assert_eq!([count(5, 7), count(5, 8)], [162, 164]);
    assert_eq!([count(6, 10), count(6, 11)], [786, 787]);
    assert_eq!([count(7, 13), count(7, 14)], [4256, 4258]);
}

#[test]
fn single_orientation_counts_dissections_into_squares() {
    let counts: Vec<usize> = (1..=8).map(|n| Search::square(n).with_minority(0).run().count()).collect();
    assert_eq!(counts, [1, 1, 2, 5, 11, 28, 74, 211]);
    for n in 2..=8 {
        let outcome = Search::square(n).with_minority(0).run();
        assert!(outcome.proportions().iter().all(|f| f.proportion.degree() == 1));
    }
}

#[test]
fn minority_bounds_the_degree() {
    for n in 3..=8 {
        for k in 0..=n / 2 {
            let outcome = Search::square(n).with_minority(k).run();
            assert!(outcome.proportions().iter().all(|f| f.proportion.degree() <= 2 * k + 1), "n = {n}, k = {k}");
        }
    }
}

#[test]
fn full_minority_is_no_restriction() {
    for (n, w, h) in [(6, 1, 1), (7, 1, 1), (6, 3, 2)] {
        let all = Search::new(n, w, h).run();
        let half = Search::new(n, w, h).with_minority(n / 2).run();
        assert_eq!(names(&all), names(&half));
        assert_eq!(all.stats().tilings, half.stats().tilings);
    }
}

#[test]
fn minority_restriction_agrees_with_exact_elimination() {
    for (n, k, w, h) in [(6, 1, 1, 1), (6, 2, 1, 1), (7, 1, 1, 1), (6, 1, 3, 2), (5, 0, 2, 1)] {
        let fast = Search::new(n, w, h).with_minority(k).run();
        let exact = Search::new(n, w, h).with_minority(k).run_exact();
        assert_eq!(names(&fast), names(&exact), "n = {n}, k = {k}, w = {w}/{h}");
        assert_eq!(fast.stats().leaves, exact.stats().leaves);
        assert_eq!(fast.stats().tilings, exact.stats().tilings);
    }
}

#[test]
fn minority_sets_are_nested() {
    let mut previous: Vec<String> = Vec::new();
    for k in 0..=3 {
        let current = names(&Search::square(7).with_minority(k).run());
        assert!(previous.iter().all(|p| current.contains(p)));
        assert!(current.len() > previous.len());
        previous = current;
    }
}

#[test]
fn proportions_persist_with_three_or_more_extra_tiles() {
    let sets: Vec<Vec<String>> = (1..=9).map(|n| names(&Search::square(n).run())).collect();
    for n in 2..=6 {
        for m in n + 3..=9 {
            assert!(sets[n - 1].iter().all(|p| sets[m - 1].contains(p)), "n = {n}, m = {m}");
        }
    }
    assert!(!sets[4].contains(&sets[0][0]));
}

#[test]
fn rational_proportions_needing_both_orientations_with_ten_tiles() {
    let rational = |k: usize| -> Vec<String> {
        let outcome = Search::square(10).with_minority(k).run();
        outcome.proportions().iter().filter(|f| f.proportion.degree() == 1).map(|f| f.proportion.min_poly().to_string()).collect()
    };
    let single = rational(0);
    let mixed = rational(2);
    let extra: Vec<&String> = mixed.iter().filter(|p| !single.contains(p)).collect();
    assert_eq!(single.len(), 1901);
    assert_eq!(extra, ["3*x - 11", "2*x - 9", "x - 6"]);
}
