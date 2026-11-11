// SPDX-License-Identifier: LGPL-3.0-or-later

//! Tests of the search against published results.

use rectiling::{Band, Outcome, Search, count_layouts};

fn certified(outcome: &Outcome) {
    assert_eq!(outcome.stats().singular, 0);
    assert_eq!(outcome.stats().constant, 0);
}

fn degrees(outcome: &Outcome, max: usize) -> Vec<usize> {
    let mut histogram = vec![0; max];
    for found in &outcome.proportions() {
        histogram[found.proportion.degree() - 1] += 1;
    }
    histogram
}

#[test]
fn layout_counts() {
    let counts: Vec<u64> = (1..=8).map(count_layouts).collect();
    assert_eq!(counts, [1, 2, 6, 22, 92, 422, 2074, 10754]);
}

#[test]
fn square_counts_up_to_six() {
    for (n, expected) in [1, 1, 3, 11, 51, 245].into_iter().enumerate() {
        let outcome = Search::square(n + 1).run();
        certified(&outcome);
        assert_eq!(outcome.count(), expected, "n = {}", n + 1);
    }
}

#[test]
fn square_with_four_tiles() {
    let outcome = Search::square(4).run();
    let found: Vec<String> = outcome.proportions().iter().map(|f| f.proportion.min_poly().to_string()).collect();
    let expected = [
        "x - 1",
        "3*x - 4",
        "2*x^3 - 3*x^2 + x - 1",
        "x^3 - 2*x^2 + 2*x - 2",
        "3*x - 5",
        "x^3 - 2*x^2 + 2*x - 3",
        "2*x^3 - 4*x^2 + x - 1",
        "2*x - 5",
        "x^3 - 3*x^2 + 2*x - 2",
        "x^3 - 3*x^2 + x - 2",
        "x - 4",
    ];
    assert_eq!(found, expected);
    let all = outcome.proportions();
    let cubic = all.iter().find(|f| f.proportion.min_poly().to_string() == "x^3 - 2*x^2 + 2*x - 2").expect("cubic");
    assert!(cubic.tilings > 1);
    assert!((cubic.proportion.approx() - 1.543689012692076).abs() < 1e-12);
}

#[test]
fn square_degree_distributions() {
    assert_eq!(degrees(&Search::square(3).run(), 3), [2, 0, 1]);
    assert_eq!(degrees(&Search::square(4).run(), 4), [5, 0, 6, 0]);
    assert_eq!(degrees(&Search::square(5).run(), 5), [11, 2, 32, 2, 4]);
}

#[test]
fn square_with_seven_tiles() {
    let outcome = Search::square(7).run();
    certified(&outcome);
    assert_eq!(outcome.count(), 1372);
    assert_eq!(degrees(&outcome, 7), [76, 16, 560, 92, 546, 38, 44]);
    let missed = "x^7 - 2*x^6 + 7*x^5 - 12*x^4 + 10*x^3 - 9*x^2 + 3*x - 1";
    assert!(outcome.proportions().iter().any(|f| f.proportion.min_poly().to_string() == missed));
}

#[test]
fn square_with_eight_tiles() {
    let outcome = Search::square(8).run();
    certified(&outcome);
    assert_eq!(outcome.count(), 8522);
    assert_eq!(outcome.stats().leaves, 128 * 10754);
}

#[test]
#[ignore = "takes a minute in release mode"]
fn square_with_nine_and_ten_tiles() {
    for (n, expected) in [(9, 58347), (10, 433926)] {
        let outcome = Search::square(n).run();
        certified(&outcome);
        assert_eq!(outcome.count(), expected);
    }
}

fn summary(outcome: &Outcome) -> Vec<(String, usize, u64)> {
    outcome.proportions().iter().map(|f| (f.proportion.min_poly().to_string(), f.proportion.index(), f.tilings)).collect()
}

#[test]
fn default_method_agrees_with_exact_elimination() {
    for (w, h) in [(1, 1), (2, 1), (3, 2), (7, 4)] {
        for n in 1..=6 {
            let fast = Search::new(n, w, h).run();
            let exact = Search::new(n, w, h).run_exact();
            certified(&exact);
            assert_eq!(summary(&fast), summary(&exact), "n = {n}, w = {w}/{h}");
            assert_eq!(fast.stats().leaves, exact.stats().leaves);
        }
    }
}

#[test]
#[ignore = "takes a few minutes in release mode"]
fn default_method_agrees_with_exact_elimination_for_more_tiles() {
    for (n, w, h) in [(7, 1, 1), (8, 1, 1), (9, 1, 1), (7, 5, 3), (8, 2, 1)] {
        let fast = Search::new(n, w, h).run();
        let exact = Search::new(n, w, h).run_exact();
        certified(&exact);
        assert_eq!(summary(&fast), summary(&exact), "n = {n}, w = {w}/{h}");
    }
}

#[test]
fn witnesses_are_complete_sequences() {
    let outcome = Search::square(6).run();
    for found in &outcome.proportions() {
        assert_eq!(found.witness.len(), 6);
        assert!(found.tilings >= 1);
    }
}

#[test]
fn transposed_rectangles_agree() {
    for (w, h) in [(2, 1), (3, 2), (5, 3)] {
        for n in 1..=5 {
            let a = Search::new(n, w, h).run();
            let b = Search::new(n, h, w).run();
            certified(&a);
            certified(&b);
            let pa: Vec<String> = a.proportions().iter().map(|f| format!("{} #{}", f.proportion.min_poly(), f.proportion.index())).collect();
            let pb: Vec<String> = b.proportions().iter().map(|f| format!("{} #{}", f.proportion.min_poly(), f.proportion.index())).collect();
            assert_eq!(pa, pb, "n = {n}, w = {w}/{h}");
            assert_eq!(a.stats().tilings, b.stats().tilings);
        }
    }
}

#[test]
fn rectangle_two_by_one() {
    let counts: Vec<usize> = (1..=4).map(|n| Search::new(n, 2, 1).run().count()).collect();
    assert_eq!(counts[0], 1);
    let two = Search::new(2, 2, 1).run();
    let found: Vec<String> = two.proportions().iter().map(|f| f.proportion.min_poly().to_string()).collect();
    assert_eq!(found, ["x - 1", "x - 4"]);
}

#[test]
fn square_search_ignores_transposed_duplicates() {
    let square = Search::square(5).run();
    let scaled = Search::new(5, 3, 3).run();
    assert_eq!(square.count(), scaled.count());
}

#[test]
fn rational_proportions_needing_both_orientations() {
    let mut mixed = Vec::new();
    let mut aligned = 0;
    for found in Search::square(6).run().proportions() {
        if found.proportion.degree() != 1 {
            continue;
        }
        let poly = found.proportion.min_poly().to_string();
        let (q, p) = poly.split_once("x - ").expect("linear polynomial");
        let q: u32 = q.trim_end_matches('*').parse().unwrap_or(1);
        let p: u32 = p.parse().expect("numerator");
        let squares = Search::new(6, p, q).run().proportions().iter().any(|f| f.proportion.min_poly().to_string() == "x - 1");
        if squares {
            aligned += 1;
        } else {
            mixed.push((p, q));
        }
    }
    assert_eq!(aligned, 28);
    assert_eq!(mixed, [(5, 3), (2, 1)]);
}

fn banded(search: Search, count: usize, run: impl Fn(&Search) -> Outcome) -> Vec<(String, usize, u64)> {
    let mut all = Vec::new();
    for index in 0..count {
        let band = Band::new(index, count);
        let outcome = run(&search.in_band(band));
        certified(&outcome);
        for found in outcome.proportions() {
            let x = found.proportion.approx();
            assert!(band.lower() <= x && x < band.upper());
        }
        all.extend(summary(&outcome));
    }
    all
}

#[test]
fn bands_partition_the_proportions() {
    let search = Search::square(7);
    let whole = summary(&search.run());
    for count in [2, 8, 64] {
        assert_eq!(banded(search, count, Search::run), whole);
    }
    assert_eq!(banded(Search::square(6), 4, Search::run_exact), summary(&Search::square(6).run()));
    let wide = Search::new(6, 3, 2);
    assert_eq!(banded(wide, 16, Search::run), summary(&wide.run()));
}

#[test]
fn bands_partition_the_tilings() {
    let search = Search::square(7).counting_bags();
    let whole = search.run();
    let census = whole.census().expect("census");
    let (mut tilings, mut classes, mut bags) = (0, 0, 0);
    for index in 0..4 {
        let outcome = search.in_band(Band::new(index, 4)).run();
        let part = outcome.census().expect("census");
        tilings += part.tilings();
        classes += part.classes();
        bags += part.bags().expect("bags");
    }
    assert_eq!((tilings, classes, Some(bags)), (census.tilings(), census.classes(), census.bags()));
}
