// SPDX-License-Identifier: LGPL-3.0-or-later

//! Tests of the search against published results.

use rectiling::{Outcome, Search, count_layouts};

fn certified(outcome: &Outcome) {
    assert_eq!(outcome.stats.singular, 0);
    assert_eq!(outcome.stats.constant, 0);
}

fn degrees(outcome: &Outcome, max: usize) -> Vec<usize> {
    let mut histogram = vec![0; max];
    for found in &outcome.proportions {
        histogram[found.proportion.degree() - 1] += 1;
    }
    histogram
}

#[test]
fn layout_counts() {
    let counts: Vec<u64> = (1..=8).map(count_layouts).collect();
    assert_eq!(counts, [1, 2, 6, 23, 104, 530, 2958, 17734]);
}

#[test]
fn square_counts_up_to_six() {
    for (n, expected) in [1, 1, 3, 11, 51, 245].into_iter().enumerate() {
        let outcome = Search::square(n + 1).run();
        certified(&outcome);
        assert_eq!(outcome.proportions.len(), expected, "n = {}", n + 1);
    }
}

#[test]
fn square_with_four_tiles() {
    let outcome = Search::square(4).run();
    let found: Vec<String> = outcome.proportions.iter().map(|f| f.proportion.min_poly().to_string()).collect();
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
    let cubic = outcome.proportions.iter().find(|f| f.proportion.min_poly().to_string() == "x^3 - 2*x^2 + 2*x - 2").expect("cubic");
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
    assert_eq!(outcome.proportions.len(), 1372);
    assert_eq!(degrees(&outcome, 7), [76, 16, 560, 92, 546, 38, 44]);
    let missed = "x^7 - 2*x^6 + 7*x^5 - 12*x^4 + 10*x^3 - 9*x^2 + 3*x - 1";
    assert!(outcome.proportions.iter().any(|f| f.proportion.min_poly().to_string() == missed));
}

#[test]
#[ignore = "takes several seconds in release mode"]
fn square_with_eight_tiles() {
    let outcome = Search::square(8).run();
    certified(&outcome);
    assert_eq!(outcome.proportions.len(), 8522);
}

#[test]
fn transposed_rectangles_agree() {
    for (w, h) in [(2, 1), (3, 2), (5, 3)] {
        for n in 1..=5 {
            let a = Search::new(n, w, h).run();
            let b = Search::new(n, h, w).run();
            certified(&a);
            certified(&b);
            let pa: Vec<String> = a.proportions.iter().map(|f| format!("{} #{}", f.proportion.min_poly(), f.proportion.index())).collect();
            let pb: Vec<String> = b.proportions.iter().map(|f| format!("{} #{}", f.proportion.min_poly(), f.proportion.index())).collect();
            assert_eq!(pa, pb, "n = {n}, w = {w}/{h}");
            assert_eq!(a.stats.tilings, b.stats.tilings);
        }
    }
}

#[test]
fn rectangle_two_by_one() {
    let counts: Vec<usize> = (1..=4).map(|n| Search::new(n, 2, 1).run().proportions.len()).collect();
    assert_eq!(counts[0], 1);
    let two = Search::new(2, 2, 1).run();
    let found: Vec<String> = two.proportions.iter().map(|f| f.proportion.min_poly().to_string()).collect();
    assert_eq!(found, ["x - 1", "x - 4"]);
}

#[test]
fn square_search_ignores_transposed_duplicates() {
    let square = Search::square(5).run();
    let scaled = Search::new(5, 3, 3).run();
    assert_eq!(square.proportions.len(), scaled.proportions.len());
}
