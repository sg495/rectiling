// SPDX-License-Identifier: LGPL-3.0-or-later

//! Timings of the search for tilings of a square.

use rectiling::Search;
use std::time::Instant;

fn main() {
    let largest: usize = std::env::var("RECTILING_BENCH_TILES").ok().and_then(|v| v.parse().ok()).unwrap_or(9);
    println!("{:>5} {:>12} {:>14} {:>12} {:>10} {:>12}", "tiles", "proportions", "cases", "polynomials", "seconds", "ns per case");
    for tiles in 5..=largest {
        let start = Instant::now();
        let outcome = Search::square(tiles).run();
        let seconds = start.elapsed().as_secs_f64();
        let threads = rayon_threads() as f64;
        println!(
            "{:>5} {:>12} {:>14} {:>12} {:>10.3} {:>12.1}",
            tiles,
            outcome.proportions.len(),
            outcome.stats.leaves,
            outcome.polynomials,
            seconds,
            seconds * threads * 1e9 / outcome.stats.leaves as f64
        );
    }
}

fn rayon_threads() -> usize {
    std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
}
