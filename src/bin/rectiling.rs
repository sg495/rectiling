// SPDX-License-Identifier: LGPL-3.0-or-later

//! Command-line interface to the search for tilings by similar rectangles.

use rectiling::Search;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut numbers: Vec<u32> = Vec::new();
    let mut list = false;
    for arg in &args {
        match arg.as_str() {
            "--list" => list = true,
            other => match other.parse() {
                Ok(v) => numbers.push(v),
                Err(_) => usage(),
            },
        }
    }
    let (tiles, width, height) = match numbers[..] {
        [n] => (n, 1, 1),
        [n, w, h] => (n, w, h),
        _ => usage(),
    };
    let start = Instant::now();
    let outcome = Search::new(tiles as usize, width, height).run();
    let elapsed = start.elapsed();
    if list {
        for found in &outcome.proportions {
            println!("{:.15}\t{}\t{}\t{}", found.proportion.approx(), found.proportion.degree(), found.tilings, found.proportion.min_poly());
        }
    }
    println!("tiles = {tiles}, main rectangle = {width}:{height}");
    println!("proportions = {}", outcome.proportions.len());
    println!("{:?}", outcome.stats);
    println!("elapsed = {:.3}s", elapsed.as_secs_f64());
}

fn usage() -> ! {
    eprintln!("usage: rectiling [--list] TILES [WIDTH HEIGHT]");
    std::process::exit(2)
}
