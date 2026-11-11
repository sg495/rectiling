// SPDX-License-Identifier: LGPL-3.0-or-later

//! Command-line interface to the search for tilings by similar rectangles.

use rectiling::Search;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut numbers: Vec<u32> = Vec::new();
    let mut list = false;
    let mut guillotine = false;
    let mut minority: Option<usize> = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--list" => list = true,
            "--guillotine" => guillotine = true,
            "--minority" => match args.next().and_then(|v| v.parse().ok()) {
                Some(v) => minority = Some(v),
                None => usage(),
            },
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
    let mut search = Search::new(tiles as usize, width, height);
    if let Some(limit) = minority {
        search = search.with_minority(limit);
    }
    let outcome = if guillotine { search.run_guillotine() } else { search.run() };
    let elapsed = start.elapsed();
    if list {
        for found in outcome.proportions() {
            println!("{:.15}\t{}\t{}\t{}", found.proportion.approx(), found.proportion.degree(), found.tilings, found.proportion.min_poly());
        }
    }
    println!("tiles = {tiles}, main rectangle = {width}:{height}");
    if guillotine {
        println!("guillotine tilings only; leaves are aspect ratio functions");
    }
    if let Some(limit) = minority {
        println!("at most {limit} tiles in the less frequent orientation");
    }
    println!("degrees = {:?}", outcome.degrees());
    println!("proportions = {}", outcome.count());
    println!("{:?}, polynomials = {}", outcome.stats(), outcome.polynomials());
    println!("elapsed = {:.3}s", elapsed.as_secs_f64());
}

fn usage() -> ! {
    eprintln!("usage: rectiling [--list] [--guillotine] [--minority LIMIT] TILES [WIDTH HEIGHT]");
    std::process::exit(2)
}
