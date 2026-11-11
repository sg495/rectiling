// SPDX-License-Identifier: LGPL-3.0-or-later

//! Command-line interface to the search for tilings by similar rectangles.

use rectiling::{Census, Fit, Outcome, SYMMETRIES, Search};
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut numbers: Vec<u32> = Vec::new();
    let mut list = false;
    let mut guillotine = false;
    let mut tilings = false;
    let mut classes = false;
    let mut bags = false;
    let mut exact = false;
    let mut minority: Option<usize> = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--list" => list = true,
            "--guillotine" => guillotine = true,
            "--tilings" => tilings = true,
            "--classes" => classes = true,
            "--bags" => bags = true,
            "--exact" => exact = true,
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
    if bags {
        search = search.counting_bags();
    }
    if classes {
        search = search.listing_tilings();
    } else if tilings {
        search = search.counting_tilings();
    }
    let outcome = if guillotine {
        search.run_guillotine()
    } else if exact {
        search.run_exact()
    } else {
        search.run()
    };
    let elapsed = start.elapsed();
    if list {
        for found in outcome.proportions() {
            if outcome.census().is_some() {
                println!(
                    "{:.15}\t{}\t{}\t{}\t{}\t{}\t{}",
                    found.proportion.approx(),
                    found.proportion.degree(),
                    found.tilings,
                    found.distinct,
                    found.classes,
                    found.bags,
                    found.proportion.min_poly()
                );
            } else {
                println!("{:.15}\t{}\t{}\t{}", found.proportion.approx(), found.proportion.degree(), found.tilings, found.proportion.min_poly());
            }
        }
    }
    if classes {
        print_classes(&outcome);
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
    if let Some(census) = outcome.census() {
        print_census(census);
    }
    println!("elapsed = {:.3}s", elapsed.as_secs_f64());
}

fn print_classes(outcome: &Outcome) {
    for (k, tiling) in outcome.classes().iter().enumerate() {
        let proportion = tiling.proportion();
        let stabiliser: Vec<&str> = tiling.stabiliser().into_iter().map(|g| SYMMETRIES[g]).collect();
        println!("class {}: proportion {:.12}, root of {}", k + 1, proportion.approx(), proportion.min_poly());
        println!("  tilings in the class = {}, fixed by: {}", tiling.orbit(), stabiliser.join("; "));
        println!("  points where four tiles meet = {}", tiling.crossings());
        for (tile, mv) in tiling.tiles().iter().zip(tiling.placements()) {
            let kind = if proportion.approx() == 1.0 {
                "square"
            } else if mv.tall {
                "tall"
            } else {
                "wide"
            };
            let fit = match mv.fit {
                Fit::Inside => "inside",
                Fit::FullHeight => "full height",
                Fit::FullWidth => "full width",
                Fit::Full => "full",
            };
            let tile = tile.map(|v| if v.abs() < 5e-7 { 0.0 } else { v });
            println!("  x = {:.6}, y = {:.6}, width = {:.6}, height = {:.6}, {kind} (tier {}, {fit})", tile[0], tile[1], tile[2], tile[3], mv.tier);
        }
    }
}

fn print_census(census: &Census) {
    println!("tilings = {}", census.tilings());
    println!("classes under symmetry = {}", census.classes());
    match census.classes_by_fixed_points() {
        Some(count) => println!("classes by fixed points = {count}"),
        None => println!("classes by fixed points = not integral"),
    }
    let fixed = census.fixed();
    for (name, count) in SYMMETRIES.iter().zip(fixed).take(census.order() as usize * 2).filter(|(_, c)| *c > 0) {
        println!("  fixed by {name} = {count}");
    }
    println!("tilings with a symmetry = {}", census.symmetric());
    for (members, count) in census.stabilisers() {
        let names: Vec<&str> = members.into_iter().map(|g| SYMMETRIES[g]).collect();
        println!("  fixed exactly by {{{}}} = {count}", names.join("; "));
    }
    println!("tilings by squares = {}, classes = {}", census.squared(), census.squared_classes());
    println!("tilings by number of points where four tiles meet = {:?}", census.by_crossings());
    let [records, squares] = census.records();
    let [examined, examined_squares] = census.examined();
    println!("sequences by such points = {:?}, of squares {:?}", trimmed(&records), trimmed(&squares));
    println!("tilings examined by such points = {:?}, of squares {:?}", trimmed(&examined), trimmed(&examined_squares));
    println!("sequences repeating tilings by squares = {}", census.reoriented());
    println!("multiplicities hold = {}", census.multiplicities_hold());
    println!("compared exactly = {}, inconsistent = {}, asymmetric = {}", census.exact(), census.inconsistent(), census.asymmetric());
    if let Some(bags) = census.bags() {
        println!("bags = {bags}");
        println!("collisions = {}, unresolved = {}", census.collisions(), census.unresolved());
    }
}

fn trimmed(counts: &[u64]) -> &[u64] {
    let len = counts.iter().rposition(|&c| c > 0).map_or(1, |k| k + 1);
    &counts[..len]
}

fn usage() -> ! {
    eprintln!("usage: rectiling [--list] [--tilings] [--classes] [--bags] [--exact] [--guillotine] [--minority LIMIT] TILES [WIDTH HEIGHT]");
    std::process::exit(2)
}
