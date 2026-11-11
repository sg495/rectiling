// SPDX-License-Identifier: LGPL-3.0-or-later

//! Inclusions between the sets of proportions of the square for different numbers of tiles.

use rectiling::Search;
use std::collections::HashMap;

fn main() {
    let largest: usize = std::env::args().nth(1).and_then(|v| v.parse().ok()).unwrap_or(9);
    let mut least: HashMap<(String, usize), usize> = HashMap::new();
    let mut sets: Vec<Vec<(String, usize)>> = Vec::new();
    for tiles in 1..=largest {
        let found = Search::square(tiles).run().proportions();
        let keys: Vec<(String, usize)> = found.iter().map(|f| (f.proportion.min_poly().to_string(), f.proportion.index())).collect();
        for key in &keys {
            least.entry(key.clone()).or_insert(tiles);
        }
        sets.push(keys);
    }
    println!("proportions for n tiles, by the least number of tiles with which they occur:");
    for (i, set) in sets.iter().enumerate() {
        let mut row = vec![0usize; i + 1];
        for key in set {
            row[least[key] - 1] += 1;
        }
        println!("{:>2} {:>9} {:?}", i + 1, set.len(), row);
    }
    println!("proportions for n tiles that occur also for m < n tiles:");
    for (i, set) in sets.iter().enumerate() {
        let row: Vec<usize> = sets[..i]
            .iter()
            .map(|earlier| {
                let earlier: std::collections::HashSet<&(String, usize)> = earlier.iter().collect();
                set.iter().filter(|key| earlier.contains(key)).count()
            })
            .collect();
        println!("{:>2} {:?}", i + 1, row);
    }
}
