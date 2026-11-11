// SPDX-License-Identifier: LGPL-3.0-or-later

//! Proportions of guillotine tilings, by series and parallel composition of aspect ratios.

use crate::algebraic::Registry;
use crate::cache::{PolyCache, WordMap};
use crate::int::{Int, take_overflow};
use crate::poly::Poly;
use crate::search::Stats;
use hashbrown::HashSet;
use rayon::prelude::*;

/// Aspect ratio of a block as a function of the tile proportion, as a reduced numerator and denominator.
type Ratio = (Poly<i64>, Poly<i64>);

fn reduced(num: Poly<i64>, den: Poly<i64>) -> Ratio {
    let g = num.gcd(&den);
    let (num, den) = if g.degree() == Some(0) { (num, den) } else { (num.div_exact(&g), den.div_exact(&g)) };
    let mut c = num.content().gcd(&den.content());
    if den.leading().is_some_and(|l| l.signum() < 0) {
        c = -c;
    }
    if c == 1 {
        return (num, den);
    }
    let scale = |p: &Poly<i64>| Poly::from_coeffs(p.coeffs().iter().map(|v| v.div_exact(&c)));
    (scale(&num), scale(&den))
}

fn sum(a: &Ratio, b: &Ratio) -> Ratio {
    take_overflow();
    let r = reduced(a.0.mul(&b.1).add(&b.0.mul(&a.1)), a.1.mul(&b.1));
    assert!(!take_overflow(), "coefficients exceed the range of machine integers");
    r
}

fn inverse(a: &Ratio) -> Ratio {
    (a.1.clone(), a.0.clone())
}

/// The aspect ratios of the blocks cut into each number of tiles up to the given one by guillotine cuts.
fn ratios(tiles: usize) -> Vec<Vec<Ratio>> {
    let mut levels: Vec<Vec<Ratio>> = vec![Vec::new(), vec![(Poly::monomial(1), Poly::one()), (Poly::one(), Poly::monomial(1))]];
    for k in 2..=tiles {
        let sums: HashSet<Ratio> = (1..=k / 2)
            .into_par_iter()
            .flat_map(|i| {
                let other = &levels[k - i];
                levels[i].par_iter().flat_map_iter(move |a| other.iter().map(move |b| sum(a, b)))
            })
            .fold(HashSet::new, |mut set, r| {
                set.insert(r);
                set
            })
            .reduce(HashSet::new, |a, b| {
                let (mut large, small) = if a.len() < b.len() { (b, a) } else { (a, b) };
                large.extend(small);
                large
            });
        let mut all: HashSet<Ratio> = sums.iter().map(inverse).collect();
        all.extend(sums);
        levels.push(all.into_iter().collect());
    }
    levels
}

/// The number of distinct aspect ratios, as functions of the tile proportion, of the rectangles cut into the given number of tiles by guillotine cuts.
pub fn count_guillotine_ratios(tiles: usize) -> usize {
    assert!((1..=14).contains(&tiles), "the number of tiles must be between 1 and 14");
    ratios(tiles)[tiles].len()
}

/// The proportions of the guillotine tilings of a main rectangle, with the number of aspect ratio functions realising each.
pub(crate) fn solve(tiles: usize, width: i64, height: i64, registry: &Registry, cache: &PolyCache) -> (Vec<u64>, Stats) {
    let levels = ratios(tiles);
    let (w, h) = (Poly::constant(width), Poly::constant(height));
    let found: Vec<(u64, WordMap<u32, u64>)> = levels[tiles]
        .par_iter()
        .fold(
            || (0u64, WordMap::default(), Vec::new()),
            |(mut candidates, mut found, mut scratch), (num, den)| {
                take_overflow();
                let equation = num.mul(&h).sub(&den.mul(&w)).primitive();
                assert!(!take_overflow(), "coefficients exceed the range of machine integers");
                assert!(!equation.is_zero(), "aspect ratio independent of the proportion");
                let roots = cache.roots(equation.coeffs(), &mut scratch, registry);
                candidates += !roots.is_empty() as u64;
                for root in roots {
                    *found.entry(root.id).or_insert(0) += 1;
                }
                (candidates, found, scratch)
            },
        )
        .map(|(candidates, found, _)| (candidates, found))
        .collect();
    let mut counts = vec![0; registry.len()];
    let mut stats = Stats {
        leaves: levels[tiles].len() as u64,
        ..Stats::default()
    };
    for (candidates, map) in found {
        stats.candidates += candidates;
        for (id, count) in map {
            counts[id as usize] += count;
            stats.tilings += count;
        }
    }
    (counts, stats)
}
