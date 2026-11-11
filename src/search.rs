// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exhaustive search for tilings of a rectangle by similar rectangles.

use crate::algebraic::{Algebraic, Registry};
use crate::cache::{PolyCache, WordMap};
use crate::exact;
use crate::fast::Engine;
use crate::staircase::{FITS, Placement, Staircase, Unit};
use rayon::prelude::*;
use std::sync::Mutex;

/// Counters describing the work performed by a search.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct Stats {
    /// Complete placement sequences with orientations examined.
    pub leaves: u64,
    /// Leaves whose proportion equation has a root not smaller than one.
    pub candidates: u64,
    /// Pairs of a leaf and a root satisfying all constraints.
    pub tilings: u64,
    /// Leaves decided by exact symbolic elimination.
    pub exact: u64,
    /// Singular linear systems met, at which uniqueness of the tiling fails.
    pub singular: u64,
    /// Leaves in which the aspect ratio of the main rectangle does not depend on the proportion.
    pub constant: u64,
    /// Leaves that required arbitrary-precision coefficients.
    pub overflows: u64,
}

impl Stats {
    fn merge(&mut self, o: &Stats) {
        self.leaves += o.leaves;
        self.candidates += o.candidates;
        self.tilings += o.tilings;
        self.exact += o.exact;
        self.singular += o.singular;
        self.constant += o.constant;
        self.overflows += o.overflows;
    }
}

/// Tile proportion found by a search.
#[derive(Clone, Debug)]
pub struct Found {
    /// The proportion, as the ratio of the long side to the short side.
    pub proportion: Algebraic,
    /// Number of placement sequences with orientations realising the proportion.
    pub tilings: u64,
    /// One placement sequence realising the proportion.
    pub witness: Vec<Placement>,
}

/// Result of a search.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// The proportions found, in increasing order.
    pub proportions: Vec<Found>,
    /// Counters describing the work performed.
    pub stats: Stats,
    /// Number of distinct proportion equations solved.
    pub polynomials: usize,
}

/// Results accumulated by one thread, before they are merged into the shared table.
#[derive(Default)]
pub(crate) struct Tally {
    pub(crate) found: WordMap<u32, (u64, Option<Box<[Placement]>>)>,
    pub(crate) stats: Stats,
}

/// Results shared by all threads of a search.
#[derive(Default)]
pub(crate) struct Shared {
    table: Mutex<Vec<(u64, Option<Box<[Placement]>>)>>,
    stats: Mutex<Stats>,
}

const FLUSH_LIMIT: usize = 1 << 18;

impl Tally {
    pub(crate) fn record(&mut self, id: u32, witness: impl FnOnce() -> Box<[Placement]>) {
        self.stats.tilings += 1;
        self.found.entry(id).and_modify(|e| e.0 += 1).or_insert_with(|| (1, Some(witness())));
    }

    /// Merges the results into the shared table if they have grown large, or unconditionally.
    pub(crate) fn flush(&mut self, shared: &Shared, force: bool) {
        if !force && self.found.len() < FLUSH_LIMIT {
            return;
        }
        {
            let mut table = shared.table.lock().expect("results lock");
            for (id, (count, witness)) in self.found.drain() {
                let id = id as usize;
                if table.len() <= id {
                    table.resize_with(id + 1, || (0, None));
                }
                table[id].0 += count;
                if table[id].1.is_none() {
                    table[id].1 = witness;
                }
            }
        }
        shared.stats.lock().expect("results lock").merge(&self.stats);
        self.stats = Stats::default();
    }
}

/// Parameters of a search.
#[derive(Clone, Copy, Debug)]
pub struct Search {
    tiles: usize,
    width: i64,
    height: i64,
}

impl Search {
    /// A search for tilings by the given number of tiles of a main rectangle with the given integer width and height.
    pub fn new(tiles: usize, width: u32, height: u32) -> Self {
        assert!((1..=14).contains(&tiles), "the number of tiles must be between 1 and 14");
        assert!(width >= 1 && height >= 1, "the sides of the main rectangle must be positive");
        Search {
            tiles,
            width: width as i64,
            height: height as i64,
        }
    }

    /// A search for tilings of a square by the given number of tiles.
    pub fn square(tiles: usize) -> Self {
        Self::new(tiles, 1, 1)
    }

    /// The number of tiles.
    pub fn tiles(&self) -> usize {
        self.tiles
    }

    /// Whether the main rectangle is a square.
    pub fn is_square(&self) -> bool {
        self.width == self.height
    }

    fn sequences(&self, depth: usize) -> Vec<Vec<Placement>> {
        fn rec(search: &Search, stairs: &Staircase<()>, remaining: usize, depth: usize, path: &mut Vec<Placement>, out: &mut Vec<Vec<Placement>>) {
            if stairs.tiers.is_empty() || path.len() == depth {
                out.push(path.clone());
                return;
            }
            for tier in 0..stairs.tiers.len() {
                for fit in FITS {
                    for tall in [false, true] {
                        let mv = Placement {
                            tier: tier as u8,
                            fit,
                            tall,
                        };
                        if stairs.admits(mv, remaining).is_none() || (tall && path.is_empty() && search.is_square()) {
                            continue;
                        }
                        let mut next = stairs.clone();
                        next.place(&mut Unit, mv);
                        path.push(mv);
                        rec(search, &next, remaining - 1, depth, path, out);
                        path.pop();
                    }
                }
            }
        }
        let mut out = Vec::new();
        rec(self, &Staircase::new((), ()), self.tiles, depth, &mut Vec::new(), &mut out);
        out
    }

    fn outcome(&self, shared: Shared, registry: &Registry, cache: &PolyCache) -> Outcome {
        let table = shared.table.into_inner().expect("results lock");
        let mut proportions: Vec<Found> = table
            .into_iter()
            .enumerate()
            .filter(|(_, (tilings, _))| *tilings > 0)
            .map(|(id, (tilings, witness))| Found {
                proportion: registry.get(id as u32),
                tilings,
                witness: witness.map(Vec::from).unwrap_or_default(),
            })
            .collect();
        proportions.sort_by(|a, b| a.proportion.approx().total_cmp(&b.proportion.approx()));
        Outcome {
            proportions,
            stats: shared.stats.into_inner().expect("results lock"),
            polynomials: cache.len(),
        }
    }

    /// Runs the search, enumerating every tiling.
    pub fn run(&self) -> Outcome {
        let registry = Registry::new();
        let cache = PolyCache::new();
        let shared = Shared::default();
        self.sequences(4).par_iter().for_each_init(
            || Engine::new(self.tiles, self.width, self.height, &registry, &cache, &shared),
            |engine, prefix| engine.run(prefix),
        );
        self.outcome(shared, &registry, &cache)
    }

    /// Runs the search with every tiling solved by exact symbolic elimination, as a reference for the default method.
    pub fn run_exact(&self) -> Outcome {
        let registry = Registry::new();
        let cache = PolyCache::new();
        let shared = Shared::default();
        self.sequences(self.tiles).par_chunks(1024).for_each(|paths| {
            let mut tally = Tally::default();
            for path in paths {
                let solved = exact::solve(self.width, self.height, &registry, &cache, path);
                tally.stats.leaves += 1;
                tally.stats.exact += 1;
                tally.stats.candidates += solved.candidate as u64;
                tally.stats.singular += solved.singular;
                tally.stats.constant += solved.constant as u64;
                tally.stats.overflows += solved.overflow as u64;
                for &id in &solved.feasible {
                    tally.record(id, || path.as_slice().into());
                }
            }
            tally.flush(&shared, true);
        });
        self.outcome(shared, &registry, &cache)
    }
}
