// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exhaustive search for tilings of a rectangle by similar rectangles.

use crate::algebraic::{Algebraic, Registry};
use crate::bags::Bags;
use crate::band::Band;
use crate::cache::{PolyCache, WordMap};
use crate::chunked::Chunked;
use crate::exact;
use crate::fast::Engine;
use crate::guillotine;
use crate::staircase::{FITS, Placement, Staircase, Unit};
use crate::tilings::{Analyst, Census, Class, Verdict};
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
    /// Number of tilings, as sets of rectangles, realising the proportion, if tilings were counted.
    pub distinct: u64,
    /// Number of classes of such tilings under the symmetries of the main rectangle, if tilings were counted.
    pub classes: u64,
    /// Number of distinct bags of tiles of such tilings, if bags were counted.
    pub bags: u64,
}

/// Representative of a class of tilings under the symmetries of the main rectangle.
#[derive(Clone, Debug)]
pub struct Tiling {
    proportion: Algebraic,
    placements: Vec<Placement>,
    tiles: Vec<[f64; 4]>,
    stabiliser: u8,
    crossings: usize,
    order: u32,
}

impl Tiling {
    /// The proportion of the tiles.
    pub fn proportion(&self) -> &Algebraic {
        &self.proportion
    }

    /// The placement sequence that represents the tiling.
    pub fn placements(&self) -> &[Placement] {
        &self.placements
    }

    /// Approximations of the left side, bottom side, width and height of each tile, in the order of placement and for a main rectangle of unit height.
    pub fn tiles(&self) -> &[[f64; 4]] {
        &self.tiles
    }

    /// The indices of the symmetries that fix the tiling, in the order of [`crate::SYMMETRIES`].
    pub fn stabiliser(&self) -> Vec<usize> {
        (0..8).filter(|g| self.stabiliser >> g & 1 == 1).collect()
    }

    /// The number of tilings in the class.
    pub fn orbit(&self) -> usize {
        self.order as usize / self.stabiliser.count_ones() as usize
    }

    /// The number of points at which four tiles meet.
    pub fn crossings(&self) -> usize {
        self.crossings
    }
}

/// Placement sequence of at most fourteen tiles, one byte per placement.
pub(crate) type Witness = [u8; 14];

const NO_PLACEMENT: u8 = u8::MAX;

/// Encodes a placement sequence.
pub(crate) fn encode_witness(moves: impl Iterator<Item = Placement>) -> Witness {
    let mut w = [NO_PLACEMENT; 14];
    for (slot, mv) in w.iter_mut().zip(moves) {
        let fit = FITS.iter().position(|&f| f == mv.fit).unwrap_or(0) as u8;
        *slot = mv.tier | fit << 3 | (mv.tall as u8) << 5;
    }
    w
}

pub(crate) fn decode_witness(w: &Witness) -> Vec<Placement> {
    w.iter()
        .take_while(|&&b| b != NO_PLACEMENT)
        .map(|&b| Placement {
            tier: b & 7,
            fit: FITS[(b >> 3 & 3) as usize],
            tall: b >> 5 & 1 == 1,
        })
        .collect()
}

const SATURATED: u32 = u32::MAX;

/// Counts and witnesses of the proportions found, indexed by the identifiers of the registry.
#[derive(Default)]
pub(crate) struct Table {
    counts: Chunked<u32>,
    overflow: WordMap<u32, u64>,
    witnesses: Chunked<Witness>,
    extras: Chunked<[u64; 2]>,
}

impl Table {
    fn count(&self, id: u32) -> u64 {
        match self.counts.find(id as usize) {
            None => 0,
            Some(SATURATED) => self.overflow[&id],
            Some(c) => c as u64,
        }
    }

    fn add(&mut self, id: u32, count: u64, witness: Witness) {
        self.counts.grow(id as usize + 1, 0);
        self.witnesses.grow(id as usize + 1, [NO_PLACEMENT; 14]);
        let slot = self.counts.at(id as usize);
        if *slot == 0 {
            *self.witnesses.at(id as usize) = witness;
        }
        if *slot == SATURATED {
            *self.overflow.entry(id).or_default() += count;
        } else if *slot as u64 + count >= SATURATED as u64 {
            self.overflow.insert(id, *slot as u64 + count);
            *slot = SATURATED;
        } else {
            *slot += count as u32;
        }
    }

    fn ids(&self) -> impl Iterator<Item = u32> + '_ {
        self.counts.iter().enumerate().filter(|(_, c)| *c > 0).map(|(id, _)| id as u32)
    }
}

/// Result of a search.
pub struct Outcome {
    registry: Registry,
    table: Table,
    stats: Stats,
    polynomials: usize,
    bags: Vec<u64>,
    census: Option<Census>,
}

impl Outcome {
    /// The counts of tilings as sets of rectangles, if the search was asked for them.
    pub fn census(&self) -> Option<&Census> {
        self.census.as_ref()
    }

    /// One tiling from each class under the symmetries of the main rectangle, if the search was asked to list them, in increasing order of proportion.
    pub fn classes(&self) -> Vec<Tiling> {
        let Some(census) = &self.census else {
            return Vec::new();
        };
        let mut classes: Vec<&Class> = census.classes.iter().collect();
        classes.sort_by(|a, b| self.registry.approx(a.id).total_cmp(&self.registry.approx(b.id)).then(a.witness.cmp(&b.witness)));
        classes
            .into_iter()
            .map(|class| {
                let placements = decode_witness(&class.witness);
                let root = self.registry.refs(&[class.id])[0];
                Tiling {
                    proportion: self.registry.get(class.id),
                    tiles: exact::coordinates(&self.registry, &root, &placements).unwrap_or_default(),
                    placements,
                    stabiliser: class.stabiliser,
                    crossings: class.crosses as usize,
                    order: census.order() as u32,
                }
            })
            .collect()
    }

    /// The number of distinct proportions found.
    pub fn count(&self) -> usize {
        self.table.ids().count()
    }

    /// The number of proportions found of each algebraic degree, starting from degree one.
    pub fn degrees(&self) -> Vec<usize> {
        let mut histogram = Vec::new();
        for id in self.table.ids() {
            let d = self.registry.degree(id);
            if histogram.len() < d {
                histogram.resize(d, 0);
            }
            histogram[d - 1] += 1;
        }
        histogram
    }

    /// The proportions found, in increasing order.
    pub fn proportions(&self) -> Vec<Found> {
        let mut ids: Vec<u32> = self.table.ids().collect();
        ids.sort_by(|&a, &b| self.registry.approx(a).total_cmp(&self.registry.approx(b)));
        ids.into_iter()
            .map(|id| {
                let [examined, classes] = self.table.extras.find(id as usize).unwrap_or_default();
                let unit = self.registry.approx(id) == 1.0;
                let doubled = self.census.as_ref().is_some_and(|c| c.square) && !unit;
                Found {
                    proportion: self.registry.get(id),
                    tilings: self.table.count(id),
                    witness: decode_witness(&self.table.witnesses.get(id as usize)),
                    distinct: examined * (1 + doubled as u64),
                    classes,
                    bags: self.bags.get(id as usize).copied().unwrap_or(0),
                }
            })
            .collect()
    }

    /// Counters describing the work performed.
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// The number of distinct proportion equations solved.
    pub fn polynomials(&self) -> usize {
        self.polynomials
    }
}

/// Results accumulated by one thread, before they are merged into the shared table.
#[derive(Default)]
pub(crate) struct Tally {
    pub(crate) found: WordMap<u32, (u64, Witness, [u64; 2])>,
    pub(crate) stats: Stats,
    pub(crate) census: Census,
}

/// Results shared by all threads of a search.
#[derive(Default)]
pub(crate) struct Shared {
    table: Mutex<Table>,
    stats: Mutex<Stats>,
    census: Mutex<Census>,
    counting: bool,
}

const FLUSH_LIMIT: usize = 1 << 16;

impl Tally {
    pub(crate) fn record(&mut self, id: u32, verdict: Verdict, witness: impl FnOnce() -> Witness) {
        self.stats.tilings += 1;
        let entry = self.found.entry(id).or_insert_with(|| (0, witness(), [0; 2]));
        entry.0 += 1;
        entry.2[0] += verdict.canonical as u64;
        entry.2[1] += verdict.minimal as u64;
    }

    /// Merges the results into the shared table if they have grown large, or unconditionally.
    pub(crate) fn flush(&mut self, shared: &Shared, force: bool) {
        if !force && self.found.len() < FLUSH_LIMIT {
            return;
        }
        {
            let mut table = shared.table.lock().expect("results lock");
            for (id, (count, witness, extra)) in self.found.drain() {
                table.add(id, count, witness);
                if shared.counting {
                    table.extras.grow(id as usize + 1, [0; 2]);
                    let slot = table.extras.at(id as usize);
                    slot[0] += extra[0];
                    slot[1] += extra[1];
                }
            }
        }
        shared.stats.lock().expect("results lock").merge(&self.stats);
        self.stats = Stats::default();
        if shared.counting {
            shared.census.lock().expect("results lock").merge(&mut self.census);
        }
    }
}

/// Parameters of a search.
#[derive(Clone, Copy, Debug)]
pub struct Search {
    tiles: usize,
    width: i64,
    height: i64,
    minority: usize,
    counting: bool,
    listing: bool,
    bags: bool,
    band: Option<Band>,
}

/// Whether a partial tiling with the given numbers of tall and of placed tiles has at most the given number of tiles in its less frequent orientation.
pub(crate) fn within(minority: usize, tall: usize, placed: usize) -> bool {
    tall.min(placed - tall) <= minority
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
            minority: tiles,
            counting: false,
            listing: false,
            bags: false,
            band: None,
        }
    }

    /// The same search restricted to the proportions in the given band, with the roots outside it disregarded throughout.
    pub fn in_band(self, band: Band) -> Self {
        Search {
            band: Some(band),
            ..self
        }
    }

    /// The band to which the search is restricted, if any.
    pub fn band(&self) -> Option<&Band> {
        self.band.as_ref()
    }

    fn registry(&self) -> Registry {
        self.band.map_or_else(Registry::new, Registry::banded)
    }

    /// The same search, which also counts the tilings and the distinct bags of tiles: the proportion with the multiset of the short sides of the tiles.
    pub fn counting_bags(self) -> Self {
        Search {
            counting: true,
            bags: true,
            ..self
        }
    }

    /// The same search, which also identifies the tilings as sets of rectangles and counts them, up to the symmetries of the main rectangle as well.
    pub fn counting_tilings(self) -> Self {
        Search {
            counting: true,
            ..self
        }
    }

    /// The same search, which also counts the tilings and keeps one from each class under the symmetries of the main rectangle.
    pub fn listing_tilings(self) -> Self {
        Search {
            counting: true,
            listing: true,
            ..self
        }
    }

    fn shared(&self) -> Shared {
        Shared {
            counting: self.counting,
            ..Shared::default()
        }
    }

    pub(crate) fn analyst<'a>(&self, registry: &'a Registry, bags: Option<&'a Bags>) -> Option<Analyst<'a>> {
        self.counting.then(|| Analyst::new(self.width, self.height, registry, self.listing, bags))
    }

    /// The same search restricted to tilings with at most the given number of tiles in the less frequent orientation.
    pub fn with_minority(self, minority: usize) -> Self {
        Search { minority, ..self }
    }

    /// The largest number of tiles allowed in the less frequent orientation.
    pub fn minority(&self) -> usize {
        self.minority
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

    pub(crate) fn sides(&self) -> (i64, i64) {
        (self.width, self.height)
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
                        let talls = path.iter().filter(|p| p.tall).count() + tall as usize;
                        if !within(search.minority, talls, path.len() + 1) {
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

    fn outcome(&self, shared: Shared, registry: Registry, cache: PolyCache, bags: Option<Bags>) -> Outcome {
        let bags = bags.map(|b| b.counts()).unwrap_or_default();
        let table = shared.table.into_inner().expect("results lock");
        let mut census = shared.census.into_inner().expect("results lock");
        census.square = self.is_square();
        census.bags = self.bags.then(|| bags.iter().sum());
        Outcome {
            polynomials: cache.len() + registry.equations(),
            registry,
            table,
            stats: shared.stats.into_inner().expect("results lock"),
            bags,
            census: self.counting.then_some(census),
        }
    }

    /// Runs the search, enumerating every tiling.
    pub fn run(&self) -> Outcome {
        let registry = self.registry();
        let cache = PolyCache::new();
        let shared = self.shared();
        let bags = self.bags.then(Bags::new);
        self.sequences(4).par_iter().for_each_init(|| Engine::new(self, &registry, &cache, &shared, bags.as_ref()), |engine, prefix| engine.run(prefix));
        self.outcome(shared, registry, cache, bags)
    }

    /// Finds the proportions of all guillotine tilings by series and parallel composition of aspect ratios, counting for each the aspect ratio functions that realise it.
    pub fn run_guillotine(&self) -> Outcome {
        let registry = self.registry();
        let cache = PolyCache::new();
        let (counts, stats) = guillotine::solve(self.tiles, self.width, self.height, &registry, &cache);
        let mut table = Table::default();
        for (id, &count) in counts.iter().enumerate().filter(|(_, c)| **c > 0) {
            table.add(id as u32, count, [NO_PLACEMENT; 14]);
        }
        Outcome {
            polynomials: cache.len() + registry.equations(),
            registry,
            table,
            stats,
            bags: Vec::new(),
            census: None,
        }
    }

    /// Runs the search with every tiling solved by exact symbolic elimination, as a reference for the default method.
    pub fn run_exact(&self) -> Outcome {
        let registry = self.registry();
        let cache = PolyCache::new();
        let shared = self.shared();
        let bags = self.bags.then(Bags::new);
        self.sequences(self.tiles).par_chunks(1024).for_each(|paths| {
            let mut tally = Tally::default();
            let mut analyst = self.analyst(&registry, bags.as_ref());
            for path in paths {
                let solved = exact::solve(self.width, self.height, &registry, &cache, path);
                tally.stats.leaves += 1;
                tally.stats.exact += 1;
                tally.stats.candidates += solved.candidate as u64;
                tally.stats.singular += solved.singular;
                tally.stats.constant += solved.constant as u64;
                tally.stats.overflows += solved.overflow as u64;
                for &id in &solved.feasible {
                    let verdict = match &mut analyst {
                        Some(analyst) => analyst.examine(&mut tally.census, path, &registry.refs(&[id])[0], None),
                        None => Verdict::default(),
                    };
                    tally.record(id, verdict, || encode_witness(path.iter().copied()));
                }
            }
            tally.flush(&shared, true);
        });
        self.outcome(shared, registry, cache, bags)
    }
}
