// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exhaustive search for tilings of a rectangle by similar rectangles.

use crate::algebraic::{Algebraic, Registry, RootRef};
use crate::form::Form;
use crate::int::{Int, take_overflow};
use crate::interval::sign_on_interval;
use crate::poly::Poly;
use num_bigint::BigInt;
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

/// Extent of a tile relative to the tier on which it is placed.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Fit {
    /// Narrower than the floor and lower than the wall.
    Inside,
    /// Narrower than the floor and as high as the wall.
    FullHeight,
    /// As wide as the floor and lower than the wall.
    FullWidth,
    /// As wide as the floor and as high as the wall.
    Full,
}

const FITS: [Fit; 4] = [Fit::Inside, Fit::FullHeight, Fit::FullWidth, Fit::Full];

/// Placement of one tile at the anchor of a tier of the staircase.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Placement {
    /// Index of the tier, counted from the top-left.
    pub tier: u8,
    /// Extent of the tile relative to the tier.
    pub fit: Fit,
    /// Whether the long side of the tile is vertical.
    pub tall: bool,
}

/// Counters describing the work performed by a search.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct Stats {
    /// Complete placement sequences with orientations examined.
    pub leaves: u64,
    /// Leaves whose proportion equation has a root not smaller than one.
    pub candidates: u64,
    /// Pairs of a leaf and a root satisfying all constraints.
    pub tilings: u64,
    /// Leaves whose linear system is singular, or degenerate at a candidate root.
    pub singular: u64,
    /// Leaves in which the aspect ratio of the main rectangle does not depend on the proportion.
    pub constant: u64,
    /// Subtrees recomputed in arbitrary precision after a machine-word overflow.
    pub overflows: u64,
}

impl Stats {
    fn merge(&mut self, o: &Stats) {
        self.leaves += o.leaves;
        self.candidates += o.candidates;
        self.tilings += o.tilings;
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
}

/// Parameters of a search.
#[derive(Clone, Copy, Debug)]
pub struct Search {
    tiles: usize,
    width: i64,
    height: i64,
    split_depth: usize,
}

#[derive(Clone)]
enum Lock<C: Int> {
    Free,
    Stale,
    Above(Form<C>),
}

#[derive(Clone)]
struct Tier<C: Int> {
    floor: Form<C>,
    wall: Form<C>,
    lock: Lock<C>,
}

#[derive(Clone)]
struct State<C: Int> {
    tiers: Vec<Tier<C>>,
    equations: Vec<Form<C>>,
    positives: Vec<Form<C>>,
    unknowns: usize,
    remaining: usize,
    path: Vec<Placement>,
}

#[derive(Default)]
struct Tally {
    found: HashMap<u32, (u64, Vec<Placement>)>,
    stats: Stats,
}

impl Tally {
    fn merge(mut self, o: Tally) -> Tally {
        self.stats.merge(&o.stats);
        for (id, (count, witness)) in o.found {
            self.found.entry(id).and_modify(|e| e.0 += count).or_insert((count, witness));
        }
        self
    }
}

struct Worker<'a, C: Int> {
    search: &'a Search,
    registry: &'a Registry,
    cache: HashMap<Poly<C>, Arc<Vec<RootRef>>>,
    tally: Tally,
}

impl<C: Int> State<C> {
    fn initial(tiles: usize) -> Self {
        State {
            tiers: vec![Tier {
                floor: Form::unknown(1),
                wall: Form::unknown(0),
                lock: Lock::Free,
            }],
            equations: Vec::new(),
            positives: Vec::new(),
            unknowns: 0,
            remaining: tiles,
            path: Vec::new(),
        }
    }

    fn place(&self, mv: Placement) -> Option<Self> {
        let i = mv.tier as usize;
        let tier = &self.tiers[i];
        if matches!(tier.lock, Lock::Stale) {
            return None;
        }
        let count = self.tiers.len();
        let after = match mv.fit {
            Fit::Inside => count + 1,
            Fit::Full => count - 1,
            _ => count,
        };
        let remaining = self.remaining - 1;
        if remaining < after || (after == 0 && remaining > 0) {
            return None;
        }
        let mut next = self.clone();
        next.remaining = remaining;
        next.path.push(mv);
        let (floor, wall) = (&tier.floor, &tier.wall);
        let (width, height) = match (mv.fit, mv.tall) {
            (Fit::Inside, tall) => {
                let side: Form<C> = Form::unknown(2 + self.unknowns);
                next.unknowns += 1;
                if !matches!(tier.lock, Lock::Above(_)) {
                    next.positives.push(side.clone());
                }
                if tall { (side.clone(), side.mul_x()) } else { (side.mul_x(), side) }
            }
            (Fit::FullHeight, false) => (wall.mul_x(), wall.clone()),
            (Fit::FullHeight, true) => (wall.div_x(), wall.clone()),
            (Fit::FullWidth, false) => (floor.clone(), floor.div_x()),
            (Fit::FullWidth, true) => (floor.clone(), floor.mul_x()),
            (Fit::Full, false) => {
                next.equations.push(floor.sub(&wall.mul_x()));
                (floor.clone(), wall.clone())
            }
            (Fit::Full, true) => {
                next.equations.push(wall.sub(&floor.mul_x()));
                (floor.clone(), wall.clone())
            }
        };
        let narrow = matches!(mv.fit, Fit::Inside | Fit::FullHeight);
        let low = matches!(mv.fit, Fit::Inside | Fit::FullWidth);
        if narrow {
            next.positives.push(floor.sub(&width));
            if let Lock::Above(bound) = &tier.lock {
                next.positives.push(width.sub(bound));
            }
        }
        if low {
            next.positives.push(wall.sub(&height));
        }
        for t in next.tiers[..i].iter_mut() {
            t.lock = Lock::Stale;
        }
        if !low && i > 0 {
            let prev = &mut next.tiers[i - 1];
            prev.lock = Lock::Above(prev.floor.clone());
            prev.floor = prev.floor.add(&width);
        }
        if !narrow && i + 1 < count {
            let below = &mut next.tiers[i + 1];
            below.wall = below.wall.add(&height);
        }
        match mv.fit {
            Fit::Inside => {
                next.tiers[i] = Tier {
                    floor: width.clone(),
                    wall: wall.sub(&height),
                    lock: Lock::Free,
                };
                next.tiers.insert(
                    i + 1,
                    Tier {
                        floor: floor.sub(&width),
                        wall: height,
                        lock: Lock::Free,
                    },
                );
            }
            Fit::FullHeight => {
                next.tiers[i] = Tier {
                    floor: floor.sub(&width),
                    wall: wall.clone(),
                    lock: Lock::Free,
                };
            }
            Fit::FullWidth => {
                next.tiers[i] = Tier {
                    floor: floor.clone(),
                    wall: wall.sub(&height),
                    lock: Lock::Free,
                };
            }
            Fit::Full => {
                next.tiers.remove(i);
            }
        }
        Some(next)
    }

    fn moves(&self, search: &Search) -> Vec<Placement> {
        let mut out = Vec::new();
        for tier in 0..self.tiers.len() {
            for fit in FITS {
                for tall in [false, true] {
                    if tall && self.path.is_empty() && search.is_square() {
                        continue;
                    }
                    out.push(Placement {
                        tier: tier as u8,
                        fit,
                        tall,
                    });
                }
            }
        }
        out
    }
}

impl<'a, C: Int> Worker<'a, C> {
    fn explore(&mut self, state: &State<C>) {
        if state.tiers.is_empty() {
            self.leaf(state);
            return;
        }
        for mv in state.moves(self.search) {
            if let Some(next) = state.place(mv) {
                self.explore(&next);
            }
        }
    }

    fn roots(&mut self, p: &Poly<C>) -> Arc<Vec<RootRef>> {
        if let Some(r) = self.cache.get(p) {
            return r.clone();
        }
        let r = self.registry.roots_from_one(&p.to_big());
        self.cache.insert(p.clone(), r.clone());
        r
    }

    fn sign_at(&self, root: &RootRef, q: &Poly<C>) -> i32 {
        if q.is_zero() {
            return 0;
        }
        let shifted = q.taylor_shift_one();
        if shifted.sign_variations() == 0 && !shifted.coeffs()[0].is_zero() {
            return shifted.coeffs()[0].signum();
        }
        match sign_on_interval(q, root.lo, root.hi) {
            Some(s) => s,
            None => self.registry.sign_at(root.id, &q.to_big()),
        }
    }

    fn leaf(&mut self, state: &State<C>) {
        self.tally.stats.leaves += 1;
        let k = state.unknowns;
        let m = k + 1;
        debug_assert_eq!(state.equations.len(), m);
        let mut a: Vec<Vec<Poly<C>>> = state
            .equations
            .iter()
            .map(|e| {
                let mut row: Vec<Poly<C>> = (0..k).map(|j| e.coeff(2 + j)).collect();
                row.push(e.coeff(1));
                row.push(e.coeff(0).neg());
                row
            })
            .collect();
        let mut prev: Poly<C> = Poly::one();
        for i in 0..m {
            let Some(pivot) = (i..m).filter(|&r| !a[r][i].is_zero()).min_by_key(|&r| a[r][i].degree()) else {
                self.tally.stats.singular += 1;
                return;
            };
            a.swap(i, pivot);
            for r in i + 1..m {
                for c in i + 1..=m {
                    let v = a[i][i].mul(&a[r][c]).sub(&a[r][i].mul(&a[i][c]));
                    a[r][c] = v.div_exact(&prev);
                }
                a[r][i] = Poly::zero();
            }
            prev = a[i][i].clone();
        }
        let det = a[k][k].clone();
        let width = a[k][m].clone();
        let target = width
            .scale(&C::from_i64(self.search.height))
            .sub(&det.scale(&C::from_i64(self.search.width)));
        if target.is_zero() {
            self.tally.stats.constant += 1;
            return;
        }
        let shifted = target.taylor_shift_one();
        if shifted.sign_variations() == 0 && !shifted.coeffs()[0].is_zero() {
            return;
        }
        let roots = self.roots(&target);
        if roots.is_empty() {
            return;
        }
        self.tally.stats.candidates += 1;
        let mut sol: Vec<Poly<C>> = vec![Poly::zero(); m];
        sol[k] = width;
        for i in (0..k).rev() {
            let mut v = det.mul(&a[i][m]);
            for j in i + 1..m {
                v = v.sub(&a[i][j].mul(&sol[j]));
            }
            sol[i] = v.div_exact(&a[i][i]);
        }
        let numerators: Vec<Poly<C>> = state
            .positives
            .iter()
            .map(|f| {
                let mut q = f.coeff(0).mul(&det).add(&f.coeff(1).mul(&sol[k]));
                for (j, c) in f.coeffs().iter().enumerate().skip(2) {
                    q = q.add(&c.mul(&sol[j - 2]));
                }
                q
            })
            .collect();
        for root in roots.iter() {
            let sd = self.sign_at(root, &det);
            if sd == 0 {
                self.tally.stats.singular += 1;
                continue;
            }
            if numerators.iter().rev().all(|q| self.sign_at(root, q) == sd) {
                self.tally.stats.tilings += 1;
                self.tally
                    .found
                    .entry(root.id)
                    .and_modify(|e| e.0 += 1)
                    .or_insert_with(|| (1, state.path.clone()));
            }
        }
    }
}

fn replay<C: Int>(search: &Search, path: &[Placement]) -> State<C> {
    let mut state = State::initial(search.tiles);
    for &mv in path {
        state = state.place(mv).expect("valid placement prefix");
    }
    state
}

fn run_task<C: Int>(search: &Search, registry: &Registry, cache: HashMap<Poly<C>, Arc<Vec<RootRef>>>, path: &[Placement]) -> (Tally, HashMap<Poly<C>, Arc<Vec<RootRef>>>) {
    let mut worker = Worker {
        search,
        registry,
        cache,
        tally: Tally::default(),
    };
    worker.explore(&replay::<C>(search, path));
    (worker.tally, worker.cache)
}

impl Search {
    /// A search for tilings by the given number of tiles of a main rectangle with the given integer width and height.
    pub fn new(tiles: usize, width: u32, height: u32) -> Self {
        assert!(tiles >= 1 && tiles <= 64, "the number of tiles must be between 1 and 64");
        assert!(width >= 1 && height >= 1, "the sides of the main rectangle must be positive");
        Search {
            tiles,
            width: width as i64,
            height: height as i64,
            split_depth: 3,
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

    fn prefixes(&self) -> Vec<Vec<Placement>> {
        let mut done = Vec::new();
        let mut frontier = vec![State::<i64>::initial(self.tiles)];
        for _ in 0..self.split_depth {
            let mut next = Vec::new();
            for state in frontier {
                if state.tiers.is_empty() {
                    done.push(state.path);
                    continue;
                }
                for mv in state.moves(self) {
                    if let Some(s) = state.place(mv) {
                        next.push(s);
                    }
                }
            }
            frontier = next;
        }
        done.extend(frontier.into_iter().map(|s| s.path));
        done
    }

    /// Runs the search, enumerating every tiling.
    pub fn run(&self) -> Outcome {
        let registry = Registry::new();
        let tally = self
            .prefixes()
            .par_iter()
            .map_init(HashMap::new, |cache, path| {
                take_overflow();
                let (tally, filled) = run_task::<i64>(self, &registry, std::mem::take(cache), path);
                if take_overflow() {
                    let (mut tally, _) = run_task::<BigInt>(self, &registry, HashMap::new(), path);
                    tally.stats.overflows += 1;
                    tally
                } else {
                    *cache = filled;
                    tally
                }
            })
            .reduce(Tally::default, Tally::merge);
        let mut proportions: Vec<Found> = tally
            .found
            .into_iter()
            .map(|(id, (tilings, witness))| Found {
                proportion: registry.get(id),
                tilings,
                witness,
            })
            .collect();
        proportions.sort_by(|a, b| a.proportion.approx().total_cmp(&b.proportion.approx()));
        Outcome {
            proportions,
            stats: tally.stats,
        }
    }
}

/// Counts the complete placement sequences for the given number of tiles, disregarding orientations.
pub fn count_layouts(tiles: usize) -> u64 {
    fn rec(stale: &[bool], remaining: usize) -> u64 {
        let k = stale.len();
        if k == 0 {
            return (remaining == 0) as u64;
        }
        if remaining < k {
            return 0;
        }
        let mut total = 0;
        for i in 0..k {
            if stale[i] {
                continue;
            }
            for fit in FITS {
                let mut next: Vec<bool> = vec![true; i];
                if matches!(fit, Fit::FullHeight | Fit::Full) && i > 0 {
                    next[i - 1] = false;
                }
                match fit {
                    Fit::Inside => next.extend([false, false]),
                    Fit::Full => {}
                    _ => next.push(false),
                }
                next.extend_from_slice(&stale[i + 1..]);
                total += rec(&next, remaining - 1);
            }
        }
        total
    }
    rec(&[false], tiles)
}
