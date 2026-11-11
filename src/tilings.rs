// SPDX-License-Identifier: LGPL-3.0-or-later

//! Identification of the tilings found by a search as sets of rectangles, and of their symmetries.

use crate::algebraic::{Registry, RootRef};
use crate::exact;
use crate::interval::Iv;
use crate::search::{Witness, encode_witness};
use crate::staircase::{Fit, Placement};
use smallvec::SmallVec;
use std::cmp::Ordering;

pub(crate) const MAX_TILES: usize = 14;
pub(crate) const MAX_LINES: usize = MAX_TILES + 2;
const MAX_POINTS: usize = 16;

/// The symmetries of a square, in the order used by the counters of fixed tilings.
pub const SYMMETRIES: [&str; 8] = [
    "identity",
    "transposition",
    "reflection x -> 1 - x",
    "rotation by 90 degrees",
    "reflection y -> 1 - y",
    "rotation by 270 degrees",
    "rotation by 180 degrees",
    "anti-transposition",
];

const SWAP: u8 = 1;
const FLIP_X: u8 = 2;
const FLIP_Y: u8 = 4;

/// The conjugate of a symmetry by the transposition.
fn conjugate(g: usize) -> usize {
    (g & 1) | (g & 2) << 1 | (g & 4) >> 1
}

/// Incidences between the tiles of a placement sequence and the lines that carry their sides.
///
/// Lines zero and one of each direction are the sides of the main rectangle; every other line is created by the tile whose right or top side it carries, and lines are numbered in the order of creation.
pub(crate) struct Layout {
    pub(crate) tiles: usize,
    /// The lines carrying the left, right, bottom and top sides of each tile.
    pub(crate) sides: [[u8; 4]; MAX_TILES],
    /// The numbers of vertical and of horizontal lines.
    pub(crate) lines: [usize; 2],
}

impl Layout {
    /// The layout of a complete placement sequence.
    pub(crate) fn new(moves: &[Placement]) -> Self {
        let mut sides = [[0u8; 4]; MAX_TILES];
        let mut lines = [2usize; 2];
        let mut tiers: SmallVec<[(u8, u8); 8]> = SmallVec::new();
        tiers.push((0, 0));
        for (q, mv) in moves.iter().enumerate() {
            let i = mv.tier as usize;
            let (left, bottom) = tiers[i];
            let narrow = matches!(mv.fit, Fit::Inside | Fit::FullHeight);
            let low = matches!(mv.fit, Fit::Inside | Fit::FullWidth);
            let right = if narrow {
                lines[0] += 1;
                (lines[0] - 1) as u8
            } else if i + 1 < tiers.len() {
                tiers[i + 1].0
            } else {
                1
            };
            let top = if low {
                lines[1] += 1;
                (lines[1] - 1) as u8
            } else if i > 0 {
                tiers[i - 1].1
            } else {
                1
            };
            sides[q] = [left, right, bottom, top];
            match mv.fit {
                Fit::Inside => {
                    tiers[i] = (left, top);
                    tiers.insert(i + 1, (right, bottom));
                }
                Fit::FullHeight => tiers[i] = (right, bottom),
                Fit::FullWidth => tiers[i] = (left, top),
                Fit::Full => {
                    tiers.remove(i);
                }
            }
        }
        Layout {
            tiles: moves.len(),
            sides,
            lines,
        }
    }
}

/// The powers of the proportion by which the width, the height and the short side of a tile differ from the side on which its positivity is tested.
pub(crate) fn exponents(mv: Placement) -> (i32, i32, i32) {
    match (mv.fit, mv.tall) {
        (Fit::Inside, false) => (1, 0, 0),
        (Fit::Inside, true) => (0, 1, 0),
        (Fit::FullHeight, false) => (1, 0, 0),
        (Fit::FullHeight, true) => (-1, 0, -1),
        (_, false) => (0, -1, -1),
        (_, true) => (0, 1, 0),
    }
}

/// Positions of the lines of a layout in the order of their coordinates, equal coordinates sharing a position.
pub(crate) struct Ranks {
    pub(crate) x: [u8; MAX_LINES],
    pub(crate) y: [u8; MAX_LINES],
}

/// Equation between the coordinates of two lines, the second possibly reflected in the main rectangle.
pub(crate) struct Relation {
    /// Direction and index of the first line.
    pub(crate) first: (usize, u8),
    /// Direction and index of the second line.
    pub(crate) second: (usize, u8),
    /// Whether the second coordinate is subtracted from the side of the main rectangle.
    pub(crate) reflected: bool,
}

/// Tiling described by the positions of the sides of its tiles amongst the distinct coordinates.
#[derive(Clone, Copy)]
struct Shape {
    tiles: usize,
    /// The positions of the right and of the top side of the main rectangle.
    max: [u8; 2],
    /// The positions of the left, right, bottom and top sides of each tile.
    rect: [[u8; 4]; MAX_TILES],
    /// The set of tall tiles.
    tall: u16,
}

impl Shape {
    fn new(layout: &Layout, ranks: &Ranks, moves: &[Placement], unit: bool) -> Self {
        let mut rect = [[0u8; 4]; MAX_TILES];
        let mut tall = 0;
        for q in 0..layout.tiles {
            let [l, r, b, t] = layout.sides[q];
            rect[q] = [ranks.x[l as usize], ranks.x[r as usize], ranks.y[b as usize], ranks.y[t as usize]];
            if moves[q].tall && !unit {
                tall |= 1 << q;
            }
        }
        Shape {
            tiles: layout.tiles,
            max: [ranks.x[1], ranks.y[1]],
            rect,
            tall,
        }
    }

    /// The image of the tiling under a symmetry, which exchanges orientations if it exchanges the axes and the tiles are not squares.
    fn image(&self, g: u8, unit: bool) -> Shape {
        let swap = g & SWAP != 0;
        let max = if swap { [self.max[1], self.max[0]] } else { self.max };
        let mut rect = [[0u8; 4]; MAX_TILES];
        for q in 0..self.tiles {
            let [l, r, b, t] = self.rect[q];
            let [mut l, mut r, mut b, mut t] = if swap { [b, t, l, r] } else { [l, r, b, t] };
            if g & FLIP_X != 0 {
                (l, r) = (max[0] - r, max[0] - l);
            }
            if g & FLIP_Y != 0 {
                (b, t) = (max[1] - t, max[1] - b);
            }
            rect[q] = [l, r, b, t];
        }
        let all = (1u16 << self.tiles) - 1;
        Shape {
            tiles: self.tiles,
            max,
            rect,
            tall: if swap && !unit { !self.tall & all } else { self.tall },
        }
    }
}

/// Tiles indexed by the positions of three of their corners.
struct Grid {
    bottom_left: [[u8; MAX_LINES]; MAX_LINES],
    top_left: [[u8; MAX_LINES]; MAX_LINES],
    bottom_right: [[u8; MAX_LINES]; MAX_LINES],
}

impl Grid {
    fn new() -> Self {
        Grid {
            bottom_left: [[0; MAX_LINES]; MAX_LINES],
            top_left: [[0; MAX_LINES]; MAX_LINES],
            bottom_right: [[0; MAX_LINES]; MAX_LINES],
        }
    }

    fn fill(&mut self, shape: &Shape) {
        for q in 0..shape.tiles {
            let [l, r, b, t] = shape.rect[q].map(|v| v as usize);
            self.bottom_left[l][b] = q as u8 + 1;
            self.top_left[l][t] = q as u8 + 1;
            self.bottom_right[r][b] = q as u8 + 1;
        }
    }

    fn clear(&mut self, shape: &Shape) {
        for q in 0..shape.tiles {
            let [l, r, b, t] = shape.rect[q].map(|v| v as usize);
            self.bottom_left[l][b] = 0;
            self.top_left[l][t] = 0;
            self.bottom_right[r][b] = 0;
        }
    }

    /// The numbers of points at which four tiles meet, split by whether the lower right tile or the upper left tile has the smaller index.
    fn crosses(&self, shape: &Shape) -> (usize, usize) {
        let mut counts = (0, 0);
        for q in 0..shape.tiles {
            let [_, r, _, t] = shape.rect[q].map(|v| v as usize);
            if r == shape.max[0] as usize || t == shape.max[1] as usize || self.bottom_left[r][t] == 0 {
                continue;
            }
            let (below, above) = (self.top_left[r][t], self.bottom_right[r][t]);
            if below != 0 && above != 0 {
                if below < above {
                    counts.0 += 1;
                } else {
                    counts.1 += 1;
                }
            }
        }
        counts
    }

    /// Whether every tile of the given shape is a tile of the indexed shape, with the same orientation.
    fn contains(&self, own: &Shape, other: &Shape) -> bool {
        if own.max != other.max {
            return false;
        }
        (0..other.tiles).all(|q| {
            let [l, _, b, _] = other.rect[q].map(|v| v as usize);
            let u = self.bottom_left[l][b] as usize;
            u != 0 && own.rect[u - 1] == other.rect[q] && (own.tall >> (u - 1) & 1) == (other.tall >> q & 1)
        })
    }

    /// Compares the placement sequence that puts each tile of the indexed shape at the first tier whose floor does not extend with the given sequence, or returns nothing if the shape is not a tiling.
    fn compare(&self, shape: &Shape, own: &Witness) -> Option<Ordering> {
        let mut tiers: SmallVec<[(u8, u8); 8]> = SmallVec::new();
        tiers.push((0, 0));
        let mut placed = 0u16;
        for &expected in own.iter().take(shape.tiles) {
            let mut i = 0;
            let (q, end) = loop {
                let (x, y) = *tiers.get(i)?;
                let end = tiers.get(i + 1).map_or(shape.max[0], |t| t.0);
                let next = self.top_left[end as usize][y as usize];
                if next != 0 && placed >> (next - 1) & 1 == 0 {
                    i += 1;
                    continue;
                }
                let q = self.bottom_left[x as usize][y as usize];
                if q == 0 || placed >> (q - 1) & 1 != 0 {
                    return None;
                }
                break (q as usize - 1, end);
            };
            let ceiling = if i > 0 { tiers[i - 1].1 } else { shape.max[1] };
            let (left, bottom) = tiers[i];
            let [_, right, _, top] = shape.rect[q];
            if right > end || top > ceiling || i >= 8 {
                return None;
            }
            let fit = (right == end) as u8 * 2 + (top == ceiling) as u8;
            let code = i as u8 | fit << 3 | ((shape.tall >> q & 1) as u8) << 5;
            if code != expected {
                return Some(code.cmp(&expected));
            }
            placed |= 1 << q;
            match fit {
                0 => {
                    tiers[i] = (left, top);
                    tiers.insert(i + 1, (right, bottom));
                }
                1 => tiers[i] = (right, bottom),
                2 => tiers[i] = (left, top),
                _ => {
                    tiers.remove(i);
                }
            }
        }
        Some(Ordering::Equal)
    }
}

/// Positions of intervals that are pairwise disjoint, in increasing order.
fn separate(coords: &[Iv]) -> Option<[u8; MAX_LINES]> {
    let mut order: SmallVec<[u8; MAX_LINES]> = (0..coords.len() as u8).collect();
    order.sort_unstable_by(|&a, &b| coords[a as usize].lo.total_cmp(&coords[b as usize].lo));
    let mut ranks = [0u8; MAX_LINES];
    for (k, &line) in order.iter().enumerate() {
        if k > 0 && !(coords[line as usize].lo > coords[order[k - 1] as usize].hi) {
            return None;
        }
        ranks[line as usize] = k as u8;
    }
    Some(ranks)
}

/// Class of tilings equivalent under the symmetries of the main rectangle.
#[derive(Clone, Debug)]
pub(crate) struct Class {
    pub(crate) id: u32,
    pub(crate) witness: Witness,
    /// The set of symmetries that fix the tiling, as a mask over their indices.
    pub(crate) stabiliser: u8,
    pub(crate) crosses: u8,
}

/// Counts of the tilings found by a search, regarded as sets of rectangles.
#[derive(Clone, Debug, Default)]
pub struct Census {
    pub(crate) square: bool,
    /// Sequences with orientations and proportion, by squareness of the tiles and number of points at which four tiles meet.
    pub(crate) records: [[u64; MAX_POINTS]; 2],
    /// Tilings examined, indexed likewise.
    pub(crate) canonical: [[u64; MAX_POINTS]; 2],
    /// Tilings examined that are fixed by each symmetry, by squareness of the tiles.
    pub(crate) fixed: [[u64; 8]; 2],
    /// Tilings examined that come first in their class, by squareness of the tiles.
    pub(crate) minimal: [u64; 2],
    pub(crate) reoriented: u64,
    pub(crate) exact: u64,
    pub(crate) inconsistent: u64,
    pub(crate) asymmetric: u64,
    pub(crate) classes: Vec<Class>,
}

impl Census {
    pub(crate) fn merge(&mut self, o: &mut Census) {
        self.square |= o.square;
        for c in 0..2 {
            for k in 0..MAX_POINTS {
                self.records[c][k] += o.records[c][k];
                self.canonical[c][k] += o.canonical[c][k];
            }
            for g in 0..8 {
                self.fixed[c][g] += o.fixed[c][g];
            }
            self.minimal[c] += o.minimal[c];
        }
        self.reoriented += o.reoriented;
        self.exact += o.exact;
        self.inconsistent += o.inconsistent;
        self.asymmetric += o.asymmetric;
        self.classes.append(&mut o.classes);
        *o = Census {
            square: o.square,
            ..Census::default()
        };
    }

    /// The factor by which the tilings with tiles that are not squares are under-represented amongst those examined.
    fn weight(&self) -> u64 {
        1 + self.square as u64
    }

    /// The number of tilings, as sets of rectangles.
    pub fn tilings(&self) -> u64 {
        self.weight() * self.canonical[0].iter().sum::<u64>() + self.squared()
    }

    /// The number of tilings whose tiles are squares.
    pub fn squared(&self) -> u64 {
        self.canonical[1].iter().sum()
    }

    /// The number of tilings by the number of points at which four tiles meet.
    pub fn by_crossings(&self) -> Vec<u64> {
        let mut out: Vec<u64> = (0..MAX_POINTS).map(|k| self.weight() * self.canonical[0][k] + self.canonical[1][k]).collect();
        while out.len() > 1 && out.last() == Some(&0) {
            out.pop();
        }
        out
    }

    /// The number of symmetries of the main rectangle.
    pub fn order(&self) -> u64 {
        if self.square { 8 } else { 4 }
    }

    /// The number of tilings fixed by each symmetry, in the order of [`SYMMETRIES`].
    pub fn fixed(&self) -> [u64; 8] {
        std::array::from_fn(|g| {
            let other = if self.square { self.fixed[0][conjugate(g)] } else { 0 };
            self.fixed[0][g] + other + self.fixed[1][g]
        })
    }

    /// The number of classes of tilings under the symmetries of the main rectangle, counted by the tilings that come first in their class.
    pub fn classes(&self) -> u64 {
        self.minimal[0] + self.minimal[1]
    }

    /// The number of classes of tilings under the symmetries of the main rectangle, counted by the lemma of Burnside, if the count is integral.
    pub fn classes_by_fixed_points(&self) -> Option<u64> {
        let total: u64 = self.fixed().iter().sum();
        total.is_multiple_of(self.order()).then_some(total / self.order())
    }

    /// The number of sequences with orientations and proportion found by the search, by the number of points at which four tiles meet, for tiles that are not squares and for squares.
    pub fn records(&self) -> [Vec<u64>; 2] {
        [0, 1].map(|c| self.records[c].to_vec())
    }

    /// The number of tilings examined by the search, indexed as the records.
    pub fn examined(&self) -> [Vec<u64>; 2] {
        [0, 1].map(|c| self.canonical[c].to_vec())
    }

    /// The number of sequences found at proportion one with some tile marked as tall, which repeat tilings by squares.
    pub fn reoriented(&self) -> u64 {
        self.reoriented
    }

    /// Whether every tiling with k points at which four tiles meet was found through exactly 2^k sequences.
    pub fn multiplicities_hold(&self) -> bool {
        (0..2).all(|c| (0..MAX_POINTS).all(|k| self.records[c][k] == self.canonical[c][k] << k))
    }

    /// The number of tilings whose coordinates were compared by exact arithmetic.
    pub fn exact(&self) -> u64 {
        self.exact
    }

    /// The number of tilings on which two independent criteria disagreed; the counts are certified only if it is zero.
    pub fn inconsistent(&self) -> u64 {
        self.inconsistent
    }

    /// The number of tilings whose combinatorial symmetry was not confirmed by exact arithmetic; the counts are certified only if it is zero.
    pub fn asymmetric(&self) -> u64 {
        self.asymmetric
    }
}

/// Examiner of the tilings found by one thread of a search.
pub(crate) struct Analyst<'a> {
    width: i64,
    height: i64,
    registry: &'a Registry,
    listing: bool,
    grid: Grid,
    scratch: Grid,
}

/// What the examination of a tiling established.
#[derive(Clone, Copy, Default)]
pub(crate) struct Verdict {
    /// Whether the sequence is the one that represents its tiling.
    pub(crate) canonical: bool,
    /// Whether the tiling comes first in its class.
    pub(crate) minimal: bool,
}

impl<'a> Analyst<'a> {
    pub(crate) fn new(width: i64, height: i64, registry: &'a Registry, listing: bool) -> Self {
        Analyst {
            width,
            height,
            registry,
            listing,
            grid: Grid::new(),
            scratch: Grid::new(),
        }
    }

    fn ranks(&self, layout: &Layout, moves: &[Placement], root: &RootRef, sizes: Option<&[Iv]>) -> Option<(Ranks, bool)> {
        let mut hints = None;
        if let Some(sizes) = sizes {
            let x = Iv { lo: root.lo, hi: root.hi };
            let mut coords = [[Iv::point(0.0); MAX_LINES]; 2];
            coords[0][1] = Iv::point(self.width as f64);
            coords[1][1] = Iv::point(self.height as f64);
            let mut created = [2usize; 2];
            for (q, &mv) in moves.iter().enumerate() {
                let (ex, ey, _) = exponents(mv);
                let [left, right, bottom, top] = layout.sides[q].map(|v| v as usize);
                if right == created[0] {
                    coords[0][right] = coords[0][left].add(sizes[q].mul(x.powi(ex)));
                    created[0] += 1;
                }
                if top == created[1] {
                    coords[1][top] = coords[1][bottom].add(sizes[q].mul(x.powi(ey)));
                    created[1] += 1;
                }
            }
            if let (Some(x), Some(y)) = (separate(&coords[0][..layout.lines[0]]), separate(&coords[1][..layout.lines[1]])) {
                return Some((Ranks { x, y }, false));
            }
            hints = Some(coords);
        }
        let ranks = exact::ranks(self.registry, root, moves, layout, hints.as_ref())?;
        Some((ranks, true))
    }

    /// Examines the tiling realised by a complete placement sequence at a proportion, given enclosures of the tested side of each tile if they are known.
    pub(crate) fn examine(&mut self, census: &mut Census, moves: &[Placement], root: &RootRef, sizes: Option<&[Iv]>) -> Verdict {
        let mut verdict = Verdict::default();
        let unit = root.lo == 1.0 && root.hi == 1.0;
        if unit && moves.iter().any(|m| m.tall) {
            census.reoriented += 1;
            return verdict;
        }
        let layout = Layout::new(moves);
        let Some((ranks, exact)) = self.ranks(&layout, moves, root, sizes) else {
            census.inconsistent += 1;
            return verdict;
        };
        census.exact += exact as u64;
        let shape = Shape::new(&layout, &ranks, moves, unit);
        let own = encode_witness(moves.iter().copied());
        self.grid.fill(&shape);
        let (below, above) = self.grid.crosses(&shape);
        let points = (below + above).min(MAX_POINTS - 1);
        let class = unit as usize;
        census.records[class][points] += 1;
        let order = self.grid.compare(&shape, &own);
        verdict.canonical = order == Some(Ordering::Equal);
        if order.is_none() || verdict.canonical != (above == 0) {
            census.inconsistent += 1;
        }
        if verdict.canonical {
            census.canonical[class][points] += 1;
            census.fixed[class][0] += 1;
            verdict.minimal = true;
            let mut stabiliser = 1u8;
            let square = self.width == self.height;
            for g in 1..8u8 {
                if g & SWAP != 0 && !square {
                    continue;
                }
                let image = shape.image(g, unit);
                let fixed = self.grid.contains(&shape, &image);
                self.scratch.fill(&image);
                let order = self.scratch.compare(&image, &own);
                self.scratch.clear(&image);
                if order.is_none() || fixed != (order == Some(Ordering::Equal)) {
                    census.inconsistent += 1;
                }
                if order == Some(Ordering::Less) {
                    verdict.minimal = false;
                }
                if fixed {
                    if self.confirmed(&layout, &ranks, moves, root, g) {
                        census.fixed[class][g as usize] += 1;
                        stabiliser |= 1 << g;
                    } else {
                        census.asymmetric += 1;
                    }
                }
            }
            if verdict.minimal {
                census.minimal[class] += 1;
                if self.listing {
                    census.classes.push(Class {
                        id: root.id,
                        witness: own,
                        stabiliser,
                        crosses: points as u8,
                    });
                }
            }
        }
        self.grid.clear(&shape);
        verdict
    }

    /// Whether exact arithmetic confirms that a symmetry maps the coordinates of the lines of a tiling to one another.
    fn confirmed(&self, layout: &Layout, ranks: &Ranks, moves: &[Placement], root: &RootRef, g: u8) -> bool {
        let lines = |d: usize, rank: u8| (0..layout.lines[d] as u8).find(|&k| [&ranks.x, &ranks.y][d][k as usize] == rank);
        let max = [ranks.x[1], ranks.y[1]];
        let mut relations = Vec::new();
        for d in 0..2 {
            let source = if g & SWAP != 0 { 1 - d } else { d };
            let reflected = g & [FLIP_X, FLIP_Y][d] != 0;
            for j in 0..=max[source] {
                let k = if reflected { max[source] - j } else { j };
                let (Some(first), Some(second)) = (lines(d, k), lines(source, j)) else {
                    return false;
                };
                relations.push(Relation {
                    first: (d, first),
                    second: (source, second),
                    reflected,
                });
            }
        }
        exact::related(self.registry, root, moves, layout, &relations) == Some(true)
    }
}
