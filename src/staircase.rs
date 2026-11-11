// SPDX-License-Identifier: LGPL-3.0-or-later

//! Staircase placement of tiles, generic in the representation of lengths.

use smallvec::SmallVec;

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

/// The four fits, in the order in which the search tries them.
pub const FITS: [Fit; 4] = [Fit::Inside, Fit::FullHeight, Fit::FullWidth, Fit::Full];

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

/// Arithmetic of lengths, together with the collection of the constraints that a tiling imposes on them.
pub(crate) trait Algebra {
    /// Representation of a length.
    type Len: Clone;
    /// Whether inequality constraints are collected.
    const CONSTRAINED: bool;
    /// The short side of a tile placed inside its tier.
    fn fresh(&mut self) -> Self::Len;
    /// Sum.
    fn add(&mut self, a: &Self::Len, b: &Self::Len) -> Self::Len;
    /// Difference.
    fn sub(&mut self, a: &Self::Len, b: &Self::Len) -> Self::Len;
    /// Product with the tile proportion.
    fn mul_x(&mut self, a: &Self::Len) -> Self::Len;
    /// Quotient by the tile proportion.
    fn div_x(&mut self, a: &Self::Len) -> Self::Len;
    /// Records that a length is positive.
    fn positive(&mut self, a: Self::Len);
    /// Records that a length vanishes.
    fn vanishes(&mut self, a: Self::Len);
}

#[derive(Clone)]
pub(crate) struct Tier<L> {
    pub(crate) floor: L,
    pub(crate) wall: L,
    /// Whether no tile can be placed until the floor grows.
    pub(crate) stale: bool,
    /// Whether a tile already stands on the segment carrying the floor.
    pub(crate) started: bool,
}

/// The tiers of the unfilled region, from the top-left to the bottom-right.
#[derive(Clone)]
pub(crate) struct Staircase<L> {
    pub(crate) tiers: SmallVec<[Tier<L>; 8]>,
}

impl<L: Clone> Staircase<L> {
    /// The staircase of an empty main rectangle with the given width and height.
    pub(crate) fn new(width: L, height: L) -> Self {
        let mut tiers = SmallVec::new();
        tiers.push(Tier {
            floor: width,
            wall: height,
            stale: false,
            started: false,
        });
        Staircase { tiers }
    }

    /// The number of tiers after the given placement, if the placement is possible with the given number of tiles still to place.
    pub(crate) fn admits(&self, mv: Placement, remaining: usize) -> Option<usize> {
        let i = mv.tier as usize;
        if self.tiers[i].stale {
            return None;
        }
        if matches!(mv.fit, Fit::FullHeight | Fit::Full) && i > 0 && self.tiers[i - 1].started {
            return None;
        }
        let count = self.tiers.len();
        let after = match mv.fit {
            Fit::Inside => count + 1,
            Fit::Full => count - 1,
            _ => count,
        };
        let left = remaining - 1;
        (left >= after && (after > 0 || left == 0)).then_some(after)
    }

    /// Places a tile.
    pub(crate) fn place<A: Algebra<Len = L>>(&mut self, alg: &mut A, mv: Placement) {
        let i = mv.tier as usize;
        let count = self.tiers.len();
        let Tier { floor, wall, .. } = self.tiers[i].clone();
        let (width, height) = match (mv.fit, mv.tall) {
            (Fit::Inside, tall) => {
                let side = alg.fresh();
                if A::CONSTRAINED {
                    alg.positive(side.clone());
                }
                let long = alg.mul_x(&side);
                if tall { (side, long) } else { (long, side) }
            }
            (Fit::FullHeight, false) => (alg.mul_x(&wall), wall.clone()),
            (Fit::FullHeight, true) => (alg.div_x(&wall), wall.clone()),
            (Fit::FullWidth, false) => (floor.clone(), alg.div_x(&floor)),
            (Fit::FullWidth, true) => (floor.clone(), alg.mul_x(&floor)),
            (Fit::Full, false) => {
                let long = alg.mul_x(&wall);
                let eq = alg.sub(&floor, &long);
                alg.vanishes(eq);
                (floor.clone(), wall.clone())
            }
            (Fit::Full, true) => {
                let long = alg.mul_x(&floor);
                let eq = alg.sub(&wall, &long);
                alg.vanishes(eq);
                (floor.clone(), wall.clone())
            }
        };
        let narrow = matches!(mv.fit, Fit::Inside | Fit::FullHeight);
        let low = matches!(mv.fit, Fit::Inside | Fit::FullWidth);
        if A::CONSTRAINED {
            match mv.fit {
                Fit::Inside => {}
                Fit::FullHeight => alg.positive(wall.clone()),
                Fit::FullWidth | Fit::Full => alg.positive(floor.clone()),
            }
        }
        for t in self.tiers[..i].iter_mut() {
            t.stale = true;
        }
        if !low && i > 0 {
            let prev = &mut self.tiers[i - 1];
            prev.stale = false;
            prev.floor = alg.add(&prev.floor, &width);
        }
        if !narrow && i + 1 < count {
            let below = &mut self.tiers[i + 1];
            below.wall = alg.add(&below.wall, &height);
        }
        match mv.fit {
            Fit::Inside => {
                let above = Tier {
                    wall: alg.sub(&wall, &height),
                    floor: width.clone(),
                    stale: false,
                    started: false,
                };
                let beside = Tier {
                    floor: alg.sub(&floor, &width),
                    wall: height,
                    stale: false,
                    started: true,
                };
                self.tiers[i] = above;
                self.tiers.insert(i + 1, beside);
            }
            Fit::FullHeight => {
                self.tiers[i] = Tier {
                    floor: alg.sub(&floor, &width),
                    wall,
                    stale: false,
                    started: true,
                };
            }
            Fit::FullWidth => {
                self.tiers[i] = Tier {
                    floor,
                    wall: alg.sub(&wall, &height),
                    stale: false,
                    started: false,
                };
            }
            Fit::Full => {
                self.tiers.remove(i);
            }
        }
    }
}

/// Algebra of lengths that carry no information, for purely combinatorial enumeration.
pub(crate) struct Unit;

impl Algebra for Unit {
    type Len = ();
    const CONSTRAINED: bool = false;
    fn fresh(&mut self) {}
    fn add(&mut self, _: &(), _: &()) {}
    fn sub(&mut self, _: &(), _: &()) {}
    fn mul_x(&mut self, _: &()) {}
    fn div_x(&mut self, _: &()) {}
    fn positive(&mut self, _: ()) {}
    fn vanishes(&mut self, _: ()) {}
}

/// Counts the complete placement sequences for the given number of tiles, disregarding orientations.
pub fn count_layouts(tiles: usize) -> u64 {
    fn rec(stairs: &Staircase<()>, remaining: usize) -> u64 {
        if stairs.tiers.is_empty() {
            return 1;
        }
        let mut total = 0;
        for tier in 0..stairs.tiers.len() {
            for fit in FITS {
                let mv = Placement {
                    tier: tier as u8,
                    fit,
                    tall: false,
                };
                if stairs.admits(mv, remaining).is_some() {
                    let mut next = stairs.clone();
                    next.place(&mut Unit, mv);
                    total += rec(&next, remaining - 1);
                }
            }
        }
        total
    }
    rec(&Staircase::new((), ()), tiles)
}
