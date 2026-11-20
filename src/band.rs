// SPDX-License-Identifier: LGPL-3.0-or-later

//! Bands of proportions, which split a search into independent passes.

use crate::roots::{Dyadic, RealRoot};
use num_bigint::BigInt;
use std::cmp::Ordering;

/// The number of cells of the grid from which bands are assembled.
pub const CELLS: usize = 64;

const SCALE_BITS: i64 = 16;

/// Lower ends of the cells, each a multiple of `2^-16`, which split the proportions of tilings of a square by eleven tiles into equal parts.
const GRID: [f64; CELLS] = [
    1.0,
    1.030487060546875,
    1.0513916015625,
    1.0726470947265625,
    1.0939483642578125,
    1.11578369140625,
    1.138336181640625,
    1.1610565185546875,
    1.184417724609375,
    1.208343505859375,
    1.2328033447265625,
    1.2571258544921875,
    1.2836151123046875,
    1.3086395263671875,
    1.3353424072265625,
    1.3612518310546875,
    1.3864593505859375,
    1.410491943359375,
    1.435150146484375,
    1.462005615234375,
    1.4901275634765625,
    1.518402099609375,
    1.5459136962890625,
    1.57342529296875,
    1.60064697265625,
    1.6280975341796875,
    1.65606689453125,
    1.6838226318359375,
    1.712860107421875,
    1.7432098388671875,
    1.7776336669921875,
    1.8083343505859375,
    1.83929443359375,
    1.8732452392578125,
    1.9110107421875,
    1.9541015625,
    2.0037384033203125,
    2.050537109375,
    2.0954437255859375,
    2.1400299072265625,
    2.183990478515625,
    2.2295074462890625,
    2.2766876220703125,
    2.3221893310546875,
    2.369354248046875,
    2.4173431396484375,
    2.4673919677734375,
    2.5200347900390625,
    2.575408935546875,
    2.633697509765625,
    2.6955108642578125,
    2.7618560791015625,
    2.8322601318359375,
    2.9101409912109375,
    3.0066986083984375,
    3.1162567138671875,
    3.22552490234375,
    3.3359832763671875,
    3.459197998046875,
    3.601165771484375,
    3.7626495361328125,
    3.9914398193359375,
    4.3210296630859375,
    4.7659149169921875,
];

const DEPTH: u32 = 5;

/// Half-open interval of proportions, closed below.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Band {
    lo: f64,
    hi: f64,
}

fn scaled(v: f64) -> BigInt {
    BigInt::from((v * (1u64 << SCALE_BITS) as f64) as i64)
}

/// Bounds on a coefficient as floats.
#[inline]
fn bounds(c: i128) -> (f64, f64) {
    let v = c as f64;
    if c.unsigned_abs() < 1 << 53 { (v, v) } else { (v.next_down(), v.next_up()) }
}

/// Bounds on the values over an interval of non-negative floats of the polynomial with the given coefficients, listed from the leading one.
#[inline]
fn range(coeffs: impl Iterator<Item = i128>, lo: f64, hi: f64) -> (f64, f64) {
    let (mut a, mut b) = (0.0f64, 0.0f64);
    for c in coeffs {
        let (cl, ch) = bounds(c);
        let (pa, pb) = if a >= 0.0 {
            (a * lo, b * hi)
        } else if b <= 0.0 {
            (a * hi, b * lo)
        } else {
            (a * hi, b * hi)
        };
        a = (pa.next_down() + cl).next_down();
        b = (pb.next_up() + ch).next_up();
    }
    (a, b)
}

fn rootless(key: &[i64], lo: f64, hi: f64, depth: u32) -> bool {
    let whole = || key.iter().map(|&c| c as i128);
    let (a, b) = range(whole(), lo, hi);
    if a > 0.0 || b < 0.0 {
        return true;
    }
    let d = key.len() - 1;
    let (da, db) = range(key[..d].iter().enumerate().map(|(i, &c)| (d - i) as i128 * c as i128), lo, hi);
    if da > 0.0 || db < 0.0 {
        let (la, lb) = range(whole(), lo, lo);
        let (ha, hb) = range(whole(), hi, hi);
        if (la > 0.0 && ha > 0.0) || (lb < 0.0 && hb < 0.0) {
            return true;
        }
        if (la > 0.0 && hb < 0.0) || (lb < 0.0 && ha > 0.0) {
            return false;
        }
    }
    if depth == 0 {
        return false;
    }
    let mid = 0.5 * (lo + hi);
    rootless(key, lo, mid, depth - 1) && rootless(key, mid, hi, depth - 1)
}

impl Band {
    /// The band with the given index amongst the given number of bands, which must divide the number of cells of the grid.
    pub fn new(index: usize, count: usize) -> Self {
        assert!(count >= 1 && CELLS.is_multiple_of(count), "the number of bands must divide {CELLS}");
        assert!(index < count, "the index of a band must be smaller than the number of bands");
        let step = CELLS / count;
        Band {
            lo: GRID[index * step],
            hi: if index + 1 == count { f64::INFINITY } else { GRID[(index + 1) * step] },
        }
    }

    /// The lower end, which belongs to the band.
    pub fn lower(&self) -> f64 {
        self.lo
    }

    /// The upper end, which does not belong to the band and may be infinite.
    pub fn upper(&self) -> f64 {
        self.hi
    }

    /// Whether the band holds the rational number with the given numerator and positive denominator.
    pub(crate) fn holds_rational(&self, num: &BigInt, den: &BigInt) -> bool {
        let shifted = num << SCALE_BITS as usize;
        shifted >= scaled(self.lo) * den && (self.hi.is_infinite() || shifted < scaled(self.hi) * den)
    }

    /// Whether the band holds the given root of an irreducible polynomial of degree at least two.
    pub(crate) fn holds_root(&self, root: &mut RealRoot) -> bool {
        let below = |root: &mut RealRoot, v: f64| root.cmp_dyadic(&Dyadic::new(scaled(v), -SCALE_BITS)) == Ordering::Less;
        !below(root, self.lo) && (self.hi.is_infinite() || below(root, self.hi))
    }

    /// Whether the non-constant polynomial with the given coefficients, listed from the constant term with neither end zero, is certified to have no root in the band.
    pub(crate) fn excludes(&self, key: &[i64]) -> bool {
        if key.len() < 2 {
            return false;
        }
        let lo = if self.hi.is_infinite() { 0.0 } else { (1.0 / self.hi).next_down() };
        let hi = (1.0 / self.lo).next_up();
        rootless(key, lo, hi, DEPTH)
    }
}
