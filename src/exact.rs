// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exact solution of a complete placement sequence, by symbolic elimination.

use crate::algebraic::{Registry, RootRef};
use crate::cache::PolyCache;
use crate::form::Form;
use crate::int::{Int, take_overflow};
use crate::interval::{Iv, sign_on_interval};
use crate::tilings::{Layout, MAX_LINES, Ranks, Relation, exponents};
use crate::poly::Poly;
use crate::staircase::{Algebra, Placement, Staircase};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use smallvec::SmallVec;
use std::cmp::Ordering;

/// Outcome of the exact solution of one placement sequence with orientations.
#[derive(Default, Debug)]
pub(crate) struct Solved {
    /// Identifiers of the proportions realised by the sequence.
    pub(crate) feasible: SmallVec<[u32; 2]>,
    /// Whether the proportion equation has a root not smaller than one.
    pub(crate) candidate: bool,
    /// Number of singular situations met.
    pub(crate) singular: u64,
    /// Whether the aspect ratio of the main rectangle does not depend on the proportion.
    pub(crate) constant: bool,
    /// Whether arbitrary precision was required.
    pub(crate) overflow: bool,
}

struct Symbolic<C: Int> {
    unknowns: usize,
    equations: Vec<Form<C>>,
    positives: Vec<Form<C>>,
}

impl<C: Int> Algebra for Symbolic<C> {
    type Len = Form<C>;
    const CONSTRAINED: bool = true;
    fn fresh(&mut self) -> Form<C> {
        self.unknowns += 1;
        Form::unknown(1 + self.unknowns)
    }
    fn add(&mut self, a: &Form<C>, b: &Form<C>) -> Form<C> {
        a.add(b)
    }
    fn sub(&mut self, a: &Form<C>, b: &Form<C>) -> Form<C> {
        a.sub(b)
    }
    fn mul_x(&mut self, a: &Form<C>) -> Form<C> {
        a.mul_x()
    }
    fn div_x(&mut self, a: &Form<C>) -> Form<C> {
        a.div_x()
    }
    fn positive(&mut self, a: Form<C>) {
        self.positives.push(a);
    }
    fn vanishes(&mut self, a: Form<C>) {
        self.equations.push(a);
    }
}

fn sign_at<C: Int>(registry: &Registry, root: &RootRef, q: &Poly<C>) -> i32 {
    if q.is_zero() {
        return 0;
    }
    let shifted = q.taylor_shift_one();
    if shifted.sign_variations() == 0 && !shifted.coeffs()[0].is_zero() {
        return shifted.coeffs()[0].signum();
    }
    match sign_on_interval(q, root.lo, root.hi) {
        Some(s) => s,
        None => registry.sign_at(root.id, &q.to_big()),
    }
}

/// The linear system of a complete placement sequence, with the sides tested for positivity.
fn system<C: Int>(path: &[Placement]) -> Symbolic<C> {
    let mut alg: Symbolic<C> = Symbolic {
        unknowns: 0,
        equations: Vec::new(),
        positives: Vec::new(),
    };
    let mut stairs = Staircase::new(Form::unknown(1), Form::unknown(0));
    for &mv in path {
        stairs.place(&mut alg, mv);
    }
    debug_assert!(stairs.tiers.is_empty());
    debug_assert_eq!(alg.equations.len(), alg.unknowns + 1);
    alg
}

/// The triangular form of a linear system by fraction-free elimination, unless the system is singular.
fn reduce<C: Int>(alg: &Symbolic<C>) -> Option<Vec<Vec<Poly<C>>>> {
    let k = alg.unknowns;
    let m = k + 1;
    let mut a: Vec<Vec<Poly<C>>> = alg
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
        let pivot = (i..m).filter(|&r| !a[r][i].is_zero()).min_by_key(|&r| a[r][i].degree())?;
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
    Some(a)
}

/// The numerators of the unknowns of a triangular system over its determinant, the width of the main rectangle last.
fn back_substitute<C: Int>(a: &[Vec<Poly<C>>]) -> Vec<Poly<C>> {
    let m = a.len();
    let k = m - 1;
    let det = &a[k][k];
    let mut sol: Vec<Poly<C>> = vec![Poly::zero(); m];
    sol[k] = a[k][m].clone();
    for i in (0..k).rev() {
        let mut v = det.mul(&a[i][m]);
        for j in i + 1..m {
            v = v.sub(&a[i][j].mul(&sol[j]));
        }
        sol[i] = v.div_exact(&a[i][i]);
    }
    sol
}

/// The numerator over the determinant of a linear form, disregarding the power of the proportion that divides the form.
fn numerator<C: Int>(f: &Form<C>, det: &Poly<C>, sol: &[Poly<C>]) -> Poly<C> {
    let k = sol.len() - 1;
    let mut q = f.coeff(0).mul(det).add(&f.coeff(1).mul(&sol[k]));
    for (j, c) in f.coeffs().iter().enumerate().skip(2) {
        q = q.add(&c.mul(&sol[j - 2]));
    }
    q
}

fn solve_in<C: Int>(width: i64, height: i64, registry: &Registry, cache: &PolyCache, path: &[Placement]) -> Solved {
    let mut out = Solved::default();
    let alg: Symbolic<C> = system(path);
    let k = alg.unknowns;
    let m = k + 1;
    let Some(a) = reduce(&alg) else {
        out.singular += 1;
        return out;
    };
    let det = a[k][k].clone();
    let main = a[k][m].clone();
    let target = main.scale(&C::from_i64(height)).sub(&det.scale(&C::from_i64(width)));
    if target.is_zero() {
        out.constant = true;
        return out;
    }
    let shifted = target.taylor_shift_one();
    if shifted.sign_variations() == 0 && !shifted.coeffs()[0].is_zero() {
        return out;
    }
    let roots = cache.roots_big(&target.to_big().primitive(), registry);
    if roots.is_empty() {
        return out;
    }
    out.candidate = true;
    let sol = back_substitute(&a);
    let numerators: Vec<Poly<C>> = alg.positives.iter().map(|f| numerator(f, &det, &sol)).collect();
    for root in roots.iter() {
        let sd = sign_at(registry, root, &det);
        if sd == 0 {
            out.singular += 1;
            continue;
        }
        if numerators.iter().all(|q| sign_at(registry, root, q) == sd) {
            out.feasible.push(root.id);
        }
    }
    out
}

/// Solves a complete placement sequence exactly, for a main rectangle with the given integer sides.
pub(crate) fn solve(width: i64, height: i64, registry: &Registry, cache: &PolyCache, path: &[Placement]) -> Solved {
    take_overflow();
    let out = solve_in::<i64>(width, height, registry, cache, path);
    if take_overflow() {
        let mut out = solve_in::<BigInt>(width, height, registry, cache, path);
        out.overflow = true;
        return out;
    }
    out
}

/// Exact coordinates of a tiling at a proportion, as numerators over a common positive or negative denominator.
struct Solution<C: Int> {
    /// The coordinates of the vertical and of the horizontal lines of the layout.
    lines: [Vec<Poly<C>>; 2],
    /// The short sides of the tiles.
    shorts: Vec<Poly<C>>,
    /// The common denominator.
    den: Poly<C>,
    /// The sign of the common denominator at the proportion.
    sign: i32,
}

fn solution_in<C: Int>(registry: &Registry, root: &RootRef, path: &[Placement], layout: &Layout) -> Option<Solution<C>> {
    let alg: Symbolic<C> = system(path);
    let a = reduce(&alg)?;
    let k = alg.unknowns;
    let det = a[k][k].clone();
    let sol = back_substitute(&a);
    let sign = sign_at(registry, root, &det);
    if sign == 0 {
        return None;
    }
    let shift = alg.positives.iter().map(|f| f.den()).max().unwrap_or(0) as i32 + 1;
    let sizes: Vec<Poly<C>> = alg.positives.iter().map(|f| numerator(f, &det, &sol)).collect();
    let scaled = |q: usize, e: i32| sizes[q].shift((shift - alg.positives[q].den() as i32 + e) as usize);
    let mut shorts = Vec::with_capacity(path.len());
    let mut lines = [vec![Poly::zero(), sol[k].shift(shift as usize)], vec![Poly::zero(), det.shift(shift as usize)]];
    for (q, &mv) in path.iter().enumerate() {
        let (ex, ey, es) = exponents(mv);
        let [left, right, bottom, top] = layout.sides[q].map(|v| v as usize);
        if right == lines[0].len() {
            let v = lines[0][left].add(&scaled(q, ex));
            lines[0].push(v);
        }
        if top == lines[1].len() {
            let v = lines[1][bottom].add(&scaled(q, ey));
            lines[1].push(v);
        }
        shorts.push(scaled(q, es));
    }
    Some(Solution {
        lines,
        shorts,
        den: det.shift(shift as usize),
        sign,
    })
}

fn ranks_in<C: Int>(registry: &Registry, root: &RootRef, path: &[Placement], layout: &Layout, hints: Option<&[[Iv; MAX_LINES]; 2]>) -> Option<Ranks> {
    let solution: Solution<C> = solution_in(registry, root, path, layout)?;
    let mut ranks = [[0u8; MAX_LINES]; 2];
    for d in 0..2 {
        let coords = &solution.lines[d];
        let compare = |&a: &u8, &b: &u8| {
            if let Some(hints) = hints {
                let (ia, ib) = (hints[d][a as usize], hints[d][b as usize]);
                if ia.hi < ib.lo {
                    return Ordering::Less;
                }
                if ib.hi < ia.lo {
                    return Ordering::Greater;
                }
            }
            (solution.sign * sign_at(registry, root, &coords[a as usize].sub(&coords[b as usize]))).cmp(&0)
        };
        let mut order: Vec<u8> = (0..coords.len() as u8).collect();
        order.sort_by(compare);
        let mut rank = 0;
        for (i, &line) in order.iter().enumerate() {
            if i > 0 && compare(&order[i - 1], &line) != Ordering::Equal {
                rank += 1;
            }
            ranks[d][line as usize] = rank;
        }
    }
    Some(Ranks { x: ranks[0], y: ranks[1] })
}

/// The positions of the lines of a tiling in the order of their coordinates, decided by exact arithmetic wherever the given enclosures do not separate two coordinates.
pub(crate) fn ranks(registry: &Registry, root: &RootRef, path: &[Placement], layout: &Layout, hints: Option<&[[Iv; MAX_LINES]; 2]>) -> Option<Ranks> {
    take_overflow();
    let out = ranks_in::<i64>(registry, root, path, layout, hints);
    if take_overflow() {
        return ranks_in::<BigInt>(registry, root, path, layout, hints);
    }
    out
}

fn related_in<C: Int>(registry: &Registry, root: &RootRef, path: &[Placement], layout: &Layout, relations: &[Relation]) -> Option<bool> {
    let solution: Solution<C> = solution_in(registry, root, path, layout)?;
    Some(relations.iter().all(|r| {
        let first = &solution.lines[r.first.0][r.first.1 as usize];
        let second = &solution.lines[r.second.0][r.second.1 as usize];
        let target = if r.reflected { solution.lines[r.second.0][1].sub(second) } else { second.clone() };
        sign_at(registry, root, &first.sub(&target)) == 0
    }))
}

/// Whether all the given relations hold between the coordinates of the lines of a tiling.
pub(crate) fn related(registry: &Registry, root: &RootRef, path: &[Placement], layout: &Layout, relations: &[Relation]) -> Option<bool> {
    take_overflow();
    let out = related_in::<i64>(registry, root, path, layout, relations);
    if take_overflow() {
        return related_in::<BigInt>(registry, root, path, layout, relations);
    }
    out
}

fn value<C: Int>(p: &Poly<C>, x: f64) -> f64 {
    p.coeffs().iter().rev().fold(0.0, |acc, c| acc * x + c.to_big().to_f64().unwrap_or(f64::NAN))
}

/// Approximations of the left side, bottom side, width and height of each tile of a tiling.
pub(crate) fn coordinates(registry: &Registry, root: &RootRef, path: &[Placement]) -> Option<Vec<[f64; 4]>> {
    let layout = Layout::new(path);
    let solution: Solution<BigInt> = solution_in(registry, root, path, &layout)?;
    let x = 0.5 * (root.lo + root.hi);
    let den = value(&solution.den, x);
    let at = |d: usize, line: u8| value(&solution.lines[d][line as usize], x) / den;
    Some(
        (0..path.len())
            .map(|q| {
                let [left, right, bottom, top] = layout.sides[q];
                [at(0, left), at(1, bottom), at(0, right) - at(0, left), at(1, top) - at(1, bottom)]
            })
            .collect(),
    )
}

/// The short sides of the tiles of a tiling, as numerators over a common denominator with machine-integer coefficients.
pub(crate) struct Measures {
    pub(crate) shorts: Vec<Vec<i64>>,
    pub(crate) den: Vec<i64>,
}

/// The short sides of the tiles of the tiling realised by a placement sequence at a proportion, unless they exceed machine integers.
pub(crate) fn measures(registry: &Registry, root: &RootRef, path: &[Placement]) -> Option<Measures> {
    take_overflow();
    let solution: Option<Solution<i64>> = solution_in(registry, root, path, &Layout::new(path));
    if take_overflow() {
        return None;
    }
    let solution = solution?;
    Some(Measures {
        shorts: solution.shorts.iter().map(|s| s.coeffs().to_vec()).collect(),
        den: solution.den.coeffs().to_vec(),
    })
}
