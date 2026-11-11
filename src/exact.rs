// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exact solution of a complete placement sequence, by symbolic elimination.

use crate::algebraic::{Registry, RootRef};
use crate::cache::PolyCache;
use crate::form::Form;
use crate::int::{Int, take_overflow};
use crate::interval::sign_on_interval;
use crate::poly::Poly;
use crate::staircase::{Algebra, Placement, Staircase};
use num_bigint::BigInt;
use smallvec::SmallVec;

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

fn solve_in<C: Int>(width: i64, height: i64, registry: &Registry, cache: &PolyCache, path: &[Placement]) -> Solved {
    let mut out = Solved::default();
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
    let k = alg.unknowns;
    let m = k + 1;
    debug_assert_eq!(alg.equations.len(), m);
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
        let Some(pivot) = (i..m).filter(|&r| !a[r][i].is_zero()).min_by_key(|&r| a[r][i].degree()) else {
            out.singular += 1;
            return out;
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
    let mut sol: Vec<Poly<C>> = vec![Poly::zero(); m];
    sol[k] = main;
    for i in (0..k).rev() {
        let mut v = det.mul(&a[i][m]);
        for j in i + 1..m {
            v = v.sub(&a[i][j].mul(&sol[j]));
        }
        sol[i] = v.div_exact(&a[i][i]);
    }
    let numerators: Vec<Poly<C>> = alg
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
