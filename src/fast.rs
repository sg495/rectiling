// SPDX-License-Identifier: LGPL-3.0-or-later

//! Depth-first search with eager fraction-free elimination and certified numerical checks.

use crate::algebraic::{Registry, RootRef};
use crate::cache::{PolyCache, Roots, WordMap};
use crate::exact;
use crate::interval::Iv;
use crate::search::{Shared, Tally, encode_witness, within};
use crate::staircase::{Algebra, FITS, Fit, Placement, Staircase, Unit};
use smallvec::SmallVec;

const SLOTS: usize = 8;
const NO_SLOT: u8 = u8::MAX;
const LIMIT: i128 = 1 << 55;
const LOCAL_CACHE_LIMIT: usize = 1 << 19;

/// Linear form in the scale of the main rectangle and the free tile sides, as identifiers of coefficient polynomials.
type Form = [u32; SLOTS];

#[derive(Clone, Copy)]
struct Head {
    start: u32,
    len: u16,
    lo: i16,
}

/// Stack of Laurent polynomials with machine-integer coefficients.
struct Arena {
    coeffs: Vec<i64>,
    heads: Vec<Head>,
    scratch: Vec<i128>,
    quotient: Vec<i128>,
    failed: bool,
}

impl Arena {
    fn new() -> Self {
        Arena {
            coeffs: Vec::with_capacity(1 << 16),
            heads: vec![Head { start: 0, len: 0, lo: 0 }],
            scratch: Vec::new(),
            quotient: Vec::new(),
            failed: false,
        }
    }

    fn mark(&self) -> (usize, usize) {
        (self.coeffs.len(), self.heads.len())
    }

    fn reset(&mut self, mark: (usize, usize)) {
        self.coeffs.truncate(mark.0);
        self.heads.truncate(mark.1);
        self.failed = false;
    }

    #[inline]
    fn slice(&self, id: u32) -> (&[i64], i32) {
        let h = self.heads[id as usize];
        (&self.coeffs[h.start as usize..h.start as usize + h.len as usize], h.lo as i32)
    }

    fn constant(&mut self, v: i64) -> u32 {
        self.push_words(&[v as i128], 0)
    }

    fn push_words(&mut self, data: &[i128], lo: i32) -> u32 {
        let mut a = 0;
        let mut b = data.len();
        while a < b && data[a] == 0 {
            a += 1;
        }
        while b > a && data[b - 1] == 0 {
            b -= 1;
        }
        if a == b {
            return 0;
        }
        let lo = lo + a as i32;
        if b - a > u16::MAX as usize || lo.abs() > i16::MAX as i32 / 2 {
            self.failed = true;
            return 0;
        }
        let start = self.coeffs.len() as u32;
        for &v in &data[a..b] {
            if v.abs() >= LIMIT {
                self.failed = true;
                self.coeffs.truncate(start as usize);
                return 0;
            }
            self.coeffs.push(v as i64);
        }
        self.heads.push(Head {
            start,
            len: (b - a) as u16,
            lo: lo as i16,
        });
        (self.heads.len() - 1) as u32
    }

    fn shift(&mut self, a: u32, k: i16) -> u32 {
        if a == 0 {
            return 0;
        }
        let h = self.heads[a as usize];
        self.heads.push(Head { lo: h.lo + k, ..h });
        (self.heads.len() - 1) as u32
    }

    fn combine(&mut self, a: u32, b: u32, sign: i128) -> u32 {
        if b == 0 {
            return a;
        }
        if a == 0 && sign == 1 {
            return b;
        }
        let mut scratch = std::mem::take(&mut self.scratch);
        let (ca, la) = self.slice(a);
        let (cb, lb) = self.slice(b);
        let lo = if a == 0 { lb } else { la.min(lb) };
        let hi = (la + ca.len() as i32).max(lb + cb.len() as i32);
        scratch.clear();
        scratch.resize((hi - lo) as usize, 0);
        for (i, &v) in ca.iter().enumerate() {
            scratch[(la - lo) as usize + i] = v as i128;
        }
        for (i, &v) in cb.iter().enumerate() {
            scratch[(lb - lo) as usize + i] += sign * v as i128;
        }
        let id = self.push_words(&scratch, lo);
        self.scratch = scratch;
        id
    }

    fn accumulate(scratch: &mut [i128], base: i32, a: (&[i64], i32), b: (&[i64], i32), sign: i128) {
        let off = (a.1 + b.1 - base) as usize;
        for (i, &x) in a.0.iter().enumerate() {
            let x = sign * x as i128;
            for (j, &y) in b.0.iter().enumerate() {
                scratch[off + i + j] += x * y as i128;
            }
        }
    }

    /// The polynomial `(p * f - g * e) / d`, the division being exact.
    fn fused(&mut self, p: u32, f: u32, g: u32, e: u32, d: u32) -> u32 {
        let first = p != 0 && f != 0;
        let second = g != 0 && e != 0;
        if !first && !second {
            return 0;
        }
        let mut scratch = std::mem::take(&mut self.scratch);
        let mut quotient = std::mem::take(&mut self.quotient);
        let (sp, sf, sg, se) = (self.slice(p), self.slice(f), self.slice(g), self.slice(e));
        let mut lo = i32::MAX;
        let mut hi = i32::MIN;
        if first {
            lo = lo.min(sp.1 + sf.1);
            hi = hi.max(sp.1 + sf.1 + (sp.0.len() + sf.0.len()) as i32 - 1);
        }
        if second {
            lo = lo.min(sg.1 + se.1);
            hi = hi.max(sg.1 + se.1 + (sg.0.len() + se.0.len()) as i32 - 1);
        }
        scratch.clear();
        scratch.resize((hi - lo) as usize, 0);
        if first {
            Self::accumulate(&mut scratch, lo, sp, sf, 1);
        }
        if second {
            Self::accumulate(&mut scratch, lo, sg, se, -1);
        }
        let (cd, ld) = self.slice(d);
        let mut ok = true;
        let from_quotient = !(cd.len() == 1 && cd[0].abs() == 1);
        if !from_quotient {
            if cd[0] < 0 {
                for v in scratch.iter_mut() {
                    *v = -*v;
                }
            }
        } else {
            let mut top = scratch.len();
            while top > 0 && scratch[top - 1] == 0 {
                top -= 1;
            }
            let dn = cd.len();
            let lead = cd[dn - 1] as i128;
            quotient.clear();
            if top == 0 {
            } else if top < dn {
                ok = false;
            } else {
                quotient.resize(top - dn + 1, 0);
                for i in (0..=top - dn).rev() {
                    let v = scratch[i + dn - 1];
                    let q = v / lead;
                    if q * lead != v || q.abs() >= LIMIT {
                        ok = false;
                        break;
                    }
                    if q != 0 {
                        for (j, &c) in cd.iter().enumerate() {
                            scratch[i + j] -= q * c as i128;
                        }
                    }
                    quotient[i] = q;
                }
                ok = ok && scratch[..dn - 1].iter().all(|&v| v == 0);
            }
        }
        let id = if !ok {
            self.failed = true;
            0
        } else if from_quotient {
            self.push_words(&quotient, lo - ld)
        } else {
            self.push_words(&scratch, lo - ld)
        };
        self.scratch = scratch;
        self.quotient = quotient;
        id
    }

    /// Encloses the value of a polynomial over an interval of positive floats.
    ///
    /// The parts with positive and with negative coefficients are evaluated separately at both endpoints; each is a sum of non-negative terms, so its relative rounding error is bounded in terms of its length.
    fn eval(&self, id: u32, x: Iv) -> Option<Iv> {
        let (c, lo) = self.slice(id);
        let (mut pl, mut ph, mut nl, mut nh) = (0.0f64, 0.0f64, 0.0f64, 0.0f64);
        for &v in c.iter().rev() {
            if v.unsigned_abs() > 1 << 53 {
                return None;
            }
            let (p, n) = if v >= 0 { (v as f64, 0.0) } else { (0.0, -(v as f64)) };
            pl = pl * x.lo + p;
            ph = ph * x.hi + p;
            nl = nl * x.lo + n;
            nh = nh * x.hi + n;
        }
        let e = (2 * c.len() + 2) as f64 * f64::EPSILON;
        let acc = Iv {
            lo: (pl * (1.0 - e) - nh * (1.0 + e)).next_down(),
            hi: (ph * (1.0 + e) - nl * (1.0 - e)).next_up(),
        };
        Some(if lo == 0 { acc } else { acc.mul(x.powi(lo)) })
    }
}

struct Symbols {
    arena: Arena,
    used: u8,
    pivot: u32,
    pending: Option<Form>,
    fresh_slot: u8,
    fresh_form: Form,
}

impl Algebra for Symbols {
    type Len = Form;
    const CONSTRAINED: bool = false;
    fn fresh(&mut self) -> Form {
        let slot = (!self.used).trailing_zeros() as usize;
        let mut f = [0; SLOTS];
        if slot >= SLOTS {
            self.arena.failed = true;
            return f;
        }
        self.used |= 1 << slot;
        self.fresh_slot = slot as u8;
        f[slot] = self.pivot;
        self.fresh_form = f;
        f
    }
    fn add(&mut self, a: &Form, b: &Form) -> Form {
        std::array::from_fn(|i| self.arena.combine(a[i], b[i], 1))
    }
    fn sub(&mut self, a: &Form, b: &Form) -> Form {
        std::array::from_fn(|i| self.arena.combine(a[i], b[i], -1))
    }
    fn mul_x(&mut self, a: &Form) -> Form {
        std::array::from_fn(|i| self.arena.shift(a[i], 1))
    }
    fn div_x(&mut self, a: &Form) -> Form {
        std::array::from_fn(|i| self.arena.shift(a[i], -1))
    }
    fn positive(&mut self, _: Form) {}
    fn vanishes(&mut self, a: Form) {
        self.pending = Some(a);
    }
}

struct Numeric<'s> {
    x: Iv,
    sides: &'s [Iv],
    next: usize,
    tile: u8,
    violated: bool,
    unsure: SmallVec<[u8; 4]>,
}

impl Algebra for Numeric<'_> {
    type Len = Iv;
    const CONSTRAINED: bool = true;
    fn fresh(&mut self) -> Iv {
        self.next += 1;
        self.sides[self.next - 1]
    }
    fn add(&mut self, a: &Iv, b: &Iv) -> Iv {
        a.add(*b)
    }
    fn sub(&mut self, a: &Iv, b: &Iv) -> Iv {
        a.sub(*b)
    }
    fn mul_x(&mut self, a: &Iv) -> Iv {
        a.mul(self.x)
    }
    fn div_x(&mut self, a: &Iv) -> Iv {
        a.div(self.x)
    }
    fn positive(&mut self, a: Iv) {
        if a.hi <= 0.0 {
            self.violated = true;
        } else if !(a.lo > 0.0) {
            self.unsure.push(self.tile);
        }
        self.tile += 1;
    }
    fn vanishes(&mut self, _: Iv) {}
}

#[derive(Clone, Copy)]
struct Step {
    mv: Placement,
    slot: u8,
    /// The side of the tile on which positivity is tested, at the stage of elimination current when it was placed.
    size: Form,
    /// The equation, the eliminated slot and the previous pivot of the elimination that followed the placement.
    eliminated: Option<(Form, u8, u32)>,
}

enum Verdict {
    Accept,
    Reject,
    Unsure,
}

/// Search engine owned by one thread.
pub(crate) struct Engine<'a> {
    width: i64,
    height: i64,
    tiles: usize,
    minority: usize,
    registry: &'a Registry,
    cache: &'a PolyCache,
    shared: &'a Shared,
    symbols: Symbols,
    path: Vec<Step>,
    local: WordMap<Box<[i64]>, Roots>,
    min_polys: WordMap<u32, Box<[i64]>>,
    key: Vec<i64>,
    scratch: Vec<u8>,
    tally: Tally,
}

impl Drop for Engine<'_> {
    fn drop(&mut self) {
        self.tally.flush(self.shared, true);
    }
}

impl<'a> Engine<'a> {
    pub(crate) fn new(tiles: usize, width: i64, height: i64, minority: usize, registry: &'a Registry, cache: &'a PolyCache, shared: &'a Shared) -> Self {
        Engine {
            width,
            height,
            tiles,
            minority,
            registry,
            cache,
            shared,
            symbols: Symbols {
                arena: Arena::new(),
                used: 1,
                pivot: 0,
                pending: None,
                fresh_slot: NO_SLOT,
                fresh_form: [0; SLOTS],
            },
            path: Vec::new(),
            local: WordMap::default(),
            min_polys: WordMap::default(),
            key: Vec::new(),
            scratch: Vec::new(),
            tally: Tally::default(),
        }
    }

    /// Explores every completion of the given sequence of placements.
    pub(crate) fn run(&mut self, prefix: &[Placement]) {
        let mark = self.symbols.arena.mark();
        let one = self.symbols.arena.constant(1);
        let w = self.symbols.arena.constant(self.width);
        let h = self.symbols.arena.constant(self.height);
        let mut floor = [0; SLOTS];
        let mut wall = [0; SLOTS];
        floor[0] = w;
        wall[0] = h;
        self.path.clear();
        self.explore(&Staircase::new(floor, wall), self.tiles, 1, one, prefix);
        self.symbols.arena.reset(mark);
        self.tally.flush(self.shared, false);
    }

    fn explore(&mut self, stairs: &Staircase<Form>, remaining: usize, used: u8, pivot: u32, prefix: &[Placement]) {
        let depth = self.path.len();
        let forced = prefix.get(depth).copied();
        let talls = if 2 * self.minority < self.tiles { self.path.iter().filter(|s| s.mv.tall).count() } else { 0 };
        if remaining == 1 && forced.is_none() && depth > 0 && self.last(stairs, talls) {
            return;
        }
        for tier in 0..stairs.tiers.len() {
            for fit in FITS {
                let probe = Placement {
                    tier: tier as u8,
                    fit,
                    tall: false,
                };
                if stairs.admits(probe, remaining).is_none() {
                    continue;
                }
                for tall in [false, true] {
                    let mv = Placement { tall, ..probe };
                    if forced.is_some_and(|f| f != mv) {
                        continue;
                    }
                    if tall && depth == 0 && self.width == self.height {
                        continue;
                    }
                    if !within(self.minority, talls + tall as usize, depth + 1) {
                        continue;
                    }
                    self.step(stairs, remaining, used, pivot, prefix, mv);
                }
            }
        }
    }

    /// Treats both orientations of the last tile directly, if the staircase has the expected shape.
    fn last(&mut self, stairs: &Staircase<Form>, talls: usize) -> bool {
        let tier = &stairs.tiers[0];
        if stairs.tiers.len() != 1 || tier.stale || tier.floor[0] == 0 || tier.wall[0] == 0 {
            return false;
        }
        if tier.floor[1..].iter().chain(tier.wall[1..].iter()).any(|&e| e != 0) {
            return false;
        }
        let (floor, wall) = (tier.floor[0], tier.wall[0]);
        for tall in [false, true] {
            if !within(self.minority, talls + tall as usize, self.tiles) {
                continue;
            }
            let (plain, scaled) = if tall { (wall, floor) } else { (floor, wall) };
            let (cp, lp) = self.symbols.arena.slice(plain);
            let (cs, ls) = self.symbols.arena.slice(scaled);
            let ls = ls + 1;
            let lo = lp.min(ls);
            let hi = (lp + cp.len() as i32).max(ls + cs.len() as i32);
            self.key.clear();
            self.key.resize((hi - lo) as usize, 0);
            for (i, &c) in cp.iter().enumerate() {
                self.key[(lp - lo) as usize + i] = c;
            }
            for (i, &c) in cs.iter().enumerate() {
                self.key[(ls - lo) as usize + i] -= c;
            }
            self.path.push(Step {
                mv: Placement {
                    tier: 0,
                    fit: Fit::Full,
                    tall,
                },
                slot: NO_SLOT,
                size: tier.floor,
                eliminated: None,
            });
            self.tally.stats.leaves += 1;
            self.finish();
            self.path.pop();
        }
        true
    }

    fn step(&mut self, stairs: &Staircase<Form>, remaining: usize, used: u8, pivot: u32, prefix: &[Placement], mv: Placement) {
        let mark = self.symbols.arena.mark();
        self.symbols.used = used;
        self.symbols.pivot = pivot;
        self.symbols.pending = None;
        self.symbols.fresh_slot = NO_SLOT;
        let mut next = stairs.clone();
        next.place(&mut self.symbols, mv);
        let tier = &stairs.tiers[mv.tier as usize];
        let mut step = Step {
            mv,
            slot: self.symbols.fresh_slot,
            size: match mv.fit {
                Fit::Inside => self.symbols.fresh_form,
                Fit::FullHeight => tier.wall,
                Fit::FullWidth | Fit::Full => tier.floor,
            },
            eliminated: None,
        };
        let mut used = self.symbols.used;
        let mut pivot = pivot;
        let mut ok = !self.symbols.arena.failed;
        let pending = self.symbols.pending;
        if ok && next.tiers.is_empty() {
            let eq = pending.expect("final placement is full");
            self.path.push(step);
            self.leaf(eq);
            self.path.pop();
            self.symbols.arena.reset(mark);
            return;
        }
        if ok {
            if let Some(eq) = pending {
                let arena = &mut self.symbols.arena;
                let m = (1..SLOTS).filter(|&j| eq[j] != 0).min_by_key(|&j| arena.heads[eq[j] as usize].len);
                match m {
                    None => ok = false,
                    Some(m) => {
                        let lead = eq[m];
                        for t in next.tiers.iter_mut() {
                            for form in [&mut t.floor, &mut t.wall] {
                                let fm = form[m];
                                for j in 0..SLOTS {
                                    if j != m {
                                        form[j] = arena.fused(lead, form[j], fm, eq[j], pivot);
                                    }
                                }
                                form[m] = 0;
                            }
                        }
                        used &= !(1 << m);
                        step.eliminated = Some((eq, m as u8, pivot));
                        pivot = lead;
                        ok = !arena.failed;
                    }
                }
            }
        }
        self.path.push(step);
        if ok {
            self.explore(&next, remaining - 1, used, pivot, prefix);
        } else {
            self.delegate(&next, remaining - 1);
        }
        self.path.pop();
        self.symbols.arena.reset(mark);
    }

    fn delegate(&mut self, stairs: &Staircase<Form>, remaining: usize) {
        let mut moves: Vec<Placement> = self.path.iter().map(|s| s.mv).collect();
        let unit = Staircase {
            tiers: stairs
                .tiers
                .iter()
                .map(|t| crate::staircase::Tier {
                    floor: (),
                    wall: (),
                    stale: t.stale,
                    started: t.started,
                })
                .collect(),
        };
        self.delegate_rec(&unit, remaining, &mut moves);
    }

    fn delegate_rec(&mut self, stairs: &Staircase<()>, remaining: usize, moves: &mut Vec<Placement>) {
        if stairs.tiers.is_empty() {
            self.tally.stats.leaves += 1;
            self.exact(moves);
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
                    if stairs.admits(mv, remaining).is_none() || (tall && moves.is_empty() && self.width == self.height) {
                        continue;
                    }
                    let talls = moves.iter().filter(|m| m.tall).count() + tall as usize;
                    if !within(self.minority, talls, moves.len() + 1) {
                        continue;
                    }
                    let mut next = stairs.clone();
                    next.place(&mut Unit, mv);
                    moves.push(mv);
                    self.delegate_rec(&next, remaining - 1, moves);
                    moves.pop();
                }
            }
        }
    }

    fn exact(&mut self, moves: &[Placement]) {
        let solved = exact::solve(self.width, self.height, self.registry, self.cache, moves);
        let stats = &mut self.tally.stats;
        stats.exact += 1;
        stats.singular += solved.singular;
        stats.constant += solved.constant as u64;
        stats.overflows += solved.overflow as u64;
        stats.candidates += solved.candidate as u64;
        for &id in &solved.feasible {
            self.tally.record(id, || encode_witness(moves.iter().copied()));
        }
    }

    fn roots(&mut self) -> Roots {
        if let Some(r) = self.local.get(self.key.as_slice()) {
            return r.clone();
        }
        let r = self.cache.roots(&self.key, &mut self.scratch, self.registry);
        if self.local.len() >= LOCAL_CACHE_LIMIT {
            self.local.clear();
        }
        self.local.insert(self.key.as_slice().into(), r.clone());
        r
    }

    fn leaf(&mut self, eq: Form) {
        self.tally.stats.leaves += 1;
        if eq[0] == 0 || eq[1..].iter().any(|&e| e != 0) {
            let moves: Vec<Placement> = self.path.iter().map(|s| s.mv).collect();
            self.exact(&moves);
            return;
        }
        let (coeffs, _) = self.symbols.arena.slice(eq[0]);
        self.key.clear();
        self.key.extend_from_slice(coeffs);
        self.finish();
    }

    /// Decides the leaf at the end of the current path, whose proportion equation is held in the key buffer.
    fn finish(&mut self) {
        while self.key.last() == Some(&0) {
            self.key.pop();
        }
        let zeros = self.key.iter().take_while(|&&c| c == 0).count();
        self.key.drain(..zeros);
        if self.key.is_empty() {
            let moves: Vec<Placement> = self.path.iter().map(|s| s.mv).collect();
            self.exact(&moves);
            return;
        }
        if self.key[self.key.len() - 1] < 0 {
            for c in self.key.iter_mut() {
                *c = -*c;
            }
        }
        let n = self.key.len();
        let mut shifted: SmallVec<[i128; 32]> = self.key.iter().map(|&c| c as i128).collect();
        for i in 0..n {
            for j in (i..n - 1).rev() {
                shifted[j] += shifted[j + 1];
            }
        }
        if shifted.iter().all(|&c| c >= 0) && shifted[0] > 0 {
            return;
        }
        let roots = self.roots();
        if roots.is_empty() {
            return;
        }
        let mut accepted: SmallVec<[u32; 2]> = SmallVec::new();
        for root in roots.iter() {
            match self.check(root) {
                Verdict::Accept => accepted.push(root.id),
                Verdict::Reject => {}
                Verdict::Unsure => {
                    let moves: Vec<Placement> = self.path.iter().map(|s| s.mv).collect();
                    self.exact(&moves);
                    return;
                }
            }
        }
        self.tally.stats.candidates += 1;
        for id in accepted {
            let path = &self.path;
            self.tally.record(id, || encode_witness(path.iter().map(|s| s.mv)));
        }
    }

    fn min_poly(&mut self, id: u32) -> Option<&[i64]> {
        if !self.min_polys.contains_key(&id) {
            if self.min_polys.len() >= LOCAL_CACHE_LIMIT {
                self.min_polys.clear();
            }
            let words = self.registry.min_poly_words(id)?;
            self.min_polys.insert(id, words);
        }
        self.min_polys.get(&id).map(|b| &**b)
    }

    /// Whether one of the given tiles is certified to have size exactly zero at the given root.
    fn degenerate(&mut self, root: &RootRef, tiles: &[u8]) -> bool {
        let mark = self.symbols.arena.mark();
        let mut found = false;
        for &q in tiles {
            let mut form = self.path[q as usize].size;
            for step in &self.path[q as usize..] {
                if let Some((eq, m, prev)) = step.eliminated {
                    let m = m as usize;
                    let fm = form[m];
                    for j in 0..SLOTS {
                        if j != m {
                            form[j] = self.symbols.arena.fused(eq[m], form[j], fm, eq[j], prev);
                        }
                    }
                    form[m] = 0;
                }
            }
            if self.symbols.arena.failed || form[1..].iter().any(|&e| e != 0) {
                break;
            }
            if form[0] == 0 {
                found = true;
                break;
            }
            let numerator: SmallVec<[i128; 32]> = self.symbols.arena.slice(form[0]).0.iter().map(|&c| c as i128).collect();
            let Some(divisor) = self.min_poly(root.id) else {
                break;
            };
            if divides(divisor, numerator) {
                found = true;
                break;
            }
        }
        self.symbols.arena.reset(mark);
        found
    }

    fn check(&mut self, root: &RootRef) -> Verdict {
        let x = Iv { lo: root.lo, hi: root.hi };
        let arena = &self.symbols.arena;
        let mut val = [Iv::point(0.0); SLOTS];
        val[0] = Iv::point(1.0);
        let mut sides: SmallVec<[Iv; 8]> = SmallVec::new();
        for step in self.path.iter().rev() {
            if let Some((eq, m, _)) = step.eliminated {
                let m = m as usize;
                let mut sum = Iv::point(0.0);
                for j in 0..SLOTS {
                    if j != m && eq[j] != 0 {
                        let Some(c) = arena.eval(eq[j], x) else {
                            return Verdict::Unsure;
                        };
                        sum = sum.add(c.mul(val[j]));
                    }
                }
                let Some(lead) = arena.eval(eq[m], x) else {
                    return Verdict::Unsure;
                };
                if lead.straddles_zero() {
                    return Verdict::Unsure;
                }
                val[m] = sum.neg().div(lead);
            }
            if step.slot != NO_SLOT {
                sides.push(val[step.slot as usize]);
            }
        }
        sides.reverse();
        let mut numeric = Numeric {
            x,
            sides: &sides,
            next: 0,
            tile: 0,
            violated: false,
            unsure: SmallVec::new(),
        };
        let mut stairs = Staircase::new(Iv::point(self.width as f64), Iv::point(self.height as f64));
        for step in &self.path {
            stairs.place(&mut numeric, step.mv);
            if numeric.violated {
                return Verdict::Reject;
            }
        }
        if numeric.unsure.is_empty() {
            return Verdict::Accept;
        }
        let tiles = numeric.unsure;
        if self.degenerate(root, &tiles) { Verdict::Reject } else { Verdict::Unsure }
    }
}

/// Whether a primitive polynomial divides another, both given by coefficients from the constant term upwards.
fn divides(divisor: &[i64], mut numerator: SmallVec<[i128; 32]>) -> bool {
    let dn = divisor.len();
    let lead = divisor[dn - 1] as i128;
    while numerator.len() >= dn {
        let top = numerator[numerator.len() - 1];
        let q = top / lead;
        if q * lead != top || q.abs() >= LIMIT {
            return false;
        }
        let base = numerator.len() - dn;
        for (j, &c) in divisor.iter().enumerate() {
            numerator[base + j] -= q * c as i128;
        }
        numerator.pop();
    }
    numerator.iter().all(|&v| v == 0)
}
