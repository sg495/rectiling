// SPDX-License-Identifier: LGPL-3.0-or-later

//! Identification of the bags of tiles of tilings: the proportion together with the multiset of the short sides.

use crate::algebraic::{Registry, RootRef};
use crate::cache::WordMap;
use crate::exact::{self, Measures};
use crate::modular::{eval_mod, inv_mod, mul_mod, primes, root_mod};
use crate::poly::Poly;
use crate::search::Witness;
use crate::staircase::Placement;
use num_bigint::BigInt;
use smallvec::SmallVec;
use std::hash::Hasher;
use std::sync::Mutex;

const SHARD_BITS: u32 = 12;

type Residues = SmallVec<[u64; 14]>;

/// What entering the bag of a tiling into the table established.
pub(crate) enum Entered {
    /// The bag is new; the flag tells whether a different bag has the same residues.
    New(bool),
    /// The bag is that of a tiling entered before.
    Known,
    /// The bag could not be identified.
    Unresolved,
}

/// Concurrent table of the distinct bags of the tilings of a search, each represented by one tiling.
pub(crate) struct Bags {
    shards: Box<[Mutex<WordMap<u64, SmallVec<[(u32, Witness); 1]>>>]>,
    points: Box<[Mutex<WordMap<u32, (u64, u64)>>]>,
}

/// Coefficients of a product of two polynomials, unless one exceeds the range of the integers used.
fn product(a: &[i64], b: &[i64]) -> Option<Vec<i128>> {
    if a.is_empty() || b.is_empty() {
        return Some(Vec::new());
    }
    let mut out = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            out[i + j] = out[i + j].checked_add(x as i128 * y as i128)?;
        }
    }
    Some(out)
}

/// Whether the difference of two polynomials is a multiple of a primitive polynomial, unless an intermediate value exceeds the range of the integers used.
fn congruent(a: &[i128], b: &[i128], f: &[i64]) -> Option<bool> {
    let mut r: Vec<i128> = (0..a.len().max(b.len())).map(|i| a.get(i).copied().unwrap_or(0).checked_sub(b.get(i).copied().unwrap_or(0))).collect::<Option<_>>()?;
    let lead = f[f.len() - 1] as i128;
    loop {
        while r.last() == Some(&0) {
            r.pop();
        }
        if r.len() < f.len() {
            return Some(r.is_empty());
        }
        let top = r[r.len() - 1];
        if top % lead != 0 {
            return Some(false);
        }
        let q = top / lead;
        let base = r.len() - f.len();
        for (j, &c) in f.iter().enumerate() {
            r[base + j] = r[base + j].checked_sub(q.checked_mul(c as i128)?)?;
        }
    }
}

fn big(coeffs: &[i64]) -> Poly<BigInt> {
    Poly::from_i64s(coeffs)
}

/// Whether two quotients of polynomials take the same value at a registered number with the given minimal polynomial.
fn equal(registry: &Registry, id: u32, f: &[i64], a: (&[i64], &[i64]), b: (&[i64], &[i64])) -> bool {
    let fast = (|| congruent(&product(a.0, b.1)?, &product(b.0, a.1)?, f))();
    fast.unwrap_or_else(|| registry.sign_at(id, &big(a.0).mul(&big(b.1)).sub(&big(b.0).mul(&big(a.1)))) == 0)
}

fn residues(measures: &Measures, p: u64, r: u64) -> Option<Residues> {
    let den = eval_mod(&measures.den, r, p);
    if den == 0 {
        return None;
    }
    let inv = inv_mod(den, p);
    Some(measures.shorts.iter().map(|s| mul_mod(eval_mod(s, r, p), inv, p)).collect())
}

fn key(id: u32, residues: &Residues) -> u64 {
    let mut sorted = residues.clone();
    sorted.sort_unstable();
    let mut hasher = crate::cache::WordHasher::default();
    hasher.write_u64(id as u64);
    for v in sorted {
        hasher.write_u64(v);
    }
    hasher.finish().wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

impl Bags {
    /// An empty table.
    pub(crate) fn new() -> Self {
        Bags {
            shards: (0..1usize << SHARD_BITS).map(|_| Mutex::default()).collect(),
            points: (0..1usize << SHARD_BITS).map(|_| Mutex::default()).collect(),
        }
    }

    /// A prime and a root of the minimal polynomial of a registered number modulo that prime, the same for every caller.
    fn point(&self, id: u32, f: &[i64]) -> Option<(u64, u64)> {
        let shard = &self.points[id as usize & ((1 << SHARD_BITS) - 1)];
        if let Some(&point) = shard.lock().expect("bags lock").get(&id) {
            return Some(point);
        }
        let point = primes().iter().find_map(|&p| root_mod(f, p).map(|r| (p, r)))?;
        shard.lock().expect("bags lock").insert(id, point);
        Some(point)
    }

    /// Enters the bag of the tiling realised by a placement sequence at a proportion.
    pub(crate) fn enter(&self, registry: &Registry, root: &RootRef, moves: &[Placement], witness: Witness) -> Entered {
        let found = (|| {
            let f = registry.min_poly_words(root.id)?;
            let point = self.point(root.id, &f)?;
            let measures = exact::measures(registry, root, moves)?;
            let values = residues(&measures, point.0, point.1)?;
            Some((f, point, measures, values))
        })();
        let Some((f, (p, r), measures, values)) = found else {
            return Entered::Unresolved;
        };
        let key = key(root.id, &values);
        let shard = &self.shards[(key >> (64 - SHARD_BITS)) as usize];
        let mut seen = 0;
        loop {
            let others: SmallVec<[(u32, Witness); 1]> = {
                let mut guard = shard.lock().expect("bags lock");
                let entry = guard.entry(key).or_default();
                if entry.len() == seen {
                    entry.push((root.id, witness));
                    return Entered::New(seen > 0);
                }
                entry[seen..].iter().copied().collect()
            };
            for (id, other) in others {
                seen += 1;
                if id != root.id {
                    continue;
                }
                let path = crate::search::decode_witness(&other);
                let Some(theirs) = exact::measures(registry, root, &path) else {
                    return Entered::Unresolved;
                };
                let Some(their_values) = residues(&theirs, p, r) else {
                    return Entered::Unresolved;
                };
                if same(registry, root.id, &f, (&measures, &values), (&theirs, &their_values)) {
                    return Entered::Known;
                }
            }
        }
    }

    /// The number of distinct bags for each registered number, by identifier.
    pub(crate) fn counts(&self) -> Vec<u64> {
        let mut counts = Vec::new();
        for shard in self.shards.iter() {
            for &(id, _) in shard.lock().expect("bags lock").values().flatten() {
                if counts.len() <= id as usize {
                    counts.resize(id as usize + 1, 0);
                }
                counts[id as usize] += 1;
            }
        }
        counts
    }
}

/// Whether two tilings with the same proportion have the same multiset of short sides, given the residues of the short sides as a filter.
fn same(registry: &Registry, id: u32, f: &[i64], a: (&Measures, &Residues), b: (&Measures, &Residues)) -> bool {
    let n = a.1.len();
    if b.1.len() != n {
        return false;
    }
    let mut used = 0u32;
    (0..n).all(|i| {
        let partner = (0..n).find(|&j| used >> j & 1 == 0 && a.1[i] == b.1[j] && equal(registry, id, f, (&a.0.shorts[i], &a.0.den), (&b.0.shorts[j], &b.0.den)));
        partner.inspect(|&j| used |= 1 << j).is_some()
    })
}
