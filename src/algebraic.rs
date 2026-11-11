// SPDX-License-Identifier: LGPL-3.0-or-later

//! Canonical real algebraic numbers not smaller than one, and a shared registry of them.

use crate::cache::hash_bytes;
use crate::factor::factor;
use crate::pack::{pack, packed_len, unpack};
use crate::poly::Poly;
use crate::roots::{isolate_roots_above_one, sign_at_rational};
use hashbrown::HashTable;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use smallvec::SmallVec;
use std::collections::HashMap;
use std::sync::RwLock;

/// Real algebraic number not smaller than one, identified by its minimal polynomial and the position of the root.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Algebraic {
    min_poly: Poly<BigInt>,
    index: u32,
    approx: (u64, u64),
}

impl Algebraic {
    /// The primitive minimal polynomial, with positive leading coefficient.
    pub fn min_poly(&self) -> &Poly<BigInt> {
        &self.min_poly
    }

    /// The position of the number amongst the roots of its minimal polynomial not smaller than one, in increasing order.
    pub fn index(&self) -> usize {
        self.index as usize
    }

    /// The algebraic degree.
    pub fn degree(&self) -> usize {
        self.min_poly.degree().unwrap_or(0)
    }

    /// Floats enclosing the number.
    pub fn enclosure(&self) -> (f64, f64) {
        (f64::from_bits(self.approx.0), f64::from_bits(self.approx.1))
    }

    /// A float approximating the number.
    pub fn approx(&self) -> f64 {
        let (lo, hi) = self.enclosure();
        0.5 * (lo + hi)
    }
}

/// Reference to a registered algebraic number, with floats enclosing it.
#[derive(Clone, Copy, Debug)]
pub struct RootRef {
    /// Identifier of the number within its registry.
    pub id: u32,
    /// A float not greater than the number.
    pub lo: f64,
    /// A float not smaller than the number.
    pub hi: f64,
}

const BIG: u64 = 1 << 63;

#[derive(Clone, Copy)]
struct Entry {
    /// Offset of the encoded minimal polynomial, or the position of an arbitrary-precision one with the top bit set.
    source: u64,
    lo: f64,
    hi: f64,
    index: u16,
}

#[derive(Default)]
struct Inner {
    entries: Vec<Entry>,
    arena: Vec<u8>,
    table: HashTable<u64>,
    big_polys: Vec<Poly<BigInt>>,
    big_table: HashMap<Poly<BigInt>, (u32, u32)>,
}

/// Registry assigning stable identifiers to the algebraic numbers encountered during a computation.
#[derive(Default)]
pub struct Registry {
    inner: RwLock<Inner>,
}

fn rational_root(f: &Poly<BigInt>) -> (BigInt, BigInt) {
    (-&f.coeffs()[0], f.coeffs()[1].clone())
}

fn locate(f: &Poly<BigInt>) -> Vec<(f64, f64)> {
    let mut out = Vec::new();
    if f.degree() == Some(1) {
        let (num, den) = rational_root(f);
        if num >= den {
            let v = num.to_f64().unwrap_or(f64::NAN) / den.to_f64().unwrap_or(f64::NAN);
            out.push(if num == den { (1.0, 1.0) } else { (v * (1.0 - 1e-14), v * (1.0 + 1e-14)) });
        }
    } else {
        for mut root in isolate_roots_above_one(f) {
            root.refine_to(64);
            out.push(root.enclosure());
        }
    }
    out
}

impl Inner {
    fn range(&self, first: u32, count: u32) -> SmallVec<[RootRef; 2]> {
        (first..first + count)
            .map(|id| {
                let e = &self.entries[id as usize];
                RootRef { id, lo: e.lo, hi: e.hi }
            })
            .collect()
    }

    fn find(&self, key: &[u8], hash: u64) -> Option<(u32, u32)> {
        let arena = &self.arena;
        let at = *self.table.find(hash, |&o| arena[o as usize..].starts_with(key))? as usize + key.len();
        let first = u32::from_le_bytes(arena[at..at + 4].try_into().expect("four bytes"));
        Some((first, arena[at + 4] as u32))
    }

    fn push_entries(&mut self, source: u64, located: &[(f64, f64)]) -> (u32, u32) {
        let first = self.entries.len() as u32;
        for (index, &(lo, hi)) in located.iter().enumerate() {
            self.entries.push(Entry {
                source,
                lo,
                hi,
                index: index as u16,
            });
        }
        (first, located.len() as u32)
    }

    fn min_poly(&self, entry: &Entry) -> Poly<BigInt> {
        if entry.source & BIG != 0 {
            self.big_polys[(entry.source & !BIG) as usize].clone()
        } else {
            Poly::from_i64s(&unpack(&self.arena[entry.source as usize..]))
        }
    }
}

impl Registry {
    /// An empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    fn factor_roots(&self, f: &Poly<BigInt>) -> SmallVec<[RootRef; 2]> {
        let words: Option<SmallVec<[i64; 16]>> = f.coeffs().iter().map(|c| c.to_i64()).collect();
        let Some(words) = words.filter(|w| w.len() <= u8::MAX as usize) else {
            return self.big_factor_roots(f);
        };
        let mut key: SmallVec<[u8; 64]> = SmallVec::new();
        let mut buffer = Vec::with_capacity(64);
        pack(&words, &mut buffer);
        key.extend_from_slice(&buffer);
        let hash = hash_bytes(&key);
        {
            let inner = self.inner.read().expect("registry lock");
            if let Some((first, count)) = inner.find(&key, hash) {
                return inner.range(first, count);
            }
        }
        let located = locate(f);
        let mut inner = self.inner.write().expect("registry lock");
        if let Some((first, count)) = inner.find(&key, hash) {
            return inner.range(first, count);
        }
        let offset = inner.arena.len() as u64;
        let (first, count) = inner.push_entries(offset, &located);
        inner.arena.extend_from_slice(&key);
        inner.arena.extend_from_slice(&first.to_le_bytes());
        inner.arena.push(count as u8);
        let inner = &mut *inner;
        let arena = &inner.arena;
        inner.table.insert_unique(hash, offset, |&o| {
            let rest = &arena[o as usize..];
            hash_bytes(&rest[..packed_len(rest)])
        });
        inner.range(first, count)
    }

    fn big_factor_roots(&self, f: &Poly<BigInt>) -> SmallVec<[RootRef; 2]> {
        {
            let inner = self.inner.read().expect("registry lock");
            if let Some(&(first, count)) = inner.big_table.get(f) {
                return inner.range(first, count);
            }
        }
        let located = locate(f);
        let mut inner = self.inner.write().expect("registry lock");
        if let Some(&(first, count)) = inner.big_table.get(f) {
            return inner.range(first, count);
        }
        let source = BIG | inner.big_polys.len() as u64;
        inner.big_polys.push(f.clone());
        let (first, count) = inner.push_entries(source, &located);
        inner.big_table.insert(f.clone(), (first, count));
        inner.range(first, count)
    }

    /// The distinct real roots not smaller than one of a non-zero polynomial, in no particular order.
    pub fn roots_from_one(&self, p: &Poly<BigInt>) -> SmallVec<[RootRef; 2]> {
        let mut refs = SmallVec::new();
        for (f, _) in factor(p) {
            refs.extend(self.factor_roots(&f));
        }
        refs
    }

    /// References to the registered numbers with the given identifiers.
    pub(crate) fn refs(&self, ids: &[u32]) -> SmallVec<[RootRef; 2]> {
        if ids.is_empty() {
            return SmallVec::new();
        }
        let inner = self.inner.read().expect("registry lock");
        ids.iter()
            .map(|&id| {
                let e = &inner.entries[id as usize];
                RootRef { id, lo: e.lo, hi: e.hi }
            })
            .collect()
    }

    /// Sign of a polynomial at a registered number.
    pub fn sign_at(&self, id: u32, q: &Poly<BigInt>) -> i32 {
        let value = self.get(id);
        let f = value.min_poly();
        if f.degree() == Some(1) {
            let (num, den) = rational_root(f);
            return sign_at_rational(q, &num, &den);
        }
        if q.is_zero() || (q.degree() >= f.degree() && q.pseudo_div_rem(f).1.is_zero()) {
            return 0;
        }
        let mut root = isolate_roots_above_one(f).swap_remove(value.index());
        root.sign_of(q)
    }

    /// The coefficients of the minimal polynomial of a registered number, if they are machine integers.
    pub(crate) fn min_poly_words(&self, id: u32) -> Option<Box<[i64]>> {
        let inner = self.inner.read().expect("registry lock");
        let entry = inner.entries[id as usize];
        (entry.source & BIG == 0).then(|| unpack(&inner.arena[entry.source as usize..]).as_slice().into())
    }

    /// The algebraic degree of a registered number.
    pub fn degree(&self, id: u32) -> usize {
        let inner = self.inner.read().expect("registry lock");
        let entry = inner.entries[id as usize];
        if entry.source & BIG != 0 {
            inner.big_polys[(entry.source & !BIG) as usize].degree().unwrap_or(0)
        } else {
            inner.arena[entry.source as usize] as usize - 1
        }
    }

    /// A float approximating a registered number.
    pub fn approx(&self, id: u32) -> f64 {
        let inner = self.inner.read().expect("registry lock");
        let entry = inner.entries[id as usize];
        0.5 * (entry.lo + entry.hi)
    }

    /// The registered number with the given identifier.
    pub fn get(&self, id: u32) -> Algebraic {
        let inner = self.inner.read().expect("registry lock");
        let entry = inner.entries[id as usize];
        Algebraic {
            min_poly: inner.min_poly(&entry),
            index: entry.index as u32,
            approx: (entry.lo.to_bits(), entry.hi.to_bits()),
        }
    }

    /// The number of registered numbers.
    pub fn len(&self) -> usize {
        self.inner.read().expect("registry lock").entries.len()
    }

    /// Whether no number has been registered.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
