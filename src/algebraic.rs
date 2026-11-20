// SPDX-License-Identifier: LGPL-3.0-or-later

//! Canonical real algebraic numbers not smaller than one, and a shared registry of them.

use crate::band::Band;
use crate::cache::{append, hash_bytes};
use crate::chunked::Chunked;
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
use std::sync::atomic::{AtomicUsize, Ordering};

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

const SHARD_BITS: u32 = 12;
const BIG: u32 = 1 << 31;
const MET: u8 = 1 << 7;

/// Registered number: the floats enclosing it, the place of its minimal polynomial and its position amongst the roots.
#[derive(Clone, Copy)]
#[repr(C, packed(4))]
struct Entry {
    lo: f64,
    gap: f32,
    offset: u32,
    tag: u32,
}

impl Entry {
    fn new(lo: f64, hi: f64, offset: u32, tag: u32) -> Self {
        let width = hi - lo;
        let mut gap = width as f32;
        if (gap as f64) < width {
            gap = gap.next_up();
        }
        Entry {
            lo,
            gap,
            offset,
            tag,
        }
    }

    fn hi(&self) -> f64 {
        let (lo, gap) = (self.lo, self.gap);
        lo + gap as f64
    }

    fn index(&self) -> u32 {
        self.tag & 0xff
    }

    fn reference(&self, id: u32) -> RootRef {
        RootRef {
            id,
            lo: self.lo,
            hi: self.hi(),
        }
    }
}

/// Irreducible polynomials with machine-integer coefficients whose hashes share their leading bits, each encoded and followed by the identifier of its first root and the number of its roots.
#[derive(Default)]
struct Shard {
    table: HashTable<u32>,
    arena: Vec<u8>,
}

impl Shard {
    fn find(&self, key: &[u8], hash: u64) -> Option<usize> {
        let arena = &self.arena;
        Some(*self.table.find(hash, |&o| arena[o as usize..].starts_with(key))? as usize + key.len())
    }

    fn span(&self, at: usize) -> (u32, u32) {
        let first = u32::from_le_bytes(self.arena[at..at + 4].try_into().expect("four bytes"));
        (first, (self.arena[at + 4] & !MET) as u32)
    }
}

#[derive(Default)]
struct Big {
    polys: Vec<Poly<BigInt>>,
    table: HashMap<Poly<BigInt>, (u32, u32)>,
}

/// Registry assigning stable identifiers to the algebraic numbers encountered during a computation.
pub struct Registry {
    shards: Box<[RwLock<Shard>]>,
    entries: RwLock<Chunked<Entry>>,
    big: RwLock<Big>,
    band: Option<Band>,
    met: AtomicUsize,
}

impl Default for Registry {
    fn default() -> Self {
        Registry {
            shards: (0..1usize << SHARD_BITS).map(|_| RwLock::default()).collect(),
            entries: RwLock::default(),
            big: RwLock::default(),
            band: None,
            met: AtomicUsize::new(0),
        }
    }
}

fn rational_root(f: &Poly<BigInt>) -> (BigInt, BigInt) {
    (-&f.coeffs()[0], f.coeffs()[1].clone())
}

/// The roots not smaller than one of an irreducible polynomial that lie in the band, if any is given, each with its position amongst all such roots and floats enclosing it.
fn locate(f: &Poly<BigInt>, band: Option<&Band>) -> Vec<(u32, f64, f64)> {
    let mut out = Vec::new();
    if f.degree() == Some(1) {
        let (num, den) = rational_root(f);
        if num >= den && band.is_none_or(|b| b.holds_rational(&num, &den)) {
            let v = num.to_f64().unwrap_or(f64::NAN) / den.to_f64().unwrap_or(f64::NAN);
            out.push(if num == den { (0, 1.0, 1.0) } else { (0, v * (1.0 - 1e-14), v * (1.0 + 1e-14)) });
        }
    } else {
        for (index, mut root) in isolate_roots_above_one(f).into_iter().enumerate() {
            if band.is_some_and(|b| !b.holds_root(&mut root)) {
                continue;
            }
            root.refine_to(64);
            let (lo, hi) = root.enclosure();
            out.push((index as u32, lo, hi));
        }
    }
    out
}

impl Registry {
    /// An empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// An empty registry that admits only the numbers in the given band.
    pub fn banded(band: Band) -> Self {
        Registry {
            band: Some(band),
            ..Self::default()
        }
    }

    /// The band to which the registry is restricted, if any.
    pub fn band(&self) -> Option<&Band> {
        self.band.as_ref()
    }

    fn shard(&self, hash: u64) -> (u32, &RwLock<Shard>) {
        let index = (hash >> (64 - SHARD_BITS)) as u32;
        (index, &self.shards[index as usize])
    }

    fn range(&self, first: u32, count: u32) -> SmallVec<[RootRef; 2]> {
        if count == 0 {
            return SmallVec::new();
        }
        let entries = self.entries.read().expect("registry lock");
        (first..first + count).map(|id| entries.get(id as usize).reference(id)).collect()
    }

    fn entry(&self, id: u32) -> Entry {
        self.entries.read().expect("registry lock").get(id as usize)
    }

    fn push_entries(&self, offset: u32, tag: u32, located: &[(u32, f64, f64)]) -> (u32, u32) {
        let mut entries = self.entries.write().expect("registry lock");
        let first = entries.len();
        assert!(first + located.len() <= u32::MAX as usize, "too many algebraic numbers for one registry");
        for &(index, lo, hi) in located {
            assert!(index < 0x100, "too many roots of one polynomial");
            entries.push(Entry::new(lo, hi, offset, tag | index));
        }
        (first as u32, located.len() as u32)
    }

    /// The registered roots of the polynomial with the given encoding and hash, if it is a registered irreducible polynomial, which is then marked as met as an equation.
    pub(crate) fn equation_roots(&self, key: &[u8], hash: u64) -> Option<SmallVec<[RootRef; 2]>> {
        let (_, lock) = self.shard(hash);
        let (first, count, met) = {
            let shard = lock.read().expect("registry lock");
            let at = shard.find(key, hash)?;
            let (first, count) = shard.span(at);
            (first, count, shard.arena[at + 4] & MET != 0)
        };
        if !met {
            let mut shard = lock.write().expect("registry lock");
            let at = shard.find(key, hash)?;
            if shard.arena[at + 4] & MET == 0 {
                shard.arena[at + 4] |= MET;
                self.met.fetch_add(1, Ordering::Relaxed);
            }
        }
        Some(self.range(first, count))
    }

    /// The number of registered polynomials met as equations.
    pub(crate) fn equations(&self) -> usize {
        self.met.load(Ordering::Relaxed)
    }

    fn factor_roots(&self, f: &Poly<BigInt>) -> SmallVec<[RootRef; 2]> {
        let words: Option<SmallVec<[i64; 16]>> = f.coeffs().iter().map(|c| c.to_i64()).collect();
        let Some(words) = words.filter(|w| w.len() <= u8::MAX as usize) else {
            return self.big_factor_roots(f);
        };
        let mut key = Vec::with_capacity(64);
        pack(&words, &mut key);
        let hash = hash_bytes(&key);
        let (index, lock) = self.shard(hash);
        {
            let shard = lock.read().expect("registry lock");
            if let Some(at) = shard.find(&key, hash) {
                let (first, count) = shard.span(at);
                drop(shard);
                return self.range(first, count);
            }
        }
        let located = locate(f, self.band.as_ref());
        assert!(located.len() < MET as usize, "too many roots of one polynomial");
        let (first, count) = {
            let mut shard = lock.write().expect("registry lock");
            if let Some(at) = shard.find(&key, hash) {
                shard.span(at)
            } else {
                let offset = u32::try_from(shard.arena.len()).expect("registry shard within four gigabytes");
                let span = self.push_entries(offset, index << 8, &located);
                append(&mut shard.arena, &key);
                append(&mut shard.arena, &span.0.to_le_bytes());
                shard.arena.push(span.1 as u8);
                let shard = &mut *shard;
                let arena = &shard.arena;
                shard.table.insert_unique(hash, offset, |&o| {
                    let rest = &arena[o as usize..];
                    hash_bytes(&rest[..packed_len(rest)])
                });
                span
            }
        };
        self.range(first, count)
    }

    fn big_factor_roots(&self, f: &Poly<BigInt>) -> SmallVec<[RootRef; 2]> {
        let known = self.big.read().expect("registry lock").table.get(f).copied();
        let (first, count) = match known {
            Some(span) => span,
            None => {
                let located = locate(f, self.band.as_ref());
                let mut big = self.big.write().expect("registry lock");
                match big.table.get(f) {
                    Some(&span) => span,
                    None => {
                        let offset = big.polys.len() as u32;
                        big.polys.push(f.clone());
                        let span = self.push_entries(offset, BIG, &located);
                        big.table.insert(f.clone(), span);
                        span
                    }
                }
            }
        };
        self.range(first, count)
    }

    /// The distinct real roots not smaller than one of a non-zero polynomial, in no particular order, restricted to the band of the registry if it has one.
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
        let entries = self.entries.read().expect("registry lock");
        ids.iter().map(|&id| entries.get(id as usize).reference(id)).collect()
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

    fn words(&self, entry: &Entry) -> SmallVec<[i64; 16]> {
        let shard = self.shards[(entry.tag >> 8 & ((1 << SHARD_BITS) - 1)) as usize].read().expect("registry lock");
        unpack(&shard.arena[entry.offset as usize..])
    }

    /// The coefficients of the minimal polynomial of a registered number, if they are machine integers.
    pub(crate) fn min_poly_words(&self, id: u32) -> Option<Box<[i64]>> {
        let entry = self.entry(id);
        (entry.tag & BIG == 0).then(|| self.words(&entry).as_slice().into())
    }

    fn min_poly(&self, entry: &Entry) -> Poly<BigInt> {
        if entry.tag & BIG != 0 {
            self.big.read().expect("registry lock").polys[entry.offset as usize].clone()
        } else {
            Poly::from_i64s(&self.words(entry))
        }
    }

    /// The algebraic degree of a registered number.
    pub fn degree(&self, id: u32) -> usize {
        let entry = self.entry(id);
        if entry.tag & BIG != 0 {
            self.big.read().expect("registry lock").polys[entry.offset as usize].degree().unwrap_or(0)
        } else {
            let shard = self.shards[(entry.tag >> 8 & ((1 << SHARD_BITS) - 1)) as usize].read().expect("registry lock");
            shard.arena[entry.offset as usize] as usize - 1
        }
    }

    /// A float approximating a registered number.
    pub fn approx(&self, id: u32) -> f64 {
        let entry = self.entry(id);
        0.5 * (entry.lo + entry.hi())
    }

    /// The registered number with the given identifier.
    pub fn get(&self, id: u32) -> Algebraic {
        let entry = self.entry(id);
        Algebraic {
            min_poly: self.min_poly(&entry),
            index: entry.index(),
            approx: (entry.lo.to_bits(), entry.hi().to_bits()),
        }
    }

    /// The number of registered numbers.
    pub fn len(&self) -> usize {
        self.entries.read().expect("registry lock").len()
    }

    /// Whether no number has been registered.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
