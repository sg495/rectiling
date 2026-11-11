// SPDX-License-Identifier: LGPL-3.0-or-later

//! Shared cache from integer polynomials to their roots not smaller than one.

use crate::algebraic::{Registry, RootRef};
use crate::pack::{pack, packed_len};
use crate::poly::Poly;
use hashbrown::HashTable;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use smallvec::SmallVec;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::sync::Mutex;

/// Multiplicative hasher for sequences of machine integers.
#[derive(Default, Clone, Copy)]
pub(crate) struct WordHasher(u64);

impl Hasher for WordHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0 ^ (self.0 >> 29)
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut b = [0u8; 8];
            b[..chunk.len()].copy_from_slice(chunk);
            self.write_u64(u64::from_le_bytes(b));
        }
    }
    #[inline]
    fn write_u32(&mut self, v: u32) {
        self.write_u64(v as u64);
    }
    #[inline]
    fn write_u64(&mut self, v: u64) {
        self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    #[inline]
    fn write_i64(&mut self, v: i64) {
        self.write_u64(v as u64);
    }
    #[inline]
    fn write_usize(&mut self, v: usize) {
        self.write_u64(v as u64);
    }
}

pub(crate) type WordMap<K, V> = HashMap<K, V, BuildHasherDefault<WordHasher>>;

/// Hash of a byte string.
pub(crate) fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut h = WordHasher::default();
    h.write(bytes);
    h.finish().wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// Appends bytes to a buffer, which grows by a quarter of its length when full.
pub(crate) fn append(buffer: &mut Vec<u8>, bytes: &[u8]) {
    if buffer.len() + bytes.len() > buffer.capacity() {
        buffer.reserve_exact((buffer.len() / 4).max(1 << 10) + bytes.len());
    }
    buffer.extend_from_slice(bytes);
}

/// Roots of a polynomial, as references into a registry.
pub(crate) type Roots = SmallVec<[RootRef; 2]>;

const SHARD_BITS: u32 = 12;

#[derive(Default)]
struct Shard {
    table: HashTable<u32>,
    arena: Vec<u8>,
}

impl Shard {
    fn find(&self, key: &[u8], hash: u64) -> Option<SmallVec<[u32; 2]>> {
        let arena = &self.arena;
        let at = *self.table.find(hash, |&o| arena[o as usize..].starts_with(key))? as usize + key.len();
        let count = arena[at] as usize;
        Some((0..count).map(|i| u32::from_le_bytes(arena[at + 1 + 4 * i..at + 5 + 4 * i].try_into().expect("four bytes"))).collect())
    }

    fn insert(&mut self, key: &[u8], hash: u64, ids: &[u32]) {
        let offset = self.arena.len() as u32;
        append(&mut self.arena, key);
        append(&mut self.arena, &[ids.len() as u8]);
        for id in ids {
            append(&mut self.arena, &id.to_le_bytes());
        }
        let arena = &self.arena;
        self.table.insert_unique(hash, offset, |&o| {
            let rest = &arena[o as usize..];
            hash_bytes(&rest[..packed_len(rest)])
        });
    }
}

/// Map from encoded polynomials to their roots, for the use of one thread, which empties itself when it reaches a given size.
pub(crate) struct LocalCache {
    table: HashTable<u32>,
    arena: Vec<u8>,
    limit: usize,
}

const ROOT_BYTES: usize = 20;

impl LocalCache {
    /// An empty map holding at most the given number of polynomials.
    pub(crate) fn new(limit: usize) -> Self {
        LocalCache {
            table: HashTable::new(),
            arena: Vec::new(),
            limit,
        }
    }

    /// The roots stored for the polynomial with the given encoding and hash.
    pub(crate) fn find(&self, key: &[u8], hash: u64) -> Option<Roots> {
        let arena = &self.arena;
        let at = *self.table.find(hash, |&o| arena[o as usize..].starts_with(key))? as usize + key.len();
        let count = arena[at] as usize;
        let field = |from: usize| -> [u8; 8] { arena[from..from + 8].try_into().expect("eight bytes") };
        Some(
            (0..count)
                .map(|i| {
                    let from = at + 1 + ROOT_BYTES * i;
                    RootRef {
                        id: u32::from_le_bytes(arena[from..from + 4].try_into().expect("four bytes")),
                        lo: f64::from_le_bytes(field(from + 4)),
                        hi: f64::from_le_bytes(field(from + 12)),
                    }
                })
                .collect(),
        )
    }

    /// Stores the roots of the polynomial with the given encoding and hash, which must not be present.
    pub(crate) fn insert(&mut self, key: &[u8], hash: u64, roots: &Roots) {
        if self.table.len() >= self.limit {
            self.table.clear();
            self.arena.clear();
        }
        let offset = self.arena.len() as u32;
        self.arena.extend_from_slice(key);
        self.arena.push(roots.len() as u8);
        for root in roots {
            self.arena.extend_from_slice(&root.id.to_le_bytes());
            self.arena.extend_from_slice(&root.lo.to_le_bytes());
            self.arena.extend_from_slice(&root.hi.to_le_bytes());
        }
        let arena = &self.arena;
        self.table.insert_unique(hash, offset, |&o| {
            let rest = &arena[o as usize..];
            hash_bytes(&rest[..packed_len(rest)])
        });
    }
}

/// Concurrent map to their roots not smaller than one from the polynomials with machine-integer coefficients that are not registered irreducible polynomials.
pub(crate) struct PolyCache {
    shards: Box<[Mutex<Shard>]>,
}

impl PolyCache {
    /// An empty cache.
    pub(crate) fn new() -> Self {
        PolyCache {
            shards: (0..1usize << SHARD_BITS).map(|_| Mutex::new(Shard::default())).collect(),
        }
    }

    /// The roots not smaller than one of the non-zero polynomial with the given coefficients, listed from the constant term upwards.
    pub(crate) fn roots(&self, key: &[i64], scratch: &mut Vec<u8>, registry: &Registry) -> Roots {
        scratch.clear();
        pack(key, scratch);
        self.roots_packed(key, scratch, hash_bytes(scratch), registry)
    }

    /// The roots not smaller than one of the non-zero polynomial with the given coefficients, encoding and hash.
    pub(crate) fn roots_packed(&self, key: &[i64], scratch: &[u8], hash: u64, registry: &Registry) -> Roots {
        if let Some(roots) = registry.equation_roots(scratch, hash) {
            return roots;
        }
        let shard = &self.shards[(hash >> (64 - SHARD_BITS)) as usize];
        let found = shard.lock().expect("cache lock").find(scratch, hash);
        if let Some(ids) = found {
            return registry.refs(&ids);
        }
        let roots = registry.roots_from_one(&Poly::from_i64s(key));
        if registry.equation_roots(scratch, hash).is_some() {
            return roots;
        }
        let ids: SmallVec<[u32; 2]> = roots.iter().map(|r| r.id).collect();
        let mut guard = shard.lock().expect("cache lock");
        if guard.find(scratch, hash).is_none() {
            guard.insert(scratch, hash, &ids);
        }
        roots
    }

    /// The roots not smaller than one of a non-zero polynomial with arbitrary-precision coefficients.
    pub(crate) fn roots_big(&self, p: &Poly<BigInt>, registry: &Registry) -> Roots {
        let words: Option<Vec<i64>> = p.coeffs().iter().map(|c| c.to_i64()).collect();
        match words {
            Some(w) if w.len() <= u8::MAX as usize => self.roots(&w, &mut Vec::new(), registry),
            _ => registry.roots_from_one(p),
        }
    }

    /// The number of cached polynomials.
    pub(crate) fn len(&self) -> usize {
        self.shards.iter().map(|s| s.lock().expect("cache lock").table.len()).sum()
    }
}
