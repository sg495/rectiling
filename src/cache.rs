// SPDX-License-Identifier: LGPL-3.0-or-later

//! Shared cache from integer polynomials to their roots not smaller than one.

use crate::algebraic::{Registry, RootRef};
use crate::poly::Poly;
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

/// Roots of a polynomial, as references into a registry.
pub(crate) type Roots = SmallVec<[RootRef; 2]>;

const SHARDS: usize = 1 << 12;

/// Concurrent map from polynomials with machine-integer coefficients to their roots not smaller than one.
pub(crate) struct PolyCache {
    shards: Box<[Mutex<WordMap<Box<[i64]>, SmallVec<[RootRef; 1]>>>]>,
}

fn hash_words(key: &[i64]) -> u64 {
    let mut h = WordHasher::default();
    for &v in key {
        h.write_i64(v);
    }
    h.finish()
}

impl PolyCache {
    /// An empty cache.
    pub(crate) fn new() -> Self {
        PolyCache {
            shards: (0..SHARDS).map(|_| Mutex::new(WordMap::default())).collect(),
        }
    }

    /// The roots not smaller than one of the non-zero polynomial with the given coefficients, listed from the constant term upwards.
    pub(crate) fn roots(&self, key: &[i64], registry: &Registry) -> Roots {
        let shard = &self.shards[(hash_words(key).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 52) as usize];
        if let Some(r) = shard.lock().expect("cache lock").get(key) {
            return r.iter().copied().collect();
        }
        let roots = registry.roots_from_one(&Poly::from_i64s(key));
        let stored: SmallVec<[RootRef; 1]> = roots.iter().copied().collect();
        shard.lock().expect("cache lock").insert(key.into(), stored);
        roots
    }

    /// The roots not smaller than one of a non-zero polynomial with arbitrary-precision coefficients.
    pub(crate) fn roots_big(&self, p: &Poly<BigInt>, registry: &Registry) -> Roots {
        let words: Option<Vec<i64>> = p.coeffs().iter().map(|c| c.to_i64()).collect();
        match words {
            Some(w) => self.roots(&w, registry),
            None => registry.roots_from_one(p),
        }
    }

    /// The number of cached polynomials.
    pub(crate) fn len(&self) -> usize {
        self.shards.iter().map(|s| s.lock().expect("cache lock").len()).sum()
    }
}
