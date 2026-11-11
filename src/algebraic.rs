// SPDX-License-Identifier: LGPL-3.0-or-later

//! Canonical real algebraic numbers not smaller than one, and a shared registry of them.

use crate::cache::WordMap;
use crate::factor::factor;
use crate::poly::Poly;
use crate::roots::{isolate_roots_above_one, sign_at_rational};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use smallvec::SmallVec;
use std::sync::{Arc, Mutex};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Coeffs {
    Words(Box<[i64]>),
    Big(Box<[BigInt]>),
}

impl Coeffs {
    fn of(p: &Poly<BigInt>) -> Self {
        let words: Option<Box<[i64]>> = p.coeffs().iter().map(|c| c.to_i64()).collect();
        match words {
            Some(w) => Coeffs::Words(w),
            None => Coeffs::Big(p.coeffs().into()),
        }
    }

    fn poly(&self) -> Poly<BigInt> {
        match self {
            Coeffs::Words(w) => Poly::from_i64s(w),
            Coeffs::Big(b) => Poly::from_coeffs(b.iter().cloned()),
        }
    }

    fn len(&self) -> usize {
        match self {
            Coeffs::Words(w) => w.len(),
            Coeffs::Big(b) => b.len(),
        }
    }
}

/// Real algebraic number not smaller than one, identified by its minimal polynomial and the position of the root.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Algebraic {
    coeffs: Arc<Coeffs>,
    index: u32,
    approx: (u64, u64),
}

impl Algebraic {
    /// The primitive minimal polynomial, with positive leading coefficient.
    pub fn min_poly(&self) -> Poly<BigInt> {
        self.coeffs.poly()
    }

    /// The position of the number amongst the roots of its minimal polynomial not smaller than one, in increasing order.
    pub fn index(&self) -> usize {
        self.index as usize
    }

    /// The algebraic degree.
    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
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

#[derive(Default)]
struct Inner {
    entries: Vec<Algebraic>,
    by_factor: WordMap<Arc<Coeffs>, (u32, u32)>,
}

/// Registry assigning stable identifiers to the algebraic numbers encountered during a computation.
#[derive(Default)]
pub struct Registry {
    inner: Mutex<Inner>,
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
    fn refs(&self, first: u32, count: u32) -> SmallVec<[RootRef; 2]> {
        (first..first + count)
            .map(|id| {
                let (lo, hi) = self.entries[id as usize].enclosure();
                RootRef { id, lo, hi }
            })
            .collect()
    }
}

impl Registry {
    /// An empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    fn factor_roots(&self, f: &Poly<BigInt>) -> SmallVec<[RootRef; 2]> {
        let key = Coeffs::of(f);
        {
            let inner = self.inner.lock().expect("registry lock");
            if let Some(&(first, count)) = inner.by_factor.get(&key) {
                return inner.refs(first, count);
            }
        }
        let located = locate(f);
        let mut inner = self.inner.lock().expect("registry lock");
        if let Some(&(first, count)) = inner.by_factor.get(&key) {
            return inner.refs(first, count);
        }
        let key = Arc::new(key);
        let first = inner.entries.len() as u32;
        for (index, (lo, hi)) in located.iter().enumerate() {
            inner.entries.push(Algebraic {
                coeffs: key.clone(),
                index: index as u32,
                approx: (lo.to_bits(), hi.to_bits()),
            });
        }
        let count = located.len() as u32;
        inner.by_factor.insert(key, (first, count));
        inner.refs(first, count)
    }

    /// The distinct real roots not smaller than one of a non-zero polynomial, in no particular order.
    pub fn roots_from_one(&self, p: &Poly<BigInt>) -> SmallVec<[RootRef; 2]> {
        let mut refs = SmallVec::new();
        for (f, _) in factor(p) {
            refs.extend(self.factor_roots(&f));
        }
        refs
    }

    /// Sign of a polynomial at a registered number.
    pub fn sign_at(&self, id: u32, q: &Poly<BigInt>) -> i32 {
        let value = self.get(id);
        let f = value.min_poly();
        if f.degree() == Some(1) {
            let (num, den) = rational_root(&f);
            return sign_at_rational(q, &num, &den);
        }
        if q.is_zero() || (q.degree() >= f.degree() && q.pseudo_div_rem(&f).1.is_zero()) {
            return 0;
        }
        let mut root = isolate_roots_above_one(&f).swap_remove(value.index());
        root.sign_of(q)
    }

    /// The coefficients of the minimal polynomial of a registered number, if they are machine integers.
    pub(crate) fn min_poly_words(&self, id: u32) -> Option<Box<[i64]>> {
        match &*self.inner.lock().expect("registry lock").entries[id as usize].coeffs {
            Coeffs::Words(w) => Some(w.clone()),
            Coeffs::Big(_) => None,
        }
    }

    /// The registered number with the given identifier.
    pub fn get(&self, id: u32) -> Algebraic {
        self.inner.lock().expect("registry lock").entries[id as usize].clone()
    }

    /// The number of registered numbers.
    pub fn len(&self) -> usize {
        self.inner.lock().expect("registry lock").entries.len()
    }

    /// Whether no number has been registered.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
