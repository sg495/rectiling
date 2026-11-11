// SPDX-License-Identifier: LGPL-3.0-or-later

//! Canonical real algebraic numbers not smaller than one, and a shared registry of them.

use crate::factor::factor;
use crate::poly::Poly;
use crate::roots::{RealRoot, isolate_roots_above_one, sign_at_rational};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Real algebraic number not smaller than one, identified by its minimal polynomial and the position of the root.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Algebraic {
    min_poly: Poly<BigInt>,
    index: usize,
    approx: (u64, u64),
}

impl Algebraic {
    /// The primitive minimal polynomial, with positive leading coefficient.
    pub fn min_poly(&self) -> &Poly<BigInt> {
        &self.min_poly
    }

    /// The position of the number amongst the roots of its minimal polynomial not smaller than one, in increasing order.
    pub fn index(&self) -> usize {
        self.index
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

enum Location {
    Rational(BigInt, BigInt),
    Isolated(RealRoot),
}

struct Entry {
    value: Algebraic,
    location: Location,
}

#[derive(Default)]
struct Inner {
    entries: Vec<Entry>,
    by_factor: HashMap<Poly<BigInt>, Arc<Vec<RootRef>>>,
    by_poly: HashMap<Poly<BigInt>, Arc<Vec<RootRef>>>,
}

/// Registry assigning stable identifiers to the algebraic numbers encountered during a computation.
#[derive(Default)]
pub struct Registry {
    inner: Mutex<Inner>,
}

impl Inner {
    fn factor_roots(&mut self, f: &Poly<BigInt>) -> Arc<Vec<RootRef>> {
        if let Some(r) = self.by_factor.get(f) {
            return r.clone();
        }
        let mut refs = Vec::new();
        if f.degree() == Some(1) {
            let (b, a) = (&f.coeffs()[0], &f.coeffs()[1]);
            let num = -b;
            if &num >= a {
                let v = num.to_f64().unwrap_or(f64::NAN) / a.to_f64().unwrap_or(f64::NAN);
                let (lo, hi) = if &num == a { (1.0, 1.0) } else { (v * (1.0 - 1e-14), v * (1.0 + 1e-14)) };
                refs.push(self.push(f, 0, lo, hi, Location::Rational(num, a.clone())));
            }
        } else {
            for (i, mut root) in isolate_roots_above_one(f).into_iter().enumerate() {
                root.refine_to(64);
                let (lo, hi) = root.enclosure();
                refs.push(self.push(f, i, lo, hi, Location::Isolated(root)));
            }
        }
        let refs = Arc::new(refs);
        self.by_factor.insert(f.clone(), refs.clone());
        refs
    }

    fn push(&mut self, f: &Poly<BigInt>, index: usize, lo: f64, hi: f64, location: Location) -> RootRef {
        let id = self.entries.len() as u32;
        self.entries.push(Entry {
            value: Algebraic {
                min_poly: f.clone(),
                index,
                approx: (lo.to_bits(), hi.to_bits()),
            },
            location,
        });
        RootRef { id, lo, hi }
    }
}

impl Registry {
    /// An empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// The distinct real roots not smaller than one of a non-zero polynomial, in no particular order.
    pub fn roots_from_one(&self, p: &Poly<BigInt>) -> Arc<Vec<RootRef>> {
        let key = p.primitive();
        let mut inner = self.inner.lock().expect("registry lock");
        if let Some(r) = inner.by_poly.get(&key) {
            return r.clone();
        }
        let mut refs = Vec::new();
        for (f, _) in factor(&key) {
            refs.extend(inner.factor_roots(&f).iter().copied());
        }
        let refs = Arc::new(refs);
        inner.by_poly.insert(key, refs.clone());
        refs
    }

    /// Sign of a polynomial at a registered number.
    pub fn sign_at(&self, id: u32, q: &Poly<BigInt>) -> i32 {
        let mut inner = self.inner.lock().expect("registry lock");
        match &mut inner.entries[id as usize].location {
            Location::Rational(num, den) => sign_at_rational(q, num, den),
            Location::Isolated(root) => root.sign_of(q),
        }
    }

    /// The registered number with the given identifier.
    pub fn get(&self, id: u32) -> Algebraic {
        self.inner.lock().expect("registry lock").entries[id as usize].value.clone()
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

/// Whether a non-zero polynomial has no real root not smaller than one.
pub fn has_no_root_from_one(p: &Poly<BigInt>) -> bool {
    for (f, _) in factor(p) {
        if f.degree() == Some(1) {
            if -&f.coeffs()[0] >= f.coeffs()[1] {
                return false;
            }
        } else if !isolate_roots_above_one(&f).is_empty() {
            return false;
        }
    }
    true
}
