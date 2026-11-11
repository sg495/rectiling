// SPDX-License-Identifier: LGPL-3.0-or-later

//! Integer coefficient rings: arbitrary precision, and machine words with overflow detection.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, ToPrimitive, Zero};
use std::cell::Cell;
use std::fmt::Debug;
use std::hash::Hash;

thread_local! {
    static OVERFLOW: Cell<bool> = const { Cell::new(false) };
}

/// Returns whether a machine-word operation has overflowed on this thread since the last call, clearing the flag.
pub fn take_overflow() -> bool {
    OVERFLOW.with(|f| f.replace(false))
}

#[cold]
fn flag_overflow() -> i64 {
    OVERFLOW.with(|f| f.set(true));
    0
}

/// Ring of integers used for polynomial coefficients.
pub trait Int: Clone + PartialEq + Eq + Hash + Debug + Send + Sync + 'static {
    /// Converts a machine integer.
    fn from_i64(v: i64) -> Self;
    /// Whether the value is zero.
    fn is_zero(&self) -> bool;
    /// Sign of the value, as -1, 0 or 1.
    fn signum(&self) -> i32;
    /// Sum.
    fn add(&self, o: &Self) -> Self;
    /// Difference.
    fn sub(&self, o: &Self) -> Self;
    /// Product.
    fn mul(&self, o: &Self) -> Self;
    /// Negation.
    fn neg(&self) -> Self;
    /// Quotient of an exact division.
    fn div_exact(&self, o: &Self) -> Self;
    /// Non-negative greatest common divisor.
    fn gcd(&self, o: &Self) -> Self;
    /// Arbitrary-precision copy of the value.
    fn to_big(&self) -> BigInt;
    /// The value as a float, if exactly representable.
    fn to_f64_exact(&self) -> Option<f64>;
}

impl Int for i64 {
    #[inline]
    fn from_i64(v: i64) -> Self {
        v
    }
    #[inline]
    fn is_zero(&self) -> bool {
        *self == 0
    }
    #[inline]
    fn signum(&self) -> i32 {
        i64::signum(*self) as i32
    }
    #[inline]
    fn add(&self, o: &Self) -> Self {
        self.checked_add(*o).unwrap_or_else(flag_overflow)
    }
    #[inline]
    fn sub(&self, o: &Self) -> Self {
        self.checked_sub(*o).unwrap_or_else(flag_overflow)
    }
    #[inline]
    fn mul(&self, o: &Self) -> Self {
        self.checked_mul(*o).unwrap_or_else(flag_overflow)
    }
    #[inline]
    fn neg(&self) -> Self {
        self.checked_neg().unwrap_or_else(flag_overflow)
    }
    #[inline]
    fn div_exact(&self, o: &Self) -> Self {
        if *o == 0 {
            return flag_overflow();
        }
        self.checked_div(*o).unwrap_or_else(flag_overflow)
    }
    #[inline]
    fn gcd(&self, o: &Self) -> Self {
        let (mut a, mut b) = (self.unsigned_abs(), o.unsigned_abs());
        while b != 0 {
            (a, b) = (b, a % b);
        }
        i64::try_from(a).unwrap_or_else(|_| flag_overflow())
    }
    fn to_big(&self) -> BigInt {
        BigInt::from(*self)
    }
    #[inline]
    fn to_f64_exact(&self) -> Option<f64> {
        (self.unsigned_abs() <= (1u64 << 53)).then_some(*self as f64)
    }
}

impl Int for BigInt {
    fn from_i64(v: i64) -> Self {
        BigInt::from(v)
    }
    fn is_zero(&self) -> bool {
        Zero::is_zero(self)
    }
    fn signum(&self) -> i32 {
        Signed::signum(self).to_i32().unwrap_or(0)
    }
    fn add(&self, o: &Self) -> Self {
        self + o
    }
    fn sub(&self, o: &Self) -> Self {
        self - o
    }
    fn mul(&self, o: &Self) -> Self {
        self * o
    }
    fn neg(&self) -> Self {
        -self
    }
    fn div_exact(&self, o: &Self) -> Self {
        self / o
    }
    fn gcd(&self, o: &Self) -> Self {
        Integer::gcd(self, o)
    }
    fn to_big(&self) -> BigInt {
        self.clone()
    }
    fn to_f64_exact(&self) -> Option<f64> {
        self.to_i64().and_then(|v| v.to_f64_exact())
    }
}
