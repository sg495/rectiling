// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exact enumeration of tilings of a rectangle by similar rectangles.

pub mod algebraic;
pub mod factor;
pub mod int;
pub mod interval;
pub mod poly;
pub mod roots;

pub use algebraic::Algebraic;
pub use poly::Poly;
