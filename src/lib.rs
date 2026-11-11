// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exact enumeration of tilings of a rectangle by similar rectangles.

pub mod algebraic;
pub mod factor;
pub mod form;
pub mod int;
pub mod interval;
pub mod poly;
pub mod roots;
pub mod search;

pub use algebraic::Algebraic;
pub use poly::Poly;
pub use search::{Fit, Found, Outcome, Placement, Search, Stats, count_layouts};
