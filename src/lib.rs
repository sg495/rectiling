// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exact enumeration of tilings of a rectangle by similar rectangles.

pub mod algebraic;
mod cache;
mod exact;
pub mod factor;
mod fast;
mod form;
pub mod int;
pub mod interval;
mod pack;
pub mod poly;
pub mod roots;
pub mod search;
pub mod staircase;

pub use algebraic::Algebraic;
pub use poly::Poly;
pub use search::{Found, Outcome, Search, Stats};
pub use staircase::{Fit, Placement, count_layouts};
