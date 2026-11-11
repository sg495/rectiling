// SPDX-License-Identifier: LGPL-3.0-or-later

//! Exact enumeration of tilings of a rectangle by similar rectangles.

pub mod algebraic;
mod bags;
pub mod band;
mod cache;
mod chunked;
mod exact;
pub mod factor;
mod fast;
mod form;
pub mod guillotine;
pub mod int;
pub mod interval;
mod modular;
mod pack;
pub mod poly;
pub mod roots;
pub mod search;
pub mod staircase;
mod tilings;

pub use algebraic::Algebraic;
pub use band::Band;
pub use guillotine::count_guillotine_ratios;
pub use poly::Poly;
pub use search::{Found, Outcome, Search, Stats, Tiling};
pub use staircase::{Fit, Placement, count_layouts};
pub use tilings::{Census, SYMMETRIES};
