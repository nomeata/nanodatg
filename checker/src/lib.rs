//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
#![allow(clippy::too_many_arguments)]
#![deny(clippy::cast_possible_truncation)]

pub mod certify;
pub mod const_store;
pub mod debug_printer;
pub mod env;
pub mod expr;
pub mod inductive;
pub mod instantiations;
pub mod level;
pub mod name;
pub mod parser;
pub mod pretty_printer;
pub mod quot;
pub(crate) mod reduct;
pub mod scope;
pub mod sealed;
pub mod stepcount;
pub mod tc;
pub mod tg;
#[cfg(test)]
mod tests;
pub mod union_find;
pub mod unique_hasher;
pub mod util;

pub(crate) const STACK_SIZE: usize = 16_777_216;
