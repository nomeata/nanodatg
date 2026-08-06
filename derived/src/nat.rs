//! **Arithmetic on `ω`, in two views of the same set.**
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here.
//!
//! | file | what it exports |
//! |---|---|
//! | [`mod@glue`] | equational chains, template congruence, and the induction assembly |
//! | [`apparatus`] | [`Nat`] — `ω`, `0`, `succ`, `ω ∈ U₁`, the recursor `natrec` and its two ι rules |
//! | [`add`] | [`Add`] — `add` by iteration, its two Peano equations, and the ring facts the binary view runs on |
//!
//! # One set, two views
//!
//! The carrier is `ω` and there is exactly one of it. `0` and `succ` are the
//! von Neumann ones, the recursor is [`Nat::natrec`], and `add` is defined by
//! iterating `succ`. **On the same carrier** the binary view adds
//!
//! ```text
//! double(x)  := add(x,x)          double1(x) := succ(double(x))
//! ```
//!
//! which are not a second type and not a second representation: they are
//! further defined symbols on `ω`, and a *numeral* is a term built from them.
//! There is no `val : B → ⟦Nat⟧`, no injectivity obligation and no
//! representation invariant, because there is nothing to relate — `double` and
//! `succ` are operations on one set and every equation between them is an
//! equation in that set.
//!
//! The point of the second view is **term size**. A unary numeral for `2⁶⁴` has
//! 1.8 × 10¹⁹ nodes and cannot be written down; the binary one is
//! `double⁶⁴(double1(0))`, **66 nodes**, and every operation on it costs work
//! polynomial in the *bit length* rather than in the value.
//!
//! # Nothing here knows what `Nat` is
//!
//! `derived/` is Lean-agnostic and this module keeps it that way: it speaks of
//! `ω`, `succ` and `add`, never of a declaration, a literal or an `Expr`. A
//! checker that wants to interpret some inductive type as `ω` has everything it
//! needs in [`Nat`]'s interface, and nothing below changes if it does not.

pub mod add;
pub mod apparatus;
pub mod glue;

pub use add::Add;
pub use apparatus::Nat;
pub use glue::{congr1, congr2_l, congr2_r, congr_tmpl, induct, induct_step, Chain};
