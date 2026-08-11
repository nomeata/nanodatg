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
//! | [`mul`] | [`Mul`] — `mul` by parametric recursion, distributivity, and the two binary equations |
//! | [`prim`] | [`prim_rec`] — primitive recursion with a parameter, which the ambient recursion theorem's fixed unary step cannot express |
//! | [`typing`] | [`natrec_mem`] — the recursor's value lands in the motive's fibre, by one induction over the two ι rules |
//! | [`unique`] | [`uniqueness`] — any operation satisfying the two Peano equations *is* `add`, and [`transfer`] fires it |
//! | [`eval`] | [`Eval`] — the certified evaluator for `succ`/`add`/`addc` at numerals, with an exact kernel-inference meter |
//! | [`binary`] | [`Binary`] — `double`, `double1`, `addc`, the numeral encoding, and the eight binary recursion equations |
//! | [`mod@sub`] | [`Sub`] — `pred`, truncated subtraction, and the zero test |
//! | [`compare`] | [`Compare`] — `ble`, `blt`, `beq` and their twelve binary recursion equations |
//! | [`ble_unique`] | [`ble_uniqueness`] — any operation satisfying `ble`'s three clauses *is* `ble`, decoded; and [`ble_transfer`] fires it |
//! | [`boolean`] | [`Boolean`] — the two-valued decode from `succ 0`/`0` to a caller-supplied pair, and the three comparisons composed with it |
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
//! # How everything here fails
//!
//! Every fallible entry returns [`crate::DResult`], not `Option`. Two shapes
//! reach a caller and the distinction is the point (see [`crate::err`]):
//!
//! * an **assembly failure** — a kernel primitive handed data it cannot accept,
//!   produced by [`crate::prim`] with the offending operands attached. That is
//!   nearly every refusal in this module, because nearly every refusal here is
//!   the code checking its *own* work: an equation it just built not being an
//!   equation, a chain link whose two ends do not meet, a generalisation over a
//!   variable of a hypothesis it forgot to discharge. [`glue::imported`] is the
//!   same verdict for the constructions in `crate::recursion`, `crate::tower`,
//!   `crate::proj` and `crate::point_fun` that this module is built on and that
//!   have not been migrated.
//! * a **decline** — a contract refusal. There are exactly two:
//!   [`glue::congr_tmpl`] handed a hole variable that occurs in the equation it
//!   is asked to rewrite, and [`Eval::mul`] on an evaluator built without
//!   multiplication.
//!
//! **This module is the only place in `derived/` that introduces a hypothesis**
//! — [`crate::discharge`]'s only importers are its files — so it is the only
//! place where [`kernel::Thm::gen`]'s side condition is live. It therefore does
//! not use [`crate::gen_all`], which folds the *panicking* rule;
//! [`glue::gen_all`] is the same fold over [`crate::prim::gen`], and reports.
//! What every export owes is `⊢`, and `derived/tests/nat.rs` asserts
//! [`crate::all_unconditional`] on every theorem field of every bundle below —
//! with a field-exhaustive pattern, so a new field cannot slip past it.
//!
//! # Nothing here knows what `Nat` is
//!
//! `derived/` is Lean-agnostic and this module keeps it that way: it speaks of
//! `ω`, `succ` and `add`, never of a declaration, a literal or an `Expr`. A
//! checker that wants to interpret some inductive type as `ω` has everything it
//! needs in [`Nat`]'s interface, and nothing below changes if it does not.

pub mod add;
pub mod apparatus;
pub mod binary;
pub mod ble_unique;
pub mod boolean;
pub mod compare;
pub mod eval;
pub mod glue;
pub mod mul;
pub mod prim;
pub mod sub;
pub mod succ_fun;
pub mod typing;
pub mod unique;

pub use add::Add;
pub use apparatus::Nat;
pub use binary::Binary;
pub use ble_unique::{ble_transfer, ble_uniqueness, BleClauses, BleSpec};
pub use boolean::{Boolean, Decode};
pub use compare::Compare;
pub use sub::Sub;
pub use succ_fun::SuccFun;
pub use eval::{numeral_size, Eval, Meter};
pub use mul::Mul;
pub use prim::{prim_rec, PrimRec};
pub use typing::natrec_mem;
pub use unique::{transfer, uniqueness, uniqueness_pointwise, Spec};
pub use glue::{congr1, congr2_l, congr2_r, congr_tmpl, induct, induct_step, Chain};
