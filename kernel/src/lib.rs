//! # `kernel` — the trusted computing base
//!
//! This crate is the **only** component that must be correct for the whole
//! system to be sound. The threat model (see `CLAUDE.md`) is a single one: a
//! bug in Lean's kernel lets someone derive `False`. Everything outside this
//! crate — the parser, the Lean type checker, the interpretation into set
//! theory — is *untrusted*. A bug there produces a *rejection*, never a false
//! theorem.
//!
//! ## What lives here
//!
//! A small LCF-style kernel for Tarski–Grothendieck set theory, and **nothing
//! else**. The interface is the type theory itself:
//!
//! * [`Term`] and [`Formula`] — first-order syntax over `{∈,=}` ([`term`]).
//! * [`Thm`] — the opaque theorem, a sequent `Γ ⊢ φ` carrying a canonically
//!   ordered set of hypotheses beside its conclusion, whose only constructors
//!   are the primitive inference rules and the axioms, so an ill-formed proof
//!   cannot be expressed ([`thm`]). Conservative definitional extension lives
//!   here too, along with the [`Env`] of symbols a development has introduced.
//!
//! Hypotheses are carried *beside* the formula, Isabelle-style, rather than
//! encoded as antecedents inside it; every rule unions its premises' sets, so a
//! theorem built without [`Thm::assume`] has an empty set and behaves exactly as
//! it did before hypotheses existed. The reasoning, the side conditions this
//! forces on `gen` and `define`, and **the obligation it places on every reader
//! of a conclusion outside this crate** — a `Thm` establishes its conclusion only
//! when `hyps()` is empty, the checker's definitional-equality cache being the
//! instance that prompted the point — are in [`thm`]'s module docs.
//!
//! What is deliberately *not* here is the interface the untrusted checker drives
//! this crate through — the `Certifier` proof-backend trait and its null
//! implementation. Neither constructs a [`Thm`], so neither can affect
//! soundness, and a trait whose methods mention Lean's expression type has no
//! business in a crate that must not know what Lean is. Both live in
//! `checker/src/certify.rs`, on the untrusted side of the boundary, where the
//! dependency they induce points untrusted → trusted as it must.
//!
//! ## Boundary rules (enforced in CI, see `ci/check-boundary.sh`)
//!
//! * No `unsafe` anywhere. This is enforced at compile time by the crate-level
//!   `#![forbid(unsafe_code)]` below, *and* by the CI grep.
//! * No external crate dependencies (one sanctioned future exception: a vetted
//!   bignum crate for native arithmetic in milestone 4).
//! * `Thm`'s fields are private and it has no public constructor.
//! * No I/O, no serialization, no printing of derivations.

// The kernel must never contain `unsafe`. Enforced by the compiler, not just by
// a grep over the source.
#![forbid(unsafe_code)]
// The kernel is dependency-free and must not silently pull in `std` conveniences
// that would complicate an eventual audit; `core`/`alloc` is all it needs. We do
// use `std` for `HashMap` in later milestones, so this stays as documentation of
// intent rather than `#![no_std]` for now.
#![deny(missing_docs)]

pub mod term;
pub mod thm;

pub use term::{FnSym, Formula, FreeVar, Term};
pub use thm::{Env, Thm};
