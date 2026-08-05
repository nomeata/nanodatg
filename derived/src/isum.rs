//! The iterated binary sum at arbitrary depth, and its `rec₊` dispatcher —
//! §5.2's tag set and its case function, at the arity a declaration actually
//! has.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::isum::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`tags`] | [`ISum`] — the term `A₀ + (… + (A_{n-1} + 0))`, the `n` injections, their memberships, injectivity and pairwise disjointness |
//! | [`dispatch`] | [`Dispatch`] — the nested `rec₊`, its typing rule, and the `n` computation rules `app(disp, Inj_i(a)) = app(fᵢ,a)` |
//! | [`symbols`] | [`ISumSyms`] — `Sum_n` and `Inj_i` as **real symbols**, cached per arity and per depth, exposing membership, injectivity, distinctness and **no junk** with the nest hidden |
//! | [`in_universe`] | `⊢ ∀c. finord(m) ∈ U(c)` — the finite-ordinal fibre is a member of every universe |
//! | [`restrict`] | [`Branch`] — `f|ⱼ = { ⟨z, app(f, Injⱼ(z))⟩ : z ∈ Aⱼ }`, the restriction of a function on the sum to one summand, with its computation rule and its typing rule |
//!
//! **Callers should use [`symbols`].** [`tags`] is the construction: its term
//! formers inline the whole nest at every mention, which is `O(n)` for the tag
//! set and `O(i)` for each injection. [`symbols`] names both and is what every
//! downstream statement in this crate is stated over; `tags` remains public
//! only because `symbols` is derived from it and because a failed proof is
//! unfolded through it.
//!
//! # Why this exists
//!
//! The thesis's `spec` judgment (`thesis.txt:1789–1791`) recurses on the
//! constructor list, producing a right-nested sum for the tag set and a
//! right-nested `rec₊` for the fibre family. `derived/src/sums/` supplies the
//! *binary* step of each and nothing iterated, which is why
//! `derived/src/enums.rs`, `wnat.rs` and `wlist.rs` are stuck at two
//! constructors. These two files are the iteration.
//!
//! # What is a nest, and what is a real symbol
//!
//! [`tags`] and [`dispatch`] are meta-level nests of symbols [`crate::sums`]
//! already introduced — `sum` and `case` — so *those two* add no definitional
//! extension and no axiom. What they add is the *induction on `n`*, carried out
//! in Rust, that turns the binary lemmas into families of theorems indexed by
//! the constructor count.
//!
//! [`symbols`] is different, and this section used to deny it: `ISumSyms` calls
//! `define_abbrev` per arity and per depth, so `Sum_n` and `Inj_i` **are** real
//! defined symbols and this module does make definitional extensions. They are
//! conservative in the usual way — `define_abbrev` names an existing term — and
//! no axiom is added. The distinction that matters downstream is only that a
//! statement over `symbols` mentions a symbol rather than an inlined nest.

pub mod dispatch;
pub mod in_universe;
pub mod restrict;
pub mod symbols;
pub mod tags;

pub use dispatch::{dispatch_of, Dispatch};
pub use in_universe::{
    finord_in_universe, finords_in_universe, isum_in_universe, isum_in_universe_under, SumClosure,
};
pub use restrict::{branch_in_funspace, Branch};
pub use symbols::ISumSyms;
pub use tags::{finord, inj_distinct, inj_injective, inj_mem_at, inj_of, isum_of, ISum};
