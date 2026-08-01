//! Cartesian products, function spaces, and the fact the tutorial needs:
//! `(a → a) ∈ U(a)`.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::funspace::…` all still resolve and no caller has to know which file
//! a theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`cartesian`] | the symbol `prod(a,b) = a × b` and its membership condition, unconditionally |
//! | [`pow_pow`] | the term `a ∪ b`, `⟨x,y⟩ ∈ 𝒫𝒫c`, and `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` |
//! | [`space`] | `isfun`, the symbol `fs(a,b)`, and `fs(a,b) ⊆ 𝒫(prod(a,b))` |
//! | [`identity`] | `id(a)`, that it is a function, and `fs(a,a)`'s members |
//! | [`closure`] | `𝒫y ∈ u` and "subset of a member" from `C₂(u)`, `C₃(u)` alone |
//! | [`in_universe`] | `fs(a,b) ∈ U(c)` conditionally, and `fs(a,a) ∈ U(a)` outright |
//! | [`pi_rule`] | `prod(a,b) ∈ U(c)` and `fs(a,b) ∈ U(c)`, both unconditional |
//! | [`glue`] | one export, [`discharge`]; the rest are private readers |
//!
//! # Why the product is built from Replacement, not Separation
//!
//! The textbook construction cuts `a × b` out of `𝒫𝒫(a ∪ b)` by Separation.
//! When this was written the only Separation available was
//! [`crate::separation::separation_nonvacuous`] (equivalently
//! [`crate::funcs::separation_nonempty`]), which requires the *result* to be
//! inhabited — and `a × b` really can be empty, so no witness could be
//! supplied. So the product is assembled from Replacement instead, where every
//! step is *total* and no inhabitation is needed:
//!
//! ```text
//! row(x, b) := { ⟨x,y⟩ : y ∈ b }        — Replacement along y ↦ ⟨x,y⟩
//! fam(a, b) := { row(x,b) : x ∈ a }     — Replacement along x ↦ row(x,b)
//! prod(a, b) := ⋃ fam(a, b)
//! ```
//!
//! Both Replacement instances have the trivial `∃!` premise `∃!v. v = t`, which
//! [`crate::exists_unique_eq`] discharges for free, and the final union is an
//! explicit definition. The characteristic property
//! `z ∈ prod(a,b) ↔ ∃x. (x ∈ a ∧ ∃y. (y ∈ b ∧ z = ⟨x,y⟩))` therefore holds
//! **unconditionally** — no inhabitation antecedent anywhere.
//!
//! # The function space, and the antecedent that used to survive
//!
//! The function space *is* carved out of a power set by a condition, and `a → b`
//! is empty when `a` is inhabited and `b` is not. For as long as Separation
//! needed its result inhabited, `fs(a,b)` had to be defined by the same
//! total-by-default trick [`crate::funcs::collection`] used — an extra
//! disjunct firing only when there were no functions at all, degenerating to
//! `𝒫(prod(a,b))` — and [`funspace_members`] was conditional on
//! `∃g. isfun(g)`, dischargeable only on the diagonal via the identity
//! function.
//!
//! `∅` removes all of that. [`crate::funcs::separation_full`] produces the
//! separated set whether or not it is inhabited, so [`funspace`] defines the
//! intended condition outright and
//!
//! ```text
//! ⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))
//! ```
//!
//! holds with no antecedent, for every `a` and `b` rather than only on the
//! diagonal. [`funspace_subset_pow_prod`] is unchanged (it was already
//! unconditional), and [`funspace_diagonal_members`] survives as the `b := a`
//! instance the universe argument quotes.
//!
//! # The chain to `(a → a) ∈ U(a)`
//!
//! | step | lemma |
//! |---|---|
//! | `a ∈ U(a)` | [`crate::universe::mem_least_universe`] |
//! | `y ∈ U(x) → 𝒫y ∈ U(x)` | [`pow_closed`] |
//! | `(y ∈ U(x) ∧ z ⊆ y) → z ∈ U(x)` | [`sub_closed`] |
//! | `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` | [`product_subset_pow_pow`] |
//! | `fs(a,b) ⊆ 𝒫(prod(a,b))` | [`funspace_subset_pow_prod`] |
//! | `f ∈ fs(a,b) ↔ isfun(f)` | [`funspace_members`] |
//! | `(a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c)` | [`funspace_in_universe_of`] |
//! | `(a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ⊆ U(c)` | [`crate::bound::funspace_subset_least_universe`] |
//! | `a ∪ a = a` | [`crate::union_singleton`] |
//! | `fs(a,a) ∈ U(a)` | [`funspace_in_universe`] |
//!
//! **The two-argument case is now complete.** Everything above `a ∪ b` always
//! went through, which is why [`funspace_in_universe_of`] is stated in full
//! with `(a ∪ b) ∈ U(c)` as its antecedent; discharging it from `a ∈ U(c)` and
//! `b ∈ U(c)` is closure of `U(c)` under binary unions, and that is
//! [`crate::universe::least_universe_bin_union`]. So
//! [`funspace_in_universe_pair`] proves
//! `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))` outright, and
//! [`product_in_universe`] the same for `prod(a,b)`. What follows in this
//! comment is the record of why that took as long as it did.
//!
//! Until 2026-07-31 that was **false**, not open: `ax_tarski` had no
//! transitivity clause, and the countermodels at the end of [`crate::universe`]
//! refuted `(a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c)` and
//! `(a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c)` outright in the standard model.
//! With the `C₁` clause those countermodels are no longer models, and the
//! statements are **open, not refutable**. What is now available and was not:
//!
//! * `U(c)` is transitive ([`crate::universe::least_universe_transitive`]), so
//!   `a ∪ b ⊆ U(c)` for members `a, b`;
//! * a subset of a universe that is the surjective image of a member is a
//!   member ([`crate::cantor::image_in_universe`]) — regularity, which is what
//!   turns `C₄`'s disjunction into a closure property.
//!
//! Binary union is `⋃{a,b}`, so what was needed was `⋃`-closure, and that is
//! [`crate::universe::universe_union_closed`]. The antecedent of
//! [`funspace_in_universe_of`] is therefore discharged in
//! [`funspace_in_universe_pair`]; the conditional statement is kept because
//! `crate::ext` and `crate::checker` consume it.
//!
//! **How far the product-free route actually reaches.** It was expected that
//! `fs(a,b) ∈ U(c)` would avoid the binary union entirely, on the grounds that
//! `f ∈ fs(a,b)` is a set of Kuratowski pairs of members of `U(c)`. That route
//! is real and is now derived — [`crate::bound::funspace_subset_least_universe`]
//! gives
//!
//! ```text
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ⊆ U(c))
//! ```
//!
//! with no product and no union — but it stops one step short of the goal: it
//! makes every *member* of `fs(a,b)` a member of `U(c)`, which is `⊆`, not `∈`.
//! Turning that into membership needs a member of `U(c)` surjecting onto
//! `fs(a,b)`, for which the only candidate is `𝒫(prod(a,b))`. So the remaining
//! obligation really was `prod(a,b) ∈ U(c)`, hence `(a ∪ b) ∈ U(c)`, and the
//! route that finally closed it went the other way round: `⋃`-closure first
//! ([`crate::universe::universe_union_closed`]), then binary union, then the
//! product and the function space as subsets of iterated power sets. No axiom
//! was added to route around any of it.
//!
//! At `b = c = a` the antecedent becomes `(a ∪ a) ∈ U(a)`, and `a ∪ a` is
//! `⋃{a,a}` — that is, `⋃{a}`, which [`crate::union_singleton`] equates with
//! `a`. So the binary union disappears rather than having to be closed over,
//! and [`funspace_in_universe`] is unconditional. That is the case the tutorial
//! needs.

pub mod cartesian;
pub mod closure;
pub mod glue;
pub mod identity;
pub mod in_universe;
pub mod pi_rule;
pub mod pow_pow;
pub mod space;

pub use cartesian::{product, product_cond, Product};
pub use closure::{pow_closed, sub_closed};
pub use glue::discharge;
pub use identity::{
    diagonal_inhabited, funspace_diagonal_members, identity_graph, identity_is_function,
};
pub use in_universe::{funspace_in_universe, funspace_in_universe_of, Development, Space};
pub use pi_rule::{funspace_in_universe_pair, product_in_universe, product_in_universe_of};
pub use pow_pow::{
    bin_union, mem_bin_union, pair_in_pow_pow, product_subset_pow_pow, upair_subset,
};
pub use space::{
    funspace, funspace_members, funspace_subset_pow_prod, is_function, is_single_valued, is_total,
    Funspace,
};
