//! **A W-type is a member of a universe** — by coding its trees as sets of
//! labelled finite paths, with no ordinals and no condition on the fibres.
//!
//! # What this module is for
//!
//! `⟦NTree⟧ ∈ U₁` for `NTree.node : (Nat → NTree) → NTree`. `W(A,B,u) ⊆ u` is
//! free — a W-type is Separated out of its bound, and
//! [`crate::bound::least_universe_closed`] makes a universe a legal bound at
//! **any** fibre. What is not free is `W ∈ Uₙ`, a *size* statement, and the
//! `ω`-tower of [`crate::cumul`] buys it only at a fibre satisfying
//! [`crate::cumul::bnd`] — which says a whole fibre-indexed family of trees
//! lands in one stage `Vₚ`, and is **refutable** at `⟦Nat⟧`. That is not a gap
//! in the plumbing: with `Nat`-branching the ranks of the trees are cofinal in
//! `ω₁`, so no `ω`-tall tower catches `W` at all.
//!
//! # The construction
//!
//! Carneiro's *The Type Theory of Lean* §6.2.1 answers this with a rank
//! argument at a regular `κ` with `cf(κ) > sup_{x∈A}|B(x)|`, which needs
//! ordinals and transfinite recursion. This module reaches the same theorem
//! without either, by the move [`crate::wrec`] already made at the recursor —
//! replace the recursion on rank by something the ambient sets already support:
//!
//! ```text
//! paths(A,B,u,Q) ⊆ prod(W, prod(Q,A))
//! ⟨w, ⟨s,x⟩⟩ ∈ paths   ≡   "s is a finite path in the tree w, labelled x"
//! code(w)              :=  { q ∈ prod(Q,A) : ⟨w,q⟩ ∈ paths }
//! ```
//!
//! `code` is injective on `W` ([`paths_injective`], one [`crate::wtype::w_rect`]),
//! so `W` is the image of a subset of `𝒫(prod(Q,A))` under a single-valued
//! relation, and [`crate::cantor::image_in_universe`] — regularity — turns that
//! into `W ∈ Uₙ`.
//!
//! **Every path is finite even when the tree's height is not.** That is the
//! whole of why this works at an arbitrary fibre: a path is built one fibre
//! element at a time, so the ambient `Q` need only be closed under *binary*
//! pairing, where the tower's `sup`-closure needed a whole fibre-indexed
//! function to land in a single stage. The failing hypothesis is not weakened,
//! it is never stated.
//!
//! # The ambient `Q`
//!
//! `Q` is a parameter, constrained by [`amb`]:
//!
//! ```text
//! amb(A,B,Q) := ∅ ∈ Q ∧ ((∀a. (a ∈ A → ∀b. (b ∈ B(a) → b ∈ Q)))
//!                        ∧ (∀x ∀y. ((x ∈ Q ∧ y ∈ Q) → ⟨x,y⟩ ∈ Q)))
//! ```
//!
//! — three facts, none of them about size. The consumer in this crate takes
//! `Q := tower(S)` and discharges all three from [`crate::cumul`], which is why
//! the `ω`-tower survives this change: it is no longer the *catcher* but the
//! set the **paths** live in, and at that job its height is never in question.
//!
//! # The shape of the development
//!
//! | fact | lemma |
//! |---|---|
//! | `p ∈ paths ↔ (p ∈ Bnd ∧ ∀C. …)` | [`paths_symbol`] |
//! | `p ∈ paths → p ∈ prod(W, prod(Q,A))` | [`paths_subset`] |
//! | `(C ⊆ Bnd ∧ path_closed(C)) → paths ⊆ C` — **P2** | [`paths_induction`] |
//! | `path_closed(paths)` — **P1** | [`paths_intro`] |
//! | every member of `paths` arises from a rule — **P3** | [`paths_inversion`] |
//! | `code` is injective on `W` — **P4** | [`paths_injective`] |
//! | `W(A,B,u) ∈ U(d)` | [`w_in_universe_paths`] |
//!
//! **Nothing here is an axiom.** `paths` is one Separation on
//! `prod(W, prod(Q,A))`; `code(w)` is one more, per call. Everything else is
//! derived from the W-type apparatus already in this crate.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here.
//!
//! | file | what it exports |
//! |---|---|
//! | [`condition`] | [`At`], the four formulas, the symbol, and `paths ⊆ Bnd` |
//! | [`induction`] | **P2** — `paths` is the least closed subset of the ambient |
//! | [`intro`] | **P1** — [`amb`], and the two rules hold of `paths` itself |
//! | [`inversion`] | **P3** — no junk: every member of `paths` arises from a rule |
//! | [`injective`] | **P4** — the code determines the tree |
//! | [`member`] | [`w_in_universe_paths`], by regularity |

pub mod condition;
pub mod decompose;
pub mod induction;
pub mod injective;
pub mod intro;
pub mod inversion;
mod shared;

pub use condition::{
    path_closed, path_cond, path_root, path_step, paths_subset, paths_symbol, At,
};
pub use decompose::{root_label, step_premise};
pub use induction::paths_induction;
pub use injective::{paths_injective, sub_paths};
pub use intro::{amb, paths_intro};
pub use inversion::{arises_root, arises_step, path_arises, paths_inversion};
