//! The **one-point extension** of the recursor, and that it is an attempt.
//!
//! # What this is for
//!
//! Totality ([`crate::wrec_total`]) is structural induction at
//! `φ(z) := indom(wrec, z)`, and its induction step is: given `a ∈ A`,
//! `f ∈ fs(B(a), W)` and `∀b ∈ B(a). indom(wrec, app(f,b))`, put `⟨a,f⟩` into
//! the recursor's domain. The only way in is
//! [`crate::wrec::attempt_indom_wrec`] — the domain of *any* attempt is
//! included in the recursor's — so an attempt containing `⟨a,f⟩` has to be
//! exhibited. It is
//!
//! ```text
//! V := app(e, ⟨a, ⟨f, comp(wrec,f,B(a))⟩⟩)
//! G := wrec ∪ {⟨⟨a,f⟩, V⟩}
//! ```
//!
//! and this file proves `G ∈ Att`. That is the whole of the induction step; the
//! induction itself is four lines.
//!
//! # Interface
//!
//! Writing `K` for the induction step's hypothesis bundle
//!
//! ```text
//! K := (((closed(A,B,u) ∧ step_typed(A,B,u,T,e)) ∧ a ∈ A) ∧ f ∈ fs(B(a),W))
//!          ∧ ∀b. (b ∈ B(a) → indom(wrec, app(f,b)))
//! ```
//!
//! — built by [`hypothesis`], so that a caller cannot get the nesting wrong —
//! the single export [`extension`] returns all five of
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀a ∀f. (K → sv(G))                      [Extension::sv]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀a ∀f. (K → G ∈ 𝒫(prod(W,T)))           [Extension::in_pow]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀a ∀f. (K → rec_cond(B,e,G))            [Extension::rec_cond]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀a ∀f. (K → G ∈ Att(A,B,u,T,e))         [Extension::attempt]
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀a ∀f. (K → indom(wrec, ⟨a,f⟩))         [Extension::indom]
//! ```
//!
//! in one pass, because they share a context and the two lemmas
//! `value_at_new_point` and `agreement`, neither of which is cheap. The
//! last line is the whole induction step; the other four are the clauses it is
//! assembled from, exported because a reader who does not believe the fifth
//! should be able to check the four.
//!
//! # Where each hypothesis is spent
//!
//! * `closed(A,B,u)` — three times: `sv(wrec)`, `rec_cond(wrec)`, and W1 for
//!   `⟨a,f⟩ ∈ W`.
//! * `step_typed` — **once**, and only in the inclusion `G ⊆ prod(W,T)`: it is
//!   what puts `V` in `T`. Its third premise, `comp(wrec,f,B(a)) ∈ fs(B(a),T)`,
//!   is [`crate::wrec_typing::wrec_composite_typed`] applied to the induction
//!   hypothesis.
//! * `a ∈ A` and `f ∈ fs(B(a),W)` — only to place `⟨a,f⟩` in `W`, and to feed
//!   `step_typed`.
//! * the induction hypothesis — twice: to type the composite, and to make the
//!   *new* point's subterm clause hold, since `G`'s domain has to contain
//!   `app(f,b)` for every `b ∈ B(a)`.
//!
//! # The shape of the two hard clauses
//!
//! **`sv(G)`.** Four cases threaten, from two membership disjunctions, and they
//! collapse to three because of `value_at_new_point`: *every* `G`-value at
//! `⟨a,f⟩` is `V`, whether it came from `wrec` or from the new pair. That lemma
//! is where step 3 pays for itself — if `⟨a,f⟩` was already in `dom wrec`, then
//! [`crate::wrec::wrec_rec_cond`] forces `app(wrec,⟨a,f⟩)` to be `V` already, so
//! no case analysis on "is it there already" is needed anywhere.
//!
//! **`rec_cond(G)`.** Two cases: an old point, where `wrec`'s own recursion
//! condition transfers; and `⟨a,f⟩` itself, where [`crate::pairs::opair_inj`]
//! recovers `a` and `f` and the equation is `V`'s definition. Both need the
//! composite moved from `wrec` to `G`, which is [`crate::wrec::compose_ext`]
//! against `agreement` — `wrec` and `G` take the same values everywhere
//! `wrec` is defined, because `wrec ⊆ G` and `G` is single-valued.
//!
//! The new-point case proves its goal at `a` and `f` and then **carries it
//! back** along `a′ = a` and `f′ = f` with two Leibniz steps, rather than
//! rewriting the hypotheses forwards. That is why the recursion condition's
//! body is built by a closure taking the constructor and the family: the two
//! substitution instances have to be the same formula on the nose, and a
//! closure is the only way to be sure they are.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::wrec_extend::…` all still resolve. Read the header of the one file
//! you need.
//!
//! | file | what it holds |
//! |---|---|
//! | [`terms`] | [`ext_of`], [`hypothesis`], and the context struct `Cx` |
//! | [`value`] | the value at the new point, `app(G, ⟨a,f⟩) = v` |
//! | [`single_valued`] | clause 1 of the attempt condition |
//! | [`product`] | clause 2 — a set of pairs over the W-type |
//! | [`recursion`] | clause 3 — the recursion condition, the long half |
//! | [`assemble`] | [`Extension`] and [`extension`] — the three clauses put together |
//!
//! `shared` holds the private implication-form movers more than one of them
//! needs; it exports no theorem and is not re-exported.

pub mod assemble;
pub mod product;
pub mod recursion;
mod shared;
pub mod single_valued;
pub mod terms;
pub mod value;

pub use assemble::{extension, Extension};
pub use terms::{ext_of, hypothesis, new_value};
