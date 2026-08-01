//! **Quotients** — `A/∼`, `mk`, `sound` and `lift`, over the equivalence
//! closure of an arbitrary relation.
//!
//! Following Carneiro's *The Type Theory of Lean* §6.2: "let `∼` be the
//! equivalence closure of `⟦Γ ⊢ R⟧γ`", after which
//!
//! ```text
//! ⟦Γ ⊢ α/R⟧γ            = ⟦Γ ⊢ α⟧γ / ∼
//! ⟦Γ ⊢ mk_R x⟧γ         = [⟦Γ ⊢ x⟧γ]∼
//! ⟦Γ ⊢ lift_R β f h⟧γ   is the function with ⟦lift_R β f h⟧γ([x]∼) = ⟦f⟧γ(x)
//! ⟦Γ ⊢ sound_R⟧γ        = •
//! ```
//!
//! `sound` and `propext` interpret to `•` — they are proofs, and proofs carry no
//! information — so what has to be *derived* on the set side is that the
//! equations those proofs assert really hold. That is [`classes::q_sound`].
//!
//! **Nothing here is an axiom.** The closure is one Separation on `prod(A,A)`,
//! the class is one Separation on `A`, the quotient set is one Separation on
//! `𝒫A`, and `lift`'s graph is one Replacement over `A`. Everything else is
//! derived from those plus the pairing, product, power set and function space
//! apparatus already in this crate.
//!
//! # Why this stays bespoke
//!
//! `Quot` is **primitive in Lean**, not an ordinary inductive: it has no
//! constructors to compile, no recursor generated from a set of introduction
//! rules, and its computation rule `Quot.lift f h (Quot.mk r a) ≡ f a` is a
//! ι-rule the kernel builds in. So the general inductive procedure in
//! [`crate::inductive`] does not and cannot cover it, and this module is not
//! superseded by that one.
//!
//! # Interface
//!
//! [`Quotient`] is the whole thing, assembled over one [`crate::sums::Sums`].
//! The headline theorems, writing `[x]` for `class(A,R,x)` and `A/∼` for
//! `quot(A,R)`:
//!
//! ```text
//! ⊢ ∀A ∀R ∀x. (x ∈ A → [x] ∈ A/∼)                                 [mk]
//! ⊢ ∀A ∀R ∀a ∀b. ((a ∈ A ∧ (b ∈ A ∧ ⟨a,b⟩ ∈ R)) → [a] = [b])      [sound]
//! ⊢ ∀A ∀R ∀c. (c ∈ A/∼ → ∃x. (x ∈ A ∧ c = [x]))                   [no junk]
//! ⊢ ∀A ∀R ∀f ∀x. ((compat(A,R,f) ∧ x ∈ A)
//!                     → app(lift(A,R,f), [x]) = app(f,x))         [lift computes]
//! ⊢ ∀A ∀R ∀B ∀f. ((f ∈ fs(A,B) ∧ compat(A,R,f))
//!                     → lift(A,R,f) ∈ fs(A/∼, B))                 [lift types]
//! ⊢ ∀A ∀R ∀f. (rcompat(A,R,f) → compat(A,R,f))                    [Lean's h suffices]
//! ```
//!
//! # The three things that were not obvious
//!
//! * **No transitive-closure recursion.** The equivalence closure is the
//!   intersection of all equivalence relations on `A` containing `R`, phrased as
//!   a *condition* rather than as `⋂{E ∈ 𝒫(A²) : …}` — the same idiom
//!   [`crate::wtype`] uses, which keeps it to one Separation and needs no power
//!   set. Reflexivity, symmetry, transitivity and "contains `R`" are Horn
//!   conditions, so they survive the intersection by direct instantiation; no
//!   ω-indexed union of relation powers is built. See [`eqv`].
//!
//! * **Lean's `Quot.lift` hypothesis is about `R`, `lift`'s well-definedness is
//!   about `∼`, and the gap is an induction.** [`compat::compat_closure`] closes
//!   it by instantiating [`eqv::eqv_induction`] at the kernel `ker(A,f)` of the
//!   function. This is the only place minimality of the closure is used for the
//!   interface proper, and it is why the intersection definition earns its keep.
//!
//! * **Non-vacuity is not free.** Every theorem here is satisfied by
//!   `eqv(A,R) = A²`, which collapses `A/∼` to a point. [`witness`] rules that
//!   out: at `R := ∅` the closure is inside the diagonal, so `mk` is injective
//!   and the quotient is as big as `A`. It gets there by the *same*
//!   `ker`-induction, at `f := id(A)`.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::quot::…` all still resolve. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`eqv`] | the closure `∼` by intersection: the symbol, minimality, and the four closure properties |
//! | [`classes`] | `class(A,R,x)`, `quot(A,R)`, `mk`, `sound`, and exactness |
//! | [`lift`] | the eliminator: its graph, well-definedness, computation rule and typing rule |
//! | [`compat`] | `ker(A,f)`, and Lean's `Quot.lift` hypothesis implying `lift`'s |
//! | [`witness`] | non-vacuity: `eqv(A,∅)` is the diagonal, and every `f` is compatible with `∅` |
//! | [`apparatus`] | [`Quotient`] — every symbol and theorem over one definitional extension |
//!
//! `shared` holds the private combinators more than one of them needs
//! (instantiating a nest of `∀`s, taking a conjunction apart, carrying a
//! membership across an equation, and existential elimination under a fixed
//! hypothesis); it exports no theorem and is not re-exported.
//!
//! # What is *not* here
//!
//! * `Quot.ind` — the eliminator into `Prop`. Its interpretation is `•`, so
//!   there is nothing set-theoretic to derive; what a consumer needs is
//!   [`classes::quot_cases`], the no-junk lemma, which is here.
//! * `quot(A,R) ∈ U(c)` — the universe membership. It is one Separation inside a
//!   power set, so it needs closure of `U(c)` under `𝒫` and under Separation,
//!   both of which exist in [`crate::universe`]; it is not derived here because
//!   nothing consumes it yet.
//! * The checker-side wiring that turns these theorems into certificates for
//!   `Quot.mk` / `Quot.lift` / `Quot.ind` declarations. That is a separate,
//!   later step in `checker/`, and none of it is part of this module.

pub mod apparatus;
pub mod classes;
pub mod compat;
pub mod eqv;
pub mod lift;
mod shared;
pub mod witness;

pub use apparatus::Quotient;
pub use classes::{
    class_eq, class_exact, class_self, class_subset, class_symbol, mk_mem, q_sound, quot_cases,
    quot_symbol, Classes,
};
pub use compat::{
    compat_closure, ker_closed, ker_pair, ker_subset, ker_symbol, pair_in_ker, rcompat, Ker,
};
pub use eqv::{
    contains_rel, eqv_atoms, eqv_closed, eqv_closed_self, eqv_cond, eqv_guard, eqv_incl,
    eqv_induction, eqv_refl, eqv_subset, eqv_sym, eqv_symbol, eqv_trans, reflexive_on, symmetric,
    transitive,
};
pub use lift::{
    compat, lift_beta, lift_in_funspace, lift_pair, lift_single_valued, lift_symbol, Lift,
};
pub use witness::{
    class_injective_at_empty, compat_at_empty, eqv_of_empty, lift_beta_at_empty, rcompat_at_empty,
    Identity,
};
