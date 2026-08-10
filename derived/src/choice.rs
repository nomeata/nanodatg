//! The choice function `ε`, named — under a hypothesis, never by `define`.
//!
//! # Interface
//!
//! Write `IsChoiceFn(f,u)` for [`kernel::thm::is_choice_fn`], `⟨a,b⟩` for the
//! Kuratowski pair *term* [`crate::opair`], `⟨a,b⟩ ∈ f` for
//! [`kernel::thm::pair_in`]'s *described* pair, and `app` for
//! [`crate::funcs::Apply`]'s application. Then the exports are
//!
//! ```text
//! ⊢ ∀a ∀b ∀p. (is_opair(p,a,b) ↔ p = ⟨a,b⟩)                    [opair_described]
//! ⊢ ∀f ∀a ∀b. ((∃p. (p ∈ f ∧ is_opair(p,a,b))) ↔ ⟨a,b⟩ ∈ f)    [pair_in_bridge]
//! ⊢ ∃f. IsChoiceFn(f, u)                          for any u    [choice_fn_existence]
//! ⊢ ∀x ∃f. IsChoiceFn(f, U(x))                                 [choice_fn_on_universe]
//! ⊢ ∀f ∀u ∀x. (IsChoiceFn(f,u)
//!        → ((x ∈ u ∧ ∃w. w ∈ x) → app(f,x) ∈ x))               [choice_app]
//! ⊢ ∃f. (IsChoiceFn(f, {{∅}}) ∧ app(f,{∅}) = ∅)                [choice_nonvacuous]
//!
//! Epsilon::on(env, u)   for a CLOSED u                         [epsilon]
//! ⊢ IsChoiceFn(ε, u)                                           [Epsilon::is_choice_fn]
//! ⊢ ∀x. ((x ∈ u ∧ ∃w. w ∈ x) → app(ε,x) ∈ x)                   [Epsilon::chooses]
//! ```
//!
//! [`choice_app`] is the lemma a caller actually needs; [`choice_nonvacuous`]
//! is the evidence that its antecedent is not empty. [`Epsilon`] is the same
//! lemma with that antecedent **discharged into a symbol**, and it is the only
//! export here whose theorems are unconditional.
//!
//! # Why `f` is a free variable, and where it stops being one
//!
//! Carneiro's model fixes **one** choice function on **one** set: "Fix a choice
//! function `ε` on `U_ω`, that is, a function such that `ε(x) ∈ x` for all
//! `x ∈ U_ω`" (*The Type Theory of Lean*, §6.2), and `⟦choice α h⟧ = ε(⟦α⟧)`.
//! `ε` is scoped by that "fix" — it is a parameter of the interpretation, not a
//! definable object.
//!
//! Everything in [`function`] reproduces that scoping in the LCF-faithful shape:
//! carry `f` as a free variable under the antecedent `IsChoiceFn(f,u)`, and
//! discharge it at the top against [`choice_fn_existence`].
//! [`kernel::thm::define`] cannot do better, and that has not changed:
//! `define` requires `∃!`, and a choice function is **never** unique — any set
//! with two or more members admits two of them.
//!
//! **The rest of this section used to read "and no `define_choice` primitive was
//! added to let it", and that is now false.** It is corrected here rather than
//! appended to, because a reader deciding whether this development can name `ε`
//! would get the wrong answer from the file that is supposed to settle it.
//!
//! What was added is *not* `define_choice`. Skolemising `⊢ ∀x⃗ ∃y. φ` at arity
//! ≥ 1 remains **unsound in this kernel** — [`kernel::thm::define`]'s comment
//! carries the argument, and it turns on [`kernel::Thm::ax_replacement`]
//! accepting formulas that mention the new symbol. What was added is
//! [`kernel::thm::henkin`]: from `⊢ ∃y. φ` with `FV(φ) ⊆ {y}`, a fresh **0-ary**
//! constant and `⊢ φ(c)`. A constant is a parameter, so the schemes survive, and
//! expanding a model by one witness needs no metatheoretic choice.
//!
//! [`epsilon`] is the single place that calls it, `ci/check-boundary.sh` rule 7
//! enforces that, and that module's header says what a replacement would have to
//! provide. The free-variable route in [`function`] is **not** deprecated: it is
//! what proves the existential [`Epsilon::on`] consumes, and it is the only route
//! available at a `u` that carries a parameter — which is precisely the case the
//! kernel rule must refuse.
//!
//! # The bridge, and why it costs anything at all
//!
//! The kernel's signature is `{∈,=}`, so [`kernel::Thm::ax_choice`] can only
//! *describe* ordered pairs: `⟨a,b⟩ ∈ f` is `∃p. (p ∈ f ∧ is_opair(p,a,b))`,
//! where `is_opair` spells out `p = {{a},{a,b}}` as a membership condition. But
//! everything downstream — [`crate::funspace::is_single_valued`],
//! [`crate::ext::app_of_pair`], `app` itself — is written with the *term*
//! `⟨a,b⟩ = upair(upair(a,a), upair(a,b))`, which exists only because `upair`
//! is a definitional extension the kernel knows nothing about.
//!
//! [`opair_described`] and [`pair_in_bridge`] are the translation, and they are
//! not specific to choice: they are the first place in this development where a
//! *described* pair meets a *constructed* one, and `ax_tarski`'s equinumerosity
//! clause will want the same bridge the day anyone tries to use it (see
//! [`crate::cantor`], which avoids the question by never leaving the described
//! form).
//!
//! # What this rests on
//!
//! Extensionality, Pairing (through `upair`), and [`kernel::Thm::ax_choice`].
//! Note in particular what it does **not** rest on: neither propositional
//! extensionality nor quotients needed a set-theoretic axiom — the first is
//! case analysis inside `U₀ = {∅,{•}}` closed by Extensionality (§6.3), the
//! second is Separation plus Replacement on `ᾱ/∼` (§6.2). Choice was the only
//! one of Lean's three non-primitive axioms that needed anything new.
//!
//! # Layout
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::choice::…` all still resolve.
//!
//! | file | what it holds |
//! |---|---|
//! | [`bridge`] | described pairs ↔ constructed pairs — reusable, and not about choice |
//! | [`function`] | the choice function itself, its values, and its non-vacuity |
//! | [`epsilon`] | `ε` as a **symbol**, and the only call to [`kernel::thm::henkin`] |
//!
//! `shared` holds the propositional and quantifier combinators the bridge needs
//! and the crate does not already have; it exports no theorem and is not
//! re-exported.

pub mod bridge;
pub mod epsilon;
pub mod function;
mod shared;

pub use bridge::{opair_described, pair_in_bridge};
pub use epsilon::Epsilon;
pub use function::{choice_app, choice_fn_existence, choice_fn_on_universe, choice_nonvacuous};
