//! **`ε` as a symbol** — the one place in the system that names a choice
//! function, and the only caller of [`kernel::thm::henkin`].
//!
//! # Interface
//!
//! ```text
//! Epsilon::on(env, u)          -> Option<Epsilon>   // mints ε; u must be CLOSED
//! Epsilon::sym / term / domain -> the symbol, the term ε, and u
//! Epsilon::is_choice_fn()      -> &Thm   ⊢ IsChoiceFn(ε, u)
//! Epsilon::chooses(env,ap,ca)  -> Option<Thm>
//!                                        ⊢ ∀x. ((x ∈ u ∧ ∃w. w ∈ x) → app(ε,x) ∈ x)
//! ```
//!
//! Both theorems are **unconditional** — `hyps()` is empty and there is no
//! `IsChoiceFn(f,u)` antecedent left to carry — and both are **closed**, because
//! `ε` is a constant and `u` has been checked to be one too. That is the entire
//! difference from [`super::function`], which states the same facts with `f`
//! free under a hypothesis and can therefore never hand a caller a `Sealed`.
//!
//! # `u` must be closed, and the kernel is what checks it
//!
//! [`kernel::thm::henkin`] mints a **0-ary** constant and refuses unless
//! `FV(φ) ⊆ {f}`. Here `φ` is `IsChoiceFn(f, u)`, so the refusal is exactly
//! "`u` mentions a free variable" — and it must be, because a choice function
//! indexed by a parameter is Skolemisation at arity ≥ 1, which `define`'s doc
//! comment shows is unsound *in this kernel*. [`Epsilon::on`] does not
//! pre-screen `u`; it passes it to the rule and returns `None` when the rule
//! does, so there is exactly one copy of the condition and it is the trusted
//! one.
//!
//! The terms this is used at are closed: [`crate::tower::Tower::u`] builds `U₀`
//! from `∅` and `{∅}` and `Uₙ₊₁` as `U(Uₙ)`, all of them applications of symbols
//! to closed arguments and none of them carrying a variable.
//! `derived/tests/epsilon.rs` measures that rather than assuming it — the claim
//! that the premise is closed is the one this whole route rests on, and a
//! parameterised universe term would collapse it back to the arity-≥1 case.
//!
//! # One `ε` per rung — and **do not try to fix this up to `U_ω`**
//!
//! §6.2 fixes **one** choice function on `U_ω`. This module fixes one per rung.
//! That reads like an approximation to be tidied away later, and it is not: it is
//! forced, and tidying it is how the free variable gets back in.
//!
//! There is no `U_ω` **term**. The tower is `U₀, U₁, …` with no limit stage, and
//! the only universe-valued *operator* this development has is `U(·)` — so the
//! nearest thing to "a universe big enough for everything" that can be written
//! down is `U(x)` at a **variable** `x`. That is exactly the term
//! [`super::choice_fn_on_universe`] is stated at, it is exactly what
//! [`kernel::thm::henkin`] must refuse, and reaching for it is not a small step
//! toward §6.2 — it is the whole arity-≥1 case, whose unsoundness
//! [`kernel::thm::define`]'s comment establishes. `derived/tests/epsilon.rs`
//! pins the refusal at that precise term, so the "fix" reds rather than lands.
//!
//! The route to a genuine single `ε` is therefore **a `U_ω` term**, not a looser
//! guard: build the limit stage as a closed term (a Replacement image over `ω`
//! of the rung operator, say), prove `Uₙ ⊆ U_ω`, and mint once at it. Until that
//! exists, per-rung is the strongest thing that is *closed*.
//!
//! Per-rung is also weaker than §6.2 in the **safe** direction: every use is
//! set-sized choice on a bounded universe, never global choice on `V`, so the
//! consistency-strength argument on [`kernel::Thm::ax_choice`] applies unchanged
//! and nothing here reaches for the §1.2 axiom the thesis declines. What it costs
//! is that `ε` at rung `m` and `ε` at rung `n` are *unrelated* symbols; a consumer
//! that needs one function across rungs mints at the larger rung and uses
//! [`crate::cumul`] to get there.
//!
//! Minting twice at the *same* `u` yields two distinct constants and no theorem
//! relating them. So a caller must mint once and thread the [`Epsilon`], not
//! call [`Epsilon::on`] wherever it needs `ε`. Nothing here can enforce that —
//! it is not a soundness property, only a coherence one — so it is stated.
//!
//! # What a replacement would have to provide
//!
//! The owner's condition on adding the kernel rule was that we might "regret
//! that choice later and build it differently". This module is the seam. A
//! replacement must produce a value of this type — or one with the same four
//! observations — such that:
//!
//! 1. `term()` is a `Term` with **no free variables**, so that theorems about it
//!    are sentences and reach a `Sealed`;
//! 2. `is_choice_fn()` is a `Thm` with **empty `hyps()`** whose conclusion is
//!    *syntactically* `kernel::thm::is_choice_fn(env, term(), domain())` — the
//!    axiom's own spelling, not a paraphrase, or `chooses` will not compose;
//!    and
//! 3. nothing in `kernel/src` grows to accommodate it.
//!
//! The obvious candidate is a **derived well-ordering**: Tarski's Axiom A
//! implies AC, via well-ordering through the universe hierarchy
//! (`kernel/README.md`, "Choice"), and a well-ordering of `u` gives a *unique*
//! least element of every non-empty member, hence an `∃!` that
//! [`kernel::thm::define`] can name with no new primitive at all. That
//! derivation does not exist in `derived/` and is substantial.
//!
//! ## The door is not merely left open, it is wired to an alarm
//!
//! The project owner's condition, in full, was to add the rule "sparingly and
//! nicely encapsulated, in case we regret that choice later and build it
//! differently". The regrettable outcome is not that the rule is *replaced* —
//! that is the plan — it is that the rule is replaced and then **left sitting in
//! the trusted base**, unused, unread, and impossible for a later reader to
//! justify deleting.
//!
//! So `ci/check-boundary.sh` rule 7 fails at **zero** callers, not only at two or
//! at a stray one. The day this file is rebuilt over a well-ordering, the build
//! goes red and the only way to green it is to take [`kernel::thm::henkin`] out
//! of `kernel/src/thm.rs`. An encapsulation that only stops the seam widening is
//! half a guarantee; this one also makes the seam's *disappearance* mandatory
//! rather than optional.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::inst_all;

use super::function::choice_fn_existence;

/// A named choice function on one closed set.
///
/// Constructed only by [`Epsilon::on`]. The fields are private so that a
/// `Thm` about `ε` cannot be paired with a `term` it is not about.
#[derive(Debug, Clone)]
pub struct Epsilon {
    sym: kernel::FnSym,
    term: Term,
    on: Term,
    is_choice_fn: Thm,
}

impl Epsilon {
    /// Mint `ε` on `u` and prove `⊢ IsChoiceFn(ε, u)`.
    ///
    /// `None` if `u` is not closed (the kernel rule's `FV(φ) ⊆ {f}` check), or
    /// if the instantiated axiom does not come back in the shape
    /// [`kernel::thm::is_choice_fn`] states — which would mean this function and
    /// [`kernel::Thm::ax_choice`] had drifted apart.
    ///
    /// # Why the premise is the axiom's own body and not a rebuild
    ///
    /// `φ` is [`kernel::thm::is_choice_fn`] at `f` and `u`, the same function
    /// [`kernel::Thm::ax_choice`] builds its existential from. The kernel rule
    /// compares the witness against `Formula::exists(f, φ)`, so a rebuilt `φ`
    /// that differed anywhere would be refused rather than mismatched silently;
    /// using the axiom's own builder means the comparison is the check that the
    /// *instantiation* was right, not a check that two spellings agree.
    pub fn on(env: &mut Env, u: &Term) -> Option<Epsilon> {
        let f = env.fresh_var();
        let phi = kernel::thm::is_choice_fn(env, Term::var(f), u.clone());
        let witness = choice_fn_existence(env, u)?;
        let (sym, is_choice_fn) = kernel::thm::henkin(env, f, phi, &witness)?;
        Some(Epsilon { sym, term: Term::apply(sym, Vec::new()), on: u.clone(), is_choice_fn })
    }

    /// The constant itself.
    pub fn sym(&self) -> kernel::FnSym { self.sym }

    /// `ε`, as a term.
    pub fn term(&self) -> &Term { &self.term }

    /// The set it chooses on.
    pub fn domain(&self) -> &Term { &self.on }

    /// `⊢ IsChoiceFn(ε, u)` — unconditional, and closed.
    pub fn is_choice_fn(&self) -> &Thm { &self.is_choice_fn }

    /// `⊢ ∀x. ((x ∈ u ∧ ∃w. w ∈ x) → app(ε,x) ∈ x)` — **the lemma a consumer
    /// needs**, with the antecedent that made [`super::choice_app`] hypothetical
    /// discharged once and for all.
    ///
    /// `choice_app_thm` is [`super::choice_app`]'s output. It is passed in
    /// rather than derived here for the reason [`super::choice_nonvacuous`] takes
    /// it too: building it needs the pair bridge and `app_of_pair`, which the
    /// caller already has assembled.
    ///
    /// The conclusion is rebuilt from the constructors and compared, so a
    /// `choice_app_thm` that is not that lemma yields `None` instead of a
    /// theorem about something else.
    pub fn chooses(&self, env: &mut Env, ap: &Apply, choice_app_thm: &Thm) -> Option<Thm> {
        let x = env.fresh_var();
        let tx = Term::var(x);
        let at = inst_all(choice_app_thm, &[self.term.clone(), self.on.clone(), tx.clone()])?;
        let discharged = Thm::mp(&at, &self.is_choice_fn)?;

        let guard = Formula::and(
            Formula::mem(tx.clone(), self.on.clone()),
            kernel::thm::nonempty(env, tx.clone()),
        );
        let goal = Formula::mem(ap.apply(self.term.clone(), tx.clone()), tx);
        if *discharged.concl() != Formula::imp(guard, goal) {
            return None
        }
        Some(Thm::gen(x, &discharged))
    }
}
