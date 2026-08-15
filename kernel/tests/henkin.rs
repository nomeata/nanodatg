//! `kernel::thm::henkin` — the 0-ary Henkin constant, and its three guards.
//!
//! # Why every witness here is a real derivation
//!
//! The rule has three checks and any one of them, on its own, returns `None`.
//! So a test that hands it a *fabricated* premise proves nothing: the refusal it
//! observes may be the conclusion check firing, and deleting the guard the test
//! is named after would leave it green. That is the failure mode
//! `tarski_regression.rs` records in another shape — an assertion that does not
//! touch the thing it is about.
//!
//! Every negative case below therefore builds its `⊢ ∃y. φ` with
//! [`exists_eq`] — five primitive rules, no shortcuts — and **asserts that the
//! witness's conclusion is exactly `Formula::exists(y, phi)`** before handing it
//! over. With that pinned, the only remaining reason the rule can decline is the
//! guard under test, and mutating that guard away turns the case red.
//!
//! # The exploit the free-variable check blocks
//!
//! [`the_tail_of_the_exploit_is_real`] derives, unconditionally and in one
//! kernel call, the step that turns the missing check into a contradiction:
//! `⊢ (∀v. c₁ = v) → c₁ = c₂` for two genuinely minted constants. The bug would
//! supply the antecedent — `⊢ c₁ = v` with `v` free, generalised — so that test
//! is the second half of `⊢ ⊥`, executed rather than described.

use kernel::term::FreeVar;
use kernel::thm::henkin;
use kernel::{Env, Formula, Term, Thm};

/// `(φ, ⊢ ∃y. φ)` for `φ := (y = t)`, built from primitive rules only.
///
/// `∃y. φ` is `¬∀y. ¬φ`, i.e. `A → ⊥` for `A := ∀y. ¬(y = t)`. The derivation:
/// `ax_inst` gives `⊢ A → ((t = t) → ⊥)`, `eq_refl` and `ax_k` give
/// `⊢ A → (t = t)`, and `ax_s` chains them into `⊢ A → ⊥`.
///
/// At `t = y` the result is closed and the rule must accept it; at `t = v` for
/// some other variable it has a stray free variable and the rule must not.
fn exists_eq(y: FreeVar, t: &Term) -> (Formula, Thm) {
    let phi = Formula::eq(Term::var(y), t.clone());
    let a = Formula::forall(y, Formula::not(phi.clone()));
    let refl_f = Formula::eq(t.clone(), t.clone());

    // ⊢ A → ((t = t) → ⊥)
    let inst = Thm::ax_inst(a.clone(), t.clone()).expect("A is universally quantified");
    // ⊢ A → (t = t)
    let a_to_refl = Thm::mp(&Thm::ax_k(refl_f.clone(), a.clone()), &Thm::eq_refl(t.clone()))
        .expect("K applied to reflexivity");
    // ⊢ (A → (t=t)) → (A → ⊥), then ⊢ A → ⊥
    let s = Thm::ax_s(a, refl_f, Formula::false_());
    let out = Thm::mp(&Thm::mp(&s, &inst).expect("S at the instantiation"), &a_to_refl)
        .expect("S at the reflexivity arm");
    (phi, out)
}

/// A closed witness: `φ := (y = y)`, so `FV(φ) = {y}` and `⊢ ∃y. y = y`.
fn closed_witness(env: &mut Env) -> (FreeVar, Formula, Thm) {
    let y = env.fresh_var();
    let (phi, thm) = exists_eq(y, &Term::var(y));
    assert_eq!(*thm.concl(), Formula::exists(y, phi.clone()), "the witness must prove the existential");
    assert!(thm.hyps().is_empty(), "the witness must be unconditional");
    (y, phi, thm)
}

/// **The rule does what it says.** A fresh 0-ary constant, and `φ` at it.
#[test]
fn it_mints_a_constant_and_asserts_phi_at_it() {
    let mut env = Env::new();
    let (y, phi, w) = closed_witness(&mut env);

    let (c, ax) = henkin(&mut env, y, phi.clone(), &w).expect("a closed witness is accepted");
    assert_eq!(c.arity(), 0, "a Henkin constant is 0-ary — the whole soundness argument is that");
    assert_eq!(*ax.concl(), Formula::eq(Term::apply(c, vec![]), Term::apply(c, vec![])));
    assert_eq!(*ax.concl(), phi.subst(y, &Term::apply(c, vec![])), "the axiom is φ at the constant");
    assert!(ax.hyps().is_empty(), "the axiom is unconditional");

    // A sentence, not a schema: the free-variable check has just established
    // that there is nothing left to close over, so `define`'s `close_all` has no
    // counterpart here and the result must have no free variables at all.
    let mut fvs = Vec::new();
    ax.concl().free_vars(&mut fvs);
    assert!(fvs.is_empty(), "the axiom must be closed, found {fvs:?}");
}

/// **The axiom is φ at the constant — asserted at a φ that can tell the
/// difference.**
///
/// [`it_mints_a_constant_and_asserts_phi_at_it`] pins this same property and
/// **cannot fail**. Its fixture is [`closed_witness`], which fixes φ := `y = y`,
/// so `φ[c/y]` *is* `c = c`: the assertion "the axiom is φ at the constant" is
/// the reflexivity assertion on the line above it, restated at the one
/// instantiation where the two readings agree. Its closedness assertion
/// follows for the same reason — `c = c` is closed whatever φ was.
///
/// Measured: replacing the axiom's formula in `kernel/src/thm.rs::henkin` with
/// `Formula::eq(Term::apply(c, Vec::new()), Term::apply(c, Vec::new()))` — a
/// rule that ignores φ outright — leaves **all 8 tests in this file green**,
/// and the whole `-p kernel` suite green. The rule's entire content was
/// untested from inside the trusted base.
///
/// Here φ := `y = d` for a second, independently minted 0-ary constant, so
/// `φ[c/y]` is `c = d` and the two readings separate. `d` is a *constant* and
/// not a variable, so `FV(φ)` is still `{y}` and the free-variable guard
/// accepts exactly as before — the guard tests are unaffected and keep using
/// [`closed_witness`].
#[test]
fn the_axiom_is_phi_at_the_constant_and_not_merely_reflexivity() {
    let mut env = Env::new();
    let y = env.fresh_var();
    let d = Term::apply(env.declare(0), vec![]);
    let (phi, w) = exists_eq(y, &d);
    assert_eq!(
        *w.concl(),
        Formula::exists(y, phi.clone()),
        "the witness must prove the existential"
    );
    assert!(w.hyps().is_empty(), "the witness must be unconditional");

    let (c, ax) = henkin(&mut env, y, phi.clone(), &w).expect("a closed witness is accepted");
    let ct = Term::apply(c, vec![]);
    assert_eq!(*ax.concl(), phi.subst(y, &ct), "the axiom is φ at the constant");
    // …and φ at the constant is a *different formula* from reflexivity at the
    // constant. This is the line the `y = y` fixture cannot state.
    assert_eq!(*ax.concl(), Formula::eq(ct.clone(), d), "φ at the constant is `c = d`");
    assert_ne!(
        *ax.concl(),
        Formula::eq(ct.clone(), ct),
        "a rule returning reflexivity at its own constant would satisfy the `y = y` fixture"
    );
    assert!(ax.hyps().is_empty(), "the axiom is unconditional");

    // Closedness, now a real assertion: `c = d` is closed because `henkin`
    // substituted the constant for the *only* free variable, not because the
    // formula was reflexivity all along.
    let mut fvs = Vec::new();
    ax.concl().free_vars(&mut fvs);
    assert!(fvs.is_empty(), "the axiom must be closed, found {fvs:?}");
}

/// **Each mint is a different constant.** Two calls on the *same* witness must
/// not collapse: `φ(c₁)` and `φ(c₂)` are two conservative expansions, and a
/// shared symbol would silently assert `c₁ = c₂`.
#[test]
fn each_mint_is_fresh() {
    let mut env = Env::new();
    let (y, phi, w) = closed_witness(&mut env);
    let (c1, _) = henkin(&mut env, y, phi.clone(), &w).expect("first mint");
    let (c2, _) = henkin(&mut env, y, phi, &w).expect("second mint");
    assert_ne!(c1, c2, "two Henkin constants from one witness must be distinct symbols");
}

/// **The guard that is the whole rule.** `φ := (y = v)` with `v` stray is
/// Skolemisation at arity ≥ 1 with the argument left implicit, and it is
/// `define`'s recorded free-variable bug with `define` swapped out.
///
/// The witness is genuine and is asserted to prove exactly `∃y. φ`, so the
/// conclusion check cannot be what declines this; deleting the `FV(φ) ⊆ {y}`
/// scan makes this test fail.
#[test]
fn a_stray_free_variable_is_refused() {
    let mut env = Env::new();
    let (y, v) = (env.fresh_var(), env.fresh_var());
    let (phi, w) = exists_eq(y, &Term::var(v));

    assert_eq!(*w.concl(), Formula::exists(y, phi.clone()), "the witness really proves ∃y. y = v");
    assert!(w.hyps().is_empty(), "and it proves it unconditionally");
    assert!(phi.occurs_free(v), "…with `v` genuinely free in φ");

    assert!(
        henkin(&mut env, y, phi, &w).is_none(),
        "a φ with a free variable other than y would mint `⊢ c = v`, hence `⊢ ∀v. c = v`"
    );
}

/// The tail of that exploit, executed. If the check above were absent the rule
/// would return `⊢ c₁ = v` with `v` free; `gen` reads that as `⊢ ∀v. c₁ = v`,
/// and *this* theorem — unconditional, one `ax_inst` — turns it into an equation
/// between two constants that were minted independently and share nothing.
#[test]
fn the_tail_of_the_exploit_is_real() {
    let mut env = Env::new();
    let (y, phi, w) = closed_witness(&mut env);
    let (c1, _) = henkin(&mut env, y, phi.clone(), &w).expect("first mint");
    let (c2, _) = henkin(&mut env, y, phi, &w).expect("second mint");
    let (t1, t2) = (Term::apply(c1, vec![]), Term::apply(c2, vec![]));

    let v = env.fresh_var();
    let bad = Formula::forall(v, Formula::eq(t1.clone(), Term::var(v)));
    let step = Thm::ax_inst(bad.clone(), t2.clone()).expect("the premise is universally quantified");
    assert_eq!(*step.concl(), Formula::imp(bad, Formula::eq(t1, t2)));
    assert!(step.hyps().is_empty());
}

/// **A hypothetical witness is refused**, for `define`'s reason: the axiom
/// returned carries no `Γ`, so accepting one would drop it silently. Same shape
/// as this project's second soundness bug.
///
/// The assumed formula is the *same* existential the accepted case uses, so the
/// conclusion check passes and the emptiness check is the only thing left to
/// decline this. Deleting it makes this test fail.
#[test]
fn a_hypothetical_witness_is_refused() {
    let mut env = Env::new();
    let (y, phi, w) = closed_witness(&mut env);
    let assumed = Thm::assume(w.concl().clone());

    assert_eq!(assumed.concl(), w.concl(), "the assumption proves the right conclusion");
    assert_eq!(assumed.hyps().len(), 1, "and it proves it only under itself");

    assert!(
        henkin(&mut env, y, phi.clone(), &assumed).is_none(),
        "a witness proved under Γ justifies a constant only where Γ holds"
    );
    // The control: with the same φ and an unconditional proof of the same
    // formula, the rule accepts. So it is the hypothesis set that decided.
    assert!(henkin(&mut env, y, phi, &w).is_some(), "the only difference is Γ");
}

/// **A witness for some other statement is refused.** `⊢ ∃y. y = y` does not
/// discharge the obligation for `φ := y ∈ y`.
#[test]
fn a_witness_for_another_formula_is_refused() {
    let mut env = Env::new();
    let (y, _, w) = closed_witness(&mut env);
    let other = Formula::mem(Term::var(y), Term::var(y));
    assert!(henkin(&mut env, y, other, &w).is_none(), "the witness must prove this existential");
}

/// **A universal is not an existential.** `⊢ ∀y. y = y` is provable and is not a
/// licence to name anything, so the shape check must reject it — the rule reads
/// its premise, it does not merely count it.
#[test]
fn a_universal_witness_is_refused() {
    let mut env = Env::new();
    let y = env.fresh_var();
    let phi = Formula::eq(Term::var(y), Term::var(y));
    let univ = Thm::gen(y, &Thm::eq_refl(Term::var(y)));
    assert_eq!(*univ.concl(), Formula::forall(y, phi.clone()));
    assert!(henkin(&mut env, y, phi, &univ).is_none(), "∀ is not ∃");
}

/// **The witness's own binder need not be the caller's variable name.** Alpha
/// equivalence is syntactic identity here, so a witness built at a different
/// fresh variable discharges the same obligation — which is what lets the
/// derived layer state `∃f. IsChoiceFn(f,u)` at whatever variable it drew.
#[test]
fn the_binder_variable_is_invisible() {
    let mut env = Env::new();
    let (y1, y2) = (env.fresh_var(), env.fresh_var());
    let (_, w) = exists_eq(y1, &Term::var(y1));
    let phi2 = Formula::eq(Term::var(y2), Term::var(y2));
    assert_eq!(*w.concl(), Formula::exists(y2, phi2.clone()), "the two spellings are one formula");
    assert!(henkin(&mut env, y2, phi2, &w).is_some(), "a differently named binder is the same premise");
}
