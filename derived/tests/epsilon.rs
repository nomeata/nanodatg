//! `ε` as a symbol — the encapsulated Henkin constant, and the claim it rests on.
//!
//! # The claim being measured
//!
//! [`kernel::thm::henkin`] refuses unless `FV(φ) ⊆ {f}`, and here `φ` is
//! `IsChoiceFn(f, u)`, so the whole route rests on **`u` being a closed term**.
//! That was a hypothesis when this file was written, not a fact:
//! `derived::choice::choice_fn_existence` is stated "for any `u`", and
//! `choice_fn_on_universe` is stated at `U(x)` with `x` a *variable*, which is
//! exactly the shape the rule must refuse.
//!
//! [`the_tower_rungs_are_closed_terms`] measures it rather than assuming it, and
//! [`a_parameterised_universe_is_refused`] pins the other side: `U(x)` at a free
//! `x` is arity-≥1 Skolemisation and does not mint. If the first ever goes red,
//! the route collapses to the arity-≥1 case and the answer is not to widen the
//! rule.
//!
//! Every positive assertion compares against a formula rebuilt from the
//! constructors, so "it returned `Some`" is never read as "it proved the right
//! thing".

use derived::choice::{self, Epsilon};
use derived::csb::prereq::Csb;
use derived::funcs::Apply;
use derived::tower::Tower;
use kernel::{Env, Formula, Term, Thm};

/// The pairing apparatus plus the two theorems `choice_app` needs.
fn choice_apparatus(env: &mut Env, ap: &Apply) -> Thm {
    let csb = Csb::with_apply(env, ap).expect("the pair bridge");
    let app_pair = derived::ext::app_of_pair(env, ap).expect("app_of_pair");
    choice::choice_app(env, ap, &csb.pair_in_bridge, &app_pair).expect("choice_app")
}

// ─────────────────────────────────────────────────────────────────────────────
// The claim.
// ─────────────────────────────────────────────────────────────────────────────

/// **The load-bearing measurement.** Every rung of the tower is a closed term,
/// so `IsChoiceFn(f, Uₙ)` has `f` as its only free variable.
///
/// This is checked at the *formula* the kernel rule actually scans, not merely
/// at the term, because that is what the guard reads.
#[test]
fn the_tower_rungs_are_closed_terms() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");

    for n in 0..3usize {
        let u = t.u(n);
        let mut fvs = Vec::new();
        u.free_vars(&mut fvs);
        assert!(fvs.is_empty(), "U{n} carries a free variable {fvs:?} — the ε route does not apply");

        let f = env.fresh_var();
        let phi = kernel::thm::is_choice_fn(&mut env, Term::var(f), u.clone());
        let mut pfvs = Vec::new();
        phi.free_vars(&mut pfvs);
        assert_eq!(pfvs, vec![f], "IsChoiceFn(f, U{n}) must have f as its only free variable");
    }
}

/// **The other side of the same claim.** `U(x)` at a free `x` is a choice
/// function *indexed by a parameter*, i.e. Skolemisation at arity ≥ 1, and the
/// kernel refuses it. `derived::choice::choice_fn_on_universe` states exactly
/// that shape, so this is not a hypothetical caller.
#[test]
fn a_parameterised_universe_is_refused() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let x = env.fresh_var();
    let parameterised = Term::apply(t.space.lu, vec![Term::var(x)]);

    // The premise is genuinely provable at this term — it is one instantiation
    // of `ax_choice` — so it is the free-variable guard that declines, not a
    // missing witness.
    let witness = choice::choice_fn_existence(&mut env, &parameterised).expect("the axiom instantiates");
    assert!(witness.hyps().is_empty(), "and it is unconditional");

    assert!(
        Epsilon::on(&mut env, &parameterised).is_none(),
        "a choice function indexed by a parameter is Skolemisation at arity ≥ 1"
    );
    // A bare variable is refused for the same reason.
    assert!(Epsilon::on(&mut env, &Term::var(x)).is_none(), "a variable domain is not closed");
}

// ─────────────────────────────────────────────────────────────────────────────
// The interface.
// ─────────────────────────────────────────────────────────────────────────────

/// **`ε` exists, is 0-ary, and its defining theorem is the axiom's own body —
/// unconditionally.**
#[test]
fn epsilon_is_a_constant_with_an_unconditional_defining_theorem() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let u1 = t.u(1);

    let eps = Epsilon::on(&mut env, &u1).expect("U₁ is closed, so ε mints");
    assert_eq!(eps.sym().arity(), 0, "ε is a constant, not a Skolem function");
    assert_eq!(*eps.term(), Term::apply(eps.sym(), vec![]));
    assert_eq!(*eps.domain(), u1);

    let want = kernel::thm::is_choice_fn(&mut env, eps.term().clone(), u1);
    assert_eq!(*eps.is_choice_fn().concl(), want, "ε's theorem is IsChoiceFn(ε, U₁), rebuilt");
    assert!(eps.is_choice_fn().hyps().is_empty(), "and it carries no hypothesis — that is the point");

    let mut fvs = Vec::new();
    eps.is_choice_fn().concl().free_vars(&mut fvs);
    assert!(fvs.is_empty(), "it is a sentence, so it can reach a Sealed");
}

/// **The lemma a consumer needs, with no antecedent left.**
/// `⊢ ∀x. ((x ∈ U₁ ∧ ∃w. w ∈ x) → app(ε,x) ∈ x)`, rebuilt and compared.
#[test]
fn epsilon_chooses_unconditionally() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let u1 = t.u(1);
    let ap = t.sums.ap.clone();
    let ca = choice_apparatus(&mut env, &ap);

    let eps = Epsilon::on(&mut env, &u1).expect("ε on U₁");
    let out = eps.chooses(&mut env, &ap, &ca).expect("the antecedent discharges");

    let x = env.fresh_var();
    let tx = Term::var(x);
    let guard = Formula::and(
        Formula::mem(tx.clone(), u1),
        kernel::thm::nonempty(&mut env, tx.clone()),
    );
    let goal = Formula::mem(ap.apply(eps.term().clone(), tx.clone()), tx);
    assert_eq!(*out.concl(), Formula::forall(x, Formula::imp(guard, goal)));
    assert!(out.hyps().is_empty(), "the whole point is that this is unconditional");
}

/// **It has bite.** The lemma above is not vacuous: at `{{∅}}` the guard is
/// discharged outright and `ε` picks `∅` out of `{∅}` — the same evidence
/// `choice_nonvacuous` gives for the hypothetical form, now as an equation about
/// a *named* function.
#[test]
fn epsilon_picks_a_member_at_a_concrete_set() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let ap = t.sums.ap.clone();
    let ca = choice_apparatus(&mut env, &ap);

    let empty = Term::apply(ap.empty, vec![]);
    let s_empty = derived::singleton(ap.sets.up, empty.clone()); // {∅}
    let ss_empty = derived::singleton(ap.sets.up, s_empty.clone()); // {{∅}}

    let eps = Epsilon::on(&mut env, &ss_empty).expect("{{∅}} is closed");
    let out = eps.chooses(&mut env, &ap, &ca).expect("chooses");
    let at = derived::inst_all(&out, std::slice::from_ref(&s_empty)).expect("at {∅}");

    // `{∅} ∈ {{∅}}` and `∃w. w ∈ {∅}` — the guard, discharged.
    let mem_here = derived::inst_all(&ap.mem_sing, &[s_empty.clone(), s_empty.clone()]).expect("mem_sing");
    let s_in_ss = Thm::mp(&derived::iff_mpr(&mem_here).expect("mpr"), &Thm::eq_refl(s_empty.clone()))
        .expect("{∅} ∈ {{∅}}");
    let mem_inner = derived::inst_all(&ap.mem_sing, &[empty.clone(), empty.clone()]).expect("mem_sing");
    let e_in_s = Thm::mp(&derived::iff_mpr(&mem_inner).expect("mpr"), &Thm::eq_refl(empty.clone()))
        .expect("∅ ∈ {∅}");
    let w = env.fresh_var();
    let ne = Thm::mp(
        &derived::exists_intro_imp(w, Formula::mem(Term::var(w), s_empty.clone()), empty).expect("∃ intro"),
        &e_in_s,
    )
    .expect("∃w. w ∈ {∅}");

    let got = Thm::mp(&at, &derived::and_intro(&s_in_ss, &ne)).expect("the guard discharges");
    assert_eq!(
        *got.concl(),
        Formula::mem(ap.apply(eps.term().clone(), s_empty.clone()), s_empty),
        "the singleton case: a closed theorem app(eps, s) in s about a named function"
    );
    assert!(got.hyps().is_empty());
}

/// **Two mints are two constants**, and nothing relates them. The interface
/// header says a caller must thread one `Epsilon` rather than re-mint; this is
/// the fact that makes that a real requirement rather than style advice.
#[test]
fn two_mints_at_one_domain_are_unrelated() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let u1 = t.u(1);
    let a = Epsilon::on(&mut env, &u1).expect("first");
    let b = Epsilon::on(&mut env, &u1).expect("second");
    assert_ne!(a.sym(), b.sym(), "each mint is a fresh constant");
    assert_ne!(a.term(), b.term());
}

/// **`chooses` refuses a theorem that is not `choice_app`.** The conclusion is
/// rebuilt and compared, so handing it some other universally quantified lemma
/// yields `None` rather than a theorem about the wrong thing.
#[test]
fn chooses_refuses_the_wrong_lemma() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    let u1 = t.u(1);
    let ap = t.sums.ap.clone();
    let eps = Epsilon::on(&mut env, &u1).expect("ε on U₁");
    // `⊢ ∀c ∀f ∀x. (f ∈ U(c) → app(f,x) ∈ U(c))` — three binders, an implication,
    // and an `app` in the conclusion, so it instantiates at the same three terms
    // and is the closest wrong answer available. It is `IsChoiceFn(ε,U₁)` that
    // fails to discharge its antecedent.
    assert!(eps.chooses(&mut env, &ap, &t.app).is_none(), "only choice_app discharges");
}
