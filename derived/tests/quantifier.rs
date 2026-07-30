//! Tests for the quantifier toolkit.
//!
//! `∃` is `¬∀¬`, so existential reasoning runs through contraposition and the
//! distribution axiom. The distribution axiom has a free-variable side
//! condition, and the negative tests here are about that condition actually
//! being enforced — it is the one place in this layer where getting it wrong
//! would let a witness-dependent conclusion escape its witness's scope.

use kernel::{Env, Formula, Term, Thm};

#[test]
fn contraposition() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let p = Formula::mem(Term::var(x), Term::var(x));
    let pp = derived::imp_refl(p.clone());
    let got = derived::contrapos(&pp).expect("contrapos");
    assert_eq!(*got.concl(), Formula::imp(Formula::not(p.clone()), Formula::not(p)));
}

#[test]
fn forall_monotonicity() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let p = Formula::mem(Term::var(x), Term::var(x));
    // ⊢ ∀x. (p → p)
    let all = Thm::gen(x, &derived::imp_refl(p.clone()));
    let got = derived::forall_mono(x, &all).expect("forall_mono");
    let allp = Formula::forall(x, p);
    assert_eq!(*got.concl(), Formula::imp(allp.clone(), allp));
}

#[test]
fn exists_monotonicity() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let p = Formula::mem(Term::var(x), Term::var(x));
    let all = Thm::gen(x, &derived::imp_refl(p.clone()));
    let got = derived::exists_mono(x, &all).expect("exists_mono");
    let exp = Formula::exists(x, p);
    assert_eq!(*got.concl(), Formula::imp(exp.clone(), exp));
}

/// The round trip: introduce an existential, then eliminate it.
#[test]
fn exists_intro_then_elim() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let c = env.declare(0);
    let t = Term::apply(c, vec![]);

    // ⊢ ∃x. x = t, from the witness t = t.
    let phi = Formula::eq(Term::var(x), t.clone());
    let witness = Thm::eq_refl(t.clone());
    let ex = derived::exists_intro(x, phi.clone(), t.clone(), &witness).expect("exists_intro");
    assert_eq!(*ex.concl(), Formula::exists(x, phi.clone()));

    // Eliminate against a conclusion that does not mention x.
    let psi = Formula::eq(t.clone(), t.clone());
    let all_imp = Thm::gen(x, &derived::a1i(&Thm::eq_refl(t), phi));
    let got = derived::exists_elim(x, &ex, &all_imp, &psi).expect("exists_elim");
    assert_eq!(*got.concl(), psi);
}

/// **The load-bearing negative test.** `exists_elim` must refuse a conclusion in
/// which the bound variable occurs free. Allowing it would let a fact about the
/// witness escape the scope in which the witness exists — from `∃x. P(x)` one
/// could conclude `P(x)` for the very variable that was supposed to be bound.
#[test]
fn exists_elim_rejects_escaping_variable() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let c = env.declare(0);
    let t = Term::apply(c, vec![]);

    let phi = Formula::eq(Term::var(x), t.clone());
    let ex = derived::exists_intro(x, phi.clone(), t.clone(), &Thm::eq_refl(t.clone())).expect("intro");

    // ψ mentions x — the conclusion would escape its binder.
    let psi = Formula::eq(Term::var(x), Term::var(x));
    let all_imp = Thm::gen(x, &derived::a1i(&Thm::eq_refl(Term::var(x)), phi));
    assert!(
        derived::exists_elim(x, &ex, &all_imp, &psi).is_none(),
        "exists_elim let a witness-dependent conclusion escape its binder"
    );
}

/// `exists_elim` must also refuse when the supplied implication does not
/// actually conclude the claimed ψ.
#[test]
fn exists_elim_rejects_mismatched_conclusion() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let c = env.declare(0);
    let t = Term::apply(c, vec![]);
    let phi = Formula::eq(Term::var(x), t.clone());
    let ex = derived::exists_intro(x, phi.clone(), t.clone(), &Thm::eq_refl(t.clone())).expect("intro");

    let all_imp = Thm::gen(x, &derived::a1i(&Thm::eq_refl(t.clone()), phi));
    let wrong = Formula::mem(t.clone(), t);
    assert!(derived::exists_elim(x, &ex, &all_imp, &wrong).is_none(), "exists_elim accepted a mismatched conclusion");
}

/// Instantiating a chain of quantifiers in order.
#[test]
fn instantiate_chain() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (c, d) = (env.declare(0), env.declare(0));
    let (tc, td) = (Term::apply(c, vec![]), Term::apply(d, vec![]));

    // ⊢ ∀x ∀y. x = x
    let base = Thm::eq_refl(Term::var(x));
    let all = derived::gen_all(&[x, y], &base);
    let got = derived::inst_all(&all, &[tc.clone(), td]).expect("inst_all");
    assert_eq!(*got.concl(), Formula::eq(tc.clone(), tc));
}
