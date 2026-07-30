//! Tests for the "reasoning under a fixed hypothesis" layer.
//!
//! This is the closest a Hilbert system gets to a deduction theorem, and every
//! multi-hypothesis derivation rests on it. The internalised combinators
//! (`syl_imp`, `com12_imp`, `and_intro_imp`) are checked for their exact
//! conclusions, because a shape that is merely derivable rather than the one
//! promised makes everything downstream fail confusingly.

use kernel::{Env, Formula, Term, Thm};

fn atoms(env: &mut Env) -> (Formula, Formula, Formula) {
    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    (
        Formula::mem(Term::var(a), Term::var(a)),
        Formula::mem(Term::var(b), Term::var(b)),
        Formula::mem(Term::var(c), Term::var(c)),
    )
}

#[test]
fn syl_imp_shape() {
    let mut env = Env::new();
    let (a, b, c) = atoms(&mut env);
    let t = derived::syl_imp(a.clone(), b.clone(), c.clone());
    let expected = Formula::imp(
        Formula::imp(a.clone(), b.clone()),
        Formula::imp(Formula::imp(b, c.clone()), Formula::imp(a, c)),
    );
    assert_eq!(*t.concl(), expected);
}

#[test]
fn com12_imp_shape() {
    let mut env = Env::new();
    let (a, b, c) = atoms(&mut env);
    let t = derived::com12_imp(a.clone(), b.clone(), c.clone());
    let expected = Formula::imp(
        Formula::imp(a.clone(), Formula::imp(b.clone(), c.clone())),
        Formula::imp(b, Formula::imp(a, c)),
    );
    assert_eq!(*t.concl(), expected);
}

#[test]
fn and_intro_imp_shape() {
    let mut env = Env::new();
    let (a, b, _) = atoms(&mut env);
    let t = derived::and_intro_imp(a.clone(), b.clone());
    let expected = Formula::imp(a.clone(), Formula::imp(b.clone(), Formula::and(a, b)));
    assert_eq!(*t.concl(), expected);
}

/// Modus ponens under a hypothesis, and its rejections.
#[test]
fn hyp_mp_works_and_rejects() {
    let mut env = Env::new();
    let (h, p, q) = atoms(&mut env);

    // ⊢ H → (p → p) and ⊢ H → p would give ⊢ H → p.
    let h_imp = derived::a1i(&derived::imp_refl(p.clone()), h.clone());
    let h_arg = derived::a1i(&Thm::eq_refl(Term::var(env.fresh_var())), h.clone());
    // Mismatched φ must be refused.
    assert!(derived::hyp_mp(&h_imp, &h_arg).is_none(), "hyp_mp accepted a mismatched argument");

    // Mismatched hypothesis must be refused.
    let other = derived::a1i(&derived::imp_refl(p.clone()), q);
    assert!(derived::hyp_mp(&other, &h_imp).is_none(), "hyp_mp accepted a mismatched hypothesis");
}

/// Build a conjunction under a hypothesis and check the shape.
#[test]
fn conjunction_under_hypothesis() {
    let mut env = Env::new();
    let (h, _, _) = atoms(&mut env);
    let x = env.fresh_var();
    let fact = Thm::eq_refl(Term::var(x));

    let hp = derived::a1i(&fact, h.clone());
    let got = derived::hyp_and(&hp, &hp).expect("hyp_and");
    let expected = Formula::imp(h, Formula::and(fact.concl().clone(), fact.concl().clone()));
    assert_eq!(*got.concl(), expected);
}

/// Biconditional projections under a hypothesis.
#[test]
fn iff_projections_under_hypothesis() {
    let mut env = Env::new();
    let (h, p, _) = atoms(&mut env);
    let pp = derived::imp_refl(p.clone());
    let iff = derived::and_intro(&pp, &pp); // ⊢ p ↔ p
    let h_iff = derived::a1i(&iff, h.clone());

    let fwd = derived::hyp_iff_mp(&h_iff).expect("hyp_iff_mp");
    let bwd = derived::hyp_iff_mpr(&h_iff).expect("hyp_iff_mpr");
    let expected = Formula::imp(h, Formula::imp(p.clone(), p));
    assert_eq!(*fwd.concl(), expected);
    assert_eq!(*bwd.concl(), expected);
}
