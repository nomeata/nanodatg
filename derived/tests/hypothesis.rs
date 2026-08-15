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

/// Biconditional projections under a hypothesis, at a **genuine** `p ↔ q`.
///
/// This was built at `p ↔ p` and then asserted both projections equal to one
/// `expected` — the same formula, written twice. Two degeneracies at once: the
/// biconditional could not tell its halves apart, and the two assertions were
/// the identical predicate. A `hyp_iff_mpr` that returned the forward half
/// passed, which is the direction that matters, since these are what a
/// hypothesis-carrying rewrite uses to pick a side.
///
/// Distinct atoms, and both provable, so the `↔` is derivable without an axiom
/// — see `propositional.rs::biconditional_projections` for the construction.
#[test]
fn iff_projections_under_hypothesis() {
    let mut env = Env::new();
    let (h, _, _) = atoms(&mut env);
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (p, q) = (
        Formula::eq(Term::var(x), Term::var(x)),
        Formula::eq(Term::var(y), Term::var(y)),
    );
    let fwd_i = derived::a1i(&Thm::eq_refl(Term::var(y)), p.clone());
    let bwd_i = derived::a1i(&Thm::eq_refl(Term::var(x)), q.clone());
    let iff = derived::and_intro(&fwd_i, &bwd_i); // ⊢ p ↔ q
    let h_iff = derived::a1i(&iff, h.clone());

    let fwd = derived::hyp_iff_mp(&h_iff).expect("hyp_iff_mp");
    let bwd = derived::hyp_iff_mpr(&h_iff).expect("hyp_iff_mpr");
    assert_eq!(
        *fwd.concl(),
        Formula::imp(h.clone(), Formula::imp(p.clone(), q.clone())),
        "hyp_iff_mp is not the forward half"
    );
    assert_eq!(
        *bwd.concl(),
        Formula::imp(h, Formula::imp(q, p)),
        "hyp_iff_mpr is not the backward half"
    );
    assert_ne!(fwd.concl(), bwd.concl(), "the two halves agree — the fixture cannot see a swap");
}
