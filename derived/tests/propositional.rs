//! Tests for the propositional toolkit.
//!
//! Each of these checks the *exact* conclusion, not merely that a theorem came
//! out. A derived rule that quietly produces a different (but still derivable)
//! formula would not be unsound, but it would make every derivation built on
//! top of it fail in a baffling way — and in a Hilbert system, where
//! implications are assembled rather than discharged, shapes have to line up to
//! the symbol.

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
fn syllogism() {
    let mut env = Env::new();
    let (p, q, r) = atoms(&mut env);
    // Manufacture ⊢ p → q and ⊢ q → r out of nothing? We cannot — so use
    // reflexivity, where the shapes are known.
    let pp = derived::imp_refl(p.clone());
    let got = derived::syl(&pp, &pp).expect("syl on two copies of p → p");
    assert_eq!(*got.concl(), Formula::imp(p.clone(), p.clone()));

    // Mismatched middles must be refused.
    let qq = derived::imp_refl(q.clone());
    assert!(derived::syl(&pp, &qq).is_none(), "syl chained mismatched middles");
    let _ = r;
}

#[test]
fn swap_antecedents() {
    let mut env = Env::new();
    let (p, q, _) = atoms(&mut env);
    // ⊢ (p → q) → (p → q), swapped, is ⊢ p → ((p → q) → q).
    let t = derived::imp_refl(Formula::imp(p.clone(), q.clone()));
    let got = derived::com12(&t).expect("com12");
    let expected = Formula::imp(p.clone(), Formula::imp(Formula::imp(p, q.clone()), q));
    assert_eq!(*got.concl(), expected);
}

#[test]
fn ex_falso_quodlibet() {
    let mut env = Env::new();
    let (p, _, _) = atoms(&mut env);
    let got = derived::ex_falso(p.clone());
    assert_eq!(*got.concl(), Formula::imp(Formula::false_(), p));
}

#[test]
fn double_negation() {
    let mut env = Env::new();
    let (p, _, _) = atoms(&mut env);
    let intro = derived::notnot_intro(p.clone());
    assert_eq!(*intro.concl(), Formula::imp(p.clone(), Formula::not(Formula::not(p.clone()))));

    let elim = derived::notnot_elim(p.clone());
    assert_eq!(*elim.concl(), Formula::imp(Formula::not(Formula::not(p.clone())), p));
}

#[test]
fn conjunction_projections() {
    let mut env = Env::new();
    let (p, q, _) = atoms(&mut env);
    let conj = Formula::and(p.clone(), q.clone());
    assert_eq!(*derived::and_left(p.clone(), q.clone()).concl(), Formula::imp(conj.clone(), p.clone()));
    assert_eq!(*derived::and_right(p.clone(), q.clone()).concl(), Formula::imp(conj, q.clone()));
}

/// The round trip that matters: build a conjunction, then take it apart again.
#[test]
fn conjunction_round_trip() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let p = Thm::eq_refl(Term::var(x));
    let both = derived::and_intro(&p, &p);

    let l = derived::and_elim_left(&both).expect("and_elim_left");
    let r = derived::and_elim_right(&both).expect("and_elim_right");
    assert_eq!(l.concl(), p.concl(), "left projection lost the conjunct");
    assert_eq!(r.concl(), p.concl(), "right projection lost the conjunct");
}

/// Conjunction elimination must refuse something that is not a conjunction.
#[test]
fn and_elim_rejects_non_conjunction() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let refl = Thm::eq_refl(Term::var(x));
    assert!(derived::and_elim_left(&refl).is_none());
    assert!(derived::and_elim_right(&refl).is_none());
}

/// Biconditional projections, on a genuine `↔` built from two implications.
#[test]
fn biconditional_projections() {
    let mut env = Env::new();
    let (p, _, _) = atoms(&mut env);
    // ⊢ p ↔ p, as the conjunction of two copies of p → p.
    let pp = derived::imp_refl(p.clone());
    let iff = derived::and_intro(&pp, &pp);
    assert_eq!(*iff.concl(), Formula::iff(p.clone(), p.clone()));

    let fwd = derived::iff_mp(&iff).expect("iff_mp");
    let bwd = derived::iff_mpr(&iff).expect("iff_mpr");
    assert_eq!(*fwd.concl(), Formula::imp(p.clone(), p.clone()));
    assert_eq!(*bwd.concl(), Formula::imp(p.clone(), p));
}

/// Monotonicity in the consequent.
#[test]
fn consequent_monotonicity() {
    let mut env = Env::new();
    let (p, q, _) = atoms(&mut env);
    let qq = derived::imp_refl(q.clone());
    let got = derived::imp_mono_r(&qq, p.clone()).expect("imp_mono_r");
    let pq = Formula::imp(p, q);
    assert_eq!(*got.concl(), Formula::imp(pq.clone(), pq));
}
