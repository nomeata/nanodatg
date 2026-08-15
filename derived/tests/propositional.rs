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
///
/// **The two conjuncts are different, and that is the whole test.** This used
/// `and_intro(&p, &p)` at one `Thm`, so both projections returned the same
/// formula and `and_elim_left` and `and_elim_right` were indistinguishable — a
/// rule that returned the wrong side, or the same side twice, passed. Since
/// `iff_mp` and `iff_mpr` are *literally* these two (`rules.rs:303,307`), the
/// whole biconditional interface rested on it. Two atoms are enough here
/// because the question is a swap and not an ordering: `x = x` and `y = y` are
/// syntactically distinct, so left-vs-right is decided.
#[test]
fn conjunction_round_trip() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (px, py) = (Thm::eq_refl(Term::var(x)), Thm::eq_refl(Term::var(y)));
    let both = derived::and_intro(&px, &py);

    let l = derived::and_elim_left(&both).expect("and_elim_left");
    let r = derived::and_elim_right(&both).expect("and_elim_right");
    assert_eq!(l.concl(), px.concl(), "left projection did not return the left conjunct");
    assert_eq!(r.concl(), py.concl(), "right projection did not return the right conjunct");
    assert_ne!(l.concl(), r.concl(), "the two projections agree — the fixture cannot see a swap");
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

/// Biconditional projections, on a genuine `↔` between **two different**
/// formulas.
///
/// This was built at `p ↔ p` from two copies of `imp_refl(p)`, so `iff_mp` and
/// `iff_mpr` both returned `p → p` and no mutation could tell them apart. They
/// are `and_elim_left` and `and_elim_right` under other names
/// (`rules.rs:303,307`), and getting a biconditional backwards is the archetypal
/// way to prove something in the wrong direction.
///
/// A genuine `⊢ p ↔ q` at distinct atoms is derivable without an axiom because
/// both atoms here are *provable*: `a1i` weakens `⊢ q` to `⊢ p → q` and `⊢ p` to
/// `⊢ q → p`, and `Formula::iff(p, q)` is exactly the conjunction of those two.
#[test]
fn biconditional_projections() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (p, q) = (
        Formula::eq(Term::var(x), Term::var(x)),
        Formula::eq(Term::var(y), Term::var(y)),
    );
    // ⊢ p → q and ⊢ q → p, weakened from the two reflexivities.
    let fwd_i = derived::a1i(&Thm::eq_refl(Term::var(y)), p.clone());
    let bwd_i = derived::a1i(&Thm::eq_refl(Term::var(x)), q.clone());
    let iff = derived::and_intro(&fwd_i, &bwd_i);
    assert_eq!(*iff.concl(), Formula::iff(p.clone(), q.clone()));

    let fwd = derived::iff_mp(&iff).expect("iff_mp");
    let bwd = derived::iff_mpr(&iff).expect("iff_mpr");
    assert_eq!(*fwd.concl(), Formula::imp(p.clone(), q.clone()), "iff_mp is not the forward half");
    assert_eq!(*bwd.concl(), Formula::imp(q, p), "iff_mpr is not the backward half");
    assert_ne!(fwd.concl(), bwd.concl(), "the two halves agree — the fixture cannot see a swap");
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

/// Clavius' law, which is how a degenerate disjunction `φ ∨ φ` collapses.
#[test]
fn clavius_law() {
    let mut env = kernel::Env::new();
    let x = env.fresh_var();
    let p = Formula::mem(Term::var(x), Term::var(x));
    let t = derived::clavius(p.clone());
    assert_eq!(*t.concl(), Formula::imp(Formula::or(p.clone(), p.clone()), p));
}
