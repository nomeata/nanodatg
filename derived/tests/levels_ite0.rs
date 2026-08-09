//! The conditional term former `ite0(g,a,b)`, exercised at both guard values.
//!
//! Every test pins the **exact** conclusion it relies on, rebuilt independently
//! from the kernel's formula constructors, and the guard values come from a
//! [`derived::recursion::Rec`] so that the `∅` of the guard, the `0` of `ω`,
//! and the `∅` the `Apply` returns off a domain are all one symbol.

use derived::levels::ite0::ite0;
use derived::recursion::Rec;
use kernel::{Env, Formula, Term, Thm};

/// `⊢ ite0(∅, a, b) = a`: the guard is `∅` on the nose, so `when_zero` fires
/// off reflexivity.
#[test]
fn ite0_at_zero_is_the_first_branch() {
    let mut env = Env::new();
    let rec = Rec::new(&mut env).expect("Rec::new");
    let ite = ite0(&mut env, &rec.ap).expect("ite0");
    assert_eq!(ite.sym.arity(), 3);
    assert_eq!(ite.empty, rec.ap.empty, "the guard's ∅ must be the Apply's");

    let a = Term::apply(env.declare(0), vec![]);
    let b = Term::apply(env.declare(0), vec![]);
    let zero = rec.zero();

    let wz = derived::inst_all(&ite.when_zero, &[zero.clone(), a.clone(), b.clone()])
        .expect("when_zero instantiates at three terms");
    let out = Thm::mp(&wz, &Thm::eq_refl(zero.clone())).expect("⊢ ∅ = ∅ discharges the guard");
    assert!(out.hyps().is_empty(), "the conclusion must be unconditional");
    assert_eq!(
        *out.concl(),
        Formula::eq(ite.at(zero, a.clone(), b), a),
        "ite0(∅,a,b) = a has the wrong shape"
    );
}

/// `⊢ ite0(succ(∅), a, b) = b`: `succ(∅) ≠ ∅` by `succ_ne_zero` at the base
/// membership `⊢ 0 ∈ ω`, so `when_nonzero` fires.
#[test]
fn ite0_at_a_successor_is_the_second_branch() {
    let mut env = Env::new();
    let rec = Rec::new(&mut env).expect("Rec::new");
    let ite = ite0(&mut env, &rec.ap).expect("ite0");

    let a = Term::apply(env.declare(0), vec![]);
    let b = Term::apply(env.declare(0), vec![]);
    // Non-vacuity: the two branch constants are distinct terms, so the equation
    // below genuinely selects one of them.
    assert_ne!(a, b);
    let s0 = rec.succ_of(rec.zero());

    // `⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))` at `n := 0`, discharged by `⊢ 0 ∈ ω`.
    let snz = derived::inst_all(&rec.peano.succ_ne_zero, &[rec.zero()])
        .expect("succ_ne_zero instantiates at 0");
    let ne = Thm::mp(&snz, &rec.core().zero_mem).expect("⊢ 0 ∈ ω discharges the antecedent");
    assert_eq!(
        *ne.concl(),
        Formula::not(Formula::eq(s0.clone(), rec.zero())),
        "succ_ne_zero at 0 has the wrong shape"
    );

    let wnz = derived::inst_all(&ite.when_nonzero, &[s0.clone(), a.clone(), b.clone()])
        .expect("when_nonzero instantiates at three terms");
    let out = Thm::mp(&wnz, &ne).expect("⊢ ¬(succ(∅) = ∅) discharges the guard");
    assert!(out.hyps().is_empty(), "the conclusion must be unconditional");
    assert_eq!(
        *out.concl(),
        Formula::eq(ite.at(s0, a, b.clone()), b),
        "ite0(succ(∅),a,b) = b has the wrong shape"
    );
}

/// The exported theorems have exactly the documented shapes, rebuilt
/// independently — locally nameless representation makes the choice of bound
/// variable names invisible, so fresh test variables compare equal.
#[test]
fn interface_shapes_are_pinned() {
    let mut env = Env::new();
    let rec = Rec::new(&mut env).expect("Rec::new");
    let ite = ite0(&mut env, &rec.ap).expect("ite0");

    assert!(kernel::thm::debug_locally_closed(ite.when_zero.concl()));
    assert!(kernel::thm::debug_locally_closed(ite.when_nonzero.concl()));
    assert!(ite.when_zero.hyps().is_empty() && ite.when_nonzero.hyps().is_empty());

    let (g, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, ta, tb) = (Term::var(g), Term::var(a), Term::var(b));
    let e = Term::apply(rec.ap.empty, vec![]);
    let guard = Formula::eq(tg.clone(), e);
    let applied = ite.at(tg, ta.clone(), tb.clone());

    let expected_zero = Formula::forall(
        g,
        Formula::forall(
            a,
            Formula::forall(b, Formula::imp(guard.clone(), Formula::eq(applied.clone(), ta))),
        ),
    );
    assert_eq!(*ite.when_zero.concl(), expected_zero, "when_zero has the wrong shape");

    let expected_nonzero = Formula::forall(
        g,
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::imp(Formula::not(guard), Formula::eq(applied, tb)),
            ),
        ),
    );
    assert_eq!(*ite.when_nonzero.concl(), expected_nonzero, "when_nonzero has the wrong shape");

    // The defining axiom is the conjunction of the two halves' bodies.
    assert!(kernel::thm::debug_locally_closed(ite.ax.concl()));
    assert!(ite.ax.hyps().is_empty());
}
