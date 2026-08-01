//! Enumerations as W-types with empty fibres — the interpretation of Lean's
//! `Bool`.
//!
//! Each test rebuilds the formula it expects from the kernel's own constructors
//! and compares with `assert_eq!`, so a theorem with the right *name* and the
//! wrong *shape* fails here rather than downstream.
//!
//! **Non-vacuity is the whole game**, twice over. `enum_mem` is trivially true
//! of an empty `W`, so [`bool_has_two_elements`] discharges its antecedent at
//! two concrete tags; and two membership theorems about one set would still be
//! true of a *one*-element `Bool`, so the same test checks the two elements are
//! provably distinct — and that they are distinct *terms*, which is what stops
//! the distinctness theorem from being about one set twice.

use kernel::{Env, Formula, Term};

use derived::bound::Bound;
use derived::enums;
use derived::wtype::Wtype;

/// The whole development, built once per test.
fn build(env: &mut Env) -> (Wtype, Bound) {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    (wt, bnd)
}

/// `⊢ ∀A. ∅ ∈ U(A)`.
#[test]
fn the_empty_set_is_in_every_canonical_universe() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let t = enums::empty_in_least_universe(&mut env, &wt, &bnd).expect("∅ ∈ U(A)");
    assert!(kernel::thm::debug_locally_closed(t.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let want = Formula::forall(
        a,
        Formula::mem(wt.empty(), Term::apply(bnd.lu, vec![ta])),
    );
    assert_eq!(*t.concl(), want);
}

/// `⊢ ∀A ∀a. (a ∈ A → ⟨a,∅⟩ ∈ W(A, ∅, U(A)))` — the typing rule for a nullary
/// constructor, with no hypothesis on the bound.
#[test]
fn a_nullary_constructor_lands_in_its_w_type() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let empty_u = enums::empty_in_least_universe(&mut env, &wt, &bnd).expect("∅ ∈ U(A)");
    let t = enums::enum_mem(&mut env, &wt, &bnd, &empty_u).expect("enum_mem");
    assert!(kernel::thm::debug_locally_closed(t.concl()));

    let (a, x) = (env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(a), Term::var(x));
    let z = wt.empty();
    let w = wt.of(ta.clone(), z.clone(), Term::apply(bnd.lu, vec![ta.clone()]));
    let want = Formula::forall(
        a,
        Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), ta),
                Formula::mem(wt.sup(tx, z), w),
            ),
        ),
    );
    assert_eq!(*t.concl(), want);
}

/// `⊢ ∀A. closed(A, ∅, U(A))` — the bound hypothesis every W-type rule used to
/// carry, discharged outright here.
#[test]
fn the_tag_sets_own_universe_bounds_the_w_type() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let empty_u = enums::empty_in_least_universe(&mut env, &wt, &bnd).expect("∅ ∈ U(A)");
    let t = enums::enum_closed(&mut env, &wt, &bnd, &empty_u).expect("enum_closed");
    assert!(kernel::thm::debug_locally_closed(t.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let want = Formula::forall(
        a,
        derived::wtype::closed(
            &mut env,
            &wt.sums,
            &ta,
            &wt.empty(),
            &Term::apply(bnd.lu, vec![ta.clone()]),
        ),
    );
    assert_eq!(*t.concl(), want);
}

/// **The non-vacuity test, and the one this file exists for.**
///
/// `Bool` is `W(1+1, ∅, U(1+1))`. Its two constructors are `⟨inl(•),∅⟩` and
/// `⟨inr(•),∅⟩`, both derived to be members with *no hypothesis left*, and
/// derived to be different from each other — so the interpretation is neither
/// empty nor a singleton.
#[test]
fn bool_has_two_elements() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let empty_u = enums::empty_in_least_universe(&mut env, &wt, &bnd).expect("∅ ∈ U(A)");
    let mem = enums::enum_mem(&mut env, &wt, &bnd, &empty_u).expect("enum_mem");
    let inj = enums::enum_inj(&mut env, &wt).expect("enum_inj");
    let b = enums::enum2(&wt, &bnd, &mem, &inj).expect("Bool");

    // The three theorems are about the terms the interface advertises.
    let s = &wt.sums;
    let (one, point) = (s.unit(), s.point());
    let tags = s.sum_of(one.clone(), one);
    let z = wt.empty();
    let ty = wt.of(tags.clone(), z.clone(), Term::apply(bnd.lu, vec![tags.clone()]));
    let f = wt.sup(s.inl(point.clone()), z.clone());
    let t = wt.sup(s.inr(point), z);

    assert_eq!(b.ty, ty);
    assert_eq!(b.fst_t, f);
    assert_eq!(b.snd_t, t);

    // No hypotheses, and the exact memberships claimed.
    assert!(kernel::thm::debug_locally_closed(b.fst.concl()));
    assert!(kernel::thm::debug_locally_closed(b.snd.concl()));
    assert_eq!(*b.fst.concl(), Formula::mem(f.clone(), ty.clone()));
    assert_eq!(*b.snd.concl(), Formula::mem(t.clone(), ty));

    // And the two are not the same term, so the distinctness theorem is not
    // `¬(x = x)` in disguise — which would make it unprovable, but the check is
    // cheap and the failure mode it guards is the expensive one.
    assert_ne!(f, t);
    assert_eq!(*b.distinct.concl(), Formula::not(Formula::eq(f, t)));
    assert!(kernel::thm::debug_locally_closed(b.distinct.concl()));
}

/// The one-constructor enumeration, for completeness: `⟨•,∅⟩ ∈ W(1, ∅, U(1))`.
#[test]
fn a_one_constructor_enumeration_is_inhabited() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let empty_u = enums::empty_in_least_universe(&mut env, &wt, &bnd).expect("∅ ∈ U(A)");
    let mem = enums::enum_mem(&mut env, &wt, &bnd, &empty_u).expect("enum_mem");
    let u1 = enums::enum1(&wt, &bnd, &mem).expect("Unit");

    let s = &wt.sums;
    let one = s.unit();
    let z = wt.empty();
    let ty = wt.of(one.clone(), z.clone(), Term::apply(bnd.lu, vec![one]));
    assert_eq!(*u1.only.concl(), Formula::mem(wt.sup(s.point(), z), ty));
    assert!(kernel::thm::debug_locally_closed(u1.only.concl()));
}
