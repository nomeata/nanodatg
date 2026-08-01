//! `N` as a W-type — Lean's `inductive N | zero | succ (n : N)`.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game.** `zero ∈ N` and `∀n ∈ N. succ n ∈ N` are
//! both true of a one-element `N`, so [`the_naturals_are_not_a_singleton`]
//! derives the two distinctness theorems and cashes them at concrete elements:
//! `zero`, `succ zero` and `succ (succ zero)` are pairwise provably distinct,
//! with no hypothesis left. And [`the_bound_is_the_tag_set_universe`] pins
//! `closed(A,B,U(A))` — the hypothesis every W-type rule carries — as an
//! *unconditional* theorem, which is what says the ω-tower is not needed.

use kernel::{Env, Formula, Term, Thm};

use derived::bound::Bound;
use derived::point_fun::PointFun;
use derived::sums::Cases;
use derived::wnat::Nat;
use derived::wtype::Wtype;

struct Dev {
    wt: Wtype,
    bnd: Bound,
    nat: Nat,
}

fn build(env: &mut Env) -> Dev {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let cases = Cases::new(env, &wt.sums).expect("rec₊");
    let pf = PointFun::over(env, &wt.sums, &wt.app_pair).expect("point functions");
    let empty_u = derived::enums::empty_in_least_universe(env, &wt, &bnd).expect("∅ ∈ U(A)");
    let nat = Nat::over(env, &wt, &bnd, &cases, &pf, &empty_u).expect("N");
    Dev { wt, bnd, nat }
}

/// The two `rec₊` computation rules, which is where the fibres come from.
#[test]
fn the_fibre_family_computes() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;

    assert!(kernel::thm::debug_locally_closed(d.nat.fibre_zero.concl()));
    assert!(kernel::thm::debug_locally_closed(d.nat.fibre_succ.concl()));
    assert_eq!(
        *d.nat.fibre_zero.concl(),
        Formula::eq(d.wt.fibre(d.nat.fam.clone(), s.inl(s.point())), s.zero())
    );
    assert_eq!(
        *d.nat.fibre_succ.concl(),
        Formula::eq(d.wt.fibre(d.nat.fam.clone(), s.inr(s.point())), s.unit())
    );
    // The two fibres are genuinely different sets, so `B` is not constant.
    assert_ne!(s.zero(), s.unit());
}

/// `⊢ closed(1+1, B, U(1+1))` — with **no** hypothesis. This is the claim the
/// `INDUCTIVES.md` note doubted; it is what makes the ω-tower unnecessary.
#[test]
fn the_bound_is_the_tag_set_universe() {
    let mut env = Env::new();
    let d = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(d.nat.closed.concl()));

    let u = d.bnd.universe_of(d.nat.tags.clone());
    let want = derived::wtype::closed(&mut env, &d.wt.sums, &d.nat.tags, &d.nat.fam, &u);
    assert_eq!(*d.nat.closed.concl(), want);
    // And the W-type really is carved out of that universe.
    assert_eq!(d.nat.ty, d.wt.of(d.nat.tags.clone(), d.nat.fam.clone(), u));
}

/// `⊢ zero ∈ N` and `⊢ ∀n. (n ∈ N → succ n ∈ N)`.
#[test]
fn both_constructors_land_in_n() {
    let mut env = Env::new();
    let d = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(d.nat.zero.concl()));
    assert!(kernel::thm::debug_locally_closed(d.nat.succ.concl()));

    assert_eq!(
        *d.nat.zero.concl(),
        Formula::mem(d.nat.zero_t.clone(), d.nat.ty.clone())
    );

    let n = env.fresh_var();
    let tn = Term::var(n);
    let want = Formula::forall(
        n,
        Formula::imp(
            Formula::mem(tn.clone(), d.nat.ty.clone()),
            Formula::mem(Nat::succ_term(&d.wt, tn), d.nat.ty.clone()),
        ),
    );
    assert_eq!(*d.nat.succ.concl(), want);
}

/// The non-vacuity check: three concrete elements, pairwise distinct, with no
/// hypothesis left.
#[test]
fn the_naturals_are_not_a_singleton() {
    let mut env = Env::new();
    let d = build(&mut env);

    let zero = d.nat.zero_t.clone();
    let one = Nat::succ_term(&d.wt, zero.clone());
    let two = Nat::succ_term(&d.wt, one.clone());

    // All three are in `N`, unconditionally.
    let one_mem = Thm::mp(
        &derived::inst_all(&d.nat.succ, std::slice::from_ref(&zero)).expect("inst"),
        &d.nat.zero,
    )
    .expect("succ zero ∈ N");
    let two_mem = Thm::mp(
        &derived::inst_all(&d.nat.succ, std::slice::from_ref(&one)).expect("inst"),
        &one_mem,
    )
    .expect("succ (succ zero) ∈ N");
    assert_eq!(*one_mem.concl(), Formula::mem(one.clone(), d.nat.ty.clone()));
    assert_eq!(*two_mem.concl(), Formula::mem(two.clone(), d.nat.ty.clone()));

    // `zero ≠ succ zero` and `zero ≠ succ (succ zero)`.
    let ne0 = derived::inst_all(&d.nat.zero_ne_succ, std::slice::from_ref(&zero)).expect("inst");
    assert_eq!(*ne0.concl(), Formula::not(Formula::eq(zero.clone(), one.clone())));
    let ne1 = derived::inst_all(&d.nat.zero_ne_succ, std::slice::from_ref(&one)).expect("inst");
    assert_eq!(*ne1.concl(), Formula::not(Formula::eq(zero.clone(), two.clone())));

    // `succ zero ≠ succ (succ zero)`, from injectivity contraposed against the
    // first: `succ 0 = succ 1 → 0 = 1`, and `0 ≠ 1`.
    let inj = derived::inst_all(&d.nat.succ_inj, &[zero.clone(), one.clone()]).expect("inst");
    assert_eq!(
        *inj.concl(),
        Formula::imp(Formula::eq(one.clone(), two.clone()), Formula::eq(zero.clone(), one.clone()))
    );
    let ne2 = Thm::mp(&derived::contrapos(&inj).expect("contrapos"), &ne0).expect("mp");
    assert_eq!(*ne2.concl(), Formula::not(Formula::eq(one.clone(), two.clone())));

    // And the three are distinct *terms*, which is what stops the three
    // theorems above from being about one set three times.
    assert_ne!(zero, one);
    assert_ne!(one, two);
    assert_ne!(zero, two);
}

/// The successor as a *set function*, which is what interpreting Lean needs.
#[test]
fn the_successor_is_a_function_from_n_to_n() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    assert!(kernel::thm::debug_locally_closed(d.nat.succ_in_funspace.concl()));

    assert_eq!(
        *d.nat.succ_in_funspace.concl(),
        Formula::mem(d.nat.succ_fun.clone(), s.fs.of(d.nat.ty.clone(), d.nat.ty.clone()))
    );

    // And it computes: `app(succ_fun, zero) = sc(zero) = succ zero`.
    let zero = d.nat.zero_t.clone();
    let beta = Thm::mp(
        &derived::inst_all(&d.nat.succ_beta, std::slice::from_ref(&zero)).expect("inst"),
        &d.nat.zero,
    )
    .expect("beta");
    assert_eq!(
        *beta.concl(),
        Formula::eq(
            s.ap.apply(d.nat.succ_fun.clone(), zero.clone()),
            Term::apply(d.nat.sc, vec![zero.clone()])
        )
    );
    let unfold = derived::inst_all(&d.nat.sc_ax, std::slice::from_ref(&zero)).expect("inst");
    assert_eq!(
        *unfold.concl(),
        Formula::eq(Term::apply(d.nat.sc, vec![zero.clone()]), Nat::succ_term(&d.wt, zero.clone()))
    );
    let chain = derived::eq_trans(&mut env, &beta, &unfold).expect("trans");
    assert_eq!(
        *chain.concl(),
        Formula::eq(
            s.ap.apply(d.nat.succ_fun.clone(), zero.clone()),
            Nat::succ_term(&d.wt, zero)
        )
    );
}
