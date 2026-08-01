//! The two-point function `{⟨a,b⟩, ⟨c,d⟩}`.
//!
//! Each test rebuilds the expected formula from the kernel's own constructors,
//! so a theorem with the right name and the wrong shape fails here.
//!
//! **Non-vacuity.** Both exports are conditional equations, so two things have
//! to be checked beyond their shape: that the two sides of the equation are
//! *different terms* (or it would be reflexivity dressed up), and that the
//! shared antecedent `¬(a = c)` is satisfiable — otherwise the file would prove
//! nothing at all. [`the_antecedent_is_satisfiable`] discharges it at two
//! concrete, provably distinct sets and reads off an unconditional equation.

use kernel::{Env, Formula, Term};

use derived::funcs::Apply;
use derived::twopoint::TwoPoint;

fn build(env: &mut Env) -> (Apply, TwoPoint) {
    let ap = Apply::new(env).expect("application");
    let tp = TwoPoint::over(env, &ap).expect("two-point functions");
    (ap, tp)
}

fn expected(env: &mut Env, ap: &Apply, second: bool) -> (Formula, Term, Term) {
    let (a, b, c, d) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(a), Term::var(b), Term::var(c), Term::var(d));
    let g = TwoPoint::of(ap, ta.clone(), tb.clone(), tc.clone(), td.clone());
    let (pt, val) = if second { (tc.clone(), td.clone()) } else { (ta.clone(), tb.clone()) };
    let lhs = ap.apply(g, pt);
    let body = Formula::imp(
        Formula::not(Formula::eq(ta, tc)),
        Formula::eq(lhs.clone(), val.clone()),
    );
    let want = Formula::forall(a, Formula::forall(b, Formula::forall(c, Formula::forall(d, body))));
    (want, lhs, val)
}

#[test]
fn the_first_point_computes() {
    let mut env = Env::new();
    let (ap, tp) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(tp.left.concl()));
    let (want, lhs, val) = expected(&mut env, &ap, false);
    assert_eq!(*tp.left.concl(), want);
    assert_ne!(lhs, val, "the equation is reflexivity in disguise");
}

#[test]
fn the_second_point_computes() {
    let mut env = Env::new();
    let (ap, tp) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(tp.right.concl()));
    let (want, lhs, val) = expected(&mut env, &ap, true);
    assert_eq!(*tp.right.concl(), want);
    assert_ne!(lhs, val, "the equation is reflexivity in disguise");
}

/// The antecedent `¬(a = c)` is not one no pair of sets satisfies: at `a := ∅`
/// and `c := {∅}` it is [`derived::empty::empty`]'s own non-membership, and both
/// equations come out with no hypothesis left.
#[test]
fn the_antecedent_is_satisfiable() {
    let mut env = Env::new();
    let (ap, tp) = build(&mut env);

    let emp = Term::apply(ap.empty, vec![]);
    let one = derived::singleton(ap.sets.up, emp.clone());
    let (b, d) = (env.fresh_var(), env.fresh_var());
    let (tb, td) = (Term::var(b), Term::var(d));

    // `⊢ ¬(∅ = {∅})`: `∅ ∈ {∅}` but nothing is in `∅`.
    let e_in_one = kernel::Thm::mp(
        &derived::iff_mpr(&derived::inst_all(&ap.mem_sing, &[emp.clone(), emp.clone()]).unwrap())
            .unwrap(),
        &kernel::Thm::eq_refl(emp.clone()),
    )
    .expect("∅ ∈ {∅}");
    let hole = env.fresh_var();
    // `∅ = {∅} → {∅} = ∅ → (∅ ∈ {∅} → ∅ ∈ ∅)`, then discharge `∅ ∈ {∅}`.
    let back = derived::syl(
        &derived::eq_symm_imp(&mut env, emp.clone(), one.clone()),
        &kernel::Thm::eq_leibniz(
            one.clone(),
            emp.clone(),
            hole,
            Formula::mem(emp.clone(), Term::var(hole)),
        ),
    )
    .expect("Leibniz along {∅} = ∅");
    let self_mem = derived::mpd_const(&back, &e_in_one).expect("∅ = {∅} → ∅ ∈ ∅");
    let ne = derived::syl(
        &self_mem,
        &derived::inst_all(&ap.empty_ax, std::slice::from_ref(&emp)).unwrap(),
    )
    .expect("¬(∅ = {∅})");
    assert_eq!(*ne.concl(), Formula::not(Formula::eq(emp.clone(), one.clone())));

    let at = derived::inst_all(&tp.left, &[emp.clone(), tb.clone(), one.clone(), td.clone()])
        .expect("instantiate");
    let out = kernel::Thm::mp(&at, &ne).expect("discharge");
    let g = TwoPoint::of(&ap, emp.clone(), tb.clone(), one.clone(), td.clone());
    assert_eq!(*out.concl(), Formula::eq(ap.apply(g.clone(), emp.clone()), tb));

    let at = derived::inst_all(&tp.right, &[emp.clone(), Term::var(b), one.clone(), td.clone()])
        .expect("instantiate");
    let out = kernel::Thm::mp(&at, &ne).expect("discharge");
    assert_eq!(*out.concl(), Formula::eq(ap.apply(g, one), Term::var(d)));
}
