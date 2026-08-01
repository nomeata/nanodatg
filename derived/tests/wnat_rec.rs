//! `N.rec` as the W-recursor: the packed step, its two computation rules, and
//! the ι equations they feed.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here.

use kernel::{Env, Formula, Term};

use derived::bound::Bound;
use derived::point_fun::PointFun;
use derived::sums::Cases;
use derived::wnat::Nat;
use derived::wnat_rec::{key_succ, key_zero, pow_prod, value_succ, NatRec};
use derived::wtype::Wtype;

struct Fix {
    wt: Wtype,
    #[allow(dead_code)]
    bnd: Bound,
    nat: Nat,
    nr: NatRec,
    rc: derived::wrec_total::Recursor,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let cases = Cases::new(env, &wt.sums).expect("rec₊");
    let pf = PointFun::over(env, &wt.sums, &wt.app_pair).expect("one-point graph");
    let empty_u = derived::enums::empty_in_least_universe(env, &wt, &bnd).expect("∅ ∈ U(A)");
    let nat = Nat::over(env, &wt, &bnd, &cases, &pf, &empty_u).expect("N");
    let pj = derived::proj::Proj::new(env, &wt.sums.ap, &pf).expect("projections");
    let rc = derived::wrec_total::Recursor::new(env, &wt).expect("recursor");
    let ext = derived::wrec_extend::extension(env, &wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &wt, &rc, &total).expect("iota");
    let fs = derived::wrec_total::wrec_funspace(env, &wt, &rc, &total).expect("fs");
    let nr = NatRec::over(env, &wt, &bnd, &nat, &rc, &pf, &pj, &iota, &fs).expect("N.rec");
    Fix { wt, bnd, nat, nr, rc }
}

#[test]
fn the_step_computes_at_zero() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.nr.app_zero.concl()));

    let (zv, sv, tv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (z, su, t) = (Term::var(zv), Term::var(sv), Term::var(tv));
    let step = f.nr.syms.step_of(&f.wt, &z, &su, &t);
    let lhs = f.wt.sums.ap.apply(step, key_zero(&f.wt));
    assert_ne!(lhs, z, "app_zero would be reflexivity");
    let want = Formula::forall(
        zv,
        Formula::forall(sv, Formula::forall(tv, Formula::eq(lhs, z))),
    );
    assert_eq!(*f.nr.app_zero.concl(), want);
}

#[test]
fn the_step_computes_at_succ() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.nr.app_succ.concl()));

    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (z, su, t, fu, r) = (&ts[0], &ts[1], &ts[2], &ts[3], &ts[4]);
    let s = &f.wt.sums;
    let step = f.nr.syms.step_of(&f.wt, z, su, t);
    let lhs = s.ap.apply(step, key_succ(&f.wt, fu, r));
    let rhs = value_succ(&s.ap, su, fu, r);
    assert_ne!(lhs, rhs, "app_succ would be reflexivity");

    let hyp = Formula::and(
        Formula::mem(fu.clone(), pow_prod(s, &f.nat.ty)),
        Formula::mem(r.clone(), pow_prod(s, t)),
    );
    let mut want = Formula::imp(hyp, Formula::eq(lhs, rhs));
    for v in vars.iter().rev() {
        want = Formula::forall(*v, want);
    }
    assert_eq!(*f.nr.app_succ.concl(), want);
}

#[test]
fn the_step_is_a_function() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.nr.sv.concl()));

    let (zv, sv, tv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (z, su, t) = (Term::var(zv), Term::var(sv), Term::var(tv));
    let step = f.nr.syms.step_of(&f.wt, &z, &su, &t);
    let body = derived::funspace::is_single_valued(&mut env, &f.wt.sums.ap.sets, &step);
    let want = Formula::forall(zv, Formula::forall(sv, Formula::forall(tv, body)));
    assert_eq!(*f.nr.sv.concl(), want);
}

/// `⊢ ∀z ∀s ∀T. (HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T)))`, rebuilt from
/// [`derived::wrec_total::step_typed`] itself rather than from a copy of it.
#[test]
fn the_step_is_typed() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.nr.step_typed.concl()));

    let (zv, sv, tv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (z, su, t) = (Term::var(zv), Term::var(sv), Term::var(tv));
    let s = &f.wt.sums;
    let step = f.nr.syms.step_of(&f.wt, &z, &su, &t);
    let u = f.bnd.universe_of(f.nat.tags.clone());
    let body = Formula::imp(
        derived::wnat_rec::premise(s, &f.nat, &z, &su, &t),
        derived::wrec_total::step_typed(
            &mut env, s, &f.wt, &f.nat.tags, &f.nat.fam, &u, &t, &step,
        ),
    );
    let want = Formula::forall(zv, Formula::forall(sv, Formula::forall(tv, body)));
    assert_eq!(*f.nr.step_typed.concl(), want);
}

#[test]
fn the_recursor_computes_at_zero() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.nr.iota_zero.concl()));

    let (zv, sv, tv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (z, su, t) = (Term::var(zv), Term::var(sv), Term::var(tv));
    let s = &f.wt.sums;
    let nrec = f.nr.of(&f.wt, &f.bnd, &f.nat, &f.rc, &z, &su, &t);
    let lhs = s.ap.apply(nrec, f.nat.zero_t.clone());
    assert_ne!(lhs, z, "iota_zero would be reflexivity");
    let body = Formula::imp(
        derived::wnat_rec::premise(s, &f.nat, &z, &su, &t),
        Formula::eq(lhs, z),
    );
    let want = Formula::forall(zv, Formula::forall(sv, Formula::forall(tv, body)));
    assert_eq!(*f.nr.iota_zero.concl(), want);
}

/// The equation the whole file exists for: ι at `N.succ`, whose right-hand side
/// mentions the recursor again.
#[test]
fn the_recursor_computes_at_succ_with_a_live_recursive_call() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.nr.iota_succ.concl()));

    let (zv, sv, tv, nv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (z, su, t, n) = (Term::var(zv), Term::var(sv), Term::var(tv), Term::var(nv));
    let s = &f.wt.sums;
    let nrec = f.nr.of(&f.wt, &f.bnd, &f.nat, &f.rc, &z, &su, &t);
    let lhs = s.ap.apply(nrec.clone(), Nat::succ_term(&f.wt, n.clone()));
    let call = s.ap.apply(nrec, n.clone());
    let rhs = s.ap.apply(s.ap.apply(su.clone(), n.clone()), call.clone());
    assert_ne!(lhs, rhs, "iota_succ would be reflexivity");

    // The recursive call really is on the right, at the *subterm* `n`.
    let mut seen = Vec::new();
    rhs.free_vars(&mut seen);
    assert!(seen.contains(&nv));
    assert_ne!(call, lhs, "the recursive call is not the redex itself");

    let body = Formula::imp(
        Formula::and(
            derived::wnat_rec::premise(s, &f.nat, &z, &su, &t),
            Formula::mem(n, f.nat.ty.clone()),
        ),
        Formula::eq(lhs, rhs),
    );
    let mut want = body;
    for v in [nv, tv, sv, zv] {
        want = Formula::forall(v, want);
    }
    assert_eq!(*f.nr.iota_succ.concl(), want);
}

/// The ι rules carry `HYP`, so `HYP` had better be satisfiable — and the
/// witness discharges it, leaving both computation rules unconditional at that
/// instance.
#[test]
fn the_hypothesis_is_satisfiable_and_the_recursor_then_computes() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let pf = PointFun::over(&mut env, &f.wt.sums, &f.wt.app_pair).expect("one-point graph");
    let (z, su, t, wit) =
        derived::wnat_rec::premise_witness(&mut env, &f.wt, &f.nat, &pf).expect("witness");
    assert_eq!(
        *wit.concl(),
        derived::wnat_rec::premise(&f.wt.sums, &f.nat, &z, &su, &t)
    );

    // With it discharged, ι at `N.zero` has no hypothesis left.
    let at = derived::inst_all(&f.nr.iota_zero, &[z.clone(), su.clone(), t.clone()])
        .expect("instantiate");
    let fired = kernel::Thm::mp(&at, &wit).expect("discharge");
    let nrec = f.nr.of(&f.wt, &f.bnd, &f.nat, &f.rc, &z, &su, &t);
    assert_eq!(
        *fired.concl(),
        Formula::eq(
            f.wt.sums.ap.apply(nrec, f.nat.zero_t.clone()),
            z.clone()
        )
    );
    assert!(kernel::thm::debug_locally_closed(fired.concl()));
}
