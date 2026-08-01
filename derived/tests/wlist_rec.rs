//! `List.rec` as the W-recursor: the packed step, its two computation rules, and
//! the ι equations they feed.
//!
//! Each test rebuilds the formula it expects from the kernel's own constructors,
//! so a theorem with the right name and the wrong shape fails here. The two that
//! matter most are [`the_recursor_computes_at_cons_with_the_field_and_the_call`]
//! — the equation the whole file exists for — and
//! [`the_hypothesis_is_satisfiable_and_the_recursor_then_computes`], which shows
//! the hypothesis both ι rules carry is not one no four sets satisfy.

use kernel::{Env, Formula, Term};

use derived::bound::Bound;
use derived::point_fun::PointFun;
use derived::sums::Cases;
use derived::wlist::WList;
use derived::wlist_rec::{key_cons, key_nil, pow_prod, value_cons, ListRec};
use derived::wtype::Wtype;

struct Fix {
    wt: Wtype,
    bnd: Bound,
    cases: Cases,
    wl: WList,
    lr: ListRec,
    rc: derived::wrec_total::Recursor,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let cases = Cases::new(env, &wt.sums).expect("rec₊");
    let pf = PointFun::over(env, &wt.sums, &wt.app_pair).expect("one-point graph");
    let empty_u = derived::enums::empty_in_least_universe(env, &wt, &bnd).expect("∅ ∈ U(A)");
    let wl = WList::over(env, &wt, &bnd, &cases, &pf, &empty_u).expect("List");
    let pj = derived::proj::Proj::new(env, &wt.sums.ap, &pf).expect("projections");
    let rc = derived::wrec_total::Recursor::new(env, &wt).expect("recursor");
    let ext = derived::wrec_extend::extension(env, &wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &wt, &rc, &total).expect("iota");
    let fs = derived::wrec_total::wrec_funspace(env, &wt, &rc, &total).expect("fs");
    let lr = ListRec::over(env, &wt, &bnd, &wl, &cases, &rc, &pf, &pj, &iota, &fs)
        .expect("List.rec");
    Fix { wt, bnd, cases, wl, lr, rc }
}

fn four(env: &mut Env) -> (Vec<kernel::FreeVar>, Vec<Term>) {
    let vs: Vec<kernel::FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ts = vs.iter().map(|v| Term::var(*v)).collect();
    (vs, ts)
}

#[test]
fn the_step_computes_at_nil() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.lr.app_nil.concl()));

    let (vs, ts) = four(&mut env);
    let (a, z, su, t) = (&ts[0], &ts[1], &ts[2], &ts[3]);
    let step = f.lr.syms.step_of(&f.wt, a, z, su, t);
    let lhs = f.wt.sums.ap.apply(step, key_nil(&f.wt));
    assert_ne!(lhs, *z, "app_nil would be reflexivity");
    let mut want = Formula::eq(lhs, z.clone());
    for v in vs.iter().rev() {
        want = Formula::forall(*v, want);
    }
    assert_eq!(*f.lr.app_nil.concl(), want);
}

/// The cons value has **three** components — the head, the subterm and the
/// recursive value — where `N`'s had two. That is the claim `derived::proj` was
/// built to make good, so it is pinned rather than described.
#[test]
fn the_step_computes_at_cons_with_the_head_in_the_value() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.lr.app_cons.concl()));

    let (vs, ts) = four(&mut env);
    let (a, z, su, t) = (ts[0].clone(), ts[1].clone(), ts[2].clone(), ts[3].clone());
    let (hv, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (h, fu, r) = (Term::var(hv), Term::var(fv), Term::var(rv));
    let s = &f.wt.sums;
    let step = f.lr.syms.step_of(&f.wt, &a, &z, &su, &t);
    let lhs = s.ap.apply(step, key_cons(&f.wt, &h, &fu, &r));
    let rhs = value_cons(&s.ap, &su, &h, &fu, &r);
    assert_ne!(lhs, rhs, "app_cons would be reflexivity");

    // The head really is in the value, and not only in the key.
    let mut seen = Vec::new();
    rhs.free_vars(&mut seen);
    assert!(seen.contains(&hv), "the cons value ignores the field");

    let hyp = Formula::and(
        Formula::mem(h, a.clone()),
        Formula::and(
            Formula::mem(fu, pow_prod(s, &f.wl.ty_of(a.clone()))),
            Formula::mem(r, pow_prod(s, &t)),
        ),
    );
    let mut want = Formula::imp(hyp, Formula::eq(lhs, rhs));
    for v in [rv, fv, hv].iter().chain(vs.iter().rev()) {
        want = Formula::forall(*v, want);
    }
    assert_eq!(*f.lr.app_cons.concl(), want);
}

#[test]
fn the_step_is_a_function() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.lr.sv.concl()));

    let (vs, ts) = four(&mut env);
    let step = f.lr.syms.step_of(&f.wt, &ts[0], &ts[1], &ts[2], &ts[3]);
    let body = derived::funspace::is_single_valued(&mut env, &f.wt.sums.ap.sets, &step);
    let mut want = body;
    for v in vs.iter().rev() {
        want = Formula::forall(*v, want);
    }
    assert_eq!(*f.lr.sv.concl(), want);
}

/// Rebuilt from [`derived::wrec_total::step_typed`] itself rather than from a
/// copy of it, so the theorem discharges the very hypothesis the W-recursor asks
/// for.
#[test]
fn the_step_is_typed() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.lr.step_typed.concl()));

    let (vs, ts) = four(&mut env);
    let (a, z, su, t) = (ts[0].clone(), ts[1].clone(), ts[2].clone(), ts[3].clone());
    let s = &f.wt.sums;
    let step = f.lr.syms.step_of(&f.wt, &a, &z, &su, &t);
    let tags = WList::tags_of(s, a.clone());
    let fam = f.wl.fam_of(s, &f.cases, a.clone());
    let u = f.bnd.universe_of(tags.clone());
    let body = Formula::imp(
        derived::wlist_rec::premise(s, &f.wl, &a, &z, &su, &t),
        derived::wrec_total::step_typed(&mut env, s, &f.wt, &tags, &fam, &u, &t, &step),
    );
    let mut want = body;
    for v in vs.iter().rev() {
        want = Formula::forall(*v, want);
    }
    assert_eq!(*f.lr.step_typed.concl(), want);
}

#[test]
fn the_recursor_computes_at_nil() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.lr.iota_nil.concl()));

    let (vs, ts) = four(&mut env);
    let (a, z, su, t) = (ts[0].clone(), ts[1].clone(), ts[2].clone(), ts[3].clone());
    let s = &f.wt.sums;
    let lrec = f.lr.of(&f.wt, &f.bnd, &f.wl, &f.cases, &f.rc, &a, &z, &su, &t);
    let lhs = s.ap.apply(lrec, f.wl.nil_t.clone());
    assert_ne!(lhs, z, "iota_nil would be reflexivity");
    let body = Formula::imp(
        derived::wlist_rec::premise(s, &f.wl, &a, &z, &su, &t),
        Formula::eq(lhs, z.clone()),
    );
    let mut want = body;
    for v in vs.iter().rev() {
        want = Formula::forall(*v, want);
    }
    assert_eq!(*f.lr.iota_nil.concl(), want);
}

/// The equation the whole file exists for: ι at `List.cons`, whose right-hand
/// side mentions the recursor again **and** the constructor's field.
#[test]
fn the_recursor_computes_at_cons_with_the_field_and_the_call() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.lr.iota_cons.concl()));

    let (vs, ts) = four(&mut env);
    let (a, z, su, t) = (ts[0].clone(), ts[1].clone(), ts[2].clone(), ts[3].clone());
    let (hv, lv) = (env.fresh_var(), env.fresh_var());
    let (h, tl) = (Term::var(hv), Term::var(lv));
    let s = &f.wt.sums;
    let lrec = f.lr.of(&f.wt, &f.bnd, &f.wl, &f.cases, &f.rc, &a, &z, &su, &t);
    let lhs = s.ap.apply(lrec.clone(), WList::cons_term(&f.wt, h.clone(), tl.clone()));
    let call = s.ap.apply(lrec, tl.clone());
    let rhs = s.ap.apply(
        s.ap.apply(s.ap.apply(su.clone(), h.clone()), tl.clone()),
        call.clone(),
    );
    assert_ne!(lhs, rhs, "iota_cons would be reflexivity");

    // The recursive call really is on the right, at the *tail*, and the head is
    // there too.
    let mut seen = Vec::new();
    rhs.free_vars(&mut seen);
    assert!(seen.contains(&lv));
    assert!(seen.contains(&hv), "the cons rule ignores the field");
    assert_ne!(call, lhs, "the recursive call is not the redex itself");

    let body = Formula::imp(
        Formula::and(
            derived::wlist_rec::premise(s, &f.wl, &a, &z, &su, &t),
            Formula::and(
                Formula::mem(h, a.clone()),
                Formula::mem(tl, f.wl.ty_of(a.clone())),
            ),
        ),
        Formula::eq(lhs, rhs),
    );
    let mut want = body;
    for v in [lv, hv].iter().chain(vs.iter().rev()) {
        want = Formula::forall(*v, want);
    }
    assert_eq!(*f.lr.iota_cons.concl(), want);
}

/// The ι rules carry `HYP`, so `HYP` had better be satisfiable — and the witness
/// discharges it, leaving the nil rule unconditional at that instance.
///
/// The witness takes `α := 1` rather than `α := 0` on purpose: with an empty
/// parameter the cons rule's own extra hypothesis `h ∈ α` would be unsatisfiable
/// and that rule would still say nothing. At `α := 1` the head `•` is a member,
/// which the second half of this test cashes in.
#[test]
fn the_hypothesis_is_satisfiable_and_the_recursor_then_computes() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let pf = PointFun::over(&mut env, &f.wt.sums, &f.wt.app_pair).expect("one-point graph");
    let (a, z, su, t, wit) =
        derived::wlist_rec::premise_witness(&mut env, &f.wt, &f.wl, &pf).expect("witness");
    assert_eq!(
        *wit.concl(),
        derived::wlist_rec::premise(&f.wt.sums, &f.wl, &a, &z, &su, &t)
    );

    // With it discharged, ι at `List.nil` has no hypothesis left.
    let at = derived::inst_all(&f.lr.iota_nil, &[a.clone(), z.clone(), su.clone(), t.clone()])
        .expect("instantiate");
    let fired = kernel::Thm::mp(&at, &wit).expect("discharge");
    let lrec = f.lr.of(&f.wt, &f.bnd, &f.wl, &f.cases, &f.rc, &a, &z, &su, &t);
    assert_eq!(
        *fired.concl(),
        Formula::eq(f.wt.sums.ap.apply(lrec, f.wl.nil_t.clone()), z.clone())
    );
    assert!(kernel::thm::debug_locally_closed(fired.concl()));

    // …and the cons rule's remaining hypothesis is `• ∈ 1 ∧ nil ∈ lt(1)`, both
    // of which are theorems, so that rule is not vacuous either.
    let s = &f.wt.sums;
    let nil = f.wl.nil_t.clone();
    let ic = derived::inst_all(
        &f.lr.iota_cons,
        &[a.clone(), z.clone(), su.clone(), t.clone(), s.point(), nil.clone()],
    )
    .expect("instantiate");
    let nil_mem = derived::inst_all(&f.wl.nil, std::slice::from_ref(&a)).expect("nil ∈ lt(1)");
    let both = derived::and_intro(&wit, &derived::and_intro(&s.unit_mem, &nil_mem));
    let fired_cons = kernel::Thm::mp(&ic, &both).expect("discharge the cons rule");
    let lrec = f.lr.of(&f.wt, &f.bnd, &f.wl, &f.cases, &f.rc, &a, &z, &su, &t);
    let want = Formula::eq(
        s.ap.apply(lrec.clone(), WList::cons_term(&f.wt, s.point(), nil.clone())),
        s.ap.apply(
            s.ap.apply(s.ap.apply(su.clone(), s.point()), nil.clone()),
            s.ap.apply(lrec, nil),
        ),
    );
    assert_eq!(*fired_cons.concl(), want);
    assert!(kernel::thm::debug_locally_closed(fired_cons.concl()));
}
