//! A constructor's recursive-argument function — the set function out of
//! `finord(m)` that hands back the `m` recursive arguments.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game.** The typing rule alone is satisfied by
//! `f := ∅` for every `m`; [`two_recursive_arguments_come_back_out`] shows the
//! function computes, at two visibly distinct points, to the two values the
//! caller chose — which is what makes a two-recursive-argument constructor (a
//! binary tree's `node`) injective in **both** subtrees.

use kernel::{Env, Formula, Term, Thm};

use derived::ext::app_of_pair;
use derived::finset::FinSet;
use derived::point_fun::PointFun;
use derived::recarg::RecArg;
use derived::isum::ISumSyms;
use derived::sums::Cases;
use derived::wtype::Wtype;
use derived::inst_all;

struct Dev {
    wt: Wtype,
    cases: Cases,
    syms: ISumSyms,
    pf: PointFun,
    fin: FinSet,
}

fn build(env: &mut Env) -> Dev {
    let wt = Wtype::new(env).expect("wtype");
    let cases = Cases::new(env, &wt.sums).expect("rec₊");
    let app_pair = app_of_pair(env, &wt.sums.ap).expect("app_of_pair");
    let pf = PointFun::over(env, &wt.sums, &app_pair).expect("point functions");
    let fin = FinSet::new(env, &wt.sums).expect("finset");
    let mut syms = ISumSyms::new();
    syms.ensure(env, &wt.sums, 4).expect("the sum symbols");
    Dev { wt, cases, syms, pf, fin }
}

fn recarg(env: &mut Env, d: &Dev, m: usize) -> RecArg {
    RecArg::new(
        env,
        &d.wt.sums,
        &d.cases,
        &d.syms,
        &d.pf,
        &d.fin,
        &d.wt.fs_mono,
        &d.wt.empty_fun,
        m,
    )
    .expect("the recursive-argument function")
}

/// A constructor with no recursive arguments gets the empty function out of the
/// empty fibre, and the typing rule has no antecedent left.
#[test]
fn no_recursive_arguments_is_the_empty_function() {
    let mut env = Env::new();
    let d = build(&mut env);
    let ra = recarg(&mut env, &d, 0);

    assert_eq!(ra.fun, d.wt.sums.zero());
    assert_eq!(ra.domain, d.syms.finord(&d.wt.sums, 0).expect("finord"));
    assert!(ra.app.is_empty());

    let s_var = Term::var(env.fresh_var());
    let at = inst_all(&ra.in_funspace, std::slice::from_ref(&s_var)).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::mem(
            d.wt.sums.zero(),
            d.wt.sums.fs.of(d.syms.finord(&d.wt.sums, 0).expect("finord"), s_var)
        ),
        "the typing rule at m = 0 carries no hypothesis"
    );
}

/// One recursive argument: the fibre is `finord(1) = 1 + 0`, which is **not**
/// the term `1`, so the function is not the one-point graph `wnat.rs` uses.
#[test]
fn one_recursive_argument_is_not_a_one_point_graph() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let ra = recarg(&mut env, &d, 1);

    assert_eq!(ra.domain, d.syms.finord(s, 1).expect("finord"));
    assert_ne!(d.syms.finord(s, 1).expect("finord"), s.unit(), "finord(1) is 1 + 0, not {{∅}}");
    assert_ne!(
        ra.fun,
        PointFun::of(s, s.point(), Term::var(ra.vars[0])),
        "the general function is a dispatcher, not the hand-written one-point graph"
    );

    let r0 = Term::var(ra.vars[0]);
    let t = Term::var(env.fresh_var());
    let typing = inst_all(&ra.in_funspace, &[t.clone(), r0.clone()]).expect("instantiate");
    assert_eq!(
        *typing.concl(),
        Formula::imp(
            Formula::mem(r0.clone(), t.clone()),
            Formula::mem(ra.fun.clone(), s.fs.of(d.syms.finord(s, 1).expect("finord"), t)),
        )
    );

    let app = inst_all(&ra.app[0], std::slice::from_ref(&r0)).expect("instantiate");
    assert_eq!(
        *app.concl(),
        Formula::eq(s.ap.apply(ra.fun.clone(), d.syms.inj(0, s.point()).expect("inj")), r0),
        "the computation rule is unconditional"
    );
}

/// Two recursive arguments, at two provably different points. This is the shape
/// nothing in `derived/` could express before: `wnat.rs` and `wlist.rs` both
/// stop at one.
#[test]
fn two_recursive_arguments_come_back_out() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let ra = recarg(&mut env, &d, 2);
    let (r0, r1) = (Term::var(ra.vars[0]), Term::var(ra.vars[1]));

    for (j, r) in [&r0, &r1].into_iter().enumerate() {
        let app = inst_all(&ra.app[j], &[r0.clone(), r1.clone()]).expect("instantiate");
        assert_eq!(
            *app.concl(),
            Formula::eq(s.ap.apply(ra.fun.clone(), d.syms.inj(j, s.point()).expect("inj")), r.clone())
        );
    }

    // The two points are distinct, so the two equations say different things.
    let apart = d.syms.inj_distinct(&mut env, s, 0, 1).expect("the injections are disjoint");
    let at = inst_all(&apart, &[s.point(), s.point()]).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::not(Formula::eq(d.syms.inj(0, s.point()).expect("inj"), d.syms.inj(1, s.point()).expect("inj")))
    );

    // And the typing rule carries exactly the two memberships.
    let t = Term::var(env.fresh_var());
    let typing =
        inst_all(&ra.in_funspace, &[t.clone(), r0.clone(), r1.clone()]).expect("instantiate");
    assert_eq!(
        *typing.concl(),
        Formula::imp(
            Formula::and(
                Formula::mem(r0, t.clone()),
                Formula::mem(r1, t.clone()),
            ),
            Formula::mem(ra.fun.clone(), s.fs.of(d.syms.finord(s, 2).expect("finord"), t)),
        )
    );
}

/// Four recursive arguments still works, and the `j`-th point still returns the
/// `j`-th argument — the construction is not secretly capped.
#[test]
fn the_arity_is_not_capped() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let ra = recarg(&mut env, &d, 4);
    let rs: Vec<Term> = ra.vars.iter().map(|v| Term::var(*v)).collect();

    for j in 0..4 {
        let app: Thm = inst_all(&ra.app[j], &rs).expect("instantiate");
        assert_eq!(
            *app.concl(),
            Formula::eq(s.ap.apply(ra.fun.clone(), d.syms.inj(j, s.point()).expect("inj")), rs[j].clone())
        );
    }
    assert_eq!(FinSet::of(s, &rs), ra.dispatch.as_ref().expect("dispatcher").target);
}
