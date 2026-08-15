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
/// the term `1`, so the function is not the one-point graph the deleted
/// `wnat.rs` used.
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
/// nothing in `derived/` could express before: `wlist.rs` stops at one, and so
/// did the deleted `wnat.rs`.
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

// ─────────────────────────────────────────────────────────────────────────────
// `RecArg::general` — a constructor whose recursive arguments are **functions**.
//
// **Three summands, and deliberately not three copies of `1`.** The fibre is
// `Sum_3(A₀,A₁,A₂)` at three *distinct* variable summands, which is what
// separates "the rule is general in its summands" from "the rule happens to
// work at `finord(3)`": at equal summands a `j`-for-`i` slip in either the
// branch typing or the computation rule is invisible.
// ─────────────────────────────────────────────────────────────────────────────

fn general(env: &mut Env, d: &Dev, ran: &derived::ran::Ran, summands: &[Term]) -> RecArg {
    RecArg::general(
        env,
        &d.wt.sums,
        &d.cases,
        &d.syms,
        ran,
        &d.fin,
        &d.wt.fs_mono,
        &d.wt.empty_fun,
        summands,
    )
    .expect("the general recursive-argument function")
}

/// Every export carries `H := ⋀ⱼ gⱼ ∈ fs(Aⱼ, S)`, and the codomain the term
/// mentions is built from the branches — never from `S`.
#[test]
fn the_general_function_is_stated_under_its_branch_typings() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let ran = derived::ran::Ran::new(&mut env, s).expect("ran");

    let summands: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let ra = general(&mut env, &d, &ran, &summands);

    assert_eq!(ra.m, 3);
    assert_eq!(ra.summands, summands);
    assert_eq!(ra.domain, d.syms.sum(&summands).expect("Sum_3"));

    let gs: Vec<Term> = ra.vars.iter().map(|v| Term::var(*v)).collect();
    let ts = Term::var(ra.target);
    let atoms: Vec<Formula> = (0..3)
        .map(|j| Formula::mem(gs[j].clone(), s.fs.of(summands[j].clone(), ts.clone())))
        .collect();
    let h = derived::conj_of(&atoms).expect("the hypothesis");
    assert_eq!(ra.hyp, Some(h.clone()));

    // The **term** mentions `⋃ⱼ ran(gⱼ)` and does not mention `S`.
    assert_eq!(ra.fun, RecArg::of_general(s, &d.cases, &ran, &summands, &gs));
    assert!(!ra.fun.occurs_free(ra.target), "the term must not mention its codomain variable");

    // ⊢ ∀S ∀g⃗. (H → f(g⃗) ∈ fs(Sum_3(A⃗), S))
    let mut args = vec![ts.clone()];
    args.extend(gs.iter().cloned());
    let typed = inst_all(&ra.in_funspace, &args).expect("instantiate the typing rule");
    assert_eq!(
        *typed.concl(),
        Formula::imp(
            h.clone(),
            Formula::mem(ra.fun.clone(), s.fs.of(ra.domain.clone(), ts.clone()))
        )
    );

    // ⊢ ∀S ∀g⃗ ∀z. (H → (z ∈ Aⱼ → app(f(g⃗), Inj_j z) = app(gⱼ, z)))
    for j in 0..3 {
        let tz = Term::var(env.fresh_var());
        let mut at = args.clone();
        at.push(tz.clone());
        let rule = inst_all(&ra.app[j], &at).expect("instantiate the computation rule");
        assert_eq!(
            *rule.concl(),
            Formula::imp(
                h.clone(),
                Formula::imp(
                    Formula::mem(tz.clone(), summands[j].clone()),
                    Formula::eq(
                        s.ap.apply(ra.fun.clone(), d.syms.inj(j, tz.clone()).expect("Inj_j")),
                        s.ap.apply(gs[j].clone(), tz),
                    ),
                )
            ),
            "computation rule {j}"
        );
    }
    assert!(derived::all_unconditional(&[&ra.in_funspace, &ra.app[0], &ra.app[1], &ra.app[2]]));

    // Non-vacuity: the three rules name three different branches at three
    // different summands, so this is not one rule stated three times.
    assert_ne!(summands[0], summands[2]);
    assert_ne!(gs[0], gs[2]);
}

/// The nullary case is the **same** function both entry points build, with no
/// hypothesis — so a declaration with no recursive arguments does not have to
/// know which door it came through.
#[test]
fn the_general_and_degenerate_entry_points_agree_at_zero() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let ran = derived::ran::Ran::new(&mut env, s).expect("ran");

    let plain = recarg(&mut env, &d, 0);
    let gen = general(&mut env, &d, &ran, &[]);
    assert_eq!(plain.fun, gen.fun);
    assert_eq!(plain.domain, gen.domain);
    assert_eq!(plain.hyp, None);
    assert_eq!(gen.hyp, None);
    assert!(gen.app.is_empty());

    let sv = Term::var(env.fresh_var());
    assert_eq!(
        *inst_all(&gen.in_funspace, std::slice::from_ref(&sv)).expect("instantiate").concl(),
        *inst_all(&plain.in_funspace, std::slice::from_ref(&sv)).expect("instantiate").concl(),
    );
}

/// **The degenerate spelling did not move.** `RecArg::of` still builds its
/// codomain as `fin(r⃗)`, which is `FinSet::chain` at the singletons — the same
/// chain the general form uses at the ranges, and a *different term* from
/// `⋃ⱼ ran({⟨•,rⱼ⟩})`, which is the same set.
#[test]
fn the_plain_codomain_is_the_chain_at_singletons_and_not_at_ranges() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let ran = derived::ran::Ran::new(&mut env, s).expect("ran");

    let rs: Vec<Term> = (0..2).map(|_| Term::var(env.fresh_var())).collect();
    let singletons: Vec<Term> =
        rs.iter().map(|r| derived::singleton(s.ap.sets.up, r.clone())).collect();
    assert_eq!(FinSet::of(s, &rs), FinSet::chain(s, &singletons));

    let graphs: Vec<Term> =
        rs.iter().map(|r| PointFun::of(s, s.point(), r.clone())).collect();
    let ranges: Vec<Term> = graphs.iter().map(|g| ran.of(g.clone())).collect();
    assert_ne!(
        FinSet::of(s, &rs),
        FinSet::chain(s, &ranges),
        "a ran-based codomain would move every constructor term in the project"
    );
    assert_ne!(
        RecArg::of(s, &d.cases, &rs),
        RecArg::of_general(s, &d.cases, &ran, &vec![s.unit(); 2], &graphs),
        "the two spellings are two terms"
    );
}
