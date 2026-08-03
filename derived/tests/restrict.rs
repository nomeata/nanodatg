//! The restriction of a function on `Sum_n(A⃗)` to one summand —
//! `f|ⱼ = { ⟨z, app(f, Injⱼ(z))⟩ : z ∈ Aⱼ }`.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Three summands, at three distinct variables.** A restriction that read the
//! wrong depth — or that dropped the depth and restricted along `Inj₀` always —
//! is invisible at two equal summands and invisible at `finord(n)`, where every
//! summand is `1`. [`the_three_summands_are_told_apart`] is what pins it.
//!
//! **Non-vacuity is the whole game.** The typing rule alone is satisfied by
//! `f|ⱼ := ∅` on an empty `Aⱼ`.
//! [`the_restriction_recovers_the_branch_it_was_packed_from`] is what says the
//! operation is the inverse of the packing it exists to undo: restricting
//! [`RecArg::general`]'s dispatcher at branch `j` computes, at every point of
//! `Aⱼ`, to the branch function `gⱼ` the caller packed.

use kernel::{Env, Formula, Term, Thm};

use derived::ext::{app_of_pair, funspace_app_mem};
use derived::finset::FinSet;
use derived::isum::ISumSyms;
use derived::point_fun::PointFun;
use derived::ran::Ran;
use derived::recarg::RecArg;
use derived::sums::Cases;
use derived::wtype::Wtype;
use derived::{eq_trans, inst_all};

struct Dev {
    wt: Wtype,
    cases: Cases,
    syms: ISumSyms,
    fin: FinSet,
    ran: Ran,
    app_mem: Thm,
}

fn build(env: &mut Env) -> Dev {
    let wt = Wtype::new(env).expect("wtype");
    let cases = Cases::new(env, &wt.sums).expect("rec₊");
    let app_pair = app_of_pair(env, &wt.sums.ap).expect("app_of_pair");
    let _pf = PointFun::over(env, &wt.sums, &app_pair).expect("point functions");
    let fin = FinSet::new(env, &wt.sums).expect("finset");
    let ran = Ran::new(env, &wt.sums).expect("ran");
    let app_mem =
        funspace_app_mem(env, &wt.sums.ap, &wt.sums.prod, &wt.sums.fs, &app_pair).expect("app_mem");
    let mut syms = ISumSyms::new();
    syms.ensure(env, &wt.sums, 4).expect("the sum symbols");
    Dev { wt, cases, syms, fin, ran, app_mem }
}

/// The computation rule, at three depths: `app(f|ⱼ, z) = app(f, Injⱼ(z))` for
/// every `z` in the domain, and **no other hypothesis**.
#[test]
fn the_restriction_computes_on_its_domain() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;

    for j in 0..3 {
        let b = d.syms.branch(&mut env, s, j).expect("the branch");
        assert_eq!(b.depth, j);
        let (f, a, z) = (
            Term::var(env.fresh_var()),
            Term::var(env.fresh_var()),
            Term::var(env.fresh_var()),
        );
        let at = inst_all(&b.app, &[f.clone(), a.clone(), z.clone()]).expect("instantiate");
        assert_eq!(
            *at.concl(),
            Formula::imp(
                Formula::mem(z.clone(), a.clone()),
                Formula::eq(
                    s.ap.apply(b.of(f.clone(), a), z.clone()),
                    s.ap.apply(f, d.syms.inj(j, z).expect("inj")),
                ),
            ),
            "the restriction at depth {j} does not compute to its own injection"
        );
        assert!(at.hyps().is_empty(), "the computation rule is unconditional");
    }
}

/// `⊢ ∀A⃗ ∀S ∀f. (f ∈ fs(Sum_3(A⃗), S) → f|₁ ∈ fs(A₁, S))` — the typing rule at
/// the shape every consumer holds, and it is a closed theorem.
#[test]
fn a_function_on_the_sum_restricts_to_a_function_on_the_summand() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let (n, j) = (3, 1);

    let th = d
        .syms
        .branch_in_funspace(&mut env, s, &d.app_mem, n, j)
        .expect("the restriction's typing rule");
    assert!(th.hyps().is_empty(), "the typing rule is unconditional");

    let b = d.syms.branch(&mut env, s, j).expect("the branch");
    let summands: Vec<Term> = (0..n).map(|_| Term::var(env.fresh_var())).collect();
    let (t_s, tf) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let mut args = summands.clone();
    args.push(t_s.clone());
    args.push(tf.clone());
    let at = inst_all(&th, &args).expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(tf.clone(), s.fs.of(d.syms.sum(&summands).expect("Sum_3"), t_s.clone())),
            Formula::mem(
                b.of(tf, summands[j].clone()),
                s.fs.of(summands[j].clone(), t_s),
            ),
        ),
    );
}

/// **Three summands, at three distinct variables.** The three restrictions of
/// one `f` are three different terms, each typed at *its own* summand and each
/// computing at *its own* injection. Two would not separate a depth that is
/// read once and reused.
#[test]
fn the_three_summands_are_told_apart() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    let n = 3;

    let summands: Vec<Term> = (0..n).map(|_| Term::var(env.fresh_var())).collect();
    let tf = Term::var(env.fresh_var());
    let branches: Vec<_> =
        (0..n).map(|j| d.syms.branch(&mut env, s, j).expect("the branch")).collect();
    let terms: Vec<Term> =
        (0..n).map(|j| branches[j].of(tf.clone(), summands[j].clone())).collect();

    for i in 0..n {
        for k in 0..n {
            assert_eq!(
                i == k,
                terms[i] == terms[k],
                "the restrictions at depths {i} and {k} are not distinguished"
            );
        }
    }

    // …and each computes at its own injection, never at another's.
    let z = Term::var(env.fresh_var());
    for j in 0..n {
        let at = inst_all(&branches[j].app, &[tf.clone(), summands[j].clone(), z.clone()])
            .expect("instantiate");
        let rhs = s.ap.apply(tf.clone(), d.syms.inj(j, z.clone()).expect("inj"));
        assert_eq!(
            *at.concl(),
            Formula::imp(
                Formula::mem(z.clone(), summands[j].clone()),
                Formula::eq(s.ap.apply(terms[j].clone(), z.clone()), rhs),
            ),
        );
    }
}

/// **The obligation this exists for.** `RecArg::general` packs `m` branch
/// functions `g⃗` into one dispatcher on `Sum_m(A⃗)`; the packed step of the
/// general recursor is defined at an arbitrary function on that sum and has to
/// hand Lean's minor premise the branch back. Restricting the dispatcher at
/// depth `j` does exactly that, pointwise:
///
/// ```text
/// {H, z ∈ Aⱼ} ⊢ app(recfun(g⃗)|ⱼ, z) = app(gⱼ, z)
/// ```
///
/// with `H` the dispatcher's own branch typings and **nothing else** in the
/// sequent — which is what makes `recfun(g⃗)|ⱼ = gⱼ` reachable by
/// `funspace_ext` at the point of use.
#[test]
fn the_restriction_recovers_the_branch_it_was_packed_from() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;

    let summands: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let ra = RecArg::general(
        &mut env,
        s,
        &d.cases,
        &d.syms,
        &d.ran,
        &d.fin,
        &d.wt.fs_mono,
        &d.wt.empty_fun,
        &summands,
    )
    .expect("the general recursive-argument function");
    let gs: Vec<Term> = ra.vars.iter().map(|v| Term::var(*v)).collect();
    let t_s = Term::var(ra.target);
    let h = ra.hyp.clone().expect("the general form carries a hypothesis");

    for j in 0..3 {
        let b = d.syms.branch(&mut env, s, j).expect("the branch");
        let z = Term::var(env.fresh_var());
        let mem_z = Formula::mem(z.clone(), summands[j].clone());

        // `app(recfun|ⱼ, z) = app(recfun, Injⱼ(z))`, on the domain.
        let restr = inst_all(&b.app, &[ra.fun.clone(), summands[j].clone(), z.clone()])
            .expect("instantiate");
        let left = Thm::mp(&restr, &Thm::assume(mem_z.clone())).expect("mp");

        // `app(recfun, Injⱼ(z)) = app(gⱼ, z)`, under `H` and on the domain.
        let mut args = vec![t_s.clone()];
        args.extend(gs.iter().cloned());
        args.push(z.clone());
        let beta = inst_all(&ra.app[j], &args).expect("instantiate");
        let right = Thm::mp(
            &Thm::mp(&beta, &Thm::assume(h.clone())).expect("mp"),
            &Thm::assume(mem_z.clone()),
        )
        .expect("mp");

        let chain = eq_trans(&mut env, &left, &right).expect("transitivity");
        assert_eq!(
            *chain.concl(),
            Formula::eq(
                s.ap.apply(b.of(ra.fun.clone(), summands[j].clone()), z.clone()),
                s.ap.apply(gs[j].clone(), z),
            ),
            "restricting the dispatcher at depth {j} did not give back branch {j}"
        );
        let mut hyps: Vec<Formula> = chain.hyps().to_vec();
        hyps.sort_by_key(|f| format!("{f:?}"));
        let mut want = vec![h.clone(), mem_z];
        want.sort_by_key(|f| format!("{f:?}"));
        assert_eq!(hyps, want, "the branch came back under an unexpected hypothesis");
    }
}

/// One symbol per **depth**, shared across arities and never minted twice —
/// the same discipline `Inj_i` is under, for the same reason: a second symbol
/// is a different restriction and nothing composes.
#[test]
fn the_restriction_symbol_is_cached_per_depth() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;

    let first = d.syms.branch(&mut env, s, 2).expect("the branch");
    let again = d.syms.branch(&mut env, s, 2).expect("the branch again");
    assert_eq!(first.graph, again.graph, "a second call minted a second symbol");
    assert_eq!(first.body, again.body);

    let other = d.syms.branch(&mut env, s, 0).expect("depth 0");
    assert_ne!(first.graph, other.graph, "two depths share one symbol");

    // The typing rule is keyed by the pair, and the *term* it speaks of is the
    // depth's one symbol whatever the arity.
    let at3 = d.syms.branch_in_funspace(&mut env, s, &d.app_mem, 3, 2).expect("n = 3");
    let at4 = d.syms.branch_in_funspace(&mut env, s, &d.app_mem, 4, 2).expect("n = 4");
    assert_ne!(at3.concl(), at4.concl(), "the typing rule must mention the arity");
}

/// The doors. A depth outside the sum, an arity the cache has not reached, and
/// an `app_mem` that is not the function-space application rule are each
/// refused rather than answered.
#[test]
fn the_restriction_refuses_what_it_cannot_state() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;

    assert!(
        d.syms.branch_in_funspace(&mut env, s, &d.app_mem, 3, 3).is_none(),
        "a depth outside the sum has no summand to restrict to"
    );
    assert!(
        d.syms.branch_in_funspace(&mut env, s, &d.app_mem, 9, 0).is_none(),
        "an arity beyond `ensure` has no `inj_mem` to spend"
    );
    assert!(d.syms.branch(&mut env, s, 9).is_none(), "a depth beyond `ensure` has no injection");

    // A theorem with the wrong conclusion is refused even though every step
    // below would happily `mp` against it.
    let bogus = Thm::assume(Formula::mem(s.point(), s.unit()));
    assert!(
        d.syms.branch_in_funspace(&mut env, s, &bogus, 3, 0).is_none(),
        "the typing rule accepted something that is not the application rule"
    );

    // …and so is a *hypothetical* application rule with the right conclusion:
    // `mp` unions the sequents in silence, and this file's header says `⊢`.
    let hypothetical = Thm::assume(d.app_mem.concl().clone());
    assert!(
        d.syms.branch_in_funspace(&mut env, s, &hypothetical, 2, 0).is_none(),
        "a hypothetical application rule rode into an unconditional theorem"
    );
}
