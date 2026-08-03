//! **Class (S) at an index** — the carrier `χ(p⃗,x⃗) = [tup(x⃗) ∈ acc(A_φ,R)]`.
//!
//! `derived/tests/family_le.rs` pins [`LeCarrier`] on `071_SortElimProp`'s
//! shape and stops at the *set*. This file pins the **proposition** built over
//! it: the symbol of arity `np + ni`, its characteristic theorem, its typing in
//! `U₀`, and the constructor rule — plus the decline the recursive case gets.
//!
//! # What each test would let through if it were weaker
//!
//! A conditional singleton is a subset of `{•}`, so a construction returning
//! the constant `1` and one returning the constant `0` each satisfy every
//! *membership* theorem the other cannot. Both polarities are therefore pinned
//! as **equations at concrete sets** — `χ = 1` where the constructor lands,
//! `χ = 0` where it does not — and `⊢ ¬(0 = 1)` turns the pair into "these are
//! different sets".
//!
//! The permutation test uses **three** indices with three *distinct* values,
//! and that is not decoration. `tup(x⃗)` is a right-nested pair, so refuting
//! `tup(x⃗) = tup(e⃗)` at a permutation that already agrees on the first
//! component requires descending into the tail. With two indices no
//! permutation of distinct values agrees on the head, the second descent is
//! never exercised, and a construction that dropped every component after the
//! first would pass.
//!
//! Everything reaches the carrier through [`LeIndexCarrier::at`],
//! [`LeIndexCarrier::chi_at`] and [`LeIndexCarrier::cond_at`] at **concrete
//! index terms**, never at the module's own fresh variables: that is what a
//! checker holds, and an interface reachable only at `x⃗` would be no interface.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::acc::Acc;
use derived::bound::Bound;
use derived::inductive::family::{
    CtorIndices, IndexSpace, IndexedDeclSpec, LeCarrier, LeIndexCarrier,
};
use derived::inductive::{CtorSpec, DeclSpec, Machine};
use derived::prop::{cond_false, cond_true};
use derived::sums::Sums;
use derived::tower::Tower;
use derived::wtype::Wtype;
use derived::{and_intro, and_left, and_right, define_abbrev, iff_mp, inst_all, syl};

fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

fn abbrev(env: &mut Env, arity: usize, body: impl Fn(&[Term]) -> Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = body(&args);
    define_abbrev(env, &vars, &t).expect("an abbreviation")
}

/// `⊢ Injⱼ(•) ∈ finord(m)`.
fn inj_pt_mem(mach: &Machine, m: usize, j: usize) -> Thm {
    let s = &mach.wt.sums;
    let mut args = vec![s.unit(); m];
    args.push(s.point());
    Thm::mp(
        &inst_all(mach.syms.inj_mem(m, j).expect("inj_mem"), &args).expect("instantiate"),
        &s.unit_mem,
    )
    .expect("mp")
}

/// From `⊢ x = y` and `⊢ φ(x)` infer `⊢ φ(y)`.
fn rw(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), base).expect("mp")
}

/// From `⊢ y = x` and `⊢ φ(x)` infer `⊢ φ(y)`.
fn rw_back(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let back = derived::eq_symm(env, eq).expect("symm");
    rw(env, &back, ctx, base)
}

/// From `⊢ x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
fn rw_h(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    syl(base, &Thm::mp(&leib, eq).expect("mp")).expect("syl")
}

/// `tup(x⃗)`.
fn tup(s: &Sums, xs: &[Term]) -> Term { IndexedDeclSpec::tup(s, xs) }

/// Fold `⊢ φ₀ … ⊢ φₙ` into `⊢ φ₀ ∧ (φ₁ ∧ …)`, matching `conj_of`'s nesting.
fn conj(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = and_intro(t, &acc);
    }
    acc
}

/// From `⊢ a = 0` and `⊢ b = 1` infer `⊢ ¬(a = b)`, through `⊢ ¬(0 = 1)`.
///
/// This is the step that makes the two polarities *bite*: the memberships
/// alone are satisfied by a carrier that is constantly `1`, the equations at
/// two concrete and provably different sets are not.
fn differ(env: &mut Env, s: &Sums, is_zero: &Thm, is_one: &Thm) -> Thm {
    let a = is_zero.concl().as_eq().expect("an equation").0;
    let one = s.unit();
    let step = rw_back(env, is_zero, move |h| Formula::not(Formula::eq(h, one.clone())), &s.tags_distinct);
    rw_back(env, is_one, move |h| Formula::not(Formula::eq(a.clone(), h)), &step)
}

// ─────────────────────────────────────────────────────────────────────────────
// The apparatus — one `Sums`, shared by the tower, the machine and `acc`
// ─────────────────────────────────────────────────────────────────────────────

struct Fix {
    tow: Tower,
    mach: Machine,
    ac: Acc,
}

/// `Tower::new` mints the signature; the W-type, the bound and `acc` all join
/// it. Without the sharing, `cond_in_u0`'s `1` is not the `1` the carrier is a
/// subset of, and every shape check inside the build refuses.
fn fixture(env: &mut Env) -> Fix {
    let tow = Tower::new(env).expect("tower");
    let wt = Wtype::over(env, tow.sums.clone()).expect("W-type over the same sums");
    let bnd =
        Bound::over(env, &wt, tow.space.lu, tow.space.lu_ax.clone()).expect("bound over U(·)");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 3).expect("three summands");
    let ac = Acc::with_apply(env, &sums.ap).expect("acc over the same pairing");
    Fix { tow, mach, ac }
}

// ─────────────────────────────────────────────────────────────────────────────
// `071`'s shape: no parameters, two `Bool` indices, one nullary constructor
// ─────────────────────────────────────────────────────────────────────────────

struct Le071 {
    spec: IndexedDeclSpec,
    /// `⊢ ι₀() = finord(2)` and `⊢ ∀x. ι₁(x) = finord(2)`.
    ity_ax: Vec<Thm>,
    /// `⊢ e₀() = Inj₀(•)`, `⊢ e₁() = Inj₀(•)`.
    res_ax: Vec<Thm>,
}

/// The fixture `family_le.rs` already exercises [`LeCarrier`] at, inherited so
/// that the two files pin the same declaration.
fn spec_071(env: &mut Env, mach: &Machine, recs: usize) -> Le071 {
    let s = &mach.wt.sums;
    let boolean = mach.syms.finord(s, 2).expect("finord(2)");
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let (i0, i0_ax) = abbrev(env, 0, |_| boolean.clone());
    let (i1, i1_ax) = abbrev(env, 1, |_| boolean.clone());
    let (e0, e0_ax) = abbrev(env, 0, |_| ff.clone());
    let (e1, e1_ax) = abbrev(env, 0, |_| ff.clone());
    let (d0, _) = abbrev(env, 0, |_| ff.clone());
    let (d1, _) = abbrev(env, 0, |_| ff.clone());
    let rec_args = if recs == 0 { Vec::new() } else { vec![vec![d0, d1]] };
    Le071 {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(0, vec![CtorSpec::new(Vec::new(), recs)]),
            vec![i0, i1],
            vec![CtorIndices { result: vec![e0, e1], rec_args }],
        ),
        ity_ax: vec![i0_ax, i1_ax],
        res_ax: vec![e0_ax, e1_ax],
    }
}

/// `⊢ e_k() ∈ ι_k(…)`, the antecedent's `k`-th conjunct at `071`.
fn index_typing_071(env: &mut Env, mach: &Machine, le: &Le071, k: usize, res: &[Term]) -> Thm {
    let s = &mach.wt.sums;
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let ia: Vec<Term> = res[..k].to_vec();
    let set = Term::apply(le.spec.indices[k], ia.clone());
    let ity = inst_all(&le.ity_ax[k], &ia).expect("the index type unfolds");
    let base = inj_pt_mem(mach, 2, 0);
    let at_set = rw_back(env, &ity, |x| Formula::mem(ff.clone(), x), &base);
    rw_back(env, &le.res_ax[k], move |x| Formula::mem(x, set.clone()), &at_set)
}

/// `⊢ ¬(tup(bad) ∈ A_φ)` at `071`, where `bad` differs from the constructor's
/// index vector in its **head** — one `pair_inj` and one injection
/// disjointness.
fn refute_071(
    env: &mut Env,
    mach: &Machine,
    le: &Le071,
    lc: &LeCarrier,
    idx: &Term,
    bad: &[Term],
    res: &[Term],
) -> Thm {
    let s = mach.wt.sums.clone();
    let bad_tup = tup(&s, bad);
    let at = inst_all(&lc.phi_ax, std::slice::from_ref(&bad_tup)).expect("A_φ's axiom");
    let mem_idx = Formula::mem(bad_tup.clone(), idx.clone());
    let matrix = Formula::eq(bad_tup.clone(), tup(&s, res));
    assert_eq!(
        *at.concl(),
        Formula::iff(
            Formula::mem(bad_tup, lc.a_phi.clone()),
            Formula::and(mem_idx.clone(), matrix.clone())
        ),
        "φ's matrix at a nullary constructor is the base-case equality alone"
    );
    let eq = syl(&iff_mp(&at).expect("forward"), &and_right(mem_idx, matrix)).expect("the matrix");

    let tail_l = s.ap.sets.pair(bad[1].clone(), s.point());
    let tail_r = s.ap.sets.pair(res[1].clone(), s.point());
    let inj = inst_all(
        &s.ap.pair_inj,
        &[bad[0].clone(), tail_l.clone(), res[0].clone(), tail_r.clone()],
    )
    .expect("pair injectivity");
    let heads = syl(
        &syl(&eq, &inj).expect("syl"),
        &and_left(
            Formula::eq(bad[0].clone(), res[0].clone()),
            Formula::eq(tail_l, tail_r),
        ),
    )
    .expect("the head equality");
    let head = bad[0].clone();
    let unfolded = rw_h(env, &le.res_ax[0], move |h| Formula::eq(head.clone(), h), &heads);
    let ne = mach.syms.inj_distinct(env, &s, 1, 0).expect("Inj₁ ≠ Inj₀");
    syl(&unfolded, &inst_all(&ne, &[s.point(), s.point()]).expect("at •")).expect("⊥")
}

// ─────────────────────────────────────────────────────────────────────────────

/// The whole interface at the degenerate case, and both polarities as
/// equations at concrete sets.
#[test]
fn the_class_s_carrier_at_an_index_is_a_conditional_singleton() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let le071 = spec_071(&mut env, &mach, 0);
    let spec = le071.spec.clone();
    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("the index space");
    let lc = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[]).expect("the (S) carrier");
    let lic = LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[])
        .expect("the carrier at an index");
    let s = mach.wt.sums.clone();
    let (one, pt) = (s.unit(), s.point());

    // ── χ is a conditional singleton at `tup(x⃗) ∈ acc(A_φ,R)` ──────────────
    assert_eq!(lic.xvs.len(), 2, "one index variable per index");
    assert_eq!(lic.acc, lc.acc_set, "the condition is about `acc`, not about `A_φ`");
    let xs: Vec<Term> = lic.xvs.iter().map(|v| Term::var(*v)).collect();
    assert_eq!(lic.tuple, tup(&s, &xs));
    assert_eq!(lic.cond, Formula::mem(lic.tuple.clone(), lc.acc_set.clone()));
    assert_eq!(lic.carrier, lic.at(&[], &xs).expect("χ at its own variables"));

    let zv = env.fresh_var();
    let tz = Term::var(zv);
    assert_eq!(
        *lic.chi_at_params.concl(),
        Formula::forall(
            zv,
            Formula::iff(
                Formula::mem(tz.clone(), lic.carrier.clone()),
                Formula::and(Formula::mem(tz, one.clone()), lic.cond.clone())
            )
        )
    );
    assert!(lic.all_unconditional());

    // ── the constructor rule, discharged into a closed theorem ──────────────
    let ctors = lic.ctor_intro.as_ref().expect("no recursion, so the rule is offered");
    assert_eq!(ctors.len(), 1);
    let res = spec.result_vec(0, &[], &[]).expect("the result indices");
    assert_eq!(ctors[0].result, res);
    assert_eq!(ctors[0].at, lic.at(&[], &res).expect("χ at the constructor's index"));

    let atoms: Vec<Thm> =
        (0..2).map(|k| index_typing_071(&mut env, &mach, &le071, k, &res)).collect();
    let e_ok = conj(&atoms);
    let mem = Thm::mp(&ctors[0].mem, &e_ok).expect("the index typings discharge it");
    assert_eq!(*mem.concl(), Formula::mem(pt.clone(), ctors[0].at.clone()));
    assert!(closed(mem.concl()) && mem.hyps().is_empty());

    // ── the typing, at the constructor's index and unconditionally ──────────
    let in_u0 = inst_all(&lic.in_u0, &res).expect("`in_u0` at concrete indices");
    assert_eq!(*in_u0.concl(), Formula::mem(ctors[0].at.clone(), f.tow.u0()));
    assert!(closed(in_u0.concl()) && in_u0.hyps().is_empty());

    // ── positive polarity, as an equation: `χ(e⃗) = 1` ───────────────────────
    let deg = lc.degenerate.clone().expect("R is empty");
    let in_a = Thm::mp(&lc.intro[0], &e_ok).expect("tup(e⃗) ∈ A_φ");
    let tup_res = tup(&s, &res);
    let in_acc = rw_back(&mut env, &deg, |h| Formula::mem(tup_res.clone(), h), &in_a);
    let cond_res = lic.cond_at(&[], &res).expect("the condition at e⃗");
    assert_eq!(*in_acc.concl(), cond_res);
    let is_one = Thm::mp(
        &cond_true(
            &mut env,
            &s,
            &cond_res,
            &ctors[0].at,
            &lic.chi_at(&[], &res).expect("χ's axiom at e⃗"),
        )
        .expect("cond_true"),
        &in_acc,
    )
    .expect("mp");
    assert_eq!(*is_one.concl(), Formula::eq(ctors[0].at.clone(), one.clone()));
    assert!(closed(is_one.concl()) && is_one.hyps().is_empty());

    // ── negative polarity, as an equation: `χ(tt,ff) = 0` ────────────────────
    let tt = mach.syms.inj(1, s.point()).expect("Inj₁");
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let bad = vec![tt, ff];
    let not_in_a = refute_071(&mut env, &mach, &le071, &lc, &ix.idx, &bad, &res);
    let bad_tup = tup(&s, &bad);
    let not_in_acc = rw_back(
        &mut env,
        &deg,
        |h| Formula::not(Formula::mem(bad_tup.clone(), h)),
        &not_in_a,
    );
    let cond_bad = lic.cond_at(&[], &bad).expect("the condition at (tt,ff)");
    assert_eq!(*not_in_acc.concl(), Formula::not(cond_bad.clone()));
    let at_bad = lic.at(&[], &bad).expect("χ at (tt,ff)");
    let is_zero = Thm::mp(
        &cond_false(
            &mut env,
            &s,
            &cond_bad,
            &at_bad,
            &lic.chi_at(&[], &bad).expect("χ's axiom at (tt,ff)"),
        )
        .expect("cond_false"),
        &not_in_acc,
    )
    .expect("mp");
    assert_eq!(*is_zero.concl(), Formula::eq(at_bad.clone(), s.zero()));

    // ── and the two are *different sets*, which is what rules out `χ ≡ 1` ───
    let distinct = differ(&mut env, &s, &is_zero, &is_one);
    assert_eq!(*distinct.concl(), Formula::not(Formula::eq(at_bad, ctors[0].at.clone())));
    assert!(closed(distinct.concl()) && distinct.hyps().is_empty());
}

/// A **recursive** class-(S) declaration: the carrier is still minted at every
/// index, and the constructor rule is declined **by name** rather than offered
/// as an empty list.
#[test]
fn a_recursive_declaration_gets_the_carrier_and_no_constructor_rule() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let le071 = spec_071(&mut env, &mach, 1);
    let spec = le071.spec.clone();
    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("the index space");
    let lc = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[]).expect("the (S) carrier");
    assert!(lc.degenerate.is_none(), "a recursive declaration has a non-empty R");
    let lic = LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[])
        .expect("the carrier at an index is built anyway");

    // The decline, and it is distinguishable from "no constructors".
    assert!(
        lic.ctor_intro.is_none(),
        "the recursive introduction rule needs `Acc::acc_intro`'s universally \
         quantified premise and a `rel_ax` inversion; neither is built"
    );

    // Everything that does not depend on the collapse is still there, and is
    // still about `acc(A_φ,R)` — *not* about `A_φ`, which is what a relaxed
    // version of the degenerate argument would silently give.
    let s = mach.wt.sums.clone();
    assert_eq!(lic.acc, f.ac.of(lc.a_phi.clone(), lc.r.clone()));
    assert_ne!(lic.acc, lc.a_phi);
    assert_eq!(lic.cond, Formula::mem(lic.tuple.clone(), lic.acc.clone()));
    assert!(lic.all_unconditional());

    // `elim` escapes to the accessibility, which is the direction that would be
    // wrong if the carrier had been built over `A_φ`.
    let xs: Vec<Term> = lic.xvs.iter().map(|v| Term::var(*v)).collect();
    let elim = inst_all(&lic.elim, &xs).expect("elim at the index variables");
    assert_eq!(
        *elim.concl(),
        Formula::imp(
            Formula::mem(s.point(), lic.carrier.clone()),
            Formula::mem(tup(&s, &xs), lic.acc.clone())
        )
    );

    // …and the typing is unconditional whatever the accessibility is.
    let in_u0 = inst_all(&lic.in_u0, &xs).expect("in_u0 at the index variables");
    assert_eq!(*in_u0.concl(), Formula::mem(lic.carrier.clone(), f.tow.u0()));
    assert!(in_u0.hyps().is_empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// Three indices, three distinct values, one parameter
// ─────────────────────────────────────────────────────────────────────────────

struct Le3 {
    spec: IndexedDeclSpec,
    /// `⊢ ∀p ∀x⃗. ι_k(p, x⃗) = p` — the index type *is* the parameter, so the
    /// parameter is load-bearing rather than a dead argument.
    ity_ax: Vec<Thm>,
    /// `⊢ ∀p. e_k(p) = Inj_k(•)` — three **different** injections.
    res_ax: Vec<Thm>,
}

fn spec_three(env: &mut Env, mach: &Machine) -> Le3 {
    let s = &mach.wt.sums;
    let (mut indices, mut ity_ax, mut result, mut res_ax) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for k in 0..3 {
        let (i, ax) = abbrev(env, 1 + k, |a| a[0].clone());
        indices.push(i);
        ity_ax.push(ax);
        let v = mach.syms.inj(k, s.point()).expect("Inj_k");
        let (e, eax) = abbrev(env, 1, move |_| v.clone());
        result.push(e);
        res_ax.push(eax);
    }
    Le3 {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(1, vec![CtorSpec::new(Vec::new(), 0)]),
            indices,
            vec![CtorIndices::nonrecursive(result)],
        ),
        ity_ax,
        res_ax,
    }
}

/// `⊢ ¬(tup(perm) ∈ A_φ(p⃗))`, descending `depth` tails into the tuple before
/// projecting the head and refuting `Inj_hi(•) = Inj_lo(•)`.
#[allow(clippy::too_many_arguments)]
fn refute_three(
    env: &mut Env,
    mach: &Machine,
    le: &Le3,
    lc: &LeCarrier,
    ix: &IndexSpace,
    ps: &[Term],
    perm: &[Term],
    res: &[Term],
    depth: usize,
    hi: usize,
    lo: usize,
) -> Thm {
    let s = mach.wt.sums.clone();
    let perm_tup = tup(&s, perm);
    let mut a = ps.to_vec();
    a.push(perm_tup.clone());
    let at = inst_all(&lc.phi_ax, &a).expect("A_φ's axiom");
    // `A_φ` and `Idx` are both at the *instantiated* parameter, not at the
    // declaration's own variable — which is the whole point of `np = 1` here.
    let mem_idx = Formula::mem(perm_tup.clone(), ix.telescope.ty_of(ps.to_vec()));
    let matrix = Formula::eq(perm_tup.clone(), tup(&s, res));
    assert_eq!(
        *at.concl(),
        Formula::iff(
            Formula::mem(perm_tup, Term::apply(lc.phi, ps.to_vec())),
            Formula::and(mem_idx.clone(), matrix.clone())
        ),
        "φ's matrix at a nullary constructor is the base-case equality alone"
    );
    let mut acc =
        syl(&iff_mp(&at).expect("forward"), &and_right(mem_idx, matrix)).expect("the matrix");

    // Peel `depth` tails, then the head.
    for d in 0..=depth {
        let (lh, lt) = (perm[d].clone(), tup(&s, &perm[d + 1..]));
        let (rh, rt) = (res[d].clone(), tup(&s, &res[d + 1..]));
        assert_eq!(tup(&s, &perm[d..]), s.ap.sets.pair(lh.clone(), lt.clone()));
        assert_eq!(tup(&s, &res[d..]), s.ap.sets.pair(rh.clone(), rt.clone()));
        let inj = inst_all(&s.ap.pair_inj, &[lh.clone(), lt.clone(), rh.clone(), rt.clone()])
            .expect("pair injectivity");
        let split = syl(&acc, &inj).expect("syl");
        let heads = Formula::eq(lh, rh);
        let tails = Formula::eq(lt, rt);
        acc = if d == depth {
            syl(&split, &and_left(heads, tails)).expect("the head equality")
        } else {
            syl(&split, &and_right(heads, tails)).expect("the tail equality")
        };
    }

    let head = perm[depth].clone();
    let e = inst_all(&le.res_ax[depth], ps).expect("e_k(p) = Inj_k(•)");
    let unfolded = rw_h(env, &e, move |h| Formula::eq(head.clone(), h), &acc);
    let ne = mach.syms.inj_distinct(env, &s, hi, lo).expect("the injections are disjoint");
    syl(&unfolded, &inst_all(&ne, &[s.point(), s.point()]).expect("at •")).expect("⊥")
}

/// **Order and nesting.** `χ` is `1` at the constructor's index vector and `0`
/// at two different permutations of it — one that moves the head, one that
/// leaves the head alone and moves the tail. The second is what a two-index
/// fixture cannot ask for.
#[test]
fn the_carrier_separates_permuted_index_vectors() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let le3 = spec_three(&mut env, &mach);
    let spec = le3.spec.clone();
    assert!(spec.well_formed());
    let pv = env.fresh_var();
    let s = mach.wt.sums.clone();
    let three = mach.syms.finord(&s, 3).expect("finord(3)");

    let ix =
        IndexSpace::build(&mut env, &mut mach, &spec, &[Term::var(pv)]).expect("the index space");
    let lc = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[pv]).expect("the (S) carrier");
    let lic = LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[pv])
        .expect("the carrier at an index");
    assert_eq!(lic.xvs.len(), 3);

    // The parameter comes first in χ's argument list, and it is *used*: the
    // index types are the parameter itself, so instantiating it at `finord(3)`
    // is what makes the typings dischargeable.
    let ps = vec![three];
    let res = spec.result_vec(0, &ps, &[]).expect("the result indices");
    let injs: Vec<Term> = (0..3).map(|k| mach.syms.inj(k, s.point()).expect("Inj_k")).collect();

    // ── `χ(finord(3), e⃗) = 1` ───────────────────────────────────────────────
    let atoms: Vec<Thm> = (0..3)
        .map(|k| {
            let mut ia = ps.clone();
            ia.extend(res[..k].iter().cloned());
            let set = Term::apply(spec.indices[k], ia.clone());
            let ity = inst_all(&le3.ity_ax[k], &ia).expect("ι_k(p,…) = p");
            let base = inj_pt_mem(&mach, 3, k);
            let v = injs[k].clone();
            let at_set = rw_back(&mut env, &ity, move |x| Formula::mem(v.clone(), x), &base);
            let e = inst_all(&le3.res_ax[k], &ps).expect("e_k(p) = Inj_k(•)");
            rw_back(&mut env, &e, move |x| Formula::mem(x, set.clone()), &at_set)
        })
        .collect();
    let e_ok = conj(&atoms);

    let ctors = lic.ctor_intro.as_ref().expect("non-recursive, so the rule is offered");
    let mem = Thm::mp(
        &inst_all(&ctors[0].mem, &ps).expect("the rule at finord(3)"),
        &e_ok,
    )
    .expect("the index typings discharge it");
    let at_res = lic.at(&ps, &res).expect("χ(finord(3), e⃗)");
    assert_eq!(*mem.concl(), Formula::mem(s.point(), at_res.clone()));
    assert!(closed(mem.concl()) && mem.hyps().is_empty());

    let deg = inst_all(&lc.degenerate.clone().expect("R is empty"), &ps).expect("the collapse");
    let in_a = Thm::mp(&inst_all(&lc.intro[0], &ps).expect("A_φ-intro"), &e_ok).expect("mp");
    let tup_res = tup(&s, &res);
    let in_acc = rw_back(&mut env, &deg, |h| Formula::mem(tup_res.clone(), h), &in_a);
    let cond_res = lic.cond_at(&ps, &res).expect("the condition at e⃗");
    assert_eq!(*in_acc.concl(), cond_res);
    let is_one = Thm::mp(
        &cond_true(&mut env, &s, &cond_res, &at_res, &lic.chi_at(&ps, &res).expect("χ's axiom"))
            .expect("cond_true"),
        &in_acc,
    )
    .expect("mp");
    assert_eq!(*is_one.concl(), Formula::eq(at_res.clone(), s.unit()));

    // ── the two permutations ─────────────────────────────────────────────────
    // `(Inj₁, Inj₀, Inj₂)` moves the head; `(Inj₀, Inj₂, Inj₁)` agrees on the
    // head and moves the tail, so refuting it needs a *second* `pair_inj`.
    for (perm, depth, hi, lo) in [
        (vec![injs[1].clone(), injs[0].clone(), injs[2].clone()], 0usize, 1usize, 0usize),
        (vec![injs[0].clone(), injs[2].clone(), injs[1].clone()], 1usize, 2usize, 1usize),
    ] {
        let not_in_a =
            refute_three(&mut env, &mach, &le3, &lc, &ix, &ps, &perm, &res, depth, hi, lo);
        let perm_tup = tup(&s, &perm);
        let not_in_acc = rw_back(
            &mut env,
            &deg,
            |h| Formula::not(Formula::mem(perm_tup.clone(), h)),
            &not_in_a,
        );
        let cond_bad = lic.cond_at(&ps, &perm).expect("the condition at the permutation");
        assert_eq!(*not_in_acc.concl(), Formula::not(cond_bad.clone()));
        let at_bad = lic.at(&ps, &perm).expect("χ at the permutation");
        let is_zero = Thm::mp(
            &cond_false(
                &mut env,
                &s,
                &cond_bad,
                &at_bad,
                &lic.chi_at(&ps, &perm).expect("χ's axiom"),
            )
            .expect("cond_false"),
            &not_in_acc,
        )
        .expect("mp");
        assert_eq!(*is_zero.concl(), Formula::eq(at_bad.clone(), s.zero()));
        assert!(closed(is_zero.concl()) && is_zero.hyps().is_empty());

        let distinct = differ(&mut env, &s, &is_zero, &is_one);
        assert_eq!(
            *distinct.concl(),
            Formula::not(Formula::eq(at_bad, at_res.clone())),
            "the permutation and the constructor's index denote different sets"
        );
    }

    // The typing holds at a permutation too — it is unconditional.
    let mut ia = ps.clone();
    ia.extend(injs.iter().cloned());
    let in_u0 = inst_all(&lic.in_u0, &ia).expect("in_u0 at concrete indices");
    assert_eq!(*in_u0.concl(), Formula::mem(lic.at(&ps, &injs).expect("χ there"), f.tow.u0()));
    assert!(closed(in_u0.concl()) && in_u0.hyps().is_empty());
}

/// A declaration with **no indices** is declined: there is nothing to mint,
/// because `Idx(p⃗) = 1` makes `A_φ` a conditional singleton already and
/// `le_prop` says so without a second Separation.
///
/// The constructor takes a **field**, deliberately. At a nullary constructor of
/// a non-indexed declaration `LeCarrier::intro` is the *unconditional*
/// `⊢ ∀p⃗. • ∈ A_φ(p⃗)`, so the build would decline on the missing implication
/// and the guard under test would never be reached — the decline would be an
/// accident of the fixture rather than the rule.
#[test]
fn a_non_indexed_declaration_is_declined() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let one = mach.wt.sums.unit();
    let (beta, _) = abbrev(&mut env, 0, move |_| one.clone());
    let spec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::new(vec![beta], 0)]),
        Vec::new(),
        vec![CtorIndices::nonrecursive(Vec::new())],
    );
    assert!(spec.well_formed());
    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("the one-point index space");
    assert!(ix.point().is_some(), "`ni = 0` is `le_prop`'s case, and it is reachable");
    let lc = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[]).expect("the (S) carrier");
    assert!(
        LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[]).is_none(),
        "minting a symbol here would duplicate the one `le_prop` describes"
    );
}

/// **The consumer half of the hypothesis discipline.** A `Γ ⊢ φ` has the
/// conclusion the real theorem has and rides through `mp` with `Γ` intact, so a
/// hypothetical [`LeCarrier`] theorem would arrive at a statement this module
/// advertises as unconditional. Every theorem read out of `lc` is checked, not
/// just shape-matched.
#[test]
fn a_hypothetical_carrier_theorem_is_refused() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let le071 = spec_071(&mut env, &mach, 0);
    let spec = le071.spec.clone();
    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("the index space");
    let mut lc =
        LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[]).expect("the (S) carrier");
    assert!(LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[]).is_some());

    // Same conclusion, one hypothesis.
    lc.intro[0] = Thm::assume(lc.intro[0].concl().clone());
    assert!(
        LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[]).is_none(),
        "a hypothetical introduction rule must not become an unconditional χ-rule"
    );
}
