//! **Class (S) at an index** — the carrier `χ(p⃗,x⃗) = [tup(x⃗) ∈ acc(A_φ,R)]`.
//!
//! `derived/tests/family_le.rs` pins [`LeCarrier`] and stops at the *set*.
//! This file pins the **proposition** built over it: the symbol of arity
//! `np + ni`, its characteristic theorem, its typing in `U₀`, and the
//! constructor rule — plus the decline the recursive case gets.
//!
//! # The fixture that is `071`'s shape, and the one that is not
//!
//! [`spec_p3`] is `071`'s real shape: one parameter, **three** index slots, and
//! a constructor with **three plain fields permuted into them**, which is what
//! `SortElimProp.mk : ∀ b b1 b2. SortElimProp b b2 b1` is. That corner —
//! `kᵢ ≥ 1 ∧ ni ≥ 1` — is where `LeCarrier::build` declined outright until the
//! variable capture in its existential closure was fixed, and no fixture in
//! this repository reached it: [`spec_nullary2`] (which this file and
//! `family_le.rs` both used to call `spec_071`) has *no* fields, and every
//! other class-(S) witness has no *indices*. The two conditions the bug needed
//! were each covered and their conjunction was not.
//!
//! **Three slots, not two.** A two-field swap is its own reversal, so a build
//! that read the result spine backwards would pass a two-slot test. The
//! constructor's index image here is a **3-cycle** of three distinct tags, and
//! the three vectors it is separated from need descents of depth 0, 1 **and 2**
//! into the index tuple — a depth-2 descent is not expressible below `ni = 3`.
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
//!
//! # Three **constructors**, and why that is not the corpus's shape
//!
//! Every fixture above has exactly one constructor, and so does the only
//! class-(S)-at-an-index declaration the tutorials contain
//! (`SortElimProp.mk`). `le_index`'s `ctor_rule` is nevertheless indexed by
//! `i` in three places — the field count, `LeCarrier::intro[i]`, and the
//! result vector — and with one constructor a build that read **`0`** in all
//! three would be indistinguishable. It was: replacing `i` by `0` throughout
//! `ctor_rule` passed all six tests here before [`spec_three_ctors`] existed.
//!
//! `derived` is general in the constructor count — φ is a *disjunction* over
//! constructors ([`LeCarrier::phi_disjuncts`]) and `family_le_prop.rs` already
//! carries a three-constructor fixture at `ni = 0` — so this is a gap in the
//! coverage, not in the library. [`spec_three_ctors`] closes it at `ni ≥ 1`:
//! three constructors with **0, 1 and 2** plain fields and three pairwise
//! distinct result vectors, so a mis-read position is visible in the field
//! count *and* in the index image.
//!
//! **Three, not two**, and the reason is measured rather than assumed. `i ↦ 0`
//! and `i ↦ n−1−i` are both caught at two constructors, because every
//! non-identity permutation of two moves *both* of them. What two cannot see is
//! a **clamp**: `i ↦ min(i,1)` is the identity on `{0,1}` and is a real
//! mis-index at three. All five position mutations tried — the three `i` sites
//! separately, all three at once, the reversal — and the clamp fail exactly
//! this test and nothing else.
//!
//! Its negative polarity is the only place in this file where φ's disjunction
//! is *eliminated* rather than injected into: refuting one index vector needs
//! all three disjuncts refuted and combined, at 0, 1 and 2 existential
//! witnesses and at descents of depth 1, 0 and 0.

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
use derived::{
    a1i, and_intro, and_left, and_right, define_abbrev, disj_of, hyp_or_elim, iff_mp, imp_refl,
    inst_all, syl,
};

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
// No parameters, two `Bool` indices, one **nullary** constructor
// ─────────────────────────────────────────────────────────────────────────────

struct Nullary2 {
    spec: IndexedDeclSpec,
    /// `⊢ ι₀() = finord(2)` and `⊢ ∀x. ι₁(x) = finord(2)`.
    ity_ax: Vec<Thm>,
    /// `⊢ e₀() = Inj₀(•)`, `⊢ e₁() = Inj₀(•)`.
    res_ax: Vec<Thm>,
}

/// A declaration with two indices and **no constructor fields**.
///
/// This used to be called `spec_071` in this file and in `family_le.rs`, and it
/// is **not** `071`'s shape: `SortElimProp.mk : ∀ b b1 b2. SortElimProp b b2 b1`
/// has three plain fields going into two index slots, and this has none. The
/// name read as coverage of a corner it cannot reach — `kᵢ ≥ 1 ∧ ni ≥ 1`, where
/// `LeCarrier::build` declined outright until the capture bug in its
/// existential closure was fixed. [`spec_p3`] is `071`'s real shape; this one is
/// kept because the recursive/degenerate split is easiest to read without
/// fields in the way.
fn spec_nullary2(env: &mut Env, mach: &Machine, recs: usize) -> Nullary2 {
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
    Nullary2 {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(0, vec![CtorSpec::new(Vec::new(), recs)]),
            vec![i0, i1],
            vec![CtorIndices { result: vec![e0, e1], rec_args }],
        ),
        ity_ax: vec![i0_ax, i1_ax],
        res_ax: vec![e0_ax, e1_ax],
    }
}

/// `⊢ e_k() ∈ ι_k(…)`, the antecedent's `k`-th conjunct at [`spec_nullary2`].
fn index_typing_n2(env: &mut Env, mach: &Machine, le: &Nullary2, k: usize, res: &[Term]) -> Thm {
    let s = &mach.wt.sums;
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let ia: Vec<Term> = res[..k].to_vec();
    let set = Term::apply(le.spec.indices[k], ia.clone());
    let ity = inst_all(&le.ity_ax[k], &ia).expect("the index type unfolds");
    let base = inj_pt_mem(mach, 2, 0);
    let at_set = rw_back(env, &ity, |x| Formula::mem(ff.clone(), x), &base);
    rw_back(env, &le.res_ax[k], move |x| Formula::mem(x, set.clone()), &at_set)
}

/// `⊢ ¬(tup(bad) ∈ A_φ)` at [`spec_nullary2`], where `bad` differs from the
/// constructor's index vector in its **head** — one `pair_inj` and one
/// injection disjointness.
fn refute_nullary2(
    env: &mut Env,
    mach: &Machine,
    le: &Nullary2,
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
    let n2 = spec_nullary2(&mut env, &mach, 0);
    let spec = n2.spec.clone();
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
        (0..2).map(|k| index_typing_n2(&mut env, &mach, &n2, k, &res)).collect();
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
    let not_in_a = refute_nullary2(&mut env, &mach, &n2, &lc, &ix.idx, &bad, &res);
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
    let n2 = spec_nullary2(&mut env, &mach, 1);
    let spec = n2.spec.clone();
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
    let n2 = spec_nullary2(&mut env, &mach, 0);
    let spec = n2.spec.clone();
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

// ─────────────────────────────────────────────────────────────────────────────
// `071`'s real shape: one parameter, three indices, three plain fields
// permuted into the index slots
// ─────────────────────────────────────────────────────────────────────────────

/// The declaration
///
/// ```text
/// P3 (α : Type) : α → α → α → Prop
///   | mk : ∀ (a b c : Unit). P3 α (Inj₁ b) (Inj₂ c) (Inj₀ a)
/// ```
///
/// — `np = 1`, `ni = 3`, `kᵢ = 3`, the corner `LeCarrier::build` used to
/// decline. The result indices are a **3-cycle** of the fields, which is
/// `SortElimProp.mk : ∀ b b1 b2. SortElimProp b b2 b1`'s permutation with a
/// third slot added, and each slot carries a *different injection tag* so the
/// image is one concrete triple rather than the whole of `α³`. Bare-variable
/// indices over a full index type would be surjective and have no negative
/// polarity at all.
struct LeP3 {
    spec: IndexedDeclSpec,
    /// `⊢ ∀α ∀x⃗. ι_k(α, x⃗) = α`.
    ity_ax: Vec<Thm>,
    /// `⊢ ∀α ∀y⃗<ⱼ. β_j(α, y⃗<ⱼ) = 1`.
    arg_ax: Vec<Thm>,
    /// `⊢ ∀α∀a∀b∀c. e₀(α,a,b,c) = Inj₁(b)`, `… e₁ = Inj₂(c)`, `… e₂ = Inj₀(a)`.
    res_ax: Vec<Thm>,
}

/// Which field feeds slot `k`, and with which tag: slot 0 ← field 1 tagged 1,
/// slot 1 ← field 2 tagged 2, slot 2 ← field 0 tagged 0.
const CYCLE: [usize; 3] = [1, 2, 0];

fn spec_p3(env: &mut Env, mach: &Machine) -> LeP3 {
    let s = mach.wt.sums.clone();
    let one = s.unit();
    let (mut indices, mut ity_ax) = (Vec::new(), Vec::new());
    let (mut args, mut arg_ax) = (Vec::new(), Vec::new());
    let (mut result, mut res_ax) = (Vec::new(), Vec::new());
    for k in 0..3 {
        let (i, ax) = abbrev(env, 1 + k, |a| a[0].clone());
        indices.push(i);
        ity_ax.push(ax);
        let o = one.clone();
        let (b, bax) = abbrev(env, 1 + k, move |_| o.clone());
        args.push(b);
        arg_ax.push(bax);
    }
    for &j in &CYCLE {
        // `e_k(α, a, b, c) = Inj_{CYCLE[k]}(field CYCLE[k])`; the arguments are
        // the parameter followed by **all** the plain fields, so slot `k` picks
        // out `a[1 + CYCLE[k]]`.
        let tag = mach.syms.inj_sym(j).expect("Inj_j's symbol");
        let (e, eax) = abbrev(env, 4, move |a| Term::apply(tag, vec![a[1 + j].clone()]));
        result.push(e);
        res_ax.push(eax);
    }
    LeP3 {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(1, vec![CtorSpec::new(args, 0)]),
            indices,
            vec![CtorIndices::nonrecursive(result)],
        ),
        ity_ax,
        arg_ax,
        res_ax,
    }
}

/// **`071`'s shape, end to end.** The constructor rule fires at a declaration
/// with plain fields at an index, `χ` is `1` at exactly the index vector the
/// 3-cycle produces, and `0` at five others — including the cycle's **inverse**
/// and a vector separated only at depth 2 of the index tuple, neither of which
/// two index slots can express.
#[test]
fn a_constructor_with_permuted_fields_reaches_the_carrier() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let p3 = spec_p3(&mut env, &mach);
    let spec = p3.spec.clone();
    assert!(spec.well_formed());
    let s = mach.wt.sums.clone();
    let (one, pt) = (s.unit(), s.point());
    let three = mach.syms.finord(&s, 3).expect("finord(3)");

    let pv = env.fresh_var();
    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[Term::var(pv)]).expect("Idx");
    let lc = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[pv])
        .expect("a constructor with plain fields at an index has a carrier");
    let lic = LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[pv])
        .expect("…and a conditional singleton over it");

    // The fields are instantiated at `•`; the parameter at `finord(3)`.
    let ps = vec![three];
    let ys = vec![pt.clone(); 3];
    let mut args = ps.clone();
    args.extend(ys.iter().cloned());
    let img = spec.result_vec(0, &ps, &ys).expect("the result indices");
    let injs: Vec<Term> = (0..3).map(|k| mach.syms.inj(k, pt.clone()).expect("Inj_k")).collect();

    // ── the antecedent: three field typings, then three index typings ───────
    let mut atoms: Vec<Thm> = Vec::new();
    for j in 0..3 {
        let mut ia = ps.clone();
        ia.extend(ys[..j].iter().cloned());
        let unfold = inst_all(&p3.arg_ax[j], &ia).expect("β_j(α,…) = 1");
        atoms.push(rw_back(&mut env, &unfold, |x| Formula::mem(pt.clone(), x), &s.unit_mem));
    }
    for k in 0..3 {
        let mut ia = ps.clone();
        ia.extend(img[..k].iter().cloned());
        let set = Term::apply(spec.indices[k], ia.clone());
        let ity = inst_all(&p3.ity_ax[k], &ia).expect("ι_k(α,…) = α");
        let base = inj_pt_mem(&mach, 3, CYCLE[k]);
        let v = injs[CYCLE[k]].clone();
        let at_set = rw_back(&mut env, &ity, move |x| Formula::mem(v.clone(), x), &base);
        let e = inst_all(&p3.res_ax[k], &args).expect("e_k(α,a,b,c) = Inj_j(·)");
        atoms.push(rw_back(&mut env, &e, move |x| Formula::mem(x, set.clone()), &at_set));
    }
    let h_ok = conj(&atoms);

    // ── the constructor rule fires ──────────────────────────────────────────
    let ctors = lic.ctor_intro.as_ref().expect("non-recursive");
    assert_eq!(ctors[0].yvs.len(), 3, "one quantified variable per plain field");
    // The rule is stated at its own quantified variables; `result` and `at` are
    // the index vector and the carrier instance *there*.
    let yts: Vec<Term> = ctors[0].yvs.iter().map(|v| Term::var(*v)).collect();
    assert_eq!(
        ctors[0].result,
        spec.result_vec(0, &[Term::var(pv)], &yts).expect("e⃗ at the rule's variables")
    );
    assert_eq!(ctors[0].at, lic.at(&[Term::var(pv)], &ctors[0].result).expect("χ there"));

    let at_img = lic.at(&ps, &img).expect("χ at the image");
    let mem = Thm::mp(&inst_all(&ctors[0].mem, &args).expect("at α and the fields"), &h_ok)
        .expect("the typings discharge the antecedent");
    assert_eq!(*mem.concl(), Formula::mem(pt.clone(), at_img.clone()));
    assert!(closed(mem.concl()) && mem.hyps().is_empty());

    // ── `χ` at the image is `1`, spelled at the *unfolded* index vector ─────
    let deg = inst_all(&lc.degenerate.clone().expect("no recursion"), &ps).expect("the collapse");
    let in_a = Thm::mp(&inst_all(&lc.intro[0], &args).expect("A_φ-intro"), &h_ok).expect("mp");
    let img_tup = tup(&s, &img);
    let in_acc = rw_back(&mut env, &deg, |h| Formula::mem(img_tup.clone(), h), &in_a);
    let cond_img = lic.cond_at(&ps, &img).expect("the condition at the image");
    assert_eq!(*in_acc.concl(), cond_img);
    let mut is_one = Thm::mp(
        &cond_true(
            &mut env,
            &s,
            &cond_img,
            &at_img,
            &lic.chi_at(&ps, &img).expect("χ's axiom"),
        )
        .expect("cond_true"),
        &in_acc,
    )
    .expect("mp");

    // Unfold slot by slot. The conclusion this lands on is the whole
    // permutation pin: a build that read the result spine backwards, or that
    // dropped the fields out of the index terms, cannot reach it.
    let mut slots = img.clone();
    for k in 0..3 {
        let eq = inst_all(&p3.res_ax[k], &args).expect("e_k unfolds");
        let (cur, o, lic2, ps2) = (slots.clone(), one.clone(), &lic, ps.clone());
        is_one = rw(
            &mut env,
            &eq,
            move |h| {
                let mut a = cur.clone();
                a[k] = h;
                Formula::eq(lic2.at(&ps2, &a).expect("χ there"), o.clone())
            },
            &is_one,
        );
        slots[k] = injs[CYCLE[k]].clone();
    }
    let cycled = vec![injs[1].clone(), injs[2].clone(), injs[0].clone()];
    assert_eq!(slots, cycled);
    assert_eq!(
        *is_one.concl(),
        Formula::eq(lic.at(&ps, &cycled).expect("χ at the 3-cycle"), one.clone()),
        "the image is (Inj₁, Inj₂, Inj₀) — the 3-cycle, in that order"
    );
    assert!(closed(is_one.concl()) && is_one.hyps().is_empty());

    // The witnesses the refutations below eliminate. `refute_p3` pins the
    // φ-disjunct's own shape against `p3_matrix` on the way through, so the
    // equation's *fixed* left-hand side is checked once per bad vector.
    let wit: Vec<FreeVar> = (0..3).map(|_| env.fresh_var()).collect();

    // ── `χ = 0` at five vectors the 3-cycle does not reach ──────────────────
    //
    // | vector            | what it is                    | descent |
    // |-------------------|-------------------------------|---------|
    // | `(Inj₀,Inj₁,Inj₂)`| the identity order            | 0       |
    // | `(Inj₀,Inj₂,Inj₁)`| the image reversed            | 0       |
    // | `(Inj₂,Inj₀,Inj₁)`| the **inverse** 3-cycle       | 0       |
    // | `(Inj₁,Inj₀,Inj₂)`| agrees on the head            | 1       |
    // | `(Inj₁,Inj₂,Inj₁)`| agrees on the first two slots | 2       |
    //
    // Rows three and five are the ones two slots cannot express: a
    // transposition is its own inverse, so `σ ≠ σ⁻¹` needs a 3-cycle, and a
    // depth-2 descent into the tuple needs a third component to descend to.
    for (badv, depth, hi) in [
        (vec![injs[0].clone(), injs[1].clone(), injs[2].clone()], 0usize, 0usize),
        (vec![injs[0].clone(), injs[2].clone(), injs[1].clone()], 0usize, 0usize),
        (vec![injs[2].clone(), injs[0].clone(), injs[1].clone()], 0usize, 2usize),
        (vec![injs[1].clone(), injs[0].clone(), injs[2].clone()], 1usize, 0usize),
        (vec![injs[1].clone(), injs[2].clone(), injs[1].clone()], 2usize, 1usize),
    ] {
        let not_in_a = refute_p3(&mut env, &mach, &p3, &lc, &ix, &ps, &wit, &badv, depth, hi);
        let bad_tup = tup(&s, &badv);
        let not_in_acc = rw_back(
            &mut env,
            &deg,
            |h| Formula::not(Formula::mem(bad_tup.clone(), h)),
            &not_in_a,
        );
        let cond_bad = lic.cond_at(&ps, &badv).expect("the condition there");
        assert_eq!(*not_in_acc.concl(), Formula::not(cond_bad.clone()));
        let at_bad = lic.at(&ps, &badv).expect("χ there");
        let is_zero = Thm::mp(
            &cond_false(
                &mut env,
                &s,
                &cond_bad,
                &at_bad,
                &lic.chi_at(&ps, &badv).expect("χ's axiom"),
            )
            .expect("cond_false"),
            &not_in_acc,
        )
        .expect("mp");
        assert_eq!(*is_zero.concl(), Formula::eq(at_bad.clone(), s.zero()));

        let distinct = differ(&mut env, &s, &is_zero, &is_one);
        assert_eq!(
            *distinct.concl(),
            Formula::not(Formula::eq(at_bad, lic.at(&ps, &cycled).expect("χ at the image"))),
            "the 3-cycle's image and this vector denote different sets"
        );
        assert!(closed(distinct.concl()) && distinct.hyps().is_empty());
    }
}

/// `∃a∃b∃c. (a ∈ β₀(α) ∧ b ∈ β₁(α,a) ∧ c ∈ β₂(α,a,b) ∧ subj = tup(e⃗(α,a,b,c)))`
/// — the φ-disjunct of [`spec_p3`]'s one constructor, at a fixed subject.
fn p3_matrix(
    s: &Sums,
    spec: &IndexedDeclSpec,
    ps: &[Term],
    wit: &[FreeVar],
    subj: &Term,
) -> Formula {
    let ws: Vec<Term> = wit.iter().map(|v| Term::var(*v)).collect();
    let mut a: Vec<Formula> = (0..3)
        .map(|j| {
            let mut ia = ps.to_vec();
            ia.extend(ws[..j].iter().cloned());
            Formula::mem(ws[j].clone(), Term::apply(spec.base.ctors[0].args[j], ia))
        })
        .collect();
    a.push(Formula::eq(
        subj.clone(),
        tup(s, &spec.result_vec(0, ps, &ws).expect("the result indices")),
    ));
    let body = a
        .iter()
        .rev()
        .skip(1)
        .fold(a.last().expect("non-empty").clone(), |acc, x| {
            Formula::and(x.clone(), acc)
        });
    wit.iter().rev().fold(body, |acc, v| Formula::exists(*v, acc))
}

/// `⊢ ¬(tup(bad) ∈ A_φ(α))` at [`spec_p3`]: eliminate the constructor's three
/// field witnesses, descend `depth` tails into the tuple equation, and refute
/// the head with the injections' disjointness.
#[allow(clippy::too_many_arguments)]
fn refute_p3(
    env: &mut Env,
    mach: &Machine,
    p3: &LeP3,
    lc: &LeCarrier,
    ix: &IndexSpace,
    ps: &[Term],
    wit: &[FreeVar],
    bad: &[Term],
    depth: usize,
    hi: usize,
) -> Thm {
    let s = mach.wt.sums.clone();
    let spec = &p3.spec;
    let bad_tup = tup(&s, bad);
    let ws: Vec<Term> = wit.iter().map(|v| Term::var(*v)).collect();
    let mut wargs = ps.to_vec();
    wargs.extend(ws.iter().cloned());
    let img = spec.result_vec(0, ps, &ws).expect("the result indices at the witnesses");

    // `⊢ tup(bad) ∈ A_φ(α) → ∃a∃b∃c. (…)`.
    let mut a = ps.to_vec();
    a.push(bad_tup.clone());
    let at = inst_all(&lc.phi_ax, &a).expect("A_φ's axiom");
    let mem_idx = Formula::mem(bad_tup.clone(), ix.telescope.ty_of(ps.to_vec()));
    let matrix = p3_matrix(&s, spec, ps, wit, &bad_tup);
    assert_eq!(
        *at.concl(),
        Formula::iff(
            Formula::mem(bad_tup.clone(), Term::apply(lc.phi, ps.to_vec())),
            Formula::and(mem_idx.clone(), matrix.clone())
        )
    );
    let to_matrix =
        syl(&iff_mp(&at).expect("forward"), &and_right(mem_idx, matrix)).expect("the matrix");

    // Under the three witnesses: project the equation and descend.
    let mut atoms: Vec<Formula> = (0..3)
        .map(|j| {
            let mut ia = ps.to_vec();
            ia.extend(ws[..j].iter().cloned());
            Formula::mem(ws[j].clone(), Term::apply(spec.base.ctors[0].args[j], ia))
        })
        .collect();
    atoms.push(Formula::eq(bad_tup, tup(&s, &img)));
    let mut acc = derived::conj_proj(&atoms, 3).expect("the equation");
    for d in 0..=depth {
        let (lh, lt) = (bad[d].clone(), tup(&s, &bad[d + 1..]));
        let (rh, rt) = (img[d].clone(), tup(&s, &img[d + 1..]));
        let inj = inst_all(&s.ap.pair_inj, &[lh.clone(), lt.clone(), rh.clone(), rt.clone()])
            .expect("pair injectivity");
        let split = syl(&acc, &inj).expect("syl");
        let (heads, tails) = (Formula::eq(lh, rh), Formula::eq(lt, rt));
        acc = if d == depth {
            syl(&split, &and_left(heads, tails)).expect("the head equality")
        } else {
            syl(&split, &and_right(heads, tails)).expect("the tail equality")
        };
    }

    // `e_depth(α,a,b,c) = Inj_{CYCLE[depth]}(w)`, so the head equality is
    // between two *differently tagged* injections whatever the witness is.
    let lo = CYCLE[depth];
    let head = bad[depth].clone();
    let e = inst_all(&p3.res_ax[depth], &wargs).expect("e_k unfolds");
    let refuted = rw_h(env, &e, move |h| Formula::eq(head.clone(), h), &acc);
    let ne = mach.syms.inj_distinct(env, &s, hi, lo).expect("the injections are disjoint");
    let mut branch = syl(
        &refuted,
        &inst_all(&ne, &[s.point(), ws[lo].clone()]).expect("at the witness"),
    )
    .expect("⊥");

    // Discharge the witnesses, innermost first.
    for j in (0..3).rev() {
        branch = derived::exists_elim_imp(wit[j], &Thm::gen(wit[j], &branch), &Formula::false_())
            .expect("the witness is not free in ⊥");
    }
    syl(&to_matrix, &branch).expect("¬(tup(bad) ∈ A_φ)")
}

// ─────────────────────────────────────────────────────────────────────────────
// Three constructors, two indices — the constructor **position**
// ─────────────────────────────────────────────────────────────────────────────

/// `TAGS[i]` is `cᵢ`'s result index vector, as injection tags; `i` is also its
/// plain-field count. Pairwise distinct, and `c₀`'s two slots agree, so the
/// refutation below descends into the tuple on one disjunct and not on the
/// other two.
const TAGS: [[usize; 2]; 3] = [[0, 0], [1, 2], [2, 1]];

/// ```text
/// Q : finord(3) → finord(3) → Prop
///   | c₀ :                 Q (Inj₀ •) (Inj₀ •)
///   | c₁ : (a : 1) →       Q (Inj₁ •) (Inj₂ •)
///   | c₂ : (a b : 1) →     Q (Inj₂ •) (Inj₁ •)
/// ```
///
/// `np = 0`, `ni = 2`, `kᵢ = i`. The parameter count is `0` on purpose: the
/// parameter spine is pinned by [`spec_three`] and [`spec_p3`], and what is
/// under test here is only the position `i`.
struct Le3C {
    spec: IndexedDeclSpec,
    /// `⊢ ∀x⃗<k. ι_k(x⃗<k) = finord(3)`.
    ity_ax: Vec<Thm>,
    /// `⊢ ∀y⃗<ⱼ. β_{i,j}(y⃗<ⱼ) = 1`.
    arg_ax: Vec<Vec<Thm>>,
    /// `⊢ ∀y⃗ᵢ. e_{i,k}(y⃗ᵢ) = Inj_{TAGS[i][k]}(•)`.
    res_ax: Vec<Vec<Thm>>,
}

fn spec_three_ctors(env: &mut Env, mach: &Machine) -> Le3C {
    let s = mach.wt.sums.clone();
    let one = s.unit();
    let three = mach.syms.finord(&s, 3).expect("finord(3)");
    let (mut indices, mut ity_ax) = (Vec::new(), Vec::new());
    for k in 0..2 {
        let t = three.clone();
        let (i, ax) = abbrev(env, k, move |_| t.clone());
        indices.push(i);
        ity_ax.push(ax);
    }
    let (mut ctors, mut cix) = (Vec::new(), Vec::new());
    let (mut arg_ax, mut res_ax) = (Vec::new(), Vec::new());
    for (i, tags) in TAGS.iter().enumerate() {
        let (mut args, mut axs) = (Vec::new(), Vec::new());
        for j in 0..i {
            let o = one.clone();
            let (b, bax) = abbrev(env, j, move |_| o.clone());
            args.push(b);
            axs.push(bax);
        }
        let (mut result, mut raxs) = (Vec::new(), Vec::new());
        for &t in tags {
            let v = mach.syms.inj(t, s.point()).expect("Inj_t");
            let (e, eax) = abbrev(env, i, move |_| v.clone());
            result.push(e);
            raxs.push(eax);
        }
        ctors.push(CtorSpec::new(args, 0));
        cix.push(CtorIndices::nonrecursive(result));
        arg_ax.push(axs);
        res_ax.push(raxs);
    }
    Le3C {
        spec: IndexedDeclSpec::new(DeclSpec::new(0, ctors), indices, cix),
        ity_ax,
        arg_ax,
        res_ax,
    }
}

/// φ's `i`-th disjunct at [`spec_three_ctors`], at a fixed subject:
/// `∃y⃗ᵢ. (⋀ⱼ yⱼ ∈ β_{i,j}(y⃗<ⱼ) ∧ subj = tup(e⃗ᵢ(y⃗ᵢ)))`, and the atom list it
/// is a conjunction of. Rebuilt here rather than read off `lc`, so the
/// assertion against [`LeCarrier::phi_disjuncts`] below is a real comparison.
fn q_disjunct(
    s: &Sums,
    spec: &IndexedDeclSpec,
    wit: &[FreeVar],
    i: usize,
    subj: &Term,
) -> (Vec<Formula>, Formula) {
    let ws: Vec<Term> = wit[..i].iter().map(|v| Term::var(*v)).collect();
    let mut atoms: Vec<Formula> = (0..i)
        .map(|j| Formula::mem(ws[j].clone(), Term::apply(spec.base.ctors[i].args[j], ws[..j].to_vec())))
        .collect();
    atoms.push(Formula::eq(
        subj.clone(),
        tup(s, &spec.result_vec(i, &[], &ws).expect("the result indices")),
    ));
    let body = atoms
        .iter()
        .rev()
        .skip(1)
        .fold(atoms.last().expect("non-empty").clone(), |acc, x| {
            Formula::and(x.clone(), acc)
        });
    (atoms, wit[..i].iter().rev().fold(body, |acc, v| Formula::exists(*v, acc)))
}

/// `⊢ Dᵢ → ⊥` — the `i`-th disjunct refuted at `bad`, which differs from `cᵢ`'s
/// result vector at slot `depth`.
#[allow(clippy::too_many_arguments)]
fn refute_q(
    env: &mut Env,
    mach: &Machine,
    q: &Le3C,
    wit: &[FreeVar],
    bad_tags: &[usize],
    i: usize,
    depth: usize,
) -> Thm {
    let s = mach.wt.sums.clone();
    let bad: Vec<Term> =
        bad_tags.iter().map(|&t| mach.syms.inj(t, s.point()).expect("Inj_t")).collect();
    let bad_tup = tup(&s, &bad);
    let ws: Vec<Term> = wit[..i].iter().map(|v| Term::var(*v)).collect();
    let img = q.spec.result_vec(i, &[], &ws).expect("the result indices at the witnesses");
    let (atoms, _) = q_disjunct(&s, &q.spec, wit, i, &bad_tup);

    // The equation is the last atom; descend `depth` tails, then the head.
    let mut acc = derived::conj_proj(&atoms, i).expect("the equation");
    for d in 0..=depth {
        let (lh, lt) = (bad[d].clone(), tup(&s, &bad[d + 1..]));
        let (rh, rt) = (img[d].clone(), tup(&s, &img[d + 1..]));
        let inj = inst_all(&s.ap.pair_inj, &[lh.clone(), lt.clone(), rh.clone(), rt.clone()])
            .expect("pair injectivity");
        let split = syl(&acc, &inj).expect("syl");
        let (heads, tails) = (Formula::eq(lh, rh), Formula::eq(lt, rt));
        acc = if d == depth {
            syl(&split, &and_left(heads, tails)).expect("the head equality")
        } else {
            syl(&split, &and_right(heads, tails)).expect("the tail equality")
        };
    }

    let head = bad[depth].clone();
    let e = inst_all(&q.res_ax[i][depth], &ws).expect("e_{i,k} unfolds");
    let refuted = rw_h(env, &e, move |h| Formula::eq(head.clone(), h), &acc);
    let ne = mach
        .syms
        .inj_distinct(env, &s, bad_tags[depth], TAGS[i][depth])
        .expect("the injections are disjoint");
    let mut branch =
        syl(&refuted, &inst_all(&ne, &[s.point(), s.point()]).expect("at •")).expect("⊥");

    for j in (0..i).rev() {
        branch = derived::exists_elim_imp(wit[j], &Thm::gen(wit[j], &branch), &Formula::false_())
            .expect("the witness is not free in ⊥");
    }
    branch
}

/// `(Inj₀ •, Inj₁ •)` — reached by no constructor: it agrees with `c₀` in the
/// head and with none of the three in both slots.
const BAD_TAGS: [usize; 2] = [0, 1];

/// Fold `⊢ D₀ → ⊥`, … into `⊢ (D₀ ∨ (D₁ ∨ D₂)) → ⊥`.
///
/// Right-nested, matching [`disj_of`]: at each step the disjunction is its own
/// hypothesis, the head's refutation discharges the left case and the tail's
/// the right.
fn refute_disj(disjuncts: &[Formula], parts: &[Thm]) -> Thm {
    let n = disjuncts.len();
    let mut acc = parts[n - 1].clone();
    for i in (0..n - 1).rev() {
        let d = disj_of(&disjuncts[i..]).expect("non-empty");
        acc = hyp_or_elim(&imp_refl(d.clone()), &a1i(&parts[i], d.clone()), &a1i(&acc, d))
            .expect("case analysis");
    }
    acc
}

/// **The constructor position.** Three constructors with different field
/// counts and different result vectors: each rule is stated at its *own*
/// constructor, `χ` is `1` at each of the three index vectors, and `0` at one
/// no constructor reaches — which is where φ's disjunction is eliminated.
#[test]
fn each_constructor_gets_its_own_rule() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let q = spec_three_ctors(&mut env, &mach);
    let spec = q.spec.clone();
    assert!(spec.well_formed());
    let s = mach.wt.sums.clone();
    let (one, pt) = (s.unit(), s.point());

    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("Idx");
    let lc = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[]).expect("the (S) carrier");
    let lic = LeIndexCarrier::build(&mut env, &mach, &f.tow, &f.ac, &spec, &lc, &[])
        .expect("the carrier at an index");
    let deg = lc.degenerate.clone().expect("no recursion");
    let injs: Vec<Term> = (0..3).map(|k| mach.syms.inj(k, pt.clone()).expect("Inj_k")).collect();

    let ctors = lic.ctor_intro.as_ref().expect("non-recursive, so the rules are offered");
    assert_eq!(ctors.len(), 3, "one rule per constructor");

    // ── each rule is its own constructor's ───────────────────────────────────
    let mut ones: Vec<Thm> = Vec::new();
    let mut images: Vec<Vec<Term>> = Vec::new();
    for i in 0..3 {
        assert_eq!(ctors[i].index, i);
        assert_eq!(ctors[i].yvs.len(), i, "cᵢ takes exactly i plain fields");
        let yts: Vec<Term> = ctors[i].yvs.iter().map(|v| Term::var(*v)).collect();
        assert_eq!(
            ctors[i].result,
            spec.result_vec(i, &[], &yts).expect("e⃗ᵢ at the rule's own variables"),
            "rule {i} is stated at constructor {i}'s result vector"
        );

        // Fire it at `y⃗ = •⃗`: i field typings, then two index typings.
        let ys = vec![pt.clone(); i];
        let img = spec.result_vec(i, &[], &ys).expect("the result indices");
        let mut atoms: Vec<Thm> = (0..i)
            .map(|j| {
                let unfold =
                    inst_all(&q.arg_ax[i][j], &ys[..j]).expect("β_{i,j}(…) = 1");
                rw_back(&mut env, &unfold, |x| Formula::mem(pt.clone(), x), &s.unit_mem)
            })
            .collect();
        for k in 0..2 {
            let set = Term::apply(spec.indices[k], img[..k].to_vec());
            let ity = inst_all(&q.ity_ax[k], &img[..k]).expect("ι_k(…) = finord(3)");
            let base = inj_pt_mem(&mach, 3, TAGS[i][k]);
            let v = injs[TAGS[i][k]].clone();
            let at_set = rw_back(&mut env, &ity, move |x| Formula::mem(v.clone(), x), &base);
            let e = inst_all(&q.res_ax[i][k], &ys).expect("e_{i,k} unfolds");
            atoms.push(rw_back(&mut env, &e, move |x| Formula::mem(x, set.clone()), &at_set));
        }
        let h_ok = conj(&atoms);

        let at_img = lic.at(&[], &img).expect("χ at cᵢ's image");
        let mem = Thm::mp(&inst_all(&ctors[i].mem, &ys).expect("at the fields"), &h_ok)
            .expect("the typings discharge the antecedent");
        assert_eq!(*mem.concl(), Formula::mem(pt.clone(), at_img.clone()));
        assert!(closed(mem.concl()) && mem.hyps().is_empty());

        // …and as an equation, through this constructor's own `A_φ`-intro.
        let in_a = Thm::mp(&inst_all(&lc.intro[i], &ys).expect("A_φ-intro"), &h_ok).expect("mp");
        let img_tup = tup(&s, &img);
        let in_acc = rw_back(&mut env, &deg, |h| Formula::mem(img_tup.clone(), h), &in_a);
        let cond_img = lic.cond_at(&[], &img).expect("the condition at the image");
        assert_eq!(*in_acc.concl(), cond_img);
        let is_one = Thm::mp(
            &cond_true(&mut env, &s, &cond_img, &at_img, &lic.chi_at(&[], &img).expect("χ's axiom"))
                .expect("cond_true"),
            &in_acc,
        )
        .expect("mp");
        assert_eq!(*is_one.concl(), Formula::eq(at_img.clone(), one.clone()));
        assert!(closed(is_one.concl()) && is_one.hyps().is_empty());
        ones.push(is_one);
        images.push(img);
    }

    // The three images are pairwise different terms — without that, "each rule
    // is its own" would be vacuous.
    for i in 0..3 {
        for j in 0..i {
            assert_ne!(images[i], images[j], "cᵢ and cⱼ land at different indices");
        }
    }

    // ── the negative polarity, which eliminates φ's disjunction ──────────────
    let wit: Vec<FreeVar> = (0..2).map(|_| env.fresh_var()).collect();
    let bad: Vec<Term> = BAD_TAGS.iter().map(|&t| injs[t].clone()).collect();
    let bad_tup = tup(&s, &bad);

    // The disjuncts, rebuilt and pinned against the carrier's own.
    let disjuncts: Vec<Formula> = (0..3)
        .map(|i| q_disjunct(&s, &spec, &wit, i, &Term::var(lc.phi_subject)).1)
        .collect();
    assert_eq!(
        disjuncts, lc.phi_disjuncts,
        "the refutation is about the disjuncts the carrier actually carved"
    );

    // `c₀` agrees with `bad` in the *head*, so its refutation descends one
    // tail; `c₁` and `c₂` do not, and are refuted at depth 0.
    let parts: Vec<Thm> = [1usize, 0, 0]
        .iter()
        .enumerate()
        .map(|(i, &d)| refute_q(&mut env, &mach, &q, &wit, &BAD_TAGS, i, d))
        .collect();
    for (i, p) in parts.iter().enumerate() {
        assert_eq!(
            *p.concl(),
            Formula::imp(
                q_disjunct(&s, &spec, &wit, i, &bad_tup).1,
                Formula::false_()
            )
        );
    }

    let at_bad = lic.at(&[], &bad).expect("χ at the unreachable vector");
    let matrix: Vec<Formula> =
        (0..3).map(|i| q_disjunct(&s, &spec, &wit, i, &bad_tup).1).collect();
    let no_disj = refute_disj(&matrix, &parts);
    let mem_idx = Formula::mem(bad_tup.clone(), ix.telescope.ty_of(Vec::new()));
    let at = inst_all(&lc.phi_ax, std::slice::from_ref(&bad_tup)).expect("A_φ's axiom");
    let whole = disj_of(&matrix).expect("three disjuncts");
    assert_eq!(
        *at.concl(),
        Formula::iff(
            Formula::mem(bad_tup.clone(), lc.a_phi.clone()),
            Formula::and(mem_idx.clone(), whole.clone())
        )
    );
    let to_matrix =
        syl(&iff_mp(&at).expect("forward"), &and_right(mem_idx, whole)).expect("the matrix");
    let not_in_a = syl(&to_matrix, &no_disj).expect("¬(tup(bad) ∈ A_φ)");

    let not_in_acc = rw_back(
        &mut env,
        &deg,
        |h| Formula::not(Formula::mem(bad_tup.clone(), h)),
        &not_in_a,
    );
    let cond_bad = lic.cond_at(&[], &bad).expect("the condition there");
    assert_eq!(*not_in_acc.concl(), Formula::not(cond_bad.clone()));
    let is_zero = Thm::mp(
        &cond_false(&mut env, &s, &cond_bad, &at_bad, &lic.chi_at(&[], &bad).expect("χ's axiom"))
            .expect("cond_false"),
        &not_in_acc,
    )
    .expect("mp");
    assert_eq!(*is_zero.concl(), Formula::eq(at_bad.clone(), s.zero()));

    // …and it is a different set from each of the three images.
    for (i, is_one) in ones.iter().enumerate() {
        let distinct = differ(&mut env, &s, &is_zero, is_one);
        assert_eq!(
            *distinct.concl(),
            Formula::not(Formula::eq(
                at_bad.clone(),
                lic.at(&[], &images[i]).expect("χ at cᵢ's image")
            ))
        );
        assert!(closed(distinct.concl()) && distinct.hyps().is_empty());
    }
}
