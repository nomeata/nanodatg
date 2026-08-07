//! **Class (S)** — the §5.3 route, at the only shape the tutorial corpus asks
//! for it in.
//!
//! `071_SortElimProp` is `P : Bool → Bool → Bool → Prop` with a single
//! **non-recursive** constructor, so its `LE ctor` recursion emits an empty
//! edge relation, `R` is provably empty, and `acc(A_φ, R)` collapses to `A_φ` —
//! a conditional singleton, which is what class (S) requires at every
//! instantiation. That collapse is [`LeCarrier::degenerate`], and it is the
//! whole of the corpus demand (`INDEXED-DESIGN.md` §6.2).
//!
//! Both polarities again: `A_φ` contains the constructor's own index tuple and
//! **provably does not contain** another one. A `φ` that came out `⊤` would
//! satisfy the first and fail the second.
//!
//! The recursive case — the one that needs `R ≠ ∅` and the full accessibility
//! argument — has no witness in the 91 files. Its carrier is built here anyway;
//! what the last test pins is that the degenerate corollary is **not** offered
//! for it, since it would be false.
//!
//! # The fieldless witness, and what it used to hide
//!
//! [`spec_nullary2`] — called `spec_071` until it was measured — drops `071`'s
//! constructor fields. Losing the *delayed elimination* of
//! `thesis.txt:1856–1858` with them is deliberate: that is a wiring question,
//! which Lean binder lands in which minor slot, and is not built here.
//!
//! **"What is kept is everything the carrier depends on" is what this header
//! used to say, and it was false.** Dropping the fields drops the only shape in
//! which the constructor's result index terms *mention* them, and
//! [`LeCarrier::build`]'s existential closure captured exactly those variables:
//! at `kᵢ ≥ 1 ∧ ni ≥ 1` it built `∃y⃗. (… ∧ tup(e⃗(y⃗)) = tup(e⃗(y⃗)))`, a
//! reflexivity rather than an instance, and declined. Both conditions were
//! covered separately — `And` and `PUnit` have fields and no indices, this
//! fixture has indices and no fields — and their conjunction was covered
//! nowhere, so a fixture named for `071` certified a corner `071` is *made of*.
//! [`a_constructor_with_fields_at_an_index_carves_a_proper_subset`] is that
//! corner; `family_le_index.rs` carries it end to end at three permuted slots.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::acc::Acc;
use derived::bound::Bound;
use derived::inductive::family::{CtorIndices, IndexSpace, IndexedDeclSpec, LeCarrier};
use derived::inductive::{CtorSpec, DeclSpec, Machine};
use derived::sums::Sums;
use derived::wtype::Wtype;
use derived::{and_intro, and_left, and_right, iff_mp, inst_all, syl};

fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

fn abbrev(env: &mut Env, arity: usize, body: impl Fn(&[Term]) -> Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = body(&args);
    derived::define_abbrev(env, &vars, &t).expect("an abbreviation")
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

struct Fix {
    mach: Machine,
    ac: Acc,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 2).expect("two summands");
    let ac = Acc::with_apply(env, &sums.ap).expect("acc over the same pairing");
    Fix { mach, ac }
}

/// A parameterless subsingleton family over two `Bool` indices with **one
/// nullary constructor** at `(ff, ff)`.
///
/// Not `071`'s shape — see the header for what the missing fields cost.
struct Nullary2 {
    spec: IndexedDeclSpec,
    /// `⊢ ι₀() = finord(2)` and `⊢ ∀x. ι₁(x) = finord(2)`.
    ity_ax: Vec<Thm>,
    /// `⊢ e₀() = Inj₀(•)`, `⊢ e₁() = Inj₀(•)`.
    res_ax: Vec<Thm>,
    /// The same for the (single) recursive argument's indices, when there is
    /// one.
    rec_ax: Vec<Thm>,
}

fn spec_nullary2(env: &mut Env, mach: &Machine, recs: usize) -> Nullary2 {
    let s = &mach.wt.sums;
    let boolean = mach.syms.finord(s, 2).expect("finord(2)");
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let (i0, i0_ax) = abbrev(env, 0, |_| boolean.clone());
    let (i1, i1_ax) = abbrev(env, 1, |_| boolean.clone());
    let (e0, e0_ax) = abbrev(env, 0, |_| ff.clone());
    let (e1, e1_ax) = abbrev(env, 0, |_| ff.clone());
    let (d0, d0_ax) = abbrev(env, 0, |_| ff.clone());
    let (d1, d1_ax) = abbrev(env, 0, |_| ff.clone());
    let rec_args = if recs == 0 { Vec::new() } else { vec![vec![d0, d1]] };
    Nullary2 {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(0, vec![CtorSpec::new(Vec::new(), recs)]),
            vec![i0, i1],
            vec![CtorIndices { result: vec![e0, e1], rec_args }],
        ),
        ity_ax: vec![i0_ax, i1_ax],
        res_ax: vec![e0_ax, e1_ax],
        rec_ax: vec![d0_ax, d1_ax],
    }
}

/// `tup(x⃗)`.
fn tup(s: &Sums, xs: &[Term]) -> Term { IndexedDeclSpec::tup(s, xs) }

/// The degenerate class-(S) carrier: `A_φ`, an empty `R`, the collapse, and
/// both polarities of membership.
#[test]
fn the_non_recursive_subsingleton_collapses_to_its_domain() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let n2 = spec_nullary2(&mut env, &mach, 0);
    let spec = n2.spec.clone();
    assert!(spec.well_formed());
    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("the index space");
    let le = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[]).expect("the (S) carrier");
    let s = mach.wt.sums.clone();
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let tt = mach.syms.inj(1, s.point()).expect("Inj₁");
    let res = spec.result_vec(0, &[], &[]).expect("the result indices");

    // ── the collapse: `R` has no members, so `acc(A_φ,R) = A_φ` ─────────────
    let deg = le.degenerate.clone().expect("no recursive argument, so R is empty");
    assert_eq!(*deg.concl(), Formula::eq(le.acc_set.clone(), le.a_phi.clone()));
    assert!(closed(deg.concl()) && deg.hyps().is_empty());
    assert_eq!(le.acc_set, f.ac.of(le.a_phi.clone(), le.r.clone()));

    // ── positive: the constructor's own index tuple is in `A_φ` ─────────────
    let mut atoms = Vec::new();
    for k in 0..2 {
        let mut ia = Vec::new();
        ia.extend(res[..k].iter().cloned());
        let set = Term::apply(spec.indices[k], ia.clone());
        let ity = inst_all(&n2.ity_ax[k], &ia).expect("the index type unfolds");
        let base = inj_pt_mem(&mach, 2, 0);
        let at_set = rw_back(&mut env, &ity, |x| Formula::mem(ff.clone(), x), &base);
        let s2 = set.clone();
        atoms.push(rw_back(
            &mut env,
            &n2.res_ax[k],
            move |x| Formula::mem(x, s2.clone()),
            &at_set,
        ));
    }
    let intro = Thm::mp(&le.intro[0], &and_intro(&atoms[0], &atoms[1])).expect("(A_φ-intro)");
    assert_eq!(*intro.concl(), Formula::mem(tup(&s, &res), le.a_phi.clone()));
    assert!(closed(intro.concl()) && intro.hyps().is_empty());

    // …and hence in `acc(A_φ, R)`, by the collapse.
    let in_acc =
        rw_back(&mut env, &deg, |hole| Formula::mem(tup(&s, &res), hole), &intro);
    assert_eq!(*in_acc.concl(), Formula::mem(tup(&s, &res), le.acc_set.clone()));
    assert!(in_acc.hyps().is_empty());

    // ── negative: `(tt, ff)` is not in `A_φ` ────────────────────────────────
    let bad = tup(&s, &[tt.clone(), ff.clone()]);
    let at = inst_all(&le.phi_ax, std::slice::from_ref(&bad)).expect("A_φ's axiom");
    let mem_idx = Formula::mem(bad.clone(), ix.idx.clone());
    let matrix = Formula::eq(bad.clone(), tup(&s, &res));
    assert_eq!(
        *at.concl(),
        Formula::iff(
            Formula::mem(bad.clone(), le.a_phi.clone()),
            Formula::and(mem_idx.clone(), matrix.clone())
        ),
        "φ's matrix at a nullary constructor is the base-case equality alone"
    );
    let eq = syl(&iff_mp(&at).expect("forward"), &and_right(mem_idx, matrix))
        .expect("the matrix");

    // Split the tuple, unfold `e₀`, and refute the head.
    let tail_l = s.ap.sets.pair(ff.clone(), s.point());
    let tail_r = s.ap.sets.pair(res[1].clone(), s.point());
    let inj = inst_all(
        &s.ap.pair_inj,
        &[tt.clone(), tail_l.clone(), res[0].clone(), tail_r.clone()],
    )
    .expect("pair injectivity");
    let heads = syl(
        &syl(&eq, &inj).expect("syl"),
        &and_left(
            Formula::eq(tt.clone(), res[0].clone()),
            Formula::eq(tail_l, tail_r),
        ),
    )
    .expect("the head equality");
    let tt_c = tt.clone();
    let unfolded = rw_h(
        &mut env,
        &n2.res_ax[0],
        move |hole| Formula::eq(tt_c.clone(), hole),
        &heads,
    );
    let ne = mach.syms.inj_distinct(&mut env, &s, 1, 0).expect("Inj₁ ≠ Inj₀");
    let out = syl(&unfolded, &inst_all(&ne, &[s.point(), s.point()]).expect("at •"))
        .expect("⊥");
    assert_eq!(*out.concl(), Formula::not(Formula::mem(bad, le.a_phi.clone())));
    assert!(closed(out.concl()) && out.hyps().is_empty());
}

/// A **recursive** class-(S) declaration gets no collapse: `R` is not provably
/// empty, and offering `acc(A_φ,R) = A_φ` there would be offering something
/// false. The carrier itself is still built — the formula recursion costs
/// nothing extra — but its recursor is deliberately deferred, per the standing
/// decline-and-count rule.
#[test]
fn a_recursive_subsingleton_gets_no_collapse() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let n2 = spec_nullary2(&mut env, &mach, 1);
    let spec = n2.spec.clone();
    assert!(spec.well_formed());
    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("the index space");
    let le = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[]).expect("the (S) carrier");
    assert!(le.degenerate.is_none(), "a recursive declaration has a non-empty R");
    assert_ne!(le.r, le.a_phi);
    assert_eq!(le.acc_set, f.ac.of(le.a_phi.clone(), le.r.clone()));

    // The edge relation is a real Separation over `Idx × Idx`, and it really
    // contains the constructor's own edge `⟨tup(d⃗), tup(e⃗)⟩` — so a `R` that
    // came out empty (which would make the collapse silently true) is ruled
    // out here, not merely not offered.
    let s = mach.wt.sums.clone();
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let res = spec.result_vec(0, &[], &[]).expect("result indices");
    let child = spec.rec_index_vec(0, 0, &[], &[]).expect("child indices");
    let edge = f.ac.edge(tup(&s, &child), tup(&s, &res));

    let in_idx = |env: &mut Env, xs: &[Term], unfold: &[Thm]| -> Thm {
        let mut atoms = Vec::new();
        for k in 0..2 {
            let ia: Vec<Term> = xs[..k].to_vec();
            let set = Term::apply(spec.indices[k], ia.clone());
            let ity = inst_all(&n2.ity_ax[k], &ia).expect("the index type unfolds");
            let base = inj_pt_mem(&mach, 2, 0);
            let at_set = rw_back(env, &ity, |x| Formula::mem(ff.clone(), x), &base);
            let s2 = set.clone();
            atoms.push(rw_back(env, &unfold[k], move |x| Formula::mem(x, s2.clone()), &at_set));
        }
        Thm::mp(
            &inst_all(ix.intro(), xs).expect("the telescope's intro"),
            &and_intro(&atoms[0], &atoms[1]),
        )
        .expect("tup(x⃗) ∈ Idx")
    };

    let at = inst_all(&le.rel_ax, std::slice::from_ref(&edge)).expect("R's axiom");
    assert_eq!(
        *at.concl(),
        Formula::iff(
            Formula::mem(edge.clone(), le.r.clone()),
            Formula::and(
                Formula::mem(edge.clone(), s.prod.of(ix.idx.clone(), ix.idx.clone())),
                Formula::eq(edge.clone(), edge.clone()),
            )
        ),
        "the edge matrix at a fieldless constructor is its own base equality"
    );
    let in_prod = derived::iff_mpr(
        &inst_all(
            &s.pair_in_prod,
            &[
                ix.idx.clone(),
                ix.idx.clone(),
                tup(&s, &child),
                tup(&s, &res),
            ],
        )
        .expect("pair in product"),
    )
    .expect("mpr");
    let child_in = in_idx(&mut env, &child, &n2.rec_ax);
    let res_in = in_idx(&mut env, &res, &n2.res_ax);
    let edge_mem = Thm::mp(
        &derived::iff_mpr(&at).expect("mpr"),
        &and_intro(
            &Thm::mp(&in_prod, &and_intro(&child_in, &res_in)).expect("mp"),
            &Thm::eq_refl(edge.clone()),
        ),
    )
    .expect("the edge is in R");
    assert_eq!(*edge_mem.concl(), Formula::mem(edge, le.r.clone()));
    assert!(closed(edge_mem.concl()) && edge_mem.hyps().is_empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// Plain fields **at an index** — the corner the fieldless fixture cannot reach
// ─────────────────────────────────────────────────────────────────────────────

/// **The regression for the capture in the existential closure.**
///
/// `LeCarrier::build` declined every declaration with `kᵢ ≥ 1 ∧ ni ≥ 1` — a
/// constructor with plain fields at an index, which is `071` and every family
/// like it. `tup(e⃗ᵢ(p⃗,y⃗))` mentions the field variables, and the closure
/// substituted it into the disjunct *before* wrapping the `∃yⱼ`, so the binders
/// abstracted the left-hand side too.
///
/// The build succeeding is half the pin. The other half is that `A_φ` is a
/// **proper** subset of the index space: had the captured reading been let
/// through, each φ-disjunct would have been `∃y⃗. (typings ∧ t = t)` — provable
/// for every `q`, so `A_φ = Idx(p⃗)` and nothing is excluded. `¬(bad ∈ A_φ)` is
/// the statement that the reflexivity is not what got built.
///
/// Two fields, so the closure's mixed step (`y⃗` already discharged, `w⃗` still
/// witnesses) runs at least once; the *slot permutation* is pinned at three
/// slots in `family_le_index.rs`, which is where it belongs.
#[test]
fn a_constructor_with_fields_at_an_index_carves_a_proper_subset() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let (one, pt) = (s.unit(), s.point());
    let two = mach.syms.finord(&s, 2).expect("finord(2)");
    let injs: Vec<Term> = (0..2).map(|k| mach.syms.inj(k, pt.clone()).expect("Inj_k")).collect();

    // `Q : Bool → Bool → Prop | mk : ∀ (a b : Unit). Q (Inj₁ b) (Inj₀ a)` — the
    // fields **swap** into the index slots, and each slot carries a different
    // tag so the image is one concrete pair rather than all of `Bool²`.
    let mut ity_ax = Vec::new();
    let mut arg_ax = Vec::new();
    let (mut indices, mut args, mut result, mut res_ax) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for k in 0..2 {
        let b = two.clone();
        let (i, ax) = abbrev(&mut env, k, move |_| b.clone());
        indices.push(i);
        ity_ax.push(ax);
        let o = one.clone();
        let (bt, bax) = abbrev(&mut env, k, move |_| o.clone());
        args.push(bt);
        arg_ax.push(bax);
    }
    for &j in &[1usize, 0] {
        let tag = mach.syms.inj_sym(j).expect("Inj_j's symbol");
        let (e, eax) = abbrev(&mut env, 2, move |a| Term::apply(tag, vec![a[j].clone()]));
        result.push(e);
        res_ax.push(eax);
    }
    let spec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::new(args, 0)]),
        indices,
        vec![CtorIndices::nonrecursive(result)],
    );
    assert!(spec.well_formed());

    let ix = IndexSpace::build(&mut env, &mut mach, &spec, &[]).expect("the index space");
    let lc = LeCarrier::build(&mut env, &mach, &f.ac, &spec, &ix, &[])
        .expect("a constructor with plain fields at an index has a carrier");

    // ── the introduction rule fires at the fields `(•, •)` ──────────────────
    let ys = vec![pt.clone(); 2];
    let img = spec.result_vec(0, &[], &ys).expect("the result indices");
    let mut atoms = Vec::new();
    for j in 0..2 {
        let unfold = inst_all(&arg_ax[j], &ys[..j]).expect("β_j(…) = 1");
        atoms.push(rw_back(&mut env, &unfold, |x| Formula::mem(pt.clone(), x), &s.unit_mem));
    }
    for (k, &j) in [1usize, 0].iter().enumerate() {
        let set = Term::apply(spec.indices[k], img[..k].to_vec());
        let ity = inst_all(&ity_ax[k], &img[..k]).expect("ι_k(…) = finord(2)");
        let base = inj_pt_mem(&mach, 2, j);
        let v = injs[j].clone();
        let at_set = rw_back(&mut env, &ity, move |x| Formula::mem(v.clone(), x), &base);
        let e = inst_all(&res_ax[k], &ys).expect("e_k(a,b) = Inj_j(·)");
        atoms.push(rw_back(&mut env, &e, move |x| Formula::mem(x, set.clone()), &at_set));
    }
    let h_ok = {
        let mut acc = atoms.last().expect("non-empty").clone();
        for a in atoms[..atoms.len() - 1].iter().rev() {
            acc = and_intro(a, &acc);
        }
        acc
    };
    let mem = Thm::mp(&inst_all(&lc.intro[0], &ys).expect("at the fields"), &h_ok)
        .expect("the typings discharge the antecedent");
    assert_eq!(*mem.concl(), Formula::mem(tup(&s, &img), lc.a_phi.clone()));
    assert!(closed(mem.concl()) && mem.hyps().is_empty());

    // ── and the carrier excludes the *swapped* pair ─────────────────────────
    // The image is `(Inj₁ •, Inj₀ •)`; `(Inj₀ •, Inj₁ •)` is in `Idx` and not in
    // `A_φ`. Under the captured reading it would have been in both.
    let bad = vec![injs[0].clone(), injs[1].clone()];
    let bad_tup = tup(&s, &bad);
    let wit: Vec<FreeVar> = (0..2).map(|_| env.fresh_var()).collect();
    let ws: Vec<Term> = wit.iter().map(|v| Term::var(*v)).collect();
    let wimg = spec.result_vec(0, &[], &ws).expect("the result indices at the witnesses");

    let at = inst_all(&lc.phi_ax, std::slice::from_ref(&bad_tup)).expect("A_φ's axiom");
    let mut disj_atoms: Vec<Formula> = (0..2)
        .map(|j| Formula::mem(ws[j].clone(), Term::apply(spec.base.ctors[0].args[j], ws[..j].to_vec())))
        .collect();
    disj_atoms.push(Formula::eq(bad_tup.clone(), tup(&s, &wimg)));
    let body = disj_atoms
        .iter()
        .rev()
        .skip(1)
        .fold(disj_atoms.last().expect("non-empty").clone(), |acc, x| {
            Formula::and(x.clone(), acc)
        });
    let matrix = wit.iter().rev().fold(body, |acc, v| Formula::exists(*v, acc));
    let mem_idx = Formula::mem(bad_tup.clone(), ix.idx.clone());
    assert_eq!(
        *at.concl(),
        Formula::iff(
            Formula::mem(bad_tup.clone(), lc.a_phi.clone()),
            Formula::and(mem_idx.clone(), matrix.clone())
        ),
        "the disjunct quantifies the fields and keeps `tup(bad)` fixed on the left"
    );
    let to_matrix =
        syl(&iff_mp(&at).expect("forward"), &and_right(mem_idx, matrix)).expect("the matrix");

    // Under the witnesses: the heads are `Inj₀ •` and `Inj₁ w₁`, and the
    // injections are disjoint whatever `w₁` is.
    let heads = syl(
        &derived::conj_proj(&disj_atoms, 2).expect("the equation"),
        &inst_all(
            &s.ap.pair_inj,
            &[
                bad[0].clone(),
                tup(&s, &bad[1..]),
                wimg[0].clone(),
                tup(&s, &wimg[1..]),
            ],
        )
        .expect("pair injectivity"),
    )
    .expect("syl");
    let heads = syl(
        &heads,
        &and_left(
            Formula::eq(bad[0].clone(), wimg[0].clone()),
            Formula::eq(tup(&s, &bad[1..]), tup(&s, &wimg[1..])),
        ),
    )
    .expect("the head equality");
    let h0 = bad[0].clone();
    let unfolded = rw_h(&mut env, &inst_all(&res_ax[0], &ws).expect("e₀ unfolds"),
        move |h| Formula::eq(h0.clone(), h), &heads);
    let ne = mach.syms.inj_distinct(&mut env, &s, 0, 1).expect("Inj₀ ≠ Inj₁");
    let mut branch = syl(&unfolded, &inst_all(&ne, &[pt.clone(), ws[1].clone()]).expect("at w₁"))
        .expect("⊥");
    for j in (0..2).rev() {
        branch = derived::exists_elim_imp(wit[j], &Thm::gen(wit[j], &branch), &Formula::false_())
            .expect("the witness is not free in ⊥");
    }
    let out = syl(&to_matrix, &branch).expect("¬(tup(bad) ∈ A_φ)");
    assert_eq!(*out.concl(), Formula::not(Formula::mem(bad_tup, lc.a_phi.clone())));
    assert!(closed(out.concl()) && out.hyps().is_empty());
}
