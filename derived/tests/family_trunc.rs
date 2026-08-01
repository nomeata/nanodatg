//! **Class (P)** — §5.2's small-eliminator clause, at the three shapes the
//! corpus asks for it in.
//!
//! The class is decided by the eliminator trichotomy, never by `numIndices` and
//! never by the constructor count (`INDEXED-DESIGN.md` §2.1). Decoding every
//! export in this repository gives thirteen class-(P) declarations in three
//! shapes, and there is a test for each:
//!
//! * **indexed, non-recursive** — `072`'s `SortElimProp2` (1 param, 2 indices,
//!   one constructor, `rec.levelParams = []`);
//! * **indexed, recursive** — `Nat.le`'s shape (1 param, 1 index, `refl` and
//!   `step`, `step` recursive), the prelude's own, and what forces the only new
//!   derivation in `family/trunc.rs`: a recursive argument of a `Prop` is a
//!   *proof*, so its hypothesis is `• ∈ ‖ind(p, d)‖` and the element it used to
//!   name has to be eliminated existentially;
//! * **non-indexed** — `Or`'s shape (2 params, two one-field constructors), the
//!   prelude's other class-(P) resident, where what is truncated is
//!   `Inductive::carrier` itself.
//!
//! **Both polarities, as equations at concrete sets.** A truncated carrier is a
//! subset of `{•}`, so a construction returning the constant `1` and one
//! returning the constant `0` would each satisfy every *membership* theorem the
//! other could not, and a careless test would pass against either. What is
//! pinned instead is `‖ind(e⃗)‖ = 1` at an index a constructor reaches,
//! `‖ind(x⃗)‖ = 0` at one no constructor reaches, and `⊢ ¬(‖ind(x⃗)‖ = ‖ind(e⃗)‖)`
//! — the two answers are *different sets*.
//!
//! Every assertion rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::family::{
    empty_at_index, CtorIndices, IndexedDeclSpec, IndexedInductive, TruncCarrier,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine};
use derived::prop::Trunc;
use derived::sums::Sums;
use derived::tower::Tower;
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{
    and_left, and_right, define_abbrev, eq_symm, eq_trans, imp_refl, inst_all, syl,
};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

// ─────────────────────────────────────────────────────────────────────────────
// Rewriting helpers — the boundary work, done by hand
// ─────────────────────────────────────────────────────────────────────────────

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
fn cong(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Term) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), &Thm::eq_refl(lhs)).expect("mp")
}

/// From `⊢ x = y` and `⊢ φ(x)` infer `⊢ φ(y)`.
fn rw(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), base).expect("mp")
}

/// From `⊢ y = x` and `⊢ φ(x)` infer `⊢ φ(y)` — the direction an unfolding
/// equation `f(args) = value` is used in when the *value* side is what holds.
fn rw_back(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let back = eq_symm(env, eq).expect("symm");
    rw(env, &back, ctx, base)
}

/// `tup(x⃗)`, the index tuple.
fn tup(s: &Sums, xs: &[Term]) -> Term { IndexedDeclSpec::tup(s, xs) }

/// From `⊢ uₖ = vₖ` for each `k`, infer `⊢ tup(u⃗) = tup(v⃗)`.
fn tup_congr(env: &mut Env, s: &Sums, eqs: &[Thm]) -> Thm {
    let mut cur = Thm::eq_refl(s.point());
    for eq in eqs.iter().rev() {
        let (_, new) = eq.concl().as_eq().expect("an equation");
        let (old_tail, _) = cur.concl().as_eq().expect("an equation");
        let one = cong(env, eq, |x| s.ap.sets.pair(x, old_tail.clone()));
        let two = cong(env, &cur, |x| s.ap.sets.pair(new.clone(), x));
        cur = eq_trans(env, &one, &two).expect("trans");
    }
    cur
}

/// `⊢ tup(u⃗) = tup(v⃗) → uₖ = vₖ`.
fn tup_proj(s: &Sums, us: &[Term], vs: &[Term], k: usize) -> Thm {
    let ap = &s.ap;
    let mut cur = imp_refl(Formula::eq(tup(s, us), tup(s, vs)));
    for lvl in 0..=k {
        let (tu, tv) = (tup(s, &us[lvl + 1..]), tup(s, &vs[lvl + 1..]));
        let inj =
            inst_all(&ap.pair_inj, &[us[lvl].clone(), tu.clone(), vs[lvl].clone(), tv.clone()])
                .expect("pair injectivity");
        let both = syl(&cur, &inj).expect("syl");
        let (l, r) = (Formula::eq(us[lvl].clone(), vs[lvl].clone()), Formula::eq(tu, tv));
        cur = if lvl == k {
            syl(&both, &and_left(l, r)).expect("head")
        } else {
            syl(&both, &and_right(l, r)).expect("tail")
        };
    }
    cur
}

/// Right-nested conjunction of closed theorems, matching `conj_of`.
fn conj_thms(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = derived::and_intro(t, &acc);
    }
    acc
}

// ─────────────────────────────────────────────────────────────────────────────
// The apparatus — one `Sums`, shared by the tower, the machine and `‖·‖`
// ─────────────────────────────────────────────────────────────────────────────

/// Everything a class-(P) build needs, over a **single** signature.
///
/// The sharing is the point: `Trunc`'s `1`, the tower's `U₀` and the machine's
/// `W` all have to be built over the same [`Sums`], or `Trunc::trunc_ax` speaks
/// about a different unit set than `cond_in_u0` does. `Tower::new` mints the
/// signature; `Wtype::over` and `Bound::over` join it rather than starting a
/// second one — which is what `cumul::Chain::new` does for the same reason.
struct Fix {
    tow: Tower,
    tr: Trunc,
    mach: Machine,
    rc: Recursor,
    iota: Thm,
    funspace: Thm,
}

fn fixture(env: &mut Env) -> Fix {
    let tow = Tower::new(env).expect("tower");
    let tr = Trunc::new(env, &tow.sums).expect("truncation over the tower's sums");
    let wt = Wtype::over(env, tow.sums.clone()).expect("W-type over the same sums");
    let bnd =
        Bound::over(env, &wt, tow.space.lu, tow.space.lu_ax.clone()).expect("bound over U(·)");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 3).expect("three summands");
    let rc = Recursor::new(env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(env, &mach.wt, &rc, &total).expect("funspace");
    Fix { tow, tr, mach, rc, iota, funspace }
}

/// A symbol of the given arity whose value is `body`, with its defining
/// equation — how a checker turns a Lean expression into the `FnSym` the spec
/// convention wants.
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

/// `⊢ t ∈ f(a⃗)` from `⊢ f(a⃗) = S`, `⊢ v ∈ S` and (optionally) `⊢ t = v` — the
/// unfolding a checker does at the boundary, in one place.
fn typed_at(env: &mut Env, set_eq: &Thm, elem_eq: Option<&Thm>, base: &Thm) -> Thm {
    let (lhs, _) = set_eq.concl().as_eq().expect("an equation");
    let v = base.concl().as_mem().expect("a membership").0;
    let in_set = rw_back(env, set_eq, |t| Formula::mem(v.clone(), t), base);
    match elem_eq {
        None => in_set,
        Some(eq) => rw_back(env, eq, |t| Formula::mem(t, lhs.clone()), &in_set),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// `072` — `SortElimProp2`, indexed and non-recursive
// ─────────────────────────────────────────────────────────────────────────────

/// A declaration, plus every defining equation a test has to unfold.
struct Decl {
    spec: IndexedDeclSpec,
    /// The index types' axioms, `[k]`.
    ity_ax: Vec<Thm>,
    /// The field types' axioms, `[ctor][j]`.
    beta_ax: Vec<Vec<Thm>>,
    /// The result indices' axioms, `[ctor][k]`.
    res_ax: Vec<Vec<Thm>>,
    /// The recursive arguments' index axioms, `[ctor][rec slot][k]`.
    rec_ax: Vec<Vec<Vec<Thm>>>,
}

/// `SortElimProp2 : Bool → Bool → Bool → Prop`,
/// `mk : ∀ b b1 b2, SortElimProp2 b b2 (id Bool b1)` **[decoded**,
/// `072_sortElimProp2Rec.ndjson`: `numParams=1`, `numIndices=2`, one
/// constructor with `numFields=2`, `isRec=false`, and
/// `SortElimProp2.rec.levelParams = []` against the declaration's own `[]` —
/// **not** large-eliminating, hence class (P)**]**.
///
/// `Bool := finord(2)`. The `id Bool b1` that makes the index non-invertible —
/// and so makes the eliminator small — is the identity at the set level, so the
/// result indices are `(b2, b1)`.
fn sort_elim_prop2(env: &mut Env, mach: &Machine) -> Decl {
    let s = &mach.wt.sums;
    let boolean = mach.syms.finord(s, 2).expect("finord(2)");
    let (i0, i0_ax) = abbrev(env, 1, |_| boolean.clone());
    let (i1, i1_ax) = abbrev(env, 2, |_| boolean.clone());
    let (b0, b0_ax) = abbrev(env, 1, |_| boolean.clone());
    let (b1, b1_ax) = abbrev(env, 2, |_| boolean.clone());
    let (e0, e0_ax) = abbrev(env, 3, |a| a[2].clone());
    let (e1, e1_ax) = abbrev(env, 3, |a| a[1].clone());
    Decl {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(1, vec![CtorSpec::new(vec![b0, b1], 0)]),
            vec![i0, i1],
            vec![CtorIndices::nonrecursive(vec![e0, e1])],
        ),
        ity_ax: vec![i0_ax, i1_ax],
        beta_ax: vec![vec![b0_ax, b1_ax]],
        res_ax: vec![vec![e0_ax, e1_ax]],
        rec_ax: vec![Vec::new()],
    }
}

/// **The whole class-(P) interface at `072`**, and the constructor's own index
/// answering `1`.
///
/// The carrier is `‖·‖` of the §5.2 carrier and nothing else — `ulift` costs
/// nothing (`thesis.txt:2106–2108`), so there is no second W-type at the lifted
/// universe and no re-derivation. `‖a‖ ∈ U₀` comes out with **no antecedent and
/// no size argument**, which is where class (P) is cheaper than class (T)
/// rather than more expensive.
#[test]
fn the_072_carrier_is_the_truncation_of_the_5_2_carrier() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = sort_elim_prop2(&mut env, &mach);
    assert!(d.spec.well_formed(), "the 072 spec is well formed");

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the indexed family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");

    let s = mach.wt.sums.clone();
    let (one, pt) = (s.unit(), s.point());
    assert_eq!(tc.carrier, f.tr.of(tc.base.clone()), "the carrier is ‖ind(p⃗,x⃗)‖");
    assert_eq!(tc.xvs.len(), 2, "two indices");
    assert!(
        derived::all_unconditional(&[
            &tc.ty_ax,
            &tc.subset_unit,
            &tc.only_point,
            &tc.irrel,
            &tc.elim,
            &tc.in_u0,
        ]),
        "every carrier-level theorem rests on nothing"
    );

    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let xs: Vec<Term> = tc.xvs.iter().map(|v| Term::var(*v)).collect();
    let mut ua = ps.clone();
    ua.extend(xs.iter().cloned());

    // `‖a‖ ∈ U₀` — no antecedent, no `C₂`, no `W`.
    let in_u0 = inst_all(&tc.in_u0, &ua).expect("instantiate");
    assert!(
        derived::establishes(&in_u0, &Formula::mem(tc.carrier.clone(), f.tow.u0())),
        "⊢ ‖ind(p⃗,x⃗)‖ ∈ U₀"
    );

    // `z ∈ ‖a‖ → z ∈ 1` and `z ∈ ‖a‖ → z = •`: the carrier is a `Prop`, and
    // every inhabitant is the point.
    let z = Term::apply(env.declare(0), vec![]);
    let mut za = ua.clone();
    za.push(z.clone());
    assert!(
        derived::establishes(
            &inst_all(&tc.subset_unit, &za).expect("instantiate"),
            &Formula::imp(
                Formula::mem(z.clone(), tc.carrier.clone()),
                Formula::mem(z.clone(), one.clone())
            )
        ),
        "⊢ z ∈ ‖a‖ → z ∈ 1"
    );
    assert!(
        derived::establishes(
            &inst_all(&tc.only_point, &za).expect("instantiate"),
            &Formula::imp(
                Formula::mem(z.clone(), tc.carrier.clone()),
                Formula::eq(z.clone(), pt.clone())
            )
        ),
        "⊢ z ∈ ‖a‖ → z = • — which is why the recursor's ι is reflexivity"
    );

    // **ι.** Any two inhabitants are equal, so `⟦rec … (mk …)⟧ = ⟦minor …⟧`
    // holds whatever the two sides are, once both are known to be in the
    // carrier. That is the whole of a class-(P) recursor.
    let w = Term::apply(env.declare(0), vec![]);
    let mut ia = ua.clone();
    ia.extend([z.clone(), w.clone()]);
    assert!(
        derived::establishes(
            &inst_all(&tc.irrel, &ia).expect("instantiate"),
            &Formula::imp(
                Formula::and(
                    Formula::mem(z.clone(), tc.carrier.clone()),
                    Formula::mem(w.clone(), tc.carrier.clone())
                ),
                Formula::eq(z, w)
            )
        ),
        "⊢ (u ∈ ‖a‖ ∧ v ∈ ‖a‖) → u = v"
    );

    // ── the constructor, at `b1 = b2 = ff` ──────────────────────────────────
    let ff = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let p = one.clone();
    let c = &tc.ctors[0];
    assert!(c.tvs.is_empty(), "072's constructor is not recursive");
    assert_eq!(c.trunc_atoms, c.mem_atoms, "nothing to truncate without recursion");

    let ys = [ff.clone(), ff.clone()];
    let at = inst_all(&c.is_unit, &[p.clone(), ff.clone(), ff.clone()]).expect("instantiate");
    let (ante, _) = at.concl().as_imp().expect("an implication");

    let bool_ff = inj_pt_mem(&mach, 2, 0);
    let res: Vec<Term> = (0..2)
        .map(|k| d.spec.result_at(0, k, std::slice::from_ref(&p), &ys).expect("result index"))
        .collect();
    let res_eqs: Vec<Thm> = (0..2)
        .map(|k| {
            inst_all(&d.res_ax[0][k], &[p.clone(), ff.clone(), ff.clone()]).expect("instantiate")
        })
        .collect();

    let mut parts = Vec::new();
    for j in 0..2 {
        let mut a = vec![p.clone()];
        a.extend(ys[..j].iter().cloned());
        let beta_eq = inst_all(&d.beta_ax[0][j], &a).expect("instantiate");
        parts.push(typed_at(&mut env, &beta_eq, None, &bool_ff));
    }
    for k in 0..2 {
        let mut a = vec![p.clone()];
        a.extend(res[..k].iter().cloned());
        let ity_eq = inst_all(&d.ity_ax[k], &a).expect("instantiate");
        parts.push(typed_at(&mut env, &ity_eq, Some(&res_eqs[k]), &bool_ff));
    }
    let discharged = conj_thms(&parts);
    assert_eq!(*discharged.concl(), ante, "the antecedent is exactly what was discharged");

    let is_unit = Thm::mp(&at, &discharged).expect("mp");
    let target = f.tr.of(fam.carrier.ty_of(std::slice::from_ref(&p), &res).expect("the carrier"));
    assert!(
        derived::establishes(&is_unit, &Formula::eq(target.clone(), one.clone())),
        "⊢ ‖ind(1, e⃗(1,ff,ff))‖ = 1 — inhabited, at a concrete set"
    );
    assert!(closed(is_unit.concl()));

    // The membership form is the same fact, weaker.
    let mem = Thm::mp(
        &inst_all(&c.mem, &[p.clone(), ff.clone(), ff]).expect("instantiate"),
        &discharged,
    )
    .expect("mp");
    assert!(derived::establishes(&mem, &Formula::mem(pt, target)), "⊢ • ∈ ‖ind(1, e⃗)‖");
}

// ─────────────────────────────────────────────────────────────────────────────
// Both polarities, at one declaration
// ─────────────────────────────────────────────────────────────────────────────

/// **The two answers are different sets.** `Int.NonNeg`'s shape — no
/// parameters, one index, one constructor — with the constructor's result index
/// a constant, so that a *third* element of the index type is reachable by
/// nothing.
///
/// `‖ind(Inj₀•)‖ = 1` and `‖ind(Inj₁•)‖ = 0`, and therefore
/// `⊢ ¬(‖ind(Inj₁•)‖ = ‖ind(Inj₀•)‖)`. Without the second equation every
/// theorem in the previous test would survive `‖·‖` being the constant `1`;
/// without the first, `0`.
#[test]
fn an_unreachable_index_truncates_to_the_empty_set() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let (zero, one, pt) = (s.zero(), s.unit(), s.point());
    let nat = mach.syms.finord(&s, 3).expect("finord(3)");
    let (i0, i0_ax) = abbrev(&mut env, 0, |_| nat.clone());
    let hit = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let miss = mach.syms.inj(1, pt.clone()).expect("Inj₁");
    let (e0, e0_ax) = abbrev(&mut env, 0, |_| hit.clone());

    let spec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::nullary()]),
        vec![i0],
        vec![CtorIndices::nonrecursive(vec![e0])],
    );
    assert!(spec.well_formed());
    let ind = Inductive::build(&mut env, &mut mach, &spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &spec, &f.rc, &f.iota, &f.funspace)
            .expect("the family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");

    // ── positive: the constructor's own index answers `1` ───────────────────
    let res = spec.result_at(0, 0, &[], &[]).expect("result index");
    let at = inst_all(&tc.ctors[0].is_unit, &[]).expect("no binders to fill");
    let ante = at.concl().as_imp().expect("an implication").0;
    let nat_hit = inj_pt_mem(&mach, 3, 0);
    let ity_eq = inst_all(&i0_ax, &[]).expect("instantiate");
    let res_eq = inst_all(&e0_ax, &[]).expect("instantiate");
    let discharged = typed_at(&mut env, &ity_eq, Some(&res_eq), &nat_hit);
    assert_eq!(*discharged.concl(), ante);
    let inhabited = Thm::mp(&at, &discharged).expect("mp");
    let hit_set = f.tr.of(fam.carrier.ty_of(&[], std::slice::from_ref(&res)).expect("carrier"));
    assert!(derived::establishes(&inhabited, &Formula::eq(hit_set.clone(), one.clone())));

    // ── negative: `Inj₁(•)` is reachable by nothing ─────────────────────────
    let xs = [miss.clone()];
    let ne = mach.syms.inj_distinct(&mut env, &s, 1, 0).expect("Inj₁ ≠ Inj₀");
    let ne_at = inst_all(&ne, &[pt.clone(), pt.clone()]).expect("at •");
    let at_vals = syl(&tup_proj(&s, &xs, std::slice::from_ref(&hit), 0), &ne_at).expect("components differ");
    let fold = tup_congr(&mut env, &s, std::slice::from_ref(&res_eq));
    let tx = tup(&s, &xs);
    let refutation = rw_back(
        &mut env,
        &fold,
        move |hole| Formula::not(Formula::eq(tx.clone(), hole)),
        &at_vals,
    );
    assert_eq!(
        *refutation.concl(),
        Formula::not(Formula::eq(tup(&s, &xs), tup(&s, std::slice::from_ref(&res))))
    );

    let general = empty_at_index(
        &mut env, &mach, &ind, &spec, &fam.ix, &fam.gv, &fam.gs, &fam.good, &fam.carrier,
        &f.rc, &xs, &[refutation],
    )
    .expect("the carrier is empty at Inj₁(•)");

    let miss_base = fam.carrier.ty_of(&[], &xs).expect("carrier");
    let empty = tc
        .empty_at(&mut env, &s, &f.tr, &miss_base, &general)
        .expect("the truncation of an empty set");
    let miss_set = f.tr.of(miss_base);
    assert!(
        derived::establishes(&empty, &Formula::eq(miss_set.clone(), zero.clone())),
        "⊢ ‖ind(Inj₁•)‖ = 0 — uninhabited, at a concrete set"
    );
    assert!(closed(empty.concl()));

    // ── and the two are different sets ──────────────────────────────────────
    assert_eq!(*s.tags_distinct.concl(), Formula::not(Formula::eq(zero.clone(), one.clone())));
    let step = rw_back(
        &mut env,
        &empty,
        |t| Formula::not(Formula::eq(t, one.clone())),
        &s.tags_distinct,
    );
    let distinct = rw_back(
        &mut env,
        &inhabited,
        |t| Formula::not(Formula::eq(miss_set.clone(), t)),
        &step,
    );
    assert!(
        derived::establishes(&distinct, &Formula::not(Formula::eq(miss_set, hit_set))),
        "⊢ ¬(‖ind(Inj₁•)‖ = ‖ind(Inj₀•)‖)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// `Nat.le` — the recursive class-(P) shape
// ─────────────────────────────────────────────────────────────────────────────

/// `Nat.le : ∀(n : Nat), Nat → Prop` with `refl : Nat.le n n` and
/// `step : ∀ m, Nat.le n m → Nat.le n (succ m)` **[decoded**,
/// `init-prelude.ndjson`: `numParams=1`, `numIndices=1`, `isRec=true`, two
/// constructors, and `Nat.le.rec.levelParams = []` — **not** large-eliminating,
/// hence class (P)**]**.
///
/// `Nat := finord(3)`, and both result indices are **constants** — the same
/// liberty `family.rs` takes with `RBTree`'s successor, and for the same reason:
/// every index expression reaches this layer as an opaque `FnSym`, so index
/// *arithmetic* is invisible here and only the index *structure* is under test.
/// What is not simplified away is the thing being tested: `step` has a genuine
/// recursive argument, whose child index `d(n, m) = m` really does depend on its
/// plain field.
fn nat_le(env: &mut Env, mach: &Machine) -> Decl {
    let s = &mach.wt.sums;
    let nat = mach.syms.finord(s, 3).expect("finord(3)");
    let pt = s.point();
    let zero = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let succ = mach.syms.inj(1, pt).expect("Inj₁");
    let (i0, i0_ax) = abbrev(env, 1, |_| nat.clone());
    let (b0, b0_ax) = abbrev(env, 1, |_| nat.clone());
    let (r0, r0_ax) = abbrev(env, 1, |_| zero.clone()); // refl's result index
    let (s0, s0_ax) = abbrev(env, 2, |_| succ.clone()); // step's result index
    let (d0, d0_ax) = abbrev(env, 2, |a| a[1].clone()); // step's child index, `m`
    Decl {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![b0], 1)]),
            vec![i0],
            vec![
                CtorIndices::nonrecursive(vec![r0]),
                CtorIndices { result: vec![s0], rec_args: vec![vec![d0]] },
            ],
        ),
        ity_ax: vec![i0_ax],
        beta_ax: vec![Vec::new(), vec![b0_ax]],
        res_ax: vec![vec![r0_ax], vec![s0_ax]],
        rec_ax: vec![Vec::new(), vec![vec![d0_ax]]],
    }
}

/// **A recursive class-(P) constructor takes a proof, not an element.**
///
/// This is the only thing in `family/trunc.rs` that is not a one-line
/// composition. `IndexedCtor::mem` types `step` with its recursive argument as
/// an *element* `r₀ ∈ ind(n, d(n,m))`; but `Nat.le n m` is a `Prop`, so what a
/// caller has is a proof, and at the set level a proof of an inhabited `Prop` is
/// `• ∈ ‖ind(n, d(n,m))‖`. Going from the one to the other is `Trunc::elim`
/// followed by an existential elimination, and the witness leaves the statement:
/// `trunc_mem` has **no `∀r₀`**.
#[test]
fn a_recursive_class_p_constructor_takes_a_proof_not_an_element() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = nat_le(&mut env, &mach);
    assert!(d.spec.well_formed(), "the Nat.le spec is well formed");
    let _ = &d.rec_ax;

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the indexed family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");

    let s = mach.wt.sums.clone();
    let pt = s.point();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let c = &tc.ctors[1];
    assert_eq!(c.yvs.len(), 1, "step has one plain field");
    assert_eq!(c.tvs.len(), 1, "and one recursive argument");
    let ys: Vec<Term> = c.yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = c.tvs.iter().map(|v| Term::var(*v)).collect();

    let child = fam
        .carrier
        .ty_of(&ps, &d.spec.rec_index_vec(1, 0, &ps, &ys).expect("child indices"))
        .expect("the carrier at the child index");
    let result = fam
        .carrier
        .ty_of(&ps, &d.spec.result_vec(1, &ps, &ys).expect("result indices"))
        .expect("the carrier at the result index");

    // The underlying rule names an element; the class-(P) rule names a proof.
    assert_eq!(
        c.mem_atoms[1],
        Formula::mem(ts[0].clone(), child.clone()),
        "(M)'s recursive hypothesis is an element of the child carrier"
    );
    assert_eq!(
        c.trunc_atoms[1],
        Formula::mem(pt.clone(), f.tr.of(child.clone())),
        "the class-(P) rule's is `• ∈ ‖child‖`"
    );
    assert_eq!(c.trunc_atoms[0], c.mem_atoms[0], "the plain field's typing is untouched");
    assert_eq!(c.trunc_atoms[2], c.mem_atoms[2], "and so is the result-index typing");

    // The statement, rebuilt: `∀n ∀m` and **no** `∀r₀`.
    let want = Formula::imp(
        derived::conj_of(&c.trunc_atoms).expect("a non-empty antecedent"),
        Formula::mem(pt.clone(), f.tr.of(result.clone())),
    );
    let mut quant = ind.params.clone();
    quant.extend(c.yvs.iter().copied());
    assert_eq!(
        *c.trunc_mem.concl(),
        quant.iter().rev().fold(want, |acc, v| Formula::forall(*v, acc)),
        "⊢ ∀n ∀m. (Hᵢ^‖‖ → • ∈ ‖ind(n, succ m)‖)"
    );
    assert!(c.trunc_mem.hyps().is_empty());
    assert!(
        !c.trunc_mem.concl().occurs_free(c.tvs[0]),
        "the witness left the statement — that is what the existential elimination bought"
    );
    // The element-shaped rule still quantifies over it.
    assert!(inst_all(&c.mem, &[ps[0].clone(), ys[0].clone(), ts[0].clone()]).is_some());

    // `refl` is non-recursive, so its two rules coincide.
    assert_eq!(tc.ctors[0].trunc_atoms, tc.ctors[0].mem_atoms);
}

// ─────────────────────────────────────────────────────────────────────────────
// `Or` — the non-indexed route
// ─────────────────────────────────────────────────────────────────────────────

/// **Class (P) does not mean indexed.** `Or : Prop → Prop → Prop` has no
/// indices at all and is still not large-eliminating (`Or.rec.levelParams = []`
/// against `Or`'s own `[]` **[decoded**, `init-prelude.ndjson`**]**), so the
/// truncation clause is what serves it. Seven of the thirteen class-(P)
/// declarations in this repository are like that.
///
/// What is truncated here is `Inductive::carrier` itself: no `IndexedCarrier`,
/// no `good`, no index space. Both constructors land in the *same* carrier, so
/// the two rules have the same conclusion — which is exactly right, and is the
/// set-level reason a small eliminator cannot tell the disjuncts apart.
#[test]
fn the_non_indexed_route_truncates_the_skeleton_directly() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let (one, pt) = (s.unit(), s.point());

    // `inl : a → Or a b`, `inr : b → Or a b`, with both field types `1`.
    let (bl, bl_ax) = abbrev(&mut env, 2, |_| one.clone());
    let (br, br_ax) = abbrev(&mut env, 2, |_| one.clone());
    let spec = DeclSpec::new(2, vec![CtorSpec::new(vec![bl], 0), CtorSpec::new(vec![br], 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let tc = TruncCarrier::over_declaration(&mut env, &mach, &f.tow, &f.tr, &ind)
        .expect("the class-(P) carrier");

    assert!(tc.xvs.is_empty(), "no indices");
    assert_eq!(tc.base, ind.carrier, "the thing truncated is the skeleton itself");
    assert_eq!(tc.carrier, f.tr.of(ind.carrier.clone()));
    assert_eq!(tc.ctors.len(), 2);

    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let in_u0 = inst_all(&tc.in_u0, &ps).expect("instantiate");
    assert!(derived::establishes(&in_u0, &Formula::mem(tc.carrier.clone(), f.tow.u0())));

    // Both constructors put `•` into the *same* set.
    let target = f.tr.of(ind.ty_of(vec![one.clone(), one.clone()]));
    let unit_mem = s.unit_mem.clone();
    for (i, ax) in [bl_ax, br_ax].iter().enumerate() {
        let c = &tc.ctors[i];
        assert!(c.tvs.is_empty() && c.yvs.len() == 1);
        assert_eq!(c.trunc_atoms, c.mem_atoms, "no recursion, nothing to truncate");

        let at = inst_all(&c.is_unit, &[one.clone(), one.clone(), pt.clone()])
            .expect("instantiate");
        let ante = at.concl().as_imp().expect("an implication").0;
        let beta_eq = inst_all(ax, &[one.clone(), one.clone()]).expect("instantiate");
        let discharged = typed_at(&mut env, &beta_eq, None, &unit_mem);
        assert_eq!(*discharged.concl(), ante);

        let out = Thm::mp(&at, &discharged).expect("mp");
        assert!(
            derived::establishes(&out, &Formula::eq(target.clone(), one.clone())),
            "⊢ ‖Or 1 1‖ = 1, from either constructor"
        );
        assert!(closed(out.concl()));
    }
}

/// The two entry points do not accept each other's declarations, and neither
/// accepts a foreign apparatus — the guards are decisions, not accidents.
#[test]
fn the_class_p_build_refuses_what_it_cannot_state() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = sort_elim_prop2(&mut env, &mach);
    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the family");

    // A second apparatus over the same `Wtype` and `Bound` has its own `Inj`.
    let m2 = Machine::over(&mut env, mach.wt.clone(), mach.bnd.clone()).expect("a second machine");
    assert!(!ind.is_over(&m2));
    assert!(
        TruncCarrier::over_family(&mut env, &m2, &f.tow, &f.tr, &ind, &fam.carrier).is_none(),
        "a foreign machine was accepted"
    );
    assert!(
        TruncCarrier::over_declaration(&mut env, &m2, &f.tow, &f.tr, &ind).is_none(),
        "a foreign machine was accepted"
    );

    // A `Trunc` over a *different* `Sums` speaks about a different `1`, so
    // every shape check fails rather than producing a theorem about two unit
    // sets at once.
    let other_tower = Tower::new(&mut env).expect("a second signature");
    let other_tr = Trunc::new(&mut env, &other_tower.sums).expect("a second truncation");
    assert!(
        TruncCarrier::over_family(&mut env, &mach, &f.tow, &other_tr, &ind, &fam.carrier)
            .is_none(),
        "a truncation over a foreign signature was accepted"
    );

    // And a tower over a different signature is refused the same way.
    assert!(
        TruncCarrier::over_family(&mut env, &mach, &other_tower, &f.tr, &ind, &fam.carrier)
            .is_none(),
        "a tower over a foreign signature was accepted"
    );
}
