//! **The class-(P) recursor, indexed** —
//! `derived/src/inductive/family/trunc_rec_ix.rs`.
//!
//! # Which half of the scope each fixture witnesses
//!
//! The module's scope has two halves and the corpus covers one of them, so this
//! file is deliberately not organised around `072` alone:
//!
//! * [`sort_elim_prop2`] is **`072`'s real shape** — `np = 1`, `ni = 2`,
//!   `kᵢ = 2`, the result indices the fields *permuted* — copied from
//!   `family_trunc.rs`, where the carrier is already tested at it. It has
//!   `recs = 0`, so it witnesses the non-constant `φ` and the
//!   `IndexedCtor::inv` forcing and **nothing else**.
//! * [`nat_le`] is a **recursive** indexed class-(P) declaration, also copied
//!   from `family_trunc.rs`. Nothing in the tutorial corpus is one — `Nat.le`,
//!   `Nat.le.below` and `List.Mem` live in the prelude and `grind-ring-5` — so
//!   the branch where the induction hypothesis is fired at the child's own
//!   index vector and actually *consumed* is exercised here and nowhere else.
//!   A passing corpus run is not evidence for it.
//! * [`interleaved`] carries a `Plain, Rec, Plain, Rec` mask and **two**
//!   recursive arguments. [`nat_le`]'s mask is `Plain, Rec`, which *is*
//!   plains-then-recs, so nothing else here can tell the declared field order
//!   from the carrier's — the `minor_atoms` ordering claim would have had no
//!   witness at all.
//! * [`cycle3`] is where the rule **fires end to end at a concrete motive**.
//!   Three index slots and a 3-cycle, not two and a swap: a transposition is its
//!   own inverse, so `σ ≠ σ⁻¹` needs three, and the `ni` Leibniz steps that move
//!   a minor's conclusion from `e⃗ᵢ` to `x⃗` are exactly the loop that would get
//!   an order wrong. Its field types are the unit set, which is what makes
//!   `MINOR₀`'s `∀y⃗` dischargeable at a one-point motive: the index vector is
//!   then a single concrete triple and the motive need only be defined there.
//!
//! **Non-vacuity cuts both ways.** A rule whose antecedent were decoration
//! would be satisfied by every motive, so the same minor is shown *refutable*
//! at the motive whose leaf is `0` — the same theorem, one constant changed,
//! which is `family_trunc_rec.rs`'s standard and is kept.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::family::{
    motive_app, trunc_minor_atoms_at, trunc_minor_body_at, CtorIndices, IndexedDeclSpec,
    IndexedInductive, IndexedTruncRecursor, TruncCarrier,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine, Slot};
use derived::point_fun::PointFun;
use derived::prop::Trunc;
use derived::sums::Sums;
use derived::tower::Tower;
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{
    a1i, and_intro, conj_of, conj_proj, define_abbrev, eq_symm, eq_symm_imp, gen_all,
    hyp_mp, imp_refl, inst_all, syl,
};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed_f(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
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
    let back = eq_symm(env, eq).expect("symm");
    rw(env, &back, ctx, base)
}

/// From `⊢ H → x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
fn rw_h(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (h, body) = eq.concl().as_imp().expect("an implication");
    let (x, y) = body.as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    let step = hyp_mp(&a1i(&leib, h), eq).expect("mp");
    hyp_mp(&step, base).expect("mp")
}

/// From `⊢ H → x = y` infer `⊢ H → y = x`.
fn hyp_eq_symm(env: &mut Env, t: &Thm) -> Thm {
    let (_, body) = t.concl().as_imp().expect("an implication");
    let (x, y) = body.as_eq().expect("an equation");
    syl(t, &eq_symm_imp(env, x, y)).expect("syl")
}

/// From `⊢ H → ∀v⃗. φ` infer `⊢ H → φ[t⃗]`.
fn hyp_inst(t: &Thm, args: &[Term]) -> Thm {
    let mut cur = t.clone();
    for a in args {
        let (_, all) = cur.concl().as_imp().expect("an implication");
        cur = syl(&cur, &Thm::ax_inst(all, a.clone()).expect("instantiate")).expect("syl");
    }
    cur
}

/// Right-nested conjunction of theorems, matching `conj_of`.
fn conj_thms(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = and_intro(t, &acc);
    }
    acc
}

/// `∀x₀ … ∀x_{n-1}. φ`, outermost first — `gen_all` at the formula level.
fn quantify(xs: &[FreeVar], phi: Formula) -> Formula {
    xs.iter().rev().fold(phi, |acc, x| Formula::forall(*x, acc))
}

// ─────────────────────────────────────────────────────────────────────────────
// The apparatus — one `Sums`, shared by the tower, the machine and `‖·‖`
// ─────────────────────────────────────────────────────────────────────────────

struct Fix {
    tow: Tower,
    tr: Trunc,
    pf: PointFun,
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
    let pf = PointFun::over(env, &wt.sums, &wt.app_pair).expect("the one-point function");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 3).expect("three summands");
    let rc = Recursor::new(env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(env, &mach.wt, &rc, &total).expect("funspace");
    Fix { tow, tr, pf, mach, rc, iota, funspace }
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

/// A declaration, plus every defining equation a test has to unfold.
struct Decl {
    spec: IndexedDeclSpec,
    /// The index types' axioms, `[k]`.
    ity_ax: Vec<Thm>,
    /// The field types' axioms, `[ctor][j]`.
    beta_ax: Vec<Vec<Thm>>,
    /// The result indices' axioms, `[ctor][k]`.
    res_ax: Vec<Vec<Thm>>,
}

// ─────────────────────────────────────────────────────────────────────────────
// The curried one-point motive
// ─────────────────────────────────────────────────────────────────────────────

/// `app(head, r⃗, •)` — [`motive_app`]'s spine with a caller-supplied head.
fn spine_from(s: &Sums, head: Term, rest: &[Term]) -> Term {
    let mut cur = head;
    for r in rest {
        cur = s.ap.apply(cur, r.clone());
    }
    s.ap.apply(cur, s.point())
}

/// The nest `{⟨v₀, {⟨v₁, … {⟨•, leaf⟩} …⟩}⟩}`, outermost first, with a trailing
/// `{⟨•, leaf⟩}`.
fn point_nest(s: &Sums, vs: &[Term], leaf: &Term) -> Vec<Term> {
    let mut ms = vec![PointFun::of(s, s.point(), leaf.clone())];
    for v in vs.iter().rev() {
        let inner = ms.last().expect("non-empty").clone();
        ms.push(PointFun::of(s, v.clone(), inner));
    }
    ms.reverse();
    ms
}

/// **A concrete motive**, defined at exactly one index vector.
///
/// Returns the motive term `m` and, from `⊢ φ(leaf)`, the same statement at
/// `⊢ φ(app(m, v⃗, •))` — four `PointFun::app` steps for three indices. A
/// one-point nest is total enough here precisely because [`cycle3`]'s field
/// types are the unit set, so the minor's `∀y⃗` reaches one index vector and no
/// other.
fn at_motive(
    env: &mut Env,
    s: &Sums,
    pf: &PointFun,
    vs: &[Term],
    leaf: &Term,
    ctx: &dyn Fn(Term) -> Formula,
    base: &Thm,
) -> (Term, Thm) {
    let pt = s.point();
    let ms = point_nest(s, vs, leaf);
    let n = vs.len();
    let eq_last = inst_all(&pf.app, &[pt.clone(), leaf.clone()]).expect("app({⟨•,leaf⟩},•) = leaf");
    let mut cur = rw_back(env, &eq_last, ctx, base);
    for j in (0..n).rev() {
        let eq = inst_all(&pf.app, &[vs[j].clone(), ms[j + 1].clone()])
            .expect("app({⟨vⱼ,mⱼ₊₁⟩}, vⱼ) = mⱼ₊₁");
        let rest = vs[j + 1..].to_vec();
        let sc = s.clone();
        cur = rw_back(env, &eq, |h| ctx(spine_from(&sc, h, &rest)), &cur);
    }
    (ms[0].clone(), cur)
}

// ─────────────────────────────────────────────────────────────────────────────
// `072` — the corpus row, and the half of the scope it witnesses
// ─────────────────────────────────────────────────────────────────────────────

/// `SortElimProp2 : ∀ (b : Bool), Bool → Bool → Prop`,
/// `mk : ∀ b b1 b2, SortElimProp2 b b2 (id Bool b1)` — `np = 1`, `ni = 2`,
/// `kᵢ = 2`, `recs = 0`, and the result indices are the fields **permuted**.
///
/// Copied from `family_trunc.rs`, where `TruncCarrier::over_family` is already
/// tested at it. `id Bool b1` is the identity at the set level, so the result
/// indices are `(b2, b1)` — the swap is the whole of `072`'s index structure,
/// and it is what makes the eliminator small.
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
    }
}

/// **The deliverable, at `072`'s shape.** The whole statement, rebuilt term by
/// term, and the minor stated at the *permuted* index vector.
///
/// This is the half of the scope the corpus witnesses: a non-constant `φ` and
/// the index forcing. `recs = 0`, so nothing here says anything about the
/// recursive minors — see [`a_recursive_minor_is_not_its_own_consequent`].
#[test]
fn the_072_rule_is_stated_at_the_permuted_index_vector() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = sort_elim_prop2(&mut env, &mach);
    assert!(d.spec.well_formed(), "the 072 spec is well formed");
    let _ = (&d.ity_ax, &d.beta_ax);

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the indexed family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let rr = IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc)
        .expect("the indexed class-(P) recursor");

    let s = f.mach.wt.sums.clone();
    let pt = s.point();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let tm = Term::var(rr.motive);

    // ── the minor: two plain fields, no `∀r⃗`, conclusion at `(e₀, e₁)` ─────
    assert_eq!(rr.minor_vars.len(), 1);
    assert_eq!(rr.minor_vars[0].len(), 2, "one binder per plain field, and no others");
    let ys: Vec<Term> = rr.minor_vars[0].iter().map(|v| Term::var(*v)).collect();
    assert_eq!(
        rr.minor_atoms[0],
        trunc_minor_atoms_at(&s, &f.tr, &d.spec, &fam.carrier, 0, &tm, &ps, &ys)
            .expect("Aᵢ rebuilt at the same terms"),
        "the exported accessor and the theorem carry the same antecedent"
    );
    assert_eq!(rr.minor_atoms[0].len(), 2, "two plain typings, no recursion");

    let res = d.spec.result_vec(0, &ps, &ys).expect("the result indices");
    let want_minor = quantify(
        &rr.minor_vars[0],
        Formula::imp(
            conj_of(&rr.minor_atoms[0]).expect("two atoms"),
            Formula::mem(pt.clone(), motive_app(&s, &tm, &res, &pt)),
        ),
    );
    assert_eq!(rr.minors[0], want_minor);
    assert_eq!(
        rr.minors[0],
        quantify(
            &rr.minor_vars[0],
            trunc_minor_body_at(&s, &f.tr, &d.spec, &fam.carrier, 0, &tm, &ps, &ys)
                .expect("the body rebuilt")
        ),
        "and the body accessor agrees too"
    );
    assert_eq!(rr.hyp, rr.minors[0], "one constructor, so HYP is the one minor");

    // The permutation, read off the unfolded index vector: slot 0 takes the
    // *second* field and slot 1 the first.
    let unfolded: Vec<Term> = (0..2)
        .map(|k| {
            let mut a = ps.clone();
            a.extend(ys.iter().cloned());
            let eq = inst_all(&d.res_ax[0][k], &a).expect("e_k unfolds");
            eq.concl().as_eq().expect("an equation").1
        })
        .collect();
    assert_eq!(unfolded, vec![ys[1].clone(), ys[0].clone()], "e⃗ = (y₁, y₀)");

    // ── the whole statement ─────────────────────────────────────────────────
    let fxs: Vec<Term> = rr.xvs.iter().map(|v| Term::var(*v)).collect();
    let tt = Term::var(rr.major);
    let base = fam.carrier.ty_of(&ps, &fxs).expect("ind(p⃗,x⃗)");
    let mut quant = ind.params.clone();
    quant.push(rr.motive);
    let want = quantify(
        &quant,
        Formula::imp(
            rr.hyp.clone(),
            quantify(
                &rr.xvs,
                Formula::forall(
                    rr.major,
                    Formula::imp(
                        Formula::mem(tt.clone(), f.tr.of(base)),
                        Formula::mem(pt.clone(), motive_app(&s, &tm, &fxs, &tt)),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*rr.rec.concl(), want);
    assert!(rr.rec.hyps().is_empty() && closed_f(rr.rec.concl()), "closed and unconditional");
}

// ─────────────────────────────────────────────────────────────────────────────
// `Nat.le` — the recursive half, which the corpus does not witness
// ─────────────────────────────────────────────────────────────────────────────

/// `Nat.le (n : Nat) : Nat → Prop`, `refl : Nat.le n n`,
/// `step : ∀ {m}, Nat.le n m → Nat.le n (m+1)` — `np = 1`, `ni = 1`, and
/// `step` has a **genuine recursive argument** whose child index `d(n,m) = m`
/// depends on its plain field.
///
/// Copied from `family_trunc.rs`. Both result indices are constants, as there:
/// index *arithmetic* is invisible at this layer, and what is under test is the
/// index *structure*.
fn nat_le(env: &mut Env, mach: &Machine) -> Decl {
    let s = &mach.wt.sums;
    let nat = mach.syms.finord(s, 3).expect("finord(3)");
    let pt = s.point();
    let zero = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let succ = mach.syms.inj(1, pt).expect("Inj₁");
    let (i0, i0_ax) = abbrev(env, 1, |_| nat.clone());
    let (b0, b0_ax) = abbrev(env, 1, |_| nat.clone());
    let (r0, r0_ax) = abbrev(env, 1, |_| zero.clone());
    let (s0, s0_ax) = abbrev(env, 2, |_| succ.clone());
    let (d0, _) = abbrev(env, 2, |a| a[1].clone());
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
    }
}

/// **The half of Petra's guard the corpus cannot witness.**
///
/// `trunc_rec.rs`'s "Scope: non-indexed only" says two things about the indexed
/// rule: that its `φ` is not constant, and that "the recursive minors stop being
/// trivial". `072` has `recs = 0` and witnesses only the first. This is the
/// second, and it is a *hand-built* fixture rather than a corpus row —
/// `Nat.le`, `Nat.le.below` and `List.Mem` are in the prelude and
/// `grind-ring-5`, not the tutorials.
///
/// What "stops being trivial" means precisely: in `trunc_rec` the induction
/// hypothesis atom **is** the minor's conclusion, so one projection proves the
/// step and the minor is never read. Here the hypothesis is at the child's index
/// `d(n,m)` and the conclusion at the result index `s(n,m)`, which are different
/// terms — so the minor carries content and the derivation has to fire it.
#[test]
fn a_recursive_minor_is_not_its_own_consequent() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = nat_le(&mut env, &mach);
    assert!(d.spec.well_formed(), "the Nat.le spec is well formed");

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the indexed family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let rr = IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc)
        .expect("a recursive indexed class-(P) declaration has an elimination rule");

    let s = f.mach.wt.sums.clone();
    let pt = s.point();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let tm = Term::var(rr.motive);

    // ── `refl`: no fields at all, so no antecedent ──────────────────────────
    assert!(rr.minor_atoms[0].is_empty());
    assert_eq!(
        rr.minors[0],
        Formula::mem(
            pt.clone(),
            motive_app(&s, &tm, &d.spec.result_vec(0, &ps, &[]).expect("r⃗"), &pt)
        ),
        "a nullary constructor's minor is the bare conclusion"
    );

    // ── `step`: one binder, three atoms, and no `∀r₀` ───────────────────────
    assert_eq!(rr.minor_vars[1].len(), 1, "the plain field only — a proof is not a variable");
    assert_eq!(rr.minor_atoms[1].len(), 3, "y₀ ∈ β₀, • ∈ ‖ind(p,d)‖, • ∈ app(m,d,•)");
    let ys: Vec<Term> = rr.minor_vars[1].iter().map(|v| Term::var(*v)).collect();
    let child = d.spec.rec_index_vec(1, 0, &ps, &ys).expect("d⃗(p,y₀)");
    let res = d.spec.result_vec(1, &ps, &ys).expect("e⃗(p,y₀)");

    assert_eq!(
        rr.minor_atoms[1][1],
        Formula::mem(pt.clone(), f.tr.of(fam.carrier.ty_of(&ps, &child).expect("ind(p,d)"))),
        "the recursive field contributes a *truncated* atom"
    );
    let ih = Formula::mem(pt.clone(), motive_app(&s, &tm, &child, &pt));
    assert_eq!(rr.minor_atoms[1][2], ih, "the induction hypothesis is at the child's own index");

    let concl = Formula::mem(pt.clone(), motive_app(&s, &tm, &res, &pt));
    assert_eq!(
        rr.minors[1],
        quantify(
            &rr.minor_vars[1],
            Formula::imp(conj_of(&rr.minor_atoms[1]).expect("three atoms"), concl.clone())
        )
    );

    // **The claim.** In `trunc_rec` these two are the same formula and the minor
    // is discharged by projecting it out of its own antecedent. Here they are
    // not, so there is nothing to project and the induction has to be run.
    assert_ne!(ih, concl, "the hypothesis is at d⃗, the conclusion at e⃗");
    assert!(!rr.minor_atoms[1].contains(&concl), "the minor is not its own consequent");

    assert!(rr.rec.hyps().is_empty() && closed_f(rr.rec.concl()));
}

/// `Nat.le`'s shape with a **second** recursive argument and an *interleaved*
/// field mask — `Plain, Rec, Plain, Rec`.
///
/// [`nat_le`]'s own mask is `Plain, Rec`, which **is** plains-then-recs, so it
/// cannot tell the declared order from the carrier's order. Nothing in the
/// corpus can either: `072` has no recursive fields at all. So the claim that
/// `minor_atoms` is positional against the Lean field spine has no witness
/// unless one is built, and this is it. The child indices depend on the plain
/// fields that *precede* their slot, which is `IndexedDeclSpec::plains_before`'s
/// restriction and the reason the interleaving has to be respected rather than
/// sorted away.
fn interleaved(env: &mut Env, mach: &Machine) -> Decl {
    let s = &mach.wt.sums;
    let nat = mach.syms.finord(s, 3).expect("finord(3)");
    let two = mach.syms.inj(2, s.point()).expect("Inj₂");
    let (i0, i0_ax) = abbrev(env, 1, |_| nat.clone());
    let (b0, b0_ax) = abbrev(env, 1, |_| nat.clone());
    let (b1, b1_ax) = abbrev(env, 2, |_| nat.clone());
    let (d0, _) = abbrev(env, 2, |a| a[1].clone()); // the first Rec sees y₀
    let (d1, _) = abbrev(env, 3, |a| a[2].clone()); // the second also sees y₁
    let (e0, e0_ax) = abbrev(env, 3, |_| two.clone());
    Decl {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(
                1,
                vec![CtorSpec::with_order(
                    vec![b0, b1],
                    2,
                    vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
                )
                .expect("a consistent mask")],
            ),
            vec![i0],
            vec![CtorIndices { result: vec![e0], rec_args: vec![vec![d0], vec![d1]] }],
        ),
        ity_ax: vec![i0_ax],
        beta_ax: vec![vec![b0_ax, b1_ax]],
        res_ax: vec![vec![e0_ax]],
    }
}

/// **`minor_atoms` is positional against the Lean field spine.** The mask is
/// `Plain, Rec, Plain, Rec`, so the six atoms are
///
/// ```text
/// y₀ ∈ β₀(p),  • ∈ ‖ind(p,d₀)‖,  y₁ ∈ β₁(p,y₀),  • ∈ ‖ind(p,d₁)‖,
/// • ∈ app(m,d₀,•),  • ∈ app(m,d₁,•)
/// ```
///
/// — fields in *declared* order, then the two induction hypotheses, which is
/// where Lean's minor premise puts them. The carrier's own order is
/// plains-then-recs and the two disagree at three of the four field positions,
/// so a build that sorted by the mask instead of respecting it would pass every
/// other test in this file: [`nat_le`]'s mask is already plains-then-recs, and
/// `072` and [`cycle3`] have no recursive fields at all.
#[test]
fn the_minor_atoms_are_lean_positional() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = interleaved(&mut env, &mach);
    assert!(d.spec.well_formed(), "the interleaved spec is well formed");

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the indexed family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let rr = IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc)
        .expect("two recursive arguments, interleaved");

    let s = f.mach.wt.sums.clone();
    let pt = s.point();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let tm = Term::var(rr.motive);
    assert_eq!(rr.minor_vars[0].len(), 2, "two plain binders, and no `∀r⃗`");
    let ys: Vec<Term> = rr.minor_vars[0].iter().map(|v| Term::var(*v)).collect();

    let child = |j: usize| d.spec.rec_index_vec(0, j, &ps, &ys).expect("d⃗ⱼ");
    let plain = |j: usize| {
        let mut a = ps.clone();
        a.extend(ys[..j].iter().cloned());
        Formula::mem(ys[j].clone(), Term::apply(d.spec.base.ctors[0].args[j], a))
    };
    let trunc_at = |j: usize| {
        Formula::mem(
            pt.clone(),
            Term::apply(
                f.tr.trunc,
                vec![fam.carrier.ty_of(&ps, &child(j)).expect("ind(p,d⃗ⱼ)")],
            ),
        )
    };
    let ih_at = |j: usize| Formula::mem(pt.clone(), motive_app(&s, &tm, &child(j), &pt));

    let want = vec![plain(0), trunc_at(0), plain(1), trunc_at(1), ih_at(0), ih_at(1)];
    assert_eq!(rr.minor_atoms[0], want, "declared order, then the hypotheses");

    // The carrier's own order is a *different* list, at three positions.
    let carrier_order = vec![plain(0), plain(1), trunc_at(0), trunc_at(1), ih_at(0), ih_at(1)];
    assert_ne!(rr.minor_atoms[0], carrier_order, "the mask interleaves, so the two disagree");
    assert_eq!(
        rr.minor_atoms[0],
        trunc_minor_atoms_at(&s, &f.tr, &d.spec, &fam.carrier, 0, &tm, &ps, &ys)
            .expect("the accessor rebuilds the same list"),
    );
    assert!(rr.rec.hyps().is_empty() && closed_f(rr.rec.concl()));
}

/// [`interleaved`] with a **third** recursive argument, at a third distinct
/// child index — mask `Plain, Rec, Plain, Rec, Rec`.
///
/// The two `Rec` slots after the second plain field see the same binders, which
/// is what makes their child symbols the same arity and their *values* the only
/// thing telling them apart. That is deliberate: it is the case where a walk
/// that took the wrong slot would still be well typed.
fn interleaved3(env: &mut Env, mach: &Machine) -> Decl {
    let s = &mach.wt.sums;
    let nat = mach.syms.finord(s, 3).expect("finord(3)");
    let pt = s.point();
    let zero = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let succ = mach.syms.inj(1, pt.clone()).expect("Inj₁");
    let two = mach.syms.inj(2, pt).expect("Inj₂");
    let (i0, i0_ax) = abbrev(env, 1, |_| nat.clone());
    let (b0, b0_ax) = abbrev(env, 1, |_| nat.clone());
    let (b1, b1_ax) = abbrev(env, 2, |_| nat.clone());
    let (d0, _) = abbrev(env, 2, |a| a[1].clone()); // the first Rec sees y₀
    let (d1, _) = abbrev(env, 3, |_| zero.clone()); // the second sees y₀, y₁
    let (d2, _) = abbrev(env, 3, |_| succ.clone()); // and so does the third
    let (e0, e0_ax) = abbrev(env, 3, |_| two.clone());
    Decl {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(
                1,
                vec![CtorSpec::with_order(
                    vec![b0, b1],
                    3,
                    vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec, Slot::Rec],
                )
                .expect("a consistent mask")],
            ),
            vec![i0],
            vec![CtorIndices {
                result: vec![e0],
                rec_args: vec![vec![d0], vec![d1], vec![d2]],
            }],
        ),
        ity_ax: vec![i0_ax],
        beta_ax: vec![vec![b0_ax, b1_ax]],
        res_ax: vec![vec![e0_ax]],
    }
}

/// **Three recursive arguments, because two cannot see a clamp.**
///
/// `IndexedTruncRecursor::over_family` walks the recursive slots at three index
/// maps — `childs[j]` for the truncated atom, `childs[j]` again for the
/// induction hypothesis at the child's own indices, and `ts[j]` for the element
/// `good_of` is fired at. Every fixture in this file has `mᵢ ≤ 2`, and so does
/// every class-(P) declaration in the repository. Measured at that coverage: the
/// clamp `j ↦ min(j,1)` at each of those three sites **passed all 868 tests**,
/// while the whole point of [`interleaved`] is that it catches a permutation.
/// A permutation of two moves both slots; a clamp is the identity on `{0,1}`,
/// so the third slot is what makes the map observable — the same reason
/// `SCOPING.md` §6 gives at `le_index`, and the same reason
/// `family_trunc.rs::the_truncated_rule_is_positional_at_three_recursive_arguments`
/// exists one layer down, at the carrier's own rule.
#[test]
fn the_minor_atoms_are_positional_at_three_recursive_arguments() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = interleaved3(&mut env, &mach);
    assert!(d.spec.well_formed(), "the three-recursive-argument spec is well formed");

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the indexed family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let rr = IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc)
        .expect("three recursive arguments, interleaved");

    let s = f.mach.wt.sums.clone();
    let pt = s.point();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let tm = Term::var(rr.motive);
    assert_eq!(rr.minor_vars[0].len(), 2, "two plain binders, and no `∀r⃗`");
    let ys: Vec<Term> = rr.minor_vars[0].iter().map(|v| Term::var(*v)).collect();

    let child = |j: usize| d.spec.rec_index_vec(0, j, &ps, &ys).expect("d⃗ⱼ");
    let child_set =
        |j: usize| fam.carrier.ty_of(&ps, &child(j)).expect("ind(p,d⃗ⱼ)");
    assert!(
        child_set(0) != child_set(1)
            && child_set(1) != child_set(2)
            && child_set(0) != child_set(2),
        "the three children are three different sets, so a mis-index is a wrong theorem"
    );

    let plain = |j: usize| {
        let mut a = ps.clone();
        a.extend(ys[..j].iter().cloned());
        Formula::mem(ys[j].clone(), Term::apply(d.spec.base.ctors[0].args[j], a))
    };
    let trunc_at =
        |j: usize| Formula::mem(pt.clone(), Term::apply(f.tr.trunc, vec![child_set(j)]));
    let ih_at = |j: usize| Formula::mem(pt.clone(), motive_app(&s, &tm, &child(j), &pt));

    // Declared field order — `Plain, Rec, Plain, Rec, Rec` — then the three
    // induction hypotheses, in slot order.
    let want = vec![
        plain(0),
        trunc_at(0),
        plain(1),
        trunc_at(1),
        trunc_at(2),
        ih_at(0),
        ih_at(1),
        ih_at(2),
    ];
    assert_eq!(rr.minor_atoms[0], want, "declared order, then the three hypotheses");
    assert_eq!(
        rr.minor_atoms[0],
        trunc_minor_atoms_at(&s, &f.tr, &d.spec, &fam.carrier, 0, &tm, &ps, &ys)
            .expect("the accessor rebuilds the same list"),
    );
    assert!(rr.rec.hyps().is_empty() && closed_f(rr.rec.concl()));
}

// ─────────────────────────────────────────────────────────────────────────────
// Three index slots, a 3-cycle, and a concrete motive
// ─────────────────────────────────────────────────────────────────────────────

/// Which field feeds slot `k`, and with which tag.
const CYCLE: [usize; 3] = [1, 2, 0];

/// ```text
/// P3 (α : Type) : α → α → α → Prop
///   | mk : ∀ (a b c : Unit). P3 α (Inj₁ b) (Inj₂ c) (Inj₀ a)
/// ```
///
/// The fields are typed at the **unit set**, which is what makes `MINOR₀`'s
/// `∀y⃗` dischargeable at a one-point motive; each slot carries a *different*
/// injection tag, so the index vector the constructor reaches is one concrete
/// triple and the 3-cycle is visible in it. Bare-variable indices over a full
/// index type would be surjective and the motive would have to be total.
fn cycle3(env: &mut Env, mach: &Machine) -> Decl {
    let s = mach.wt.sums.clone();
    let one = s.unit();
    let (mut indices, mut ity_ax) = (Vec::new(), Vec::new());
    let (mut args, mut beta_ax) = (Vec::new(), Vec::new());
    let (mut result, mut res_ax) = (Vec::new(), Vec::new());
    for k in 0..3 {
        let (i, ax) = abbrev(env, 1 + k, |a| a[0].clone());
        indices.push(i);
        ity_ax.push(ax);
        let o = one.clone();
        let (b, bax) = abbrev(env, 1 + k, move |_| o.clone());
        args.push(b);
        beta_ax.push(bax);
    }
    for &j in &CYCLE {
        let tag = mach.syms.inj_sym(j).expect("Inj_j's symbol");
        let (e, eax) = abbrev(env, 4, move |a| Term::apply(tag, vec![a[1 + j].clone()]));
        result.push(e);
        res_ax.push(eax);
    }
    Decl {
        spec: IndexedDeclSpec::new(
            DeclSpec::new(1, vec![CtorSpec::new(args, 0)]),
            indices,
            vec![CtorIndices::nonrecursive(result)],
        ),
        ity_ax,
        beta_ax: vec![beta_ax],
        res_ax: vec![res_ax],
    }
}

/// **The rule fires, end to end, at a concrete motive** — and its antecedent is
/// load-bearing.
///
/// Three slots and a 3-cycle, not two and a swap: a transposition is its own
/// inverse, so nothing at `ni = 2` can tell a permutation from its inverse, and
/// the `ni` Leibniz steps that carry a minor's conclusion from `e⃗ᵢ` to `x⃗` are
/// exactly the loop where an order goes wrong silently.
#[test]
fn the_indexed_class_p_rule_fires_at_a_concrete_motive() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = cycle3(&mut env, &mach);
    assert!(d.spec.well_formed());

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("the indexed family");
    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let rr = IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc)
        .expect("the indexed class-(P) recursor");

    let s = f.mach.wt.sums.clone();
    let (one, pt, zero) = (s.unit(), s.point(), s.zero());
    let three = f.mach.syms.finord(&s, 3).expect("finord(3)");
    let injs: Vec<Term> =
        (0..3).map(|k| f.mach.syms.inj(k, pt.clone()).expect("Inj_k")).collect();
    let alpha = vec![three.clone()];
    let pts = vec![pt.clone(); 3];
    // The index vector the constructor reaches: the 3-cycle of the tags.
    let image: Vec<Term> = CYCLE.iter().map(|&j| injs[j].clone()).collect();
    assert_eq!(image, vec![injs[1].clone(), injs[2].clone(), injs[0].clone()]);

    // ── `MINOR₀` at the motive whose value there is `v` ─────────────────────
    //
    // Under the three field typings each `yⱼ ∈ 1`, hence `yⱼ = •`, so the
    // conclusion's index vector collapses to `e⃗(α,•,•,•)` and the motive need
    // only be defined at that one triple.
    // `MINORᵢ` is stated at the declaration's parameter *variable*; a consumer
    // holds an interpretation, so everything below is at `p := finord(3)`.
    let pv = ind.params[0];
    let yvs = rr.minor_vars[0].clone();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let atoms: Vec<Formula> =
        rr.minor_atoms[0].iter().map(|a| a.subst(pv, &three)).collect();
    assert_eq!(atoms.len(), 3, "three plain typings, no recursion");
    let hyp = conj_of(&atoms).expect("three atoms");
    let minor_want = |m: &Term| rr.minors[0].subst(pv, &three).subst(rr.motive, m);

    // The parameter followed by the three fields at `•` — the argument list
    // every `e_k`, `βⱼ` and constructor rule is instantiated at below.
    let cargs = {
        let mut a = alpha.clone();
        a.extend(pts.iter().cloned());
        a
    };

    let concl_at = |ys: &[Term], m: &Term| -> Formula {
        let res = d.spec.result_vec(0, &alpha, ys).expect("e⃗");
        Formula::mem(pt.clone(), motive_app(&s, m, &res, &pt))
    };

    // `⊢ H → yⱼ = •`, one per field.
    let to_pt: Vec<Thm> = (0..3)
        .map(|j| {
            let mut a = alpha.clone();
            a.extend(ys[..j].iter().cloned());
            let unfold = inst_all(&d.beta_ax[0][j], &a).expect("βⱼ(α,…) = 1");
            let in_one = rw(
                &mut env,
                &unfold,
                |t| {
                    Formula::imp(
                        Formula::mem(ys[j].clone(), Term::apply(d.spec.base.ctors[0].args[j], a.clone())),
                        Formula::mem(ys[j].clone(), t),
                    )
                },
                &imp_refl(atoms[j].clone()),
            );
            syl(
                &syl(&conj_proj(&atoms, j).expect("project"), &in_one).expect("syl"),
                &inst_all(&s.unit_eta, std::slice::from_ref(&ys[j])).expect("unit η"),
            )
            .expect("yⱼ = •")
        })
        .collect();

    // The minor, at a caller-chosen leaf value. The motive is keyed on the
    // **image** — the concrete tag triple — so that `PointFun::app` reduces at
    // it directly; the minor's own conclusion is at `e⃗(α,y⃗)`, and the two are
    // bridged by the result symbols' defining equations.
    let res_pts = d.spec.result_vec(0, &alpha, &pts).expect("e⃗(α,•,•,•)");
    let minor_of = |env: &mut Env, leaf: &Term, leaf_mem: &Thm| -> (Term, Thm) {
        let ptc = pt.clone();
        let (m, mut cur) = at_motive(
            env,
            &s,
            &f.pf,
            &image,
            leaf,
            &move |t| Formula::mem(ptc.clone(), t),
            leaf_mem,
        );
        // `image` back to `e⃗(α,•,•,•)`, slot by slot.
        let mut slots = image.clone();
        for k in (0..3).rev() {
            let eq = inst_all(&d.res_ax[0][k], &cargs).expect("e_k unfolds");
            slots[k] = res_pts[k].clone();
            let (cur_slots, sc, mc, ptc) = (slots.clone(), s.clone(), m.clone(), pt.clone());
            cur = rw_back(
                env,
                &eq,
                move |h| {
                    let mut v = cur_slots.clone();
                    v[k] = h;
                    Formula::mem(ptc.clone(), motive_app(&sc, &mc, &v, &ptc))
                },
                &cur,
            );
        }
        // Lift under `H` and put the field variables back, one at a time.
        let mut cur = a1i(&cur, hyp.clone());
        for j in 0..3 {
            let back = hyp_eq_symm(env, &to_pt[j]);
            let mut slots = pts.clone();
            slots[..j].clone_from_slice(&ys[..j]);
            let mc = m.clone();
            cur = rw_h(
                env,
                &back,
                |h| {
                    let mut v = slots.clone();
                    v[j] = h;
                    concl_at(&v, &mc)
                },
                &cur,
            );
        }
        (m, gen_all(&yvs, &cur))
    };

    // ── positive: leaf `1`, and the rule fires to a closed theorem ──────────
    let unit_mem = s.unit_mem.clone();
    let (m1, minor1) = minor_of(&mut env, &one, &unit_mem);
    assert_eq!(*minor1.concl(), minor_want(&m1), "MINOR₀ at this motive");
    assert!(minor1.hyps().is_empty() && closed_f(minor1.concl()));

    let at = inst_all(&rr.rec, &[three.clone(), m1.clone()]).expect("at α and m");
    let fired = Thm::mp(&at, &conj_thms(&[minor1])).expect("the one minor");

    // `• ∈ ‖ind(α, Inj₁•, Inj₂•, Inj₀•)‖` — the carrier is inhabited there, so
    // the `∀x⃗∀t` is not decoration.
    let mut ctor_atoms: Vec<Thm> = Vec::new();
    for j in 0..3 {
        let mut a = alpha.clone();
        a.extend(pts[..j].iter().cloned());
        let unfold = inst_all(&d.beta_ax[0][j], &a).expect("βⱼ = 1");
        ctor_atoms.push(rw_back(&mut env, &unfold, |t| Formula::mem(pt.clone(), t), &s.unit_mem));
    }
    for k in 0..3 {
        let mut a = alpha.clone();
        a.extend(res_pts[..k].iter().cloned());
        let set = Term::apply(d.spec.indices[k], a.clone());
        let ity = inst_all(&d.ity_ax[k], &a).expect("ι_k(α,…) = α");
        let base = inj_pt_mem(&f.mach, 3, CYCLE[k]);
        let v = injs[CYCLE[k]].clone();
        let at_set = rw_back(&mut env, &ity, move |x| Formula::mem(v.clone(), x), &base);
        let e = inst_all(&d.res_ax[0][k], &cargs).expect("e_k unfolds");
        ctor_atoms.push(rw_back(&mut env, &e, move |x| Formula::mem(x, set.clone()), &at_set));
    }
    let mut in_carrier = Thm::mp(
        &inst_all(&tc.ctors[0].mem, &cargs).expect("the constructor rule at α and •,•,•"),
        &conj_thms(&ctor_atoms),
    )
    .expect("the typings discharge it");

    // Unfold `e⃗(α,•,•,•)` to the concrete image, slot by slot.
    let mut slots = res_pts.clone();
    for k in 0..3 {
        let eq = inst_all(&d.res_ax[0][k], &cargs).expect("e_k unfolds");
        let (cur, trunc, alphac, ptc) =
            (slots.clone(), f.tr.trunc, alpha.clone(), pt.clone());
        let ixc = fam.carrier.ty;
        in_carrier = rw(
            &mut env,
            &eq,
            move |h| {
                let mut v = cur.clone();
                v[k] = h;
                let mut a = alphac.clone();
                a.extend(v);
                Formula::mem(ptc.clone(), Term::apply(trunc, vec![Term::apply(ixc, a)]))
            },
            &in_carrier,
        );
        slots[k] = injs[CYCLE[k]].clone();
    }
    assert_eq!(slots, image, "the constructor reaches the 3-cycle, in that order");

    let mut ia = image.clone();
    ia.push(pt.clone());
    let out = Thm::mp(
        &inst_all(&fired, &ia).expect("at the image and t := •"),
        &in_carrier,
    )
    .expect("the point is in the carrier there");
    assert_eq!(
        *out.concl(),
        Formula::mem(pt.clone(), motive_app(&s, &m1, &image, &pt)),
        "⊢ • ∈ app(m, Inj₁•, Inj₂•, Inj₀•, •)"
    );
    assert!(out.hyps().is_empty() && closed_f(out.concl()), "closed and unconditional");

    // ── negative: the same theorem at leaf `0`, and the minor is refutable ──
    //
    // The rule is not satisfied by every motive: at the motive whose value is
    // the empty set, its own conclusion refutes the minor.
    let not_in_zero = inst_all(&s.ap.empty_ax, std::slice::from_ref(&pt)).expect("¬(• ∈ 0)");
    let ptc = pt.clone();
    let (m0, zero_at) = at_motive(
        &mut env,
        &s,
        &f.pf,
        &image,
        &zero,
        &move |t| Formula::not(Formula::mem(ptc.clone(), t)),
        &not_in_zero,
    );
    let hyp0 = minor_want(&m0);
    let at0 = inst_all(&rr.rec, &[three, m0.clone()]).expect("at α and m₀");
    let hit = hyp_mp(&hyp_inst(&at0, &ia), &a1i(&in_carrier, hyp0.clone()))
        .expect("the carrier membership");
    assert_eq!(
        *hit.concl(),
        Formula::imp(hyp0.clone(), Formula::mem(pt.clone(), motive_app(&s, &m0, &image, &pt)))
    );
    let refuted = syl(&hit, &zero_at).expect("⊥");
    assert_eq!(
        *refuted.concl(),
        Formula::not(hyp0),
        "⊢ ¬MINOR₀ at the motive whose value is 0 — the antecedent is not decoration"
    );
    assert!(refuted.hyps().is_empty() && closed_f(refuted.concl()));
}

// ─────────────────────────────────────────────────────────────────────────────

/// **The truncation has to be *this* family's.** A `TruncCarrier` over another
/// declaration, or over a non-indexed one, is refused rather than eliminated
/// into the wrong induction; and the matching pair builds, which is what a
/// mutation of the index spine breaks.
///
/// The two refusals are *behavioural* pins rather than guard pins: there is no
/// provenance check on `tc` — one was written and removed, because deleting it
/// changed nothing — and what actually refuses is that `TruncCarrier`'s
/// `only_point` and `elim` are compared against the carrier the build rebuilds
/// from the family itself. The non-indexed case is the reachable spelling of
/// "`ni = 0` is `trunc_rec`'s".
#[test]
fn the_recursor_refuses_a_truncation_of_another_declaration() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let d = sort_elim_prop2(&mut env, &mach);
    let e = cycle3(&mut env, &mach);

    let ind = Inductive::build(&mut env, &mut mach, &d.spec.base).expect("072's skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &d.spec, &f.rc, &f.iota, &f.funspace)
            .expect("072's family");
    let ind2 = Inductive::build(&mut env, &mut mach, &e.spec.base).expect("P3's skeleton");
    let fam2 =
        IndexedInductive::build(&mut env, &mut mach, &ind2, &e.spec, &f.rc, &f.iota, &f.funspace)
            .expect("P3's family");

    let tc = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind, &fam.carrier)
        .expect("072's carrier");
    let tc2 = TruncCarrier::over_family(&mut env, &mach, &f.tow, &f.tr, &ind2, &fam2.carrier)
        .expect("P3's carrier");
    let flat = Inductive::build(&mut env, &mut mach, &DeclSpec::new(0, vec![CtorSpec::nullary()]))
        .expect("a non-indexed declaration");
    let tc0 = TruncCarrier::over_declaration(&mut env, &mach, &f.tow, &f.tr, &flat)
        .expect("its non-indexed carrier");
    let f = Fix { mach, ..f };

    assert!(
        IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc).is_some(),
        "the matching pair builds"
    );
    assert!(
        IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc2).is_none(),
        "another family's truncation is not this family's carrier"
    );
    assert!(
        IndexedTruncRecursor::over_family(&mut env, &f.mach, &f.tr, &ind, &fam, &tc0).is_none(),
        "a non-indexed truncation belongs to `trunc_rec`"
    );
}
