//! **Class (S)'s ι rule at `ni = 0`** — `derived/src/inductive/family/le_prop_rec.rs`.
//!
//! `LeRecursor::build` refuses `ni = 0`, and the reason is not a missing case:
//! at `ni = 0` the index tuple is `•` for every constructor and every field
//! assignment, so `rec_acc`'s step is addressed by nothing while Lean's minor
//! is still addressed by the fields. What bridges them is §5.3's own side
//! condition — with no result index, every field is propositional — and that is
//! `LePropRecursor::erase`.
//!
//! Four things are pinned here:
//!
//! 1. the shapes, at `And` (two fields) and at `PUnit` (none), so the
//!    empty-antecedent case sits beside the conditional one;
//! 2. **that it computes**: ι fired closed, at a minor that is a genuine
//!    two-argument graph, landing on the minor's *value*. Twice, at two
//!    different values, with `⊢ ¬(∅ = 1)` separating them — a recursor that
//!    computed to a constant would satisfy one of those and fail the other;
//! 3. field erasure at **three** distinct field assignments, so "the minor does
//!    not see its fields" is not read off a single point;
//! 4. the negative half: an indexed spec, a two-constructor one, a recursive
//!    one and a constructorless one are all refused.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::acc::Acc;
use derived::bound::Bound;
use derived::inductive::family::le_prop_rec::{rec_term, LePropRecursor};
use derived::inductive::family::{
    CtorIndices, IndexSpace, IndexedDeclSpec, LeCarrier, LeProp,
};
use derived::inductive::{CtorSpec, DeclSpec, Machine};
use derived::point_fun::PointFun;
use derived::wtype::Wtype;
use derived::{and_intro, conj_of, inst_all, sums::Sums};

struct Fix {
    mach: Machine,
    ac: Acc,
    pf: PointFun,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    let ac = Acc::with_apply(env, &sums.ap).expect("acc over the same pairing");
    let pf = PointFun::over(env, &sums, &mach.wt.app_pair).expect("the one-point function");
    Fix { mach, ac, pf }
}

fn abbrev(env: &mut Env, arity: usize, body: impl Fn(&[Term]) -> Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = body(&args);
    derived::define_abbrev(env, &vars, &t).expect("an abbreviation")
}

/// `βⱼ(p⃗, y⃗<ⱼ) = p_which` — what `And`'s two fields are.
fn proj_field(env: &mut Env, np: usize, j: usize, which: usize) -> (FnSym, Thm) {
    abbrev(env, np + j, move |a| a[which].clone())
}

fn nonindexed(np: usize, ctors: Vec<CtorSpec>) -> IndexedDeclSpec {
    let n = ctors.len();
    IndexedDeclSpec::new(
        DeclSpec::new(np, ctors),
        Vec::new(),
        (0..n).map(|_| CtorIndices::nonrecursive(Vec::new())).collect(),
    )
}

fn stack(
    env: &mut Env,
    f: &mut Fix,
    spec: &IndexedDeclSpec,
    params: &[FreeVar],
) -> (IndexSpace, LeCarrier, LeProp) {
    let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    let ix = IndexSpace::build(env, &mut f.mach, spec, &ps).expect("the one-point index space");
    let lc = LeCarrier::build(env, &f.mach, &f.ac, spec, &ix, params).expect("the (S) carrier");
    let lp = LeProp::build(env, &f.mach, spec, &ix, &lc, params).expect("the prop reading");
    (ix, lc, lp)
}

/// `app(app(m, a), b)`, the two-field minor spine.
fn app2(s: &Sums, m: &Term, a: &Term, b: &Term) -> Term {
    s.ap.apply(s.ap.apply(m.clone(), a.clone()), b.clone())
}

/// `⊢ βⱼ(args) ⊆ 1` from `⊢ βⱼ(args) = 1`.
fn subset_unit_from_eq(env: &mut Env, s: &Sums, def_eq: &Thm) -> Thm {
    let (lhs, rhs) = def_eq.concl().as_eq().expect("a defining equation");
    assert_eq!(rhs, s.unit(), "the field's type really is `1`");
    let want = kernel::thm::subset(env, s.unit(), s.unit());
    let refl = {
        let v = env.fresh_var();
        Thm::gen(v, &derived::imp_refl(Formula::mem(Term::var(v), s.unit())))
    };
    assert_eq!(*refl.concl(), want);
    let back = derived::eq_symm(env, def_eq).expect("symm");
    let hole = env.fresh_var();
    let ctx = kernel::thm::subset(env, Term::var(hole), s.unit());
    Thm::mp(&Thm::mp(&Thm::eq_leibniz(rhs, lhs, hole, ctx), &back).expect("mp"), &refl)
        .expect("mp")
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. The shapes, at `And` and at `PUnit`.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole interface at an `And`-shaped declaration: two fields, no
/// recursion, no indices.
#[test]
fn a_two_field_non_indexed_subsingleton_has_a_lean_shaped_iota() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let (b0, _) = proj_field(&mut env, 2, 0, 0);
    let (b1, _) = proj_field(&mut env, 2, 1, 1);
    let spec = nonindexed(2, vec![CtorSpec::new(vec![b0, b1], 0)]);
    let params: Vec<FreeVar> = (0..2).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    let (ix, lc, lp) = stack(&mut env, &mut f, &spec, &params);
    let s = f.mach.wt.sums.clone();

    let r = LePropRecursor::build(&mut env, &f.mach, &f.pf, &spec, &ix, &lc, &lp, &params)
        .expect("the ni = 0 recursor");
    assert!(r.all_unconditional(), "every rule rests on nothing");
    assert_eq!(r.fields.len(), 2);

    let (point, unit) = (s.point(), s.unit());
    let tm = Term::var(r.minor);
    let ys: Vec<Term> = r.fields.iter().map(|v| Term::var(*v)).collect();
    let rec = rec_term(&s, &spec, &tm).expect("the recursor term");
    assert_eq!(rec, PointFun::of(&s, point.clone(), app2(&s, &tm, &point, &point)));

    // ── `carrier_point` ────────────────────────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let cp = inst_all(&r.carrier_point, &[ps[0].clone(), ps[1].clone(), tz.clone()])
        .expect("at the parameters and a witness");
    assert_eq!(
        *cp.concl(),
        Formula::imp(Formula::mem(tz.clone(), lc.a_phi.clone()), Formula::eq(tz.clone(), point.clone())),
    );

    // ── `G`, in the order the header promises ──────────────────────────────
    //
    // Three or more elements, and their nesting: `P₀ ∧ (P₁ ∧ (H₀ ∧ H₁))`. The
    // `Hⱼ` run is contiguous and last, which is what lets a consumer holding
    // `LeCarrier::intro[0]` recover its antecedent with one `conj_sub`.
    let beta = |j: usize, ys: &[Term]| {
        let mut a = ps.clone();
        a.extend(ys[..j].iter().cloned());
        Term::apply(spec.base.ctors[0].args[j], a)
    };
    let sub = |t: Term, env: &mut Env| kernel::thm::subset(env, t, unit.clone());
    let atoms_at = |ys: &[Term], env: &mut Env| {
        vec![
            sub(beta(0, ys), env),
            sub(beta(1, ys), env),
            Formula::mem(ys[0].clone(), beta(0, ys)),
            Formula::mem(ys[1].clone(), beta(1, ys)),
        ]
    };
    let atoms = atoms_at(&ys, &mut env);
    let g = conj_of(&atoms).expect("k = 2, so G is present");
    assert_eq!(atoms.len(), 4);
    // The `Hⱼ` run is exactly `LeCarrier::intro[0]`'s antecedent at `ni = 0`.
    let intro = inst_all(&lc.intro[0], &[ps[0].clone(), ps[1].clone(), ys[0].clone(), ys[1].clone()])
        .expect("the introduction rule at our own variables");
    assert_eq!(
        intro.concl().as_imp().expect("conditional at k = 2").0,
        conj_of(&atoms[2..]).expect("the H run"),
    );
    assert_eq!(LeCarrier::intro_is_conditional(&spec, 0), Some(true));

    // ── `erase` ────────────────────────────────────────────────────────────
    let minor_y = app2(&s, &tm, &ys[0], &ys[1]);
    let minor_pt = app2(&s, &tm, &point, &point);
    let erase = r.erase.as_ref().expect("k = 2, so erasure is a statement");
    let erase_at = inst_all(erase, &[ps[0].clone(), ps[1].clone(), tm.clone(), ys[0].clone(), ys[1].clone()])
        .expect("at our own variables");
    assert_eq!(
        *erase_at.concl(),
        Formula::imp(g.clone(), Formula::eq(minor_y.clone(), minor_pt.clone())),
    );
    assert_ne!(minor_y, minor_pt, "the two sides are different terms");

    // ── ι, at the point and at any member ──────────────────────────────────
    let iota_pt = inst_all(&r.iota_at_point, &[ps[0].clone(), ps[1].clone(), tm.clone(), ys[0].clone(), ys[1].clone()])
        .expect("at our own variables");
    assert_eq!(
        *iota_pt.concl(),
        Formula::imp(
            g.clone(),
            Formula::eq(s.ap.apply(rec.clone(), point.clone()), minor_y.clone()),
        ),
    );

    let mut atoms2 = atoms.clone();
    atoms2.push(Formula::mem(tz.clone(), lc.a_phi.clone()));
    let iota = inst_all(
        &r.iota,
        &[ps[0].clone(), ps[1].clone(), tm.clone(), ys[0].clone(), ys[1].clone(), tz.clone()],
    )
    .expect("at our own variables");
    assert_eq!(
        *iota.concl(),
        Formula::imp(
            conj_of(&atoms2).expect("never empty"),
            Formula::eq(s.ap.apply(rec.clone(), tz.clone()), minor_y.clone()),
        ),
    );

    // ── Typing ─────────────────────────────────────────────────────────────
    let tt = Term::var(r.target);
    let typed = inst_all(&r.rec_typed, &[ps[0].clone(), ps[1].clone(), tm.clone(), tt.clone()])
        .expect("at our own variables");
    assert_eq!(
        *typed.concl(),
        Formula::imp(
            Formula::mem(minor_pt.clone(), tt.clone()),
            Formula::mem(rec.clone(), s.fs.of(unit.clone(), tt.clone())),
        ),
    );

    // ── Erasure at THREE distinct field assignments ────────────────────────
    //
    // A construction that read the fields would have to agree with the point at
    // each of them; a construction that only ever looked at `•` would agree
    // trivially, and the `assert_ne!`s below are what rule that out.
    let (u0, u1) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    for pair in [
        [point.clone(), u0.clone()],
        [u0.clone(), point.clone()],
        [u0.clone(), u1.clone()],
    ] {
        let at = inst_all(erase, &[ps[0].clone(), ps[1].clone(), tm.clone(), pair[0].clone(), pair[1].clone()])
            .expect("at this assignment");
        let atoms_here = atoms_at(&pair, &mut env);
        assert_eq!(
            *at.concl(),
            Formula::imp(
                conj_of(&atoms_here).expect("G here"),
                Formula::eq(app2(&s, &tm, &pair[0], &pair[1]), minor_pt.clone()),
            ),
        );
        assert_ne!(*at.concl(), *erase_at.concl(), "a different assignment is a different statement");
    }
}

/// `PUnit` — no fields, so `G` is **empty**, and this kernel has no `⊤` to
/// weaken it to. `erase` is absent and `iota_at_point` is unconditional; `iota`
/// is still conditional, because `z ∈ A_φ(p⃗)` is always in its antecedent.
#[test]
fn a_fieldless_constructor_has_no_antecedent_to_carry() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let spec = nonindexed(0, vec![CtorSpec::nullary()]);
    let (ix, lc, lp) = stack(&mut env, &mut f, &spec, &[]);
    let s = f.mach.wt.sums.clone();

    let r = LePropRecursor::build(&mut env, &f.mach, &f.pf, &spec, &ix, &lc, &lp, &[])
        .expect("the ni = 0 recursor");
    assert!(r.all_unconditional());
    assert!(r.fields.is_empty());
    assert!(r.erase.is_none(), "`⊢ m = m` is not a statement worth exporting");
    assert_eq!(LeCarrier::intro_is_conditional(&spec, 0), Some(false));

    let point = s.point();
    let tm = Term::var(r.minor);
    // At `k = 0` the minor spine is `m` itself and the recursor is `{⟨•, m⟩}`.
    let rec = rec_term(&s, &spec, &tm).expect("the recursor term");
    assert_eq!(rec, PointFun::of(&s, point.clone(), tm.clone()));

    let iota_pt = inst_all(&r.iota_at_point, std::slice::from_ref(&tm)).expect("at `m`");
    assert_eq!(
        *iota_pt.concl(),
        Formula::eq(s.ap.apply(rec.clone(), point.clone()), tm.clone()),
        "unconditional: there is no `⊤` standing in for an absent guard",
    );
    assert!(iota_pt.concl().as_imp().is_none(), "not an implication with an invented antecedent");

    // `iota` still has one conjunct — the major premise's membership.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let iota = inst_all(&r.iota, &[tm.clone(), tz.clone()]).expect("at `m` and `z`");
    assert_eq!(
        *iota.concl(),
        Formula::imp(
            Formula::mem(tz.clone(), lc.a_phi.clone()),
            Formula::eq(s.ap.apply(rec.clone(), tz.clone()), tm.clone()),
        ),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. It computes.
// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable.** ι fired **closed**, at a minor that is a genuine
/// two-argument graph, landing on the value the minor gives.
///
/// The declaration is `And 1 1` — both field types are the *one-point set*, so
/// `G` is discharged outright — and the minor is
/// `m(v) := {⟨•, {⟨•, v⟩}⟩}`, a curried pair of one-point functions. ι then
/// says `app(rec(m(v)), •) = v`, and the test runs it at `v := ∅` and at
/// `v := 1` and separates the two with `⊢ ¬(∅ = 1)`. A recursor that computed
/// to a constant would satisfy at most one of them.
#[test]
fn iota_computes_to_the_minor_and_not_to_a_constant() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let (point, unit) = (s.point(), s.unit());

    // `β₀() = 1` and `β₁(y₀) = 1` — closed, and inhabited by `•`.
    let (b0, b0_ax) = abbrev(&mut env, 0, |_| unit.clone());
    let (b1, b1_ax) = abbrev(&mut env, 1, |_| unit.clone());
    assert_ne!(b0, b1);
    let spec = nonindexed(0, vec![CtorSpec::new(vec![b0, b1], 0)]);
    let (ix, lc, lp) = stack(&mut env, &mut f, &spec, &[]);

    let r = LePropRecursor::build(&mut env, &f.mach, &f.pf, &spec, &ix, &lc, &lp, &[])
        .expect("the ni = 0 recursor");
    let tm = Term::var(r.minor);
    assert_eq!(r.fields.len(), 2);

    // ── Discharge `G` at `y₀ = y₁ = •` ─────────────────────────────────────
    let b0_at = inst_all(&b0_ax, &[]).expect("β₀() = 1");
    let b1_at = inst_all(&b1_ax, std::slice::from_ref(&point)).expect("β₁(•) = 1");
    let p0 = subset_unit_from_eq(&mut env, &s, &b0_at);
    let p1 = subset_unit_from_eq(&mut env, &s, &b1_at);
    let into = |env: &mut Env, def_eq: &Thm, mem: &Thm| {
        let (lhs, rhs) = def_eq.concl().as_eq().expect("an equation");
        let back = derived::eq_symm(env, def_eq).expect("symm");
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(rhs, lhs, hole, Formula::mem(point.clone(), Term::var(hole)));
        Thm::mp(&Thm::mp(&leib, &back).expect("mp"), mem).expect("mp")
    };
    let h0 = into(&mut env, &b0_at, &s.unit_mem);
    let h1 = into(&mut env, &b1_at, &s.unit_mem);
    let g_thm = and_intro(&p0, &and_intro(&p1, &and_intro(&h0, &h1)));
    assert!(g_thm.hyps().is_empty(), "G is discharged outright, not assumed");

    // ── ι at `y₀ = y₁ = •` ─────────────────────────────────────────────────
    let iota_pt = inst_all(&r.iota_at_point, &[tm.clone(), point.clone(), point.clone()])
        .expect("at `m` and the point twice");
    assert_eq!(iota_pt.concl().as_imp().expect("conditional").0, *g_thm.concl());
    let fired = Thm::mp(&iota_pt, &g_thm).expect("discharge G");
    let rec = rec_term(&s, &spec, &tm).expect("the recursor term");
    assert_eq!(
        *fired.concl(),
        Formula::eq(s.ap.apply(rec.clone(), point.clone()), app2(&s, &tm, &point, &point)),
    );
    assert!(fired.hyps().is_empty());

    // ── At two concrete minors ─────────────────────────────────────────────
    let land = |v: &Term, env: &mut Env| {
        // `m := {⟨•, {⟨•, v⟩}⟩}`, so `app(app(m,•),•) = v` by `point_app` twice.
        let inner = PointFun::of(&s, point.clone(), v.clone());
        let m = PointFun::of(&s, point.clone(), inner.clone());
        let outer_app = inst_all(&f.pf.app, &[point.clone(), inner.clone()]).expect("app(m,•)");
        let inner_app = inst_all(&f.pf.app, &[point.clone(), v.clone()]).expect("app(inner,•)");
        // `⊢ app(app(m,•),•) = v`: rewrite the function slot, then chain.
        let step = derived::congr_arg(
            env,
            s.ap.app,
            &[s.ap.apply(m.clone(), point.clone()), point.clone()],
            0,
            &outer_app,
        )
        .expect("rewrite the function slot");
        let spine = derived::eq_trans(env, &step, &inner_app).expect("chain");
        assert_eq!(*spine.concl(), Formula::eq(app2(&s, &m, &point, &point), v.clone()));

        // The same ι at this concrete minor, then transported along the spine.
        let at_m = derived::inst_all(
            &Thm::gen(r.minor, &fired),
            std::slice::from_ref(&m),
        )
        .expect("ι at this minor");
        let rec_m = rec_term(&s, &spec, &m).expect("the recursor at this minor");
        assert_eq!(
            *at_m.concl(),
            Formula::eq(s.ap.apply(rec_m.clone(), point.clone()), app2(&s, &m, &point, &point)),
        );
        let out = derived::eq_trans(env, &at_m, &spine).expect("chain");
        assert!(out.hyps().is_empty());
        assert_eq!(
            *out.concl(),
            Formula::eq(s.ap.apply(rec_m, point.clone()), v.clone()),
            "the recursor computes to the value the minor gives",
        );
        out
    };

    let at_zero = land(&point, &mut env);
    let at_unit = land(&unit, &mut env);
    // Two different values, and they are provably different: `⊢ ¬(∅ = 1)`.
    assert_ne!(*at_zero.concl(), *at_unit.concl());
    assert_eq!(*s.tags_distinct.concl(), Formula::not(Formula::eq(point.clone(), unit.clone())));
    // So the two recursors do not compute to the same thing.
    let (l0, _) = at_zero.concl().as_eq().expect("an equation");
    let (l1, _) = at_unit.concl().as_eq().expect("an equation");
    assert_ne!(l0, l1, "different minors give different recursors");
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. The negative half.
// ─────────────────────────────────────────────────────────────────────────────

/// Four specs this construction is **not** about, each refused rather than
/// answered with a vacuous theorem.
#[test]
fn indexed_multi_constructor_recursive_and_empty_specs_are_refused() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let unit = s.unit();

    // A working baseline, so the refusals below are about the spec and not
    // about the apparatus.
    let (b0, _) = abbrev(&mut env, 0, |_| unit.clone());
    let ok = nonindexed(0, vec![CtorSpec::new(vec![b0], 0)]);
    let (ix, lc, lp) = stack(&mut env, &mut f, &ok, &[]);
    assert!(LePropRecursor::build(&mut env, &f.mach, &f.pf, &ok, &ix, &lc, &lp, &[]).is_some());
    // …and a parameter-count mismatch on that very spec is refused.
    let stray = env.fresh_var();
    assert!(
        LePropRecursor::build(&mut env, &f.mach, &f.pf, &ok, &ix, &lc, &lp, &[stray]).is_none(),
        "parameter count",
    );

    // An **indexed** spec. `LeProp::build` refuses `ni ≥ 1` outright, so the
    // only way this call can be made is with a spec and a stack that disagree —
    // which is exactly what the guard is for.
    let (iota_ty, _) = abbrev(&mut env, 0, |_| unit.clone());
    let (res, _) = abbrev(&mut env, 1, |a| a[0].clone());
    let indexed = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0)]),
        vec![iota_ty],
        vec![CtorIndices::nonrecursive(vec![res])],
    );
    assert_eq!(indexed.num_indices(), 1);
    assert!(
        LePropRecursor::build(&mut env, &f.mach, &f.pf, &indexed, &ix, &lc, &lp, &[]).is_none(),
        "an indexed spec",
    );

    // Two constructors: at `ni = 0` both result indices are `•`, so no ι could
    // choose between their minors.
    let two = nonindexed(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let (ix2, lc2, lp2) = stack(&mut env, &mut f, &two, &[]);
    assert!(
        LePropRecursor::build(&mut env, &f.mach, &f.pf, &two, &ix2, &lc2, &lp2, &[]).is_none(),
        "two constructors",
    );

    // A carrier from a *different* declaration: `lp` and `lc` must describe the
    // same set, and a look-alike would make every equation speak about another.
    assert!(
        LePropRecursor::build(&mut env, &f.mach, &f.pf, &ok, &ix, &lc2, &lp, &[]).is_none(),
        "a carrier from another declaration",
    );
    assert!(
        LePropRecursor::build(&mut env, &f.mach, &f.pf, &ok, &ix, &lc, &lp2, &[]).is_none(),
        "a prop reading of another declaration",
    );

    // No constructor at all: `LeProp::false_` already gives `⊢ A_φ = 0`.
    let none = nonindexed(0, Vec::new());
    let (ix3, lc3, lp3) = stack(&mut env, &mut f, &none, &[]);
    assert!(
        LePropRecursor::build(&mut env, &f.mach, &f.pf, &none, &ix3, &lc3, &lp3, &[]).is_none(),
        "no constructor",
    );
    assert!(rec_term(&s, &none, &Term::var(env.fresh_var())).is_none());

    // A recursive field: its child index tuple is `•`, the same as its own
    // result index, so the edge would be a self loop and `acc` would be empty.
    let rec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::new(Vec::new(), 1)]),
        Vec::new(),
        vec![CtorIndices { result: Vec::new(), rec_args: vec![Vec::new()] }],
    );
    assert!(rec.well_formed(), "the spec itself is fine; it is the ι that is not");
    let (ix4, lc4, lp4) = stack(&mut env, &mut f, &rec, &[]);
    assert!(
        LePropRecursor::build(&mut env, &f.mach, &f.pf, &rec, &ix4, &lc4, &lp4, &[]).is_none(),
        "a recursive field",
    );
    assert!(rec_term(&s, &rec, &Term::var(env.fresh_var())).is_none());
}
