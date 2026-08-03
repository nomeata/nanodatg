//! The general recursor and its ι rules, exercised at the shapes the design
//! marks as the ones bugs hide behind (`RECURSOR-DESIGN.md` §4.4):
//!
//! * the **last** constructor of an `n = 3` declaration, not the first —
//!   injection-depth bugs hide at the end;
//! * `m ≥ 2` recursive arguments, **interleaved** with non-recursive ones
//!   (`Plain, Rec, Plain, Rec` — the `RBTree.red` mask, which is
//!   corpus-demanded, not hypothetical);
//! * `HYP` **discharged outright** and the ι rule fired to a closed,
//!   unconditional equation — the only thing standing between "derived" and
//!   "derived about nothing";
//! * two constructors with **identical argument types**, which share one
//!   telescope by cache design, so branch separation can only come from the
//!   injections.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::bound::Bound;
use derived::inductive::{
    applied_minor, carrier_at, premise, CtorSpec, DeclSpec, GenRecursor, Inductive, Machine, Slot,
};
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{and_intro, define_abbrev, eq_symm, eq_trans, inst_all};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// The whole apparatus: one machine, one W-recursor, its totality, ι and
/// function-space theorems — everything a declaration's recursor is derived
/// over, built once.
struct Fix {
    mach: Machine,
    rc: Recursor,
    iota: Thm,
    funspace: Thm,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mach = Machine::over(env, wt, bnd).expect("machine");
    let rc = Recursor::new(env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(env, &mach.wt, &rc, &total).expect("funspace");
    Fix { mach, rc, iota, funspace }
}

/// A constant argument-type symbol of the given arity, with value `1` — so
/// that `• ∈ βⱼ(…)` is derivable and every constructor hypothesis is
/// satisfiable at the witness.
fn const_unit_beta(env: &mut Env, mach: &Machine, arity: usize) -> (FnSym, Thm) {
    let vars: Vec<kernel::FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let one = mach.wt.sums.unit();
    define_abbrev(env, &vars, &one).expect("β")
}

/// `⊢ • ∈ βⱼ(args)`, from the constant abbreviation's defining equation.
fn point_in_beta(env: &mut Env, mach: &Machine, ax: &Thm, args: &[Term]) -> Thm {
    let s = &mach.wt.sums;
    let at = inst_all(ax, args).expect("β at args");
    let back = eq_symm(env, &at).expect("symm");
    let (one, beta) = back.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(one, beta, hole, Formula::mem(s.point(), Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, &back).expect("mp"), &s.unit_mem).expect("mp")
}

/// `⊢ minor_typedᵢ` at minor `sᵢ := • (= ∅)` and target `T := 1` — the `HYP`
/// witness. `app(∅, x) = ∅` unconditionally, so the whole application chain
/// collapses to `•`, which is in `1`; the antecedent is never used, which is
/// exactly what makes this witness derivable at every arity and mask.
fn empty_minor(env: &mut Env, mach: &Machine, ctor: &CtorSpec, ps: &[Term], w: &Term) -> Thm {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let (k, m) = (ctor.args.len(), ctor.recs);
    let pt = s.point();
    let one = s.unit();

    let yvs: Vec<kernel::FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let vvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();

    // The arguments in application order: the mask over (y⃗, t⃗), then v⃗.
    let mut args = Vec::new();
    let (mut pi, mut ri) = (0, 0);
    for sl in &ctor.order {
        match sl {
            Slot::Plain => {
                args.push(ys[pi].clone());
                pi += 1;
            }
            Slot::Rec => {
                args.push(ts[ri].clone());
                ri += 1;
            }
        }
    }
    args.extend(vs.iter().cloned());

    // `⊢ • x₀ … x_{l-1} = •`, one `app(∅, a) = ∅` per argument.
    let in_unit = if args.is_empty() {
        s.unit_mem.clone()
    } else {
        let mut cur =
            inst_all(&mach.wt.app_empty, std::slice::from_ref(&args[0])).expect("app_empty");
        for x in &args[1..] {
            let (lhs, _) = cur.concl().as_eq().expect("an equation");
            let hole = env.fresh_var();
            let spine = ap.apply(lhs.clone(), x.clone());
            let leib = Thm::eq_leibniz(
                lhs.clone(),
                pt.clone(),
                hole,
                Formula::eq(spine.clone(), ap.apply(Term::var(hole), x.clone())),
            );
            let lift = Thm::mp(&Thm::mp(&leib, &cur).expect("mp"), &Thm::eq_refl(spine))
                .expect("mp");
            let step = inst_all(&mach.wt.app_empty, std::slice::from_ref(x)).expect("app_empty");
            cur = eq_trans(env, &lift, &step).expect("trans");
        }
        // Carry `• ∈ 1` back along `chain = •`.
        let back = eq_symm(env, &cur).expect("symm");
        let (l, r) = back.concl().as_eq().expect("an equation");
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(l, r, hole, Formula::mem(Term::var(hole), one.clone()));
        Thm::mp(&Thm::mp(&leib, &back).expect("mp"), &s.unit_mem).expect("mp")
    };

    // Under the (unused) atoms, generalised.
    let mut atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.to_vec();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    atoms.extend(ts.iter().map(|t| Formula::mem(t.clone(), w.clone())));
    atoms.extend(vs.iter().map(|v| Formula::mem(v.clone(), one.clone())));
    let body = match derived::conj_of(&atoms) {
        Some(h) => derived::a1i(&in_unit, h),
        None => in_unit,
    };
    let mut quant = yvs;
    quant.extend(tvs);
    quant.extend(vvs);
    let out = derived::gen_all(&quant, &body);
    assert_eq!(
        *out.concl(),
        premise::minor_typed(env, s, ctor, ps, w, &pt, &one),
        "the witness derivation drifted from the HYP builder"
    );
    out
}

/// Right-nested conjunction of closed theorems, matching `conj_of`.
fn conj_thms(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = and_intro(t, &acc);
    }
    acc
}

/// The witness declaration: `np = 1`, three constructors, the **last** one
/// carrying the `RBTree.red` mask `Plain, Rec, Plain, Rec`.
fn witness_spec(env: &mut Env, mach: &Machine) -> (DeclSpec, Thm, Thm) {
    let (b0, b0_ax) = const_unit_beta(env, mach, 1);
    let (b1, b1_ax) = const_unit_beta(env, mach, 2);
    let c0 = CtorSpec::nullary();
    let c1 = CtorSpec::new(vec![], 1);
    let c2 = CtorSpec::with_order(
        vec![b0, b1],
        2,
        vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
    )
    .expect("a consistent mask");
    (DeclSpec::new(1, vec![c0, c1, c2]), b0_ax, b1_ax)
}

/// The mask is a real input: an inconsistent one is refused, at both doors.
#[test]
fn an_inconsistent_mask_is_declined() {
    let mut env = Env::new();
    let mach = Machine::new(&mut env).expect("machine");
    let (b0, _) = const_unit_beta(&mut env, &mach, 0);
    assert!(CtorSpec::with_order(vec![b0], 1, vec![Slot::Plain]).is_none());
    let mut bad = CtorSpec::new(vec![b0], 1);
    bad.order = vec![Slot::Rec, Slot::Rec];
    let spec = DeclSpec::new(0, vec![bad]);
    assert!(!spec.well_formed());
    let mut mach = mach;
    assert!(Inductive::build(&mut env, &mut mach, &spec).is_none());
}

/// The ι statement at the last, interleaved constructor: instantiated at
/// fresh variables it is *exactly* `(HYP ∧ H₂^ctor) → grec(ctor₂ y₀ t₀ y₁ t₁)
/// = s₂ y₀ t₀ y₁ t₁ (grec t₀) (grec t₁)` — the mask order, not
/// fields-then-recs, and the recursive calls live.
#[test]
fn the_interleaved_iota_statement_is_the_mask_order() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (spec, _, _) = witness_spec(&mut env, &mach);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the witness declaration");
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    let s = &mach.wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..9).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (p, s0, s1, s2, t) = (&ts[0], &ts[1], &ts[2], &ts[3], &ts[4]);
    let (y0, y1, t0, t1) = (&ts[5], &ts[6], &ts[7], &ts[8]);

    let at = inst_all(&gr.iota[2], &[
        p.clone(), s0.clone(), s1.clone(), s2.clone(), t.clone(),
        y0.clone(), y1.clone(), t0.clone(), t1.clone(),
    ])
    .expect("instantiate ι₂");

    // Rebuild the whole expected implication from scratch.
    let ps = [p.clone()];
    let minors = [s0.clone(), s1.clone(), s2.clone()];
    let (_, _, _, w) = carrier_at(&mach, &ind, &ps).expect("carrier parts");
    let hyp = premise::hyp_of(&mut env, s, &spec.ctors, &ps, &w, &minors, t).expect("HYP");
    let carrier = ind.ty_of(vec![p.clone()]);
    let atoms = [
        Formula::mem(y0.clone(), Term::apply(spec.ctors[2].args[0], vec![p.clone()])),
        Formula::mem(y1.clone(), Term::apply(spec.ctors[2].args[1], vec![p.clone(), y0.clone()])),
        Formula::mem(t0.clone(), carrier.clone()),
        Formula::mem(t1.clone(), carrier),
    ];
    let grec = gr
        .rec_of(&mach, &ind, &f.rc, &ps, &minors, t)
        .expect("the recursor term");
    let ctor = ind
        .ctor_term(&mach, 2, &[y0.clone(), y1.clone()], &[t0.clone(), t1.clone()])
        .expect("ctor₂");
    let ihs = [ap.apply(grec.clone(), t0.clone()), ap.apply(grec.clone(), t1.clone())];
    let rhs = applied_minor(
        ap,
        &spec.ctors[2].order,
        s2,
        &[y0.clone(), y1.clone()],
        &[t0.clone(), t1.clone()],
        &ihs,
    );
    let lhs = ap.apply(grec, ctor);
    let expected = Formula::imp(
        Formula::and(hyp, derived::conj_of(&atoms).expect("H₂")),
        Formula::eq(lhs.clone(), rhs.clone()),
    );
    assert_eq!(*at.concl(), expected, "ι₂'s statement is not the rebuilt one");
    assert_ne!(lhs, rhs, "ι₂ would be reflexivity");

    // The mis-spelling the mask exists to rule out: fields first, recs after.
    let wrong = applied_minor(
        ap,
        &CtorSpec::new(spec.ctors[2].args.clone(), 2).order,
        s2,
        &[y0.clone(), y1.clone()],
        &[t0.clone(), t1.clone()],
        &ihs,
    );
    assert_ne!(rhs, wrong, "the mask made no difference — the interleaving is lost");
}

/// **The non-vacuity witness**: `HYP` discharged outright at `T := 1`,
/// minors `:= •`, parameter `:= 1`, and ι fired at the **last** constructor
/// with `n = 3`, `m = 2` and the interleaved mask, to a **closed,
/// unconditional** equation whose right side still mentions the recursor.
#[test]
fn hyp_is_discharged_and_the_last_interleaved_iota_fires_closed() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (spec, b0_ax, b1_ax) = witness_spec(&mut env, &mach);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the witness declaration");
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    let s = &mach.wt.sums;
    let ap = &s.ap;
    let (one, pt) = (s.unit(), s.point());
    let ps = [one.clone()];
    let minors = [pt.clone(), pt.clone(), pt.clone()];
    let (_, _, _, w) = carrier_at(&mach, &ind, &ps).expect("carrier parts");

    // The recursive-argument witness: the nullary constructor, closed.
    let c0 = ind.ctor_term(&mach, 0, &[], &[]).expect("ctor₀");
    let c0_mem = inst_all(&ind.ctors[0].mem, std::slice::from_ref(&one)).expect("ctor₀ ∈ ind(1)");
    assert!(closed(c0_mem.concl()));

    // ── HYP, discharged conjunct by conjunct ────────────────────────────────
    let hyp_thm = conj_thms(&[
        empty_minor(&mut env, &mach, &spec.ctors[0], &ps, &w),
        empty_minor(&mut env, &mach, &spec.ctors[1], &ps, &w),
        empty_minor(&mut env, &mach, &spec.ctors[2], &ps, &w),
    ]);

    // ── H₂^ctor, discharged atom by atom ────────────────────────────────────
    let h_thm = conj_thms(&[
        point_in_beta(&mut env, &mach, &b0_ax, std::slice::from_ref(&one)),
        point_in_beta(&mut env, &mach, &b1_ax, &[one.clone(), pt.clone()]),
        c0_mem.clone(),
        c0_mem,
    ]);

    // ── fire ι at the last constructor ──────────────────────────────────────
    let at = inst_all(&gr.iota[2], &[
        one.clone(), pt.clone(), pt.clone(), pt.clone(), one.clone(),
        pt.clone(), pt.clone(), c0.clone(), c0.clone(),
    ])
    .expect("instantiate ι₂ at the witness");
    let fired = Thm::mp(&at, &and_intro(&hyp_thm, &h_thm))
        .expect("the discharged hypotheses are not the ones ι₂ carries");

    // ── the equation is closed, non-trivial, and recursive ──────────────────
    let grec = gr
        .rec_of(&mach, &ind, &f.rc, &ps, &minors, &one)
        .expect("the recursor term");
    let ctor = ind
        .ctor_term(&mach, 2, &[pt.clone(), pt.clone()], &[c0.clone(), c0.clone()])
        .expect("ctor₂ at the witness");
    let ihs = [ap.apply(grec.clone(), c0.clone()), ap.apply(grec.clone(), c0.clone())];
    let rhs = applied_minor(
        ap,
        &spec.ctors[2].order,
        &pt,
        &[pt.clone(), pt.clone()],
        &[c0.clone(), c0.clone()],
        &ihs,
    );
    let lhs = ap.apply(grec, ctor);
    assert_eq!(*fired.concl(), Formula::eq(lhs.clone(), rhs.clone()));
    assert!(closed(fired.concl()), "the fired ι rule still carries hypotheses");
    assert_ne!(lhs, rhs, "the fired ι rule is reflexivity");
}

/// Two constructors with **identical argument types** share one telescope by
/// cache design, so their summands are the same term — branch separation must
/// come from the injections alone, and the two ι rules must still say
/// different things.
#[test]
fn colliding_telescopes_are_separated_by_the_injections_alone() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (g, g_ax) = const_unit_beta(&mut env, &mach, 0);
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![g], 0), CtorSpec::new(vec![g], 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the colliding declaration");
    assert_eq!(
        ind.summands[0], ind.summands[1],
        "the two summands should be the same term — that is the point"
    );
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    let s = &mach.wt.sums;
    let ap = &s.ap;
    let (one, pt) = (s.unit(), s.point());

    // The two ι rules differ exactly in which minor they return.
    let vars: Vec<kernel::FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let rhss: Vec<Term> = (0..2)
        .map(|i| {
            let at = inst_all(&gr.iota[i], &[
                ts[0].clone(), ts[1].clone(), ts[2].clone(), ts[3].clone(),
            ])
            .expect("instantiate");
            let (_, eq) = at.concl().as_imp().expect("an implication");
            eq.as_eq().expect("an equation").1
        })
        .collect();
    assert_ne!(rhss[0], rhss[1], "the two branches collapsed");

    // Fire the **last** one closed, at the shared summand.
    let ps: [Term; 0] = [];
    let minors = [pt.clone(), pt.clone()];
    let (_, _, _, w) = carrier_at(&mach, &ind, &ps).expect("carrier parts");
    let hyp_thm = conj_thms(&[
        empty_minor(&mut env, &mach, &spec.ctors[0], &ps, &w),
        empty_minor(&mut env, &mach, &spec.ctors[1], &ps, &w),
    ]);
    let y_mem = point_in_beta(&mut env, &mach, &g_ax, &[]);
    let at = inst_all(&gr.iota[1], &[pt.clone(), pt.clone(), one.clone(), pt.clone()])
        .expect("instantiate ι₁");
    let fired = Thm::mp(&at, &and_intro(&hyp_thm, &y_mem)).expect("discharge");
    assert!(closed(fired.concl()));

    let grec = gr.rec_of(&mach, &ind, &f.rc, &ps, &minors, &one).expect("recursor term");
    let ctor = ind.ctor_term(&mach, 1, std::slice::from_ref(&pt), &[]).expect("ctor₁");
    assert_eq!(
        *fired.concl(),
        Formula::eq(ap.apply(grec, ctor), ap.apply(pt.clone(), pt.clone())),
    );
}

/// The `N` shape, as a cross-check against the hand-written `wnat_rec`: the
/// general machine's ι at the successor fires closed with the zero
/// constructor as the recursive witness. (The terms are *not* `wnat_rec`'s —
/// the fibres differ, `finord(1) ≠ 1` — so the check is that both fire, not
/// term equality.)
#[test]
fn the_nat_shape_fires_at_the_successor() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(vec![], 1)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("N");
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    let s = &mach.wt.sums;
    let ap = &s.ap;
    let (one, pt) = (s.unit(), s.point());
    let ps: [Term; 0] = [];
    let minors = [pt.clone(), pt.clone()];
    let (_, _, _, w) = carrier_at(&mach, &ind, &ps).expect("carrier parts");

    let zero = ind.ctor_term(&mach, 0, &[], &[]).expect("N.zero");
    let zero_mem = ind.ctors[0].mem.clone();
    assert!(closed(zero_mem.concl()));

    let hyp_thm = conj_thms(&[
        empty_minor(&mut env, &mach, &spec.ctors[0], &ps, &w),
        empty_minor(&mut env, &mach, &spec.ctors[1], &ps, &w),
    ]);
    let at = inst_all(&gr.iota[1], &[pt.clone(), pt.clone(), one.clone(), zero.clone()])
        .expect("instantiate ι at succ");
    let fired = Thm::mp(&at, &and_intro(&hyp_thm, &zero_mem)).expect("discharge");
    assert!(closed(fired.concl()));

    let grec = gr.rec_of(&mach, &ind, &f.rc, &ps, &minors, &one).expect("recursor term");
    let succ_zero = ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&zero)).expect("succ zero");
    let rhs = ap.apply(ap.apply(pt.clone(), zero.clone()), ap.apply(grec.clone(), zero));
    assert_eq!(*fired.concl(), Formula::eq(ap.apply(grec, succ_zero), rhs));
}

/// (S3)'s statement is `HYP → step_typed(A, B, U({A,T'}), T, e)` — the same
/// `step_typed` the shared W-recursor carries, at the carrier's own data.
#[test]
fn step_typed_matches_the_w_recursors_hypothesis() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (spec, _, _) = witness_spec(&mut env, &mach);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the witness declaration");
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    let s = &mach.wt.sums;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let ps = [ts[0].clone()];
    let minors = [ts[1].clone(), ts[2].clone(), ts[3].clone()];
    let t = &ts[4];

    let at = inst_all(&gr.step_typed, &ts).expect("instantiate (S3)");
    let (tags, fam, u, w) = carrier_at(&mach, &ind, &ps).expect("carrier parts");
    let step = gr.step_of(&mach, &ind, &ps, &minors, t).expect("the packed step");
    let hyp = premise::hyp_of(&mut env, s, &spec.ctors, &ps, &w, &minors, t).expect("HYP");
    let expected = Formula::imp(
        hyp,
        derived::wrec_total::step_typed(&mut env, s, &mach.wt, &tags, &fam, &u, t, &step),
    );
    assert_eq!(*at.concl(), expected);
}

/// The `ParserDescr.sepBy` mask, `Rec, Plain, Rec, Plain` — the corpus's
/// *other* interleaving, with a **leading** recursive field, so the very
/// first application the minor sees is a subterm. (The in-scope corpus
/// witnesses for interleaving are `Name.str : Name → String → Name` and
/// `ParserDescr.sepBy/sepBy1`; `RBTree`, which `RECURSOR-DESIGN.md` §1.6
/// cites, is an *indexed* family in the export — `numIndices: 2` — and out
/// of this machine's scope entirely.)
#[test]
fn the_leading_rec_mask_fires_closed() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (b0, b0_ax) = const_unit_beta(&mut env, &mach, 0);
    let (b1, b1_ax) = const_unit_beta(&mut env, &mach, 1);
    let c0 = CtorSpec::nullary();
    let c1 = CtorSpec::with_order(vec![b0], 1, vec![Slot::Rec, Slot::Plain]).expect("Name.str");
    let c2 = CtorSpec::with_order(
        vec![b0, b1],
        2,
        vec![Slot::Rec, Slot::Plain, Slot::Rec, Slot::Plain],
    )
    .expect("sepBy");
    let spec = DeclSpec::new(0, vec![c0, c1, c2]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the sepBy shape");
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    let s = &mach.wt.sums;
    let ap = &s.ap;
    let (one, pt) = (s.unit(), s.point());
    let ps: [Term; 0] = [];
    let minors = [pt.clone(), pt.clone(), pt.clone()];
    let (_, _, _, w) = carrier_at(&mach, &ind, &ps).expect("carrier parts");

    let c0t = ind.ctor_term(&mach, 0, &[], &[]).expect("ctor₀");
    let c0_mem = ind.ctors[0].mem.clone();
    assert!(closed(c0_mem.concl()));

    let hyp_thm = conj_thms(&[
        empty_minor(&mut env, &mach, &spec.ctors[0], &ps, &w),
        empty_minor(&mut env, &mach, &spec.ctors[1], &ps, &w),
        empty_minor(&mut env, &mach, &spec.ctors[2], &ps, &w),
    ]);
    let h_thm = conj_thms(&[
        point_in_beta(&mut env, &mach, &b0_ax, &[]),
        point_in_beta(&mut env, &mach, &b1_ax, std::slice::from_ref(&pt)),
        c0_mem.clone(),
        c0_mem,
    ]);
    let at = inst_all(&gr.iota[2], &[
        pt.clone(), pt.clone(), pt.clone(), one.clone(),
        pt.clone(), pt.clone(), c0t.clone(), c0t.clone(),
    ])
    .expect("instantiate ι₂");
    let fired = Thm::mp(&at, &and_intro(&hyp_thm, &h_thm)).expect("discharge");
    assert!(closed(fired.concl()));

    // The right side leads with the recursive field, per the mask.
    let grec = gr.rec_of(&mach, &ind, &f.rc, &ps, &minors, &one).expect("recursor term");
    let ctor = ind
        .ctor_term(&mach, 2, &[pt.clone(), pt.clone()], &[c0t.clone(), c0t.clone()])
        .expect("ctor₂");
    let ihs = [ap.apply(grec.clone(), c0t.clone()), ap.apply(grec.clone(), c0t.clone())];
    let rhs = applied_minor(
        ap,
        &spec.ctors[2].order,
        &pt,
        &[pt.clone(), pt.clone()],
        &[c0t.clone(), c0t.clone()],
        &ihs,
    );
    assert_eq!(*fired.concl(), Formula::eq(ap.apply(grec, ctor), rhs));
}

/// (S1) and (S2), pinned directly: the step is single-valued with no
/// hypothesis at all, and its value at an interleaved key is the minor
/// applied in mask order to the key's own components.
#[test]
fn the_step_computes_and_is_single_valued() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (spec, _, _) = witness_spec(&mut env, &mach);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the witness declaration");
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    let s = &mach.wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..8).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let ps = [ts[0].clone()];
    let minors = [ts[1].clone(), ts[2].clone(), ts[3].clone()];
    let t = &ts[4];
    let (sigma, fv, rv) = (&ts[5], &ts[6], &ts[7]);

    // (S2): unconditional single-valuedness.
    let sv_at = inst_all(&gr.sv, &ts[..5]).expect("instantiate (S2)");
    let step = gr.step_of(&mach, &ind, &ps, &minors, t).expect("the packed step");
    assert_eq!(
        *sv_at.concl(),
        derived::funspace::is_single_valued(&mut env, &ap.sets, &step),
    );

    // (S1) at the interleaved constructor.
    let at = inst_all(&gr.computes[2], &ts).expect("instantiate (S1)");
    let (_, _, _, w) = carrier_at(&mach, &ind, &ps).expect("carrier parts");
    let two = mach.syms.finord(s, 2).expect("finord(2)");
    let fw = derived::inductive::pow_prod(s, &two, &w);
    let ft = derived::inductive::pow_prod(s, &two, t);
    let summand = ind.telescopes[2].ty_of(vec![ps[0].clone()]);
    let hyp = Formula::and(
        Formula::mem(sigma.clone(), summand),
        Formula::and(Formula::mem(fv.clone(), fw), Formula::mem(rv.clone(), ft)),
    );
    let pj = &mach.proj;
    let comps: Vec<Term> = (0..2)
        .map(|j| derived::sigma::Telescope::comp_of(ap, pj, j, sigma.clone()))
        .collect();
    let subs: Vec<Term> = (0..2)
        .map(|j| ap.apply(fv.clone(), mach.syms.inj(j, s.point()).expect("Inj")))
        .collect();
    let ihs: Vec<Term> = (0..2)
        .map(|j| ap.apply(rv.clone(), mach.syms.inj(j, s.point()).expect("Inj")))
        .collect();
    let val = applied_minor(ap, &spec.ctors[2].order, &minors[2], &comps, &subs, &ihs);
    let key = ap.sets.pair(
        mach.syms.inj(2, sigma.clone()).expect("Inj₂"),
        ap.sets.pair(fv.clone(), rv.clone()),
    );
    let expected = Formula::imp(hyp, Formula::eq(ap.apply(step, key), val));
    assert_eq!(*at.concl(), expected, "(S1)'s statement is not the rebuilt one");
}

/// `Empty` gets no recursor from this module, by design: no ι rule exists to
/// state and no `HYP` to carry. A wiring that wants `Empty.rec` must treat it
/// separately, as a counted gap until then.
#[test]
fn the_empty_declaration_is_declined() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let ind =
        Inductive::build(&mut env, &mut mach, &DeclSpec::new(0, vec![])).expect("Empty");
    assert!(GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace).is_none());
}

/// **The hypothesis leg of the house rule, at the flagship entry.**
///
/// `GenRecursor::build` takes `iota` and `funspace` as bare `&Thm`s and `mp`s
/// against both, and `Thm::mp` unions the two sides' hypothesis sets in
/// silence. So a theorem that merely *concludes* what `wrec_total::iota`
/// concludes — `Thm::assume` of its conclusion, which is a perfectly ordinary
/// sequent and needs no privilege to build — used to produce a `GenRecursor`
/// whose every `iota[i]` was `{φ} ⊢ …` under a header promising `⊢ …`.
///
/// Both theorems are now required to be unconditional. Note the fake's
/// *conclusion* is exact, so nothing downstream could have noticed.
#[test]
fn a_merely_assumed_w_recursor_theorem_is_refused() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (spec, _, _) = witness_spec(&mut env, &mach);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the witness declaration");

    let fake_iota = Thm::assume(f.iota.concl().clone());
    let fake_funspace = Thm::assume(f.funspace.concl().clone());
    assert_eq!(fake_iota.concl(), f.iota.concl(), "the fake must be conclusion-exact");
    assert_eq!(fake_funspace.concl(), f.funspace.concl(), "likewise");
    assert!(!fake_iota.hyps().is_empty() && !fake_funspace.hyps().is_empty());

    assert!(
        GenRecursor::build(&mut env, &mach, &ind, &f.rc, &fake_iota, &f.funspace).is_none(),
        "a hypothetical ι was accepted"
    );
    assert!(
        GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &fake_funspace).is_none(),
        "a hypothetical funspace was accepted"
    );

    // The real pair still builds, and everything it hands back is a `⊢`.
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");
    let mut ts: Vec<&Thm> = vec![&gr.sv, &gr.step_typed];
    ts.extend(gr.computes.iter());
    ts.extend(gr.iota.iter());
    assert!(ts.iter().all(|t| t.hyps().is_empty()), "(S1)–(S4) must rest on nothing");
}

/// **The term-builders resolve against a machine, so the machine is not a free
/// choice.**
///
/// `carrier_at`, `rec_of` and `step_of` return *terms*, and a term carries no
/// evidence: nothing downstream can catch one that was built from the wrong
/// apparatus's symbols. A second `Machine` over the same `Wtype` and `Bound`,
/// with its caches warmed by a second declaration of the same shape, answers
/// every lookup they make — and hands back `(Sum′₃(A⃗), fam′, U(…), W(A′,…))`,
/// which is not this declaration's carrier at those parameters.
///
/// The same holds one level in: a *second declaration over the same machine*
/// has its own injections and its own carrier, so splicing this recursor's step
/// symbols into it is the same mislabelling.
#[test]
fn the_term_builders_refuse_a_foreign_apparatus() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (spec, _, _) = witness_spec(&mut env, &mach);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the witness declaration");
    let gr = GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace)
        .expect("the general recursor");

    // A second apparatus over the *same* W-type and bound.
    let mut other = Machine::over(&mut env, mach.wt.clone(), mach.bnd.clone())
        .expect("a second machine");
    let ind_other =
        Inductive::build(&mut env, &mut other, &spec).expect("the same shape, elsewhere");
    // A second declaration over the *first* machine — same apparatus, other ι.
    let (spec2, _, _) = witness_spec(&mut env, &mach);
    let ind2 = Inductive::build(&mut env, &mut mach, &spec2).expect("a second declaration");

    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let ps = [ts[0].clone()];
    let minors = [ts[1].clone(), ts[2].clone(), ts[3].clone()];
    let t = &ts[4];

    // The honest triple: this declaration, its own machine, its own recursor.
    let good_carrier = carrier_at(&mach, &ind, &ps).expect("the carrier parts");
    assert!(gr.rec_of(&mach, &ind, &f.rc, &ps, &minors, t).is_some());
    assert!(gr.step_of(&mach, &ind, &ps, &minors, t).is_some());

    // A foreign machine is refused at all three doors.
    assert!(carrier_at(&other, &ind, &ps).is_none(), "carrier_at took a foreign machine");
    assert!(
        gr.rec_of(&other, &ind, &f.rc, &ps, &minors, t).is_none(),
        "rec_of took a foreign machine"
    );
    assert!(
        gr.step_of(&other, &ind, &ps, &minors, t).is_none(),
        "step_of took a foreign machine"
    );
    // …including with the declaration that *is* over it, whose carrier is a
    // different set built from a different `Sum₃`.
    assert!(carrier_at(&other, &ind_other, &ps).is_some(), "the other pair is consistent");
    assert_ne!(
        carrier_at(&other, &ind_other, &ps).expect("the other carrier"),
        good_carrier,
        "the two apparatuses would have to disagree for this test to mean anything"
    );
    assert!(
        gr.rec_of(&other, &ind_other, &f.rc, &ps, &minors, t).is_none(),
        "rec_of spliced this recursor's steps into another apparatus"
    );

    // A second declaration over the *same* machine is refused too.
    assert!(
        gr.rec_of(&mach, &ind2, &f.rc, &ps, &minors, t).is_none(),
        "rec_of spliced this recursor's steps into another declaration's carrier"
    );

    // The arities are inputs, not decoration: `Term::apply` asserts on them, so
    // without these checks a short `p⃗` was a panic and a short `s⃗` an
    // out-of-bounds index rather than a `None`.
    assert!(carrier_at(&mach, &ind, &[]).is_none(), "carrier_at took no parameters");
    assert!(gr.step_of(&mach, &ind, &ps, &minors[..2], t).is_none(), "step_of took two minors");
    assert!(gr.rec_of(&mach, &ind, &f.rc, &[], &minors, t).is_none(), "rec_of took no parameters");
}

/// **The recursor declines a function-typed recursive argument rather than
/// deriving something about the wrong terms.**
///
/// Its minor premises say `rⱼ ∈ ind(p⃗)` and its ι rules apply the
/// recursive-argument function at `Inj_j(•)`; neither is true when the argument
/// is a *function* into the carrier and the fibre is `Σ(z::γⱼ)`. The
/// declaration itself still builds — only the eliminator is refused.
#[test]
fn the_recursor_refuses_a_function_typed_recursive_argument() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    mach.syms.ensure(&mut env, &s, 4).expect("the sum symbols");
    let boolean = mach.syms.finord(&s, 2).expect("finord(2)");
    let (bool_sym, _) = define_abbrev(&mut env, &[], &boolean).expect("Bool");

    let spec = DeclSpec::new(
        0,
        vec![
            CtorSpec::nullary(),
            CtorSpec::with_rec_doms(Vec::new(), vec![vec![bool_sym]]),
        ],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the declaration builds");
    assert!(ind.has_function_typed_recs());
    assert!(
        GenRecursor::build(&mut env, &mach, &ind, &f.rc, &f.iota, &f.funspace).is_none(),
        "the recursor must decline, not derive"
    );

    // The plain sibling over the same apparatus is unaffected.
    let plain = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(Vec::new(), 1)]);
    let np = Inductive::build(&mut env, &mut mach, &plain).expect("N");
    assert!(!np.has_function_typed_recs());
    assert!(GenRecursor::build(&mut env, &mach, &np, &f.rc, &f.iota, &f.funspace).is_some());
}

// ─────────────────────────────────────────────────────────────────────────────
// The per-slot spelling of a minor premise's recursive arguments.
// ─────────────────────────────────────────────────────────────────────────────

/// **The two spellings are chosen per recursive argument, not per
/// constructor**, and `minor_typed` is `minor_typed_at` at no function-typed
/// slot.
///
/// Three constructors and not two, because two cannot tell the rules apart. A
/// `rec_slot_domains` keyed off `Inductive::has_function_typed_recs` — or off
/// which `RecArg` the constructor took, which really *is* per constructor —
/// agrees with the right answer on the plain-only and the function-only cases
/// and disagrees on the **mixed** one, whose first slot is a plain recursive
/// occurrence inside a constructor that takes `RecArg::general` as a whole.
#[test]
fn a_minor_premises_recursive_slots_are_stated_one_at_a_time() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    mach.syms.ensure(&mut env, &s, 4).expect("the sum symbols");
    let boolean = mach.syms.finord(&s, 2).expect("finord(2)");
    let (bool_sym, _) = define_abbrev(&mut env, &[], &boolean).expect("Bool");

    // `leaf | plain (r : ind) | node (g : Bool → ind) | both (r : ind) (g : Bool → ind)`
    let spec = DeclSpec::new(
        0,
        vec![
            CtorSpec::nullary(),
            CtorSpec::new(Vec::new(), 1),
            CtorSpec::with_rec_doms(Vec::new(), vec![vec![bool_sym]]),
            CtorSpec::with_rec_doms(Vec::new(), vec![vec![], vec![bool_sym]]),
        ],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the declaration builds");

    // ── the funnel ──────────────────────────────────────────────────────────
    assert!(ind.rec_slot_domains(0).is_empty(), "a nullary constructor has no slots");
    assert_eq!(ind.rec_slot_domains(1), vec![None], "a plain recursive argument");
    let node = ind.rec_slot_domains(2);
    let both = ind.rec_slot_domains(3);
    assert_eq!(node.len(), 1);
    assert!(node[0].is_some(), "a function-typed recursive argument");
    assert_eq!(
        both,
        vec![None, node[0].clone()],
        "the mixed constructor's first slot is plain and its second is the same Aⱼ"
    );
    assert!(ind.rec_slot_domains(9).is_empty(), "out of range is the plain spelling");

    // ── `minor_typed` is `minor_typed_at` at no function-typed slot ─────────
    let (su, t) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let w = ind.wty.clone();
    for i in 0..4 {
        let c = &spec.ctors[i];
        let plain = premise::minor_typed(&mut env, &s, c, &[], &w, &su, &t);
        let at = premise::minor_typed_at(&mut env, &s, c, &[], &w, &su, &t, &[]);
        assert_eq!(plain, at, "constructor {i}: the absent slice is not the plain spelling");
    }

    // ── and a function-typed slot really states a function space ────────────
    let a1 = both[1].clone().expect("Aⱼ");
    let stated =
        premise::minor_typed_at(&mut env, &s, &spec.ctors[3], &[], &w, &su, &t, &both);
    let plain = premise::minor_typed(&mut env, &s, &spec.ctors[3], &[], &w, &su, &t);
    assert_ne!(stated, plain, "the function-typed slot changed nothing");
    let printed = format!("{stated:?}");
    assert!(
        printed.contains(&format!("{:?}", s.fs.of(a1.clone(), w.clone())))
            && printed.contains(&format!("{:?}", s.fs.of(a1, t.clone()))),
        "the second slot states neither fs(A,W) nor fs(A,T)"
    );
    // The *first* slot is untouched: the carrier itself still occurs bare.
    assert!(printed.contains(&format!("{:?}", w)), "the plain slot lost its carrier");
}
