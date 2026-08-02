//! **The class-(P) recursor, non-indexed** — `derived/src/inductive/family/trunc_rec.rs`.
//!
//! Three shapes, and both polarities:
//!
//! * `BoolProp`'s (two nullary constructors, `069`) — the rule fires end to end
//!   at a **concrete motive**, `{⟨•,1⟩}`, and yields `⊢ • ∈ app(m,•)` at closed
//!   terms;
//! * a **recursive, interleaved** shape — `Plain, Rec, Plain, Rec` — where the
//!   minor's antecedent has six atoms and the constructor's declared order is
//!   not the carrier's plains-then-recs order. Nothing in the tutorial corpus is
//!   both non-indexed class (P) *and* recursive (the three recursive class-(P)
//!   declarations — `Nat.le`, `Nat.le.below`, `List.Mem` — are all indexed), so
//!   this shape is synthetic; it is here because the theorem is general in it
//!   and an untested permutation is exactly the kind of thing that has been
//!   wrong before;
//! * a declaration whose only field type is `∅`, where the carrier is **empty**
//!   and the rule is provably vacuous.
//!
//! **Non-vacuity cuts both ways, and is pinned at concrete sets.** A rule proved
//! about a `‖·‖` that is constantly `1` would satisfy every membership theorem
//! here, so what is pinned is `‖ind‖ = 0` at the empty declaration against
//! `⊢ ¬(0 = 1)`; and a rule whose antecedent were decoration would be satisfied
//! by every motive, so the minors are shown **refutable** at the motive
//! `{⟨•,0⟩}` — the same theorem, one constant changed.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::family::{TruncCarrier, TruncRecursor};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine, Slot};
use derived::point_fun::PointFun;
use derived::prop::Trunc;
use derived::sums::Sums;
use derived::tower::Tower;
use derived::wtype::Wtype;
use derived::{
    and_intro, and_left, conj_of, conj_proj, define_abbrev, eq_symm, ex_falso, exists_elim_imp,
    gen_all, imp_refl, inst_all, opair, syl,
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

/// Right-nested conjunction of closed theorems, matching `conj_of`.
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
    Fix { tow, tr, pf, mach }
}

/// A symbol of the given arity whose value is `body`, with its defining
/// equation.
fn abbrev(env: &mut Env, arity: usize, body: impl Fn(&[Term]) -> Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = body(&args);
    define_abbrev(env, &vars, &t).expect("an abbreviation")
}

/// The motive `{⟨•,v⟩}`, and `⊢ • ∈ app({⟨•,v⟩}, •)` derived from `⊢ • ∈ v`.
///
/// A *concrete* motive, so that "the rule fires" is a statement at closed terms
/// rather than a rearrangement of the same variable.
fn motive_at(f: &Fix, v: &Term) -> (Term, Thm) {
    let s = &f.mach.wt.sums;
    let pt = s.point();
    let m = PointFun::of(s, pt.clone(), v.clone());
    let app_eq = inst_all(&f.pf.app, &[pt.clone(), v.clone()]).expect("app({⟨•,v⟩}, •) = v");
    (m, app_eq)
}

// ─────────────────────────────────────────────────────────────────────────────
// `BoolProp` — two nullary constructors, `069`
// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable.** `⊢ ∀m. ((• ∈ app(m,•) ∧ • ∈ app(m,•)) → ∀t. (t ∈ ‖P‖ →
/// • ∈ app(m,t)))`, and it fires: at the motive `{⟨•,1⟩}` both minors are
/// discharged from `⊢ • ∈ 1` and the conclusion comes out closed.
///
/// The set the conclusion quantifies over is **not empty** — `TruncCtor::mem`
/// puts `•` in it — which is what stops the `∀t` from being decoration.
#[test]
fn the_class_p_rule_fires_at_two_nullary_constructors() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let (one, pt, zero) = (s.unit(), s.point(), s.zero());

    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("BoolProp");
    let tc = TruncCarrier::over_declaration(&mut env, &mach, &f.tow, &f.tr, &ind)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let tr = TruncRecursor::over_declaration(&mut env, &f.mach, &ind, &tc)
        .expect("the class-(P) recursor");

    // ── the statement, rebuilt ──────────────────────────────────────────────
    let mt = Term::var(tr.motive);
    let phi = Formula::mem(pt.clone(), s.ap.apply(mt.clone(), pt.clone()));
    assert_eq!(tr.minor_atoms, vec![Vec::<Formula>::new(), Vec::new()], "no fields at all");
    assert_eq!(tr.minors, vec![phi.clone(), phi.clone()], "each minor is the bare φ");
    assert_eq!(tr.hyp, Formula::and(phi.clone(), phi.clone()));

    let tv = env.fresh_var();
    let tt = Term::var(tv);
    let want = Formula::forall(
        tr.motive,
        Formula::imp(
            tr.hyp.clone(),
            Formula::forall(
                tv,
                Formula::imp(
                    Formula::mem(tt.clone(), tc.carrier.clone()),
                    Formula::mem(pt.clone(), s.ap.apply(mt.clone(), tt.clone())),
                ),
            ),
        ),
    );
    assert_eq!(*tr.rec.concl(), want, "⊢ ∀m. (MINOR₀ ∧ MINOR₁ → ∀t. (t ∈ ‖P‖ → • ∈ app(m,t)))");
    assert!(tr.rec.hyps().is_empty() && closed_f(tr.rec.concl()));

    // ── it fires, at the concrete motive `{⟨•,1⟩}` ──────────────────────────
    let (m1, app_eq) = motive_at(&f, &one);
    let phi_m = rw_back(&mut env, &app_eq, |t| Formula::mem(pt.clone(), t), &s.unit_mem);
    assert_eq!(*phi_m.concl(), phi.subst(tr.motive, &m1), "the minor at this motive");

    let at = inst_all(&tr.rec, std::slice::from_ref(&m1)).expect("at m := {⟨•,1⟩}");
    let fired = Thm::mp(&at, &conj_thms(&[phi_m.clone(), phi_m])).expect("both minors");
    let at_pt = inst_all(&fired, std::slice::from_ref(&pt)).expect("at t := •");

    // `• ∈ ‖P‖`: the carrier the conclusion quantifies over is inhabited.
    let ctor_mem = inst_all(&tc.ctors[0].mem, &[]).expect("no binders to fill");
    assert_eq!(*ctor_mem.concl(), Formula::mem(pt.clone(), tc.carrier.clone()));
    let out = Thm::mp(&at_pt, &ctor_mem).expect("the point is in the carrier");
    assert_eq!(*out.concl(), Formula::mem(pt.clone(), s.ap.apply(m1, pt.clone())));
    assert!(out.hyps().is_empty() && closed_f(out.concl()), "closed and unconditional");

    // ── the antecedent is load-bearing: at `{⟨•,0⟩}` it is refutable ────────
    let (m0, app_eq0) = motive_at(&f, &zero);
    let not_in_zero =
        inst_all(&s.ap.empty_ax, std::slice::from_ref(&pt)).expect("¬(• ∈ 0)");
    let not_phi = rw_back(
        &mut env,
        &app_eq0,
        |t| Formula::not(Formula::mem(pt.clone(), t)),
        &not_in_zero,
    );
    let phi0 = phi.subst(tr.motive, &m0);
    let hyp0 = tr.hyp.subst(tr.motive, &m0);
    assert_eq!(hyp0, Formula::and(phi0.clone(), phi0.clone()));
    let refuted = syl(&and_left(phi0.clone(), phi0), &not_phi).expect("syl");
    assert_eq!(*refuted.concl(), Formula::not(hyp0), "the minors are not always satisfiable");
    assert!(closed_f(refuted.concl()));
}

// ─────────────────────────────────────────────────────────────────────────────
// A recursive, interleaved constructor — the Lean field order
// ─────────────────────────────────────────────────────────────────────────────

/// **`minor_atoms` is positional against the Lean field spine.** The mask is
/// `Plain, Rec, Plain, Rec`, so the minor's six atoms are
///
/// ```text
/// y₀ ∈ β₀(p),  • ∈ ‖ind(p)‖,  y₁ ∈ β₁(p,y₀),  • ∈ ‖ind(p)‖,  φ,  φ
/// ```
///
/// — fields in *declared* order, then the two induction hypotheses, which is
/// where Lean's minor premise puts them. The carrier's own order is
/// plains-then-recs and the two disagree at four positions.
///
/// The test also *derives* the recursive minor rather than assuming it: with
/// `φ` constant, `MINOR₁` is its own consequent, so one projection proves it.
/// That is the claim the module header makes about why Lean's `step` minor for
/// `Nat.le` carries no content either.
#[test]
fn the_recursive_minor_is_lean_positional_and_carries_no_content() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let (one, pt) = (s.unit(), s.point());

    // `base : P α`, `step : ∀ (y₀ : 1) (r₀ : P α) (y₁ : α) (r₁ : P α), P α`.
    let (b0, _) = abbrev(&mut env, 1, |_| one.clone());
    let (b1, _) = abbrev(&mut env, 2, |a| a[0].clone());
    let spec = DeclSpec::new(
        1,
        vec![
            CtorSpec::nullary(),
            CtorSpec::with_order(
                vec![b0, b1],
                2,
                vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
            )
            .expect("step's mask"),
        ],
    );
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the declaration");
    let tc = TruncCarrier::over_declaration(&mut env, &mach, &f.tow, &f.tr, &ind)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let tr = TruncRecursor::over_declaration(&mut env, &f.mach, &ind, &tc)
        .expect("the class-(P) recursor");

    let pv = ind.params[0];
    let mt = Term::var(tr.motive);
    let phi = Formula::mem(pt.clone(), s.ap.apply(mt.clone(), pt.clone()));
    let rec_atom = Formula::mem(pt.clone(), tc.carrier.clone());

    // The nullary constructor's minor is the bare `φ`.
    assert!(tr.minor_atoms[0].is_empty());
    assert_eq!(tr.minors[0], phi);

    // The interleaved one's, in declared order.
    let c = &tc.ctors[1];
    assert_eq!(c.yvs.len(), 2);
    assert_eq!(c.tvs.len(), 2);
    assert_eq!(c.trunc_atoms.len(), 4);
    let want_atoms = vec![
        c.trunc_atoms[0].clone(), // y₀ ∈ β₀(p)
        rec_atom.clone(),         // • ∈ ‖ind(p)‖  — the first Rec slot
        c.trunc_atoms[1].clone(), // y₁ ∈ β₁(p,y₀)
        rec_atom.clone(),         // • ∈ ‖ind(p)‖
        phi.clone(),
        phi.clone(),
    ];
    assert_eq!(tr.minor_atoms[1], want_atoms, "fields in declared order, then the IHs");
    assert_eq!(c.trunc_atoms[2], rec_atom, "the truncated recursive atom is the same one");
    assert_eq!(c.trunc_atoms[3], rec_atom);

    // …and that is *not* the carrier's own order.
    let carrier_order: Vec<Formula> = c
        .trunc_atoms
        .iter()
        .cloned()
        .chain([phi.clone(), phi.clone()])
        .collect();
    assert_ne!(tr.minor_atoms[1], carrier_order, "the mask interleaves; the carrier does not");

    assert_eq!(
        tr.minors[1],
        quantify(&c.yvs, Formula::imp(conj_of(&want_atoms).expect("six atoms"), phi.clone()))
    );

    // **The recursive minor is its own consequent**: one projection proves it.
    let minor1 = gen_all(&c.yvs, &conj_proj(&want_atoms, 4).expect("the first IH"));
    assert!(
        derived::establishes(&minor1, &tr.minors[1]),
        "with φ constant, MINOR₁ is trivially provable — no content, as in Lean"
    );

    // ── the rule still fires, through the *non*-recursive constructor ───────
    let (m1, app_eq) = motive_at(&f, &one);
    let phi_m = rw_back(&mut env, &app_eq, |t| Formula::mem(pt.clone(), t), &s.unit_mem);
    let minor1_m = inst_all(&gen_all(&[pv, tr.motive], &minor1), &[one.clone(), m1.clone()])
        .expect("at p := 1, m := {⟨•,1⟩}");

    let at = inst_all(&tr.rec, &[one.clone(), m1.clone()]).expect("at p := 1, m := {⟨•,1⟩}");
    let (ante, _) = at.concl().as_imp().expect("an implication");
    assert_eq!(ante, tr.hyp.subst(pv, &one).subst(tr.motive, &m1));

    let fired = Thm::mp(&at, &conj_thms(&[phi_m, minor1_m])).expect("both minors");
    let at_pt = inst_all(&fired, std::slice::from_ref(&pt)).expect("at t := •");
    let ctor_mem =
        inst_all(&tc.ctors[0].mem, std::slice::from_ref(&one)).expect("base ∈ ‖ind 1‖");
    let out = Thm::mp(&at_pt, &ctor_mem).expect("the point is in the carrier");
    assert_eq!(*out.concl(), Formula::mem(pt.clone(), s.ap.apply(m1, pt)));
    assert!(out.hyps().is_empty() && closed_f(out.concl()));
}

// ─────────────────────────────────────────────────────────────────────────────
// The negative polarity — an empty carrier, and a vacuous rule
// ─────────────────────────────────────────────────────────────────────────────

/// **`‖ind‖ = 0`, so the rule quantifies over nothing.**
///
/// One constructor whose only field type is `∅`: the tag set has no members, so
/// `closed(A,B,∅)` holds vacuously, W2 puts the carrier inside `∅`, and
/// `TruncCarrier::empty_at` turns that into an **equation at a concrete set**.
/// `⊢ ¬(0 = 1)` then says this is a different answer from
/// `TruncCtor::is_unit`'s, which is what stops `‖·‖` being read as the constant
/// `1` — and the conclusion of the recursor is derivable here *without any
/// minor at all*, which is what "vacuous" means.
#[test]
fn the_rule_is_vacuous_where_the_carrier_is_empty() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let (one, pt, zero) = (s.unit(), s.point(), s.zero());

    let (b0, b0_ax) = abbrev(&mut env, 0, |_| zero.clone());
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the declaration");
    let tc = TruncCarrier::over_declaration(&mut env, &mach, &f.tow, &f.tr, &ind)
        .expect("the class-(P) carrier");
    let f = Fix { mach, ..f };
    let tr = TruncRecursor::over_declaration(&mut env, &f.mach, &ind, &tc)
        .expect("the class-(P) recursor");

    // ── `⊢ ∀a. ¬(a ∈ A)` — nothing is a tag ─────────────────────────────────
    let av = env.fresh_var();
    let ta = Term::var(av);
    let nj = f.mach.syms.no_junk(&mut env, &s, 1).expect("no_junk at one summand");
    let mut nj_args = ind.summands.clone();
    nj_args.push(ta.clone());
    let nj_at = inst_all(&nj, &nj_args).expect("instantiate");
    let (ma, disj) = nj_at.concl().as_imp().expect("an implication");
    assert_eq!(ma, Formula::mem(ta.clone(), ind.tags.clone()));

    let sv = env.fresh_var();
    let tsig = Term::var(sv);
    let mem_sig = Formula::mem(tsig.clone(), ind.summands[0].clone());
    let eq_a = Formula::eq(ta.clone(), f.mach.syms.inj(0, tsig.clone()).expect("Inj₀"));
    let body = Formula::and(mem_sig.clone(), eq_a.clone());
    assert_eq!(disj, Formula::exists(sv, body.clone()), "one summand, one disjunct");

    // `σ ∈ A₀ → comp₀(σ) ∈ β₀()`, and `β₀() = ∅`.
    let pm = inst_all(&ind.telescopes[0].proj_mem[0], std::slice::from_ref(&tsig))
        .expect("the telescope's projection");
    let comp = pm
        .concl()
        .as_imp()
        .expect("an implication")
        .1
        .as_mem()
        .expect("a membership")
        .0;
    let mem_b0 = Formula::mem(comp.clone(), Term::apply(b0, vec![]));
    let to_zero = {
        let (mb, cc) = (mem_b0.clone(), comp.clone());
        rw(
            &mut env,
            &b0_ax,
            move |t| Formula::imp(mb.clone(), Formula::mem(cc.clone(), t)),
            &imp_refl(mem_b0.clone()),
        )
    };
    let not_in = inst_all(&s.ap.empty_ax, std::slice::from_ref(&comp)).expect("¬(comp ∈ ∅)");
    let no_sig = syl(&syl(&pm, &to_zero).expect("syl"), &not_in).expect("¬(σ ∈ A₀)");
    let no_body = syl(&and_left(mem_sig, eq_a), &no_sig).expect("the disjunct is refuted");
    let no_disj = exists_elim_imp(sv, &Thm::gen(sv, &no_body), &Formula::false_())
        .expect("the witness is discharged");
    let not_a = syl(&nj_at, &no_disj).expect("¬(a ∈ A)");
    assert_eq!(*not_a.concl(), Formula::not(ma));

    // ── `closed(A,B,∅)` and `∅ ⊆ u`, hence `W ⊆ ∅` by W2 ────────────────────
    let fv = env.fresh_var();
    let tf = Term::var(fv);
    let inner = Formula::forall(
        fv,
        Formula::imp(
            Formula::mem(
                tf.clone(),
                s.fs.of(s.ap.apply(ind.fibre.fam.clone(), ta.clone()), zero.clone()),
            ),
            Formula::mem(opair(s.ap.sets.up, ta.clone(), tf.clone()), zero.clone()),
        ),
    );
    let closed_thm = Thm::gen(av, &syl(&not_a, &ex_falso(inner)).expect("vacuously closed"));
    assert_eq!(
        *closed_thm.concl(),
        derived::wtype::closed(&mut env, &s, &ind.tags, &ind.fibre.fam, &zero),
        "⊢ closed(A, B, ∅) — nothing is a tag, so there is nothing to close under"
    );

    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let sub = Thm::gen(
        zv,
        &syl(
            &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz)).expect("¬(z ∈ ∅)"),
            &ex_falso(Formula::mem(tz.clone(), ind.bound.clone())),
        )
        .expect("syl"),
    );
    assert_eq!(*sub.concl(), kernel::thm::subset(&mut env, zero.clone(), ind.bound.clone()));

    let w2 = derived::wtype::w_induction(&mut env, &s, f.mach.wt.w, &f.mach.wt.w_ax)
        .expect("W2");
    let at = inst_all(
        &w2,
        &[ind.tags.clone(), ind.fibre.fam.clone(), ind.bound.clone(), zero.clone()],
    )
    .expect("instantiate");
    let sub_w = Thm::mp(&at, &and_intro(&sub, &closed_thm)).expect("W ⊆ ∅");

    let zv2 = env.fresh_var();
    let tz2 = Term::var(zv2);
    let empty_w = syl(
        &inst_all(&sub_w, std::slice::from_ref(&tz2)).expect("at z"),
        &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz2)).expect("¬(z ∈ ∅)"),
    )
    .expect("¬(z ∈ W)");
    let to_w = inst_all(&ind.ty_ax, &[]).expect("ind = W");
    let empty_all = Thm::gen(
        zv2,
        &rw_back(
            &mut env,
            &to_w,
            |t| Formula::not(Formula::mem(tz2.clone(), t)),
            &empty_w,
        ),
    );

    // ── the equation, and the two polarities against each other ─────────────
    let eq0 = tc
        .empty_at(&mut env, &s, &f.tr, &ind.carrier, &empty_all)
        .expect("‖ind‖ = 0");
    assert_eq!(*eq0.concl(), Formula::eq(tc.carrier.clone(), zero.clone()));
    assert!(eq0.hyps().is_empty() && closed_f(eq0.concl()));
    assert_eq!(*s.tags_distinct.concl(), Formula::not(Formula::eq(zero.clone(), one.clone())));
    let not_unit = rw_back(
        &mut env,
        &eq0,
        |t| Formula::not(Formula::eq(t, one.clone())),
        &s.tags_distinct,
    );
    assert_eq!(
        *not_unit.concl(),
        Formula::not(Formula::eq(tc.carrier.clone(), one.clone())),
        "⊢ ¬(‖ind‖ = 1) — the truncation is not the constant 1"
    );

    // ── the rule's conclusion holds here with no minor at all ───────────────
    let tv = env.fresh_var();
    let tt = Term::var(tv);
    let mv = env.fresh_var();
    let goal = Formula::mem(pt.clone(), s.ap.apply(Term::var(mv), tt.clone()));
    let no_t = rw_back(
        &mut env,
        &eq0,
        |t| Formula::not(Formula::mem(tt.clone(), t)),
        &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tt)).expect("¬(t ∈ 0)"),
    );
    let vacuous = gen_all(&[mv, tv], &syl(&no_t, &ex_falso(goal.clone())).expect("syl"));

    // …and that really is what the recursor concludes, minors stripped: the
    // consequent of `rec` at this motive is a theorem outright.
    let want_concl =
        Formula::forall(tv, Formula::imp(Formula::mem(tt, tc.carrier.clone()), goal));
    assert_eq!(*vacuous.concl(), quantify(&[mv], want_concl.clone()));
    let inst = inst_all(&tr.rec, std::slice::from_ref(&Term::var(mv))).expect("at a motive");
    let (_, concl) = inst.concl().as_imp().expect("an implication");
    assert_eq!(concl, want_concl, "the rule promises exactly what emptiness already gives");
    assert!(
        derived::establishes(
            &inst_all(&vacuous, std::slice::from_ref(&Term::var(mv))).expect("at the motive"),
            &want_concl
        ),
        "no minor is needed here — the rule has no content at an empty carrier"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The guards
// ─────────────────────────────────────────────────────────────────────────────

/// What the build refuses, and why each refusal is a decision.
///
/// `n = 0` is declined rather than special-cased: `decl_rect` has no induction
/// to state there, and the true statement is a different one. An **indexed**
/// `TruncCarrier` is declined because its `φ` is not constant in `z` and none of
/// the simplifications this file rests on apply. And a `TruncCarrier` built over
/// *another* declaration is refused rather than composed, which would otherwise
/// produce a well-formed theorem about two different carriers at once.
#[test]
fn the_class_p_recursor_refuses_what_it_cannot_state() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let one = s.unit();

    // Zero constructors: `TruncCarrier` itself declines, so there is nothing to
    // hand in — the two guards agree.
    let empty_spec = DeclSpec::new(0, Vec::new());
    let empty_ind = Inductive::build(&mut env, &mut mach, &empty_spec).expect("Empty");
    assert!(
        TruncCarrier::over_declaration(&mut env, &mach, &f.tow, &f.tr, &empty_ind).is_none(),
        "no constructors, no class-(P) carrier"
    );

    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("BoolProp");
    let tc = TruncCarrier::over_declaration(&mut env, &mach, &f.tow, &f.tr, &ind)
        .expect("the carrier");

    // A second declaration over the same apparatus has its own carrier.
    let (b0, _) = abbrev(&mut env, 0, |_| one.clone());
    let other_spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0)]);
    let other = Inductive::build(&mut env, &mut mach, &other_spec).expect("a second declaration");
    assert_ne!(other.carrier, ind.carrier);
    assert!(
        TruncRecursor::over_declaration(&mut env, &mach, &other, &tc).is_none(),
        "a carrier for another declaration was accepted"
    );

    // A foreign apparatus answers every internal step out of its own symbols.
    let m2 = Machine::over(&mut env, mach.wt.clone(), mach.bnd.clone()).expect("a second machine");
    assert!(!ind.is_over(&m2));
    assert!(
        TruncRecursor::over_declaration(&mut env, &m2, &ind, &tc).is_none(),
        "a foreign machine was accepted"
    );

    // The honest call still builds.
    assert!(TruncRecursor::over_declaration(&mut env, &mach, &ind, &tc).is_some());
}

/// A second [`Sums`] would make `‖·‖` speak about a different unit set; the
/// fixture shares one, and this pins that the sharing is real rather than
/// incidental.
#[test]
fn the_apparatus_shares_one_signature() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s: &Sums = &f.mach.wt.sums;
    assert_eq!(s.ap.sets.up, f.tow.sums.ap.sets.up, "one pairing");
    assert_eq!(s.sum, f.tow.sums.sum, "one `+`");
    let one = s.unit();
    assert_eq!(
        *f.tr.unit.concl(),
        Formula::eq(f.tr.of(one.clone()), one),
        "`‖·‖`'s `1` is this signature's `1`"
    );
}
