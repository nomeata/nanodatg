//! The **dependent** recursor: structural induction over a declaration's
//! carrier ([`derived::inductive::rect`]), the guarded minors that make `HYP`
//! dischargeable at a variable motive, and the recursor's typing and ι rules at
//! a genuinely dependent motive.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::bound::Bound;
use derived::inductive::rect::{decl_rect, recarg_eta, rect_step};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine, Slot};
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{conj_of, define_abbrev, disj_of, inst_all};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

struct Fix {
    mach: Machine,
    #[allow(dead_code)]
    rc: Recursor,
    #[allow(dead_code)]
    iota: Thm,
    #[allow(dead_code)]
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

/// A constant argument-type symbol of the given arity, with value `1`.
///
/// **It ignores its arity**, so every `βⱼ(p⃗, y⃗<ⱼ)` built with it has the same
/// closed body. That is fine for the shapes it is used at — they are about
/// masks, slots and arities — and it is *not* the same as the fixture being
/// blind to the parameters: `βⱼ` is an opaque symbol applied to `p⃗`, so the
/// parameters ride on the application whatever the body is
/// (`inductive.rs`'s `ctor_term_at_moves_with_the_parameters_…` measures
/// exactly this, and refuted the opposite reading). What this file had no
/// fixture for at all was the parameter **arity**: see
/// [`param_beta`] and the three-parameter cell at the end.
fn const_unit_beta(env: &mut Env, mach: &Machine, arity: usize) -> FnSym {
    let vars: Vec<kernel::FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let one = mach.wt.sums.unit();
    define_abbrev(env, &vars, &one).expect("β").0
}

/// An argument-type symbol of arity `np + j` whose body is its `which`-th
/// argument — **parameter-live** when `which < np`.
///
/// `decl_proj.rs` and `decl_fields.rs`'s idiom, brought here for the same
/// reason they have it: `Decidable.isTrue : p → Decidable p` types its field at
/// the parameter itself, and a `β` that ignores its arguments cannot express
/// that.
fn param_beta(env: &mut Env, np: usize, j: usize, which: usize) -> FnSym {
    let vars: Vec<kernel::FreeVar> = (0..np + j).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = args[which].clone();
    define_abbrev(env, &vars, &t).expect("β").0
}

// ─────────────────────────────────────────────────────────────────────────────
// Structural induction
// ─────────────────────────────────────────────────────────────────────────────

/// The premise's antecedent is one flat right-nested chain of `k + 2m` atoms in
/// the order *arguments, recursive arguments, induction hypotheses* — pinned at
/// an interleaved `Plain, Rec, Plain, Rec` mask, where a "fields then recs"
/// reading and a "grouped" reading both differ from this one.
#[test]
fn the_induction_step_orders_its_atoms_by_role_not_by_declaration() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    let b0 = const_unit_beta(env, &mach, 0);
    let b1 = const_unit_beta(env, &mach, 1);
    let spec = DeclSpec {
        params: 0,
        ctors: vec![
            CtorSpec { args: vec![], recs: 0, order: vec![] , rec_doms: Vec::new() },
            CtorSpec {
                args: vec![b0, b1],
                recs: 2,
                order: vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
                rec_doms: Vec::new(),
            },
        ],
    };
    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration");

    let zv = env.fresh_var();
    let phi = Formula::mem(Term::var(zv), mach.wt.sums.unit());
    let step = rect_step(env, &mach, &ind, 1, zv, &phi).expect("step");

    // Rebuilt from the kernel's own constructors: four binders in declaration
    // order, then `y₀ ∈ β₀`, `y₁ ∈ β₁(y₀)`, `t₀ ∈ W`, `t₁ ∈ W`, `φ(t₀)`,
    // `φ(t₁)`, then the conclusion at the constructor.
    let vs: Vec<kernel::FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ts: Vec<Term> = vs.iter().map(|v| Term::var(*v)).collect();
    let (ys, rs) = (&ts[..2], &ts[2..]);
    let ante = conj_of(&[
        Formula::mem(ys[0].clone(), Term::apply(b0, vec![])),
        Formula::mem(ys[1].clone(), Term::apply(b1, vec![ys[0].clone()])),
        Formula::mem(rs[0].clone(), ind.wty.clone()),
        Formula::mem(rs[1].clone(), ind.wty.clone()),
        phi.subst(zv, &rs[0]),
        phi.subst(zv, &rs[1]),
    ])
    .expect("six atoms");
    let concl = phi.subst(zv, &ind.ctor_term(&mach, 1, ys, rs).expect("constructor"));
    let want = vs
        .iter()
        .rev()
        .fold(Formula::imp(ante, concl), |acc, v| Formula::forall(*v, acc));
    assert_eq!(step, want, "the induction step is not the documented chain");

    // And the principle itself goes through at this shape — which is where the
    // two η rules are actually used: `k = 2` needs the telescope's, `m = 2`
    // needs [`recarg_eta`], and neither fires at the all-nullary declaration.
    let rule = decl_rect(env, &mach, &ind, zv, &phi).expect("induction at k=2, m=2");
    let hyp = conj_of(&[
        rect_step(env, &mach, &ind, 0, zv, &phi).expect("step 0"),
        want,
    ])
    .expect("two steps");
    let goal = Formula::forall(
        zv,
        Formula::imp(Formula::mem(Term::var(zv), ind.wty.clone()), phi.clone()),
    );
    assert!(derived::establishes(&rule, &Formula::imp(hyp, goal)));
}

/// **Three recursive slots, because two cannot distinguish a clamp.**
///
/// The test above pins the atom *order* at `m = 2`, and `m = 2` is enough only
/// for a permutation: every non-identity permutation of two moves both slots.
/// It is not enough for a **clamp**. Replace the slot index `j` by
/// `min(j, 1)` in either of the dependent path's two per-slot loops —
/// `rect::rect_step`'s induction-hypothesis atoms or
/// `motive::dep_minor`'s, which is where `ih_at_motive` is spent — and on
/// `{0, 1}` the clamp *is* the identity. Measured: the `motive` mutation
/// passes all 874 tests of this crate.
///
/// So the same `Rec, Plain, Rec, Rec` shape is put through both builders here,
/// and in each the clamped spelling — the third slot's hypothesis stated about
/// the *second* slot's binder — is pinned as a different formula.
#[test]
fn the_third_recursive_slot_is_positional_in_both_dependent_premises() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    let b0 = const_unit_beta(env, &mach, 0);
    let c1 = CtorSpec::with_order(
        vec![b0],
        3,
        vec![Slot::Rec, Slot::Plain, Slot::Rec, Slot::Rec],
    )
    .expect("a consistent three-slot mask");
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary(), c1]);
    let ind = Inductive::build(env, &mut mach, &spec).expect("the three-slot declaration");
    let s = mach.wt.sums.clone();
    let ap = &s.ap;
    let order = spec.ctors[1].order.clone();

    // ── the induction step: `φ(t₀), φ(t₁), φ(t₂)`, one per slot ─────────────
    let zv = env.fresh_var();
    let phi = Formula::mem(Term::var(zv), s.unit());
    let step = rect_step(env, &mach, &ind, 1, zv, &phi).expect("step");

    let vs: Vec<kernel::FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let tms: Vec<Term> = vs.iter().map(|v| Term::var(*v)).collect();
    let (ys, rs) = (&tms[..1], &tms[1..]);
    let step_want = |ihs: [&Term; 3]| {
        let ante = conj_of(&[
            Formula::mem(ys[0].clone(), Term::apply(b0, vec![])),
            Formula::mem(rs[0].clone(), ind.wty.clone()),
            Formula::mem(rs[1].clone(), ind.wty.clone()),
            Formula::mem(rs[2].clone(), ind.wty.clone()),
            phi.subst(zv, ihs[0]),
            phi.subst(zv, ihs[1]),
            phi.subst(zv, ihs[2]),
        ])
        .expect("seven atoms");
        let concl = phi.subst(zv, &ind.ctor_term(&mach, 1, ys, rs).expect("constructor"));
        vs.iter().rev().fold(Formula::imp(ante, concl), |acc, v| Formula::forall(*v, acc))
    };
    assert_eq!(
        step,
        step_want([&rs[0], &rs[1], &rs[2]]),
        "the induction step is not the documented chain at three slots"
    );
    assert_ne!(
        step,
        step_want([&rs[0], &rs[1], &rs[1]]),
        "a clamp on `rect_step`'s slot index would be invisible here"
    );

    // ── the dependent minor: `vⱼ ∈ app(C, tⱼ)`, one per slot ────────────────
    let (cv, sv) = (env.fresh_var(), env.fresh_var());
    let (tc, su) = (Term::var(cv), Term::var(sv));
    let dep = derived::inductive::motive::dep_minor(env, &mach, &ind, 1, &tc, &su)
        .expect("DEP₁");

    let qs: Vec<kernel::FreeVar> = (0..7).map(|_| env.fresh_var()).collect();
    let qt: Vec<Term> = qs.iter().map(|v| Term::var(*v)).collect();
    let (dy, dt, dv) = (&qt[..1], &qt[1..4], &qt[4..]);
    let dep_want = |subs: [&Term; 3]| {
        let ante = conj_of(&[
            Formula::mem(dy[0].clone(), Term::apply(b0, vec![])),
            Formula::mem(dt[0].clone(), ind.wty.clone()),
            Formula::mem(dt[1].clone(), ind.wty.clone()),
            Formula::mem(dt[2].clone(), ind.wty.clone()),
            Formula::mem(dv[0].clone(), ap.apply(tc.clone(), subs[0].clone())),
            Formula::mem(dv[1].clone(), ap.apply(tc.clone(), subs[1].clone())),
            Formula::mem(dv[2].clone(), ap.apply(tc.clone(), subs[2].clone())),
        ])
        .expect("seven atoms");
        let concl = Formula::mem(
            derived::inductive::applied_minor(ap, &order, &su, dy, dt, dv),
            ap.apply(tc.clone(), ind.ctor_term(&mach, 1, dy, dt).expect("constructor")),
        );
        qs.iter().rev().fold(Formula::imp(ante, concl), |acc, v| Formula::forall(*v, acc))
    };
    assert_eq!(
        dep,
        dep_want([&dt[0], &dt[1], &dt[2]]),
        "`DEP₁` is not Lean's dependent minor premise at three slots"
    );
    assert_ne!(
        dep,
        dep_want([&dt[0], &dt[1], &dt[1]]),
        "a clamp on `dep_minor`'s slot index would be invisible here"
    );

    // ── and the recursor itself derives at this width ───────────────────────
    //
    // `DepRecursor::build` runs `dep::fire` for the typing and ι theorems, and
    // `fire`'s own per-slot loops assemble one guard atom per slot from
    // `k_atom[k + j]` and `minor_subs[j]`. Nothing else in this crate reaches
    // them at three slots, so a clamp there is caught by this line alone:
    // `guard_atoms_match` compares the atoms against `ih_at_motive` and a
    // clamped `k_phi` makes the whole build `None`.
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("the general recursor at three slots");
    derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("the dependent recursor at three slots");
}

/// **Non-vacuity.** At a three-constructor enumeration the premise is
/// discharged outright and the principle yields a closed, unconditional
/// theorem that says the carrier has *no other members* — something no
/// per-constructor typing rule states and `w_rect` cannot say at all, because
/// it does not know what a constructor is.
#[test]
fn induction_proves_a_three_constructor_enumeration_has_no_junk() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    let spec = DeclSpec {
        params: 0,
        ctors: (0..3)
            .map(|_| CtorSpec { args: vec![], recs: 0, order: vec![] , rec_doms: Vec::new() })
            .collect(),
    };
    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration");
    let es: Vec<Term> = (0..3)
        .map(|i| ind.ctor_term(&mach, i, &[], &[]).expect("constructor"))
        .collect();

    let zv = env.fresh_var();
    let phi = disj_of(&es.iter().map(|e| Formula::eq(Term::var(zv), e.clone())).collect::<Vec<_>>())
        .expect("three disjuncts");
    let rule = decl_rect(env, &mach, &ind, zv, &phi).expect("induction");

    // Each step is `eᵢ = e₀ ∨ (eᵢ = e₁ ∨ eᵢ = e₂)`, by reflexivity.
    let steps: Vec<Thm> = (0..3)
        .map(|i| {
            let atoms: Vec<Formula> =
                es.iter().map(|e| Formula::eq(es[i].clone(), e.clone())).collect();
            let mut th = Thm::eq_refl(es[i].clone());
            if let Some(tail) = disj_of(&atoms[i + 1..]) {
                th = Thm::mp(&derived::funcs::or_intro_left(atoms[i].clone(), tail), &th)
                    .expect("left injection");
            }
            for j in (0..i).rev() {
                let tail = disj_of(&atoms[j + 1..]).expect("a non-empty tail");
                th = Thm::mp(&derived::funcs::or_intro_right(atoms[j].clone(), tail), &th)
                    .expect("right injection");
            }
            th
        })
        .collect();

    let hyp = steps
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .expect("the premise");
    let out = Thm::mp(&rule, &hyp).expect("modus ponens");

    let want = Formula::forall(
        zv,
        Formula::imp(Formula::mem(Term::var(zv), ind.wty.clone()), phi.clone()),
    );
    assert!(derived::establishes(&out, &want), "no-junk is not what came out");
    assert!(closed(out.concl()), "the no-junk theorem should be closed");

    // …and it is not vacuous: the three constructors are provably distinct, so
    // the carrier it describes has three members, not one.
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        let d = ind.distinct(env, &mach, i, j).expect("distinctness");
        assert!(d.hyps().is_empty());
    }
    let _ = inst_all(&out, &[es[2].clone()]).expect("instantiable at a constructor");
}

// ─────────────────────────────────────────────────────────────────────────────
// The guarded minors
// ─────────────────────────────────────────────────────────────────────────────

/// A `List`-shaped declaration: `nil`, and `cons` with one field and one
/// recursive argument. `nil` needs no guard; `cons` needs a three-level lambda
/// nest and one Separation.
fn list_like(env: &mut Env, mach: &mut Machine) -> (Inductive, FnSym) {
    let b0 = const_unit_beta(env, mach, 0);
    let spec = DeclSpec {
        params: 0,
        ctors: vec![
            CtorSpec { args: vec![], recs: 0, order: vec![] , rec_doms: Vec::new() },
            CtorSpec { args: vec![b0], recs: 1, order: vec![Slot::Plain, Slot::Rec] , rec_doms: Vec::new() },
        ],
    };
    (Inductive::build(env, mach, &spec).expect("declaration"), b0)
}

#[test]
fn the_guarded_minors_discharge_hyp_at_a_variable_motive() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let (ind, _) = list_like(env, &mut mach);

    let motive = env.fresh_var();
    let minors: Vec<kernel::FreeVar> = (0..2).map(|_| env.fresh_var()).collect();
    let target = env.fresh_var();
    let gm = derived::inductive::guard::GuardedMinors::build(
        env, &mach, &ind, motive, &minors, target,
    )
    .expect("guarded minors");

    // `nil` is unguarded — its minor is Lean's own; `cons` is not.
    assert_eq!(gm.terms[0], Term::var(minors[0]), "a field-free constructor needs no guard");
    assert_ne!(gm.terms[1], Term::var(minors[1]), "a recursive constructor must be guarded");
    assert!(gm.fires[0].is_none() && gm.fires[1].is_some());

    // `HYP` at the guarded minors follows from `COD ∧ DEP` alone.
    let want = Formula::imp(
        Formula::and(gm.cod.clone(), gm.dep.clone()),
        conj_of(&gm.minor_typed).expect("HYP"),
    );
    assert!(derived::establishes(&gm.hyp, &want), "HYP is not discharged as documented");
}

// ─────────────────────────────────────────────────────────────────────────────
// The recursor at a dependent motive
// ─────────────────────────────────────────────────────────────────────────────

/// The whole development goes through at a recursive declaration, and both
/// statements come out at **Lean's own** minor premises — the guard, the
/// lambda nest and the Separation are gone from what a caller reads.
#[test]
fn the_dependent_recursor_is_derived_at_a_recursive_declaration() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let (ind, b0) = list_like(env, &mut mach);
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("dependent recursor");

    let ap = &mach.wt.sums.ap;
    let tc = Term::var(dr.motive);

    // The typing obligation, rebuilt.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let want = Formula::imp(
        dr.premise.clone(),
        Formula::forall(
            zv,
            Formula::imp(
                Formula::mem(tz.clone(), ind.wty.clone()),
                Formula::mem(
                    ap.apply(dr.rec.clone(), tz.clone()),
                    ap.apply(tc.clone(), tz.clone()),
                ),
            ),
        ),
    );
    assert!(derived::establishes(&dr.typing, &want), "the typing obligation is not what came out");

    // The ι rule of `cons`, rebuilt: one field, one recursive argument, the
    // recursive call live, and Lean's minor `S₁` — not the guarded one.
    let (yv, tv) = (env.fresh_var(), env.fresh_var());
    let (ty, tt) = (Term::var(yv), Term::var(tv));
    let concl = Formula::eq(
        ap.apply(dr.rec.clone(), ind.ctor_term(&mach, 1, std::slice::from_ref(&ty), std::slice::from_ref(&tt)).unwrap()),
        ap.apply(
            ap.apply(
                ap.apply(Term::var(dr.minors[1]), ty.clone()),
                tt.clone(),
            ),
            ap.apply(dr.rec.clone(), tt.clone()),
        ),
    );
    let ante = conj_of(&[
        Formula::mem(ty, Term::apply(b0, vec![])),
        Formula::mem(tt, ind.wty.clone()),
    ])
    .expect("two atoms");
    let want_iota = Formula::imp(
        dr.premise.clone(),
        Formula::forall(yv, Formula::forall(tv, Formula::imp(ante, concl))),
    );
    assert!(
        derived::establishes(&dr.iota[1], &want_iota),
        "the dependent ι rule is not stated at Lean's minor"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Non-vacuity: a motive that really does differ from constructor to constructor
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ H → ∀v. φ`, for `v` not free in `H`.
fn gen_under(v: kernel::FreeVar, h: &Formula, thm: &Thm) -> Thm {
    let (_, body) = thm.concl().as_imp().expect("an implication");
    Thm::mp(&Thm::ax_dist(v, h.clone(), body).expect("dist"), &Thm::gen(v, thm)).expect("mp")
}

/// `⊢ H → φ[t⃗]` from `⊢ H → ∀v⃗. φ`.
fn hyp_inst(thm: &Thm, ts: &[Term]) -> Thm {
    let mut cur = thm.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp().expect("an implication");
        cur = derived::syl(&cur, &Thm::ax_inst(all, t.clone()).expect("inst")).expect("syl");
    }
    cur
}

/// `⊢ H → φ(y)` from `⊢ H → x = y` and `⊢ H → φ(x)`.
fn rewrite_under<F: Fn(Term) -> Formula>(env: &mut Env, h_eq: &Thm, ctx: F, h_phi: &Thm) -> Thm {
    let (h, eq) = h_eq.concl().as_imp().expect("an implication");
    let (x, y) = eq.as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    let step = derived::hyp_mp(&derived::a1i(&leib, h), h_eq).expect("mp");
    derived::hyp_mp(&step, h_phi).expect("mp")
}

/// `⊢ H → y = x` from `⊢ H → x = y`.
fn hyp_eq_symm(env: &mut Env, h: &Thm) -> Thm {
    let (hh, eq) = h.concl().as_imp().expect("imp");
    let (x, y) = eq.as_eq().expect("eq");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x.clone(), y, hole, Formula::eq(Term::var(hole), x.clone()));
    let refl = derived::a1i(&Thm::eq_refl(x), hh.clone());
    let step = derived::hyp_mp(&derived::a1i(&leib, hh), h).expect("mp");
    derived::hyp_mp(&step, &refl).expect("mp")
}

/// `⊢ H → x = z` from `⊢ H → x = y` and `⊢ H → y = z`.
fn hyp_eq_trans(env: &mut Env, xy: &Thm, yz: &Thm) -> Thm {
    let (x, _) = xy.concl().as_imp().expect("imp").1.as_eq().expect("eq");
    rewrite_under(env, yz, move |q| Formula::eq(x.clone(), q), xy)
}

/// The motive `λx. {x}` as a lambda graph over the carrier — a motive whose
/// value at any two *distinct* carrier elements is a different set.
struct Motive {
    c: Term,
    /// `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = sing(a))`
    beta: Thm,
    /// `⊢ ∀x. sing(x) = {x}`
    sing_ax: Thm,
}

fn singleton_motive(env: &mut Env, mach: &Machine, ind: &Inductive) -> Motive {
    let ap = &mach.wt.sums.ap;
    let xv = env.fresh_var();
    let (sing, sing_ax) =
        define_abbrev(env, &[xv], &derived::singleton(ap.sets.up, Term::var(xv))).expect("sing");
    let (lam, lam_ax) = derived::funcs::lambda(env, ap, sing).expect("lambda");
    let beta = derived::funcs::beta_conditional(env, ap, sing, lam, &lam_ax).expect("beta");
    Motive { c: Term::apply(lam, vec![ind.wty.clone()]), beta, sing_ax }
}

/// `⊢ a ∈ W → app(C, a) = {a}`.
fn motive_at(env: &mut Env, mach: &Machine, ind: &Inductive, mot: &Motive, a: &Term) -> Thm {
    let hyp = Formula::mem(a.clone(), ind.wty.clone());
    let step = inst_all(&mot.beta, &[ind.wty.clone(), a.clone()]).expect("beta at a");
    let unfold = derived::a1i(
        &inst_all(&mot.sing_ax, std::slice::from_ref(a)).expect("sing at a"),
        hyp,
    );
    let _ = mach;
    hyp_eq_trans(env, &step, &unfold)
}

/// `⊢ ctorᵢ(y⃗,t⃗) ∈ W` for a nullary constructor.
fn nullary_in_carrier(env: &mut Env, ind: &Inductive, i: usize) -> Thm {
    let ty_ax = &ind.ty_ax;
    let (ind_t, w_t) = ty_ax.concl().as_eq().expect("the carrier equation");
    let hole = env.fresh_var();
    let e = ind.ctors[i].term.clone();
    let leib = Thm::eq_leibniz(ind_t, w_t, hole, Formula::mem(e, Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, ty_ax).expect("mp"), &ind.ctors[i].mem).expect("mp")
}

/// `⊢ COD(C, W ∪ {∅})` for the singleton motive.
fn cod_for_motive(env: &mut Env, mach: &Machine, ind: &Inductive, mot: &Motive) -> (Term, Thm) {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let t = derived::funspace::bin_union(
        &ap.sets,
        ind.wty.clone(),
        derived::singleton(ap.sets.up, s.zero()),
    );
    let (inj_l, inj_r) = derived::funspace::mem_bin_union(env, &ap.sets).expect("injections");
    let sing_zero = derived::singleton(ap.sets.up, s.zero());

    // `∅ ∈ {∅} ⊆ T`.
    let in_sing = Thm::mp(
        &derived::iff_mpr(
            &inst_all(&ap.mem_sing, &[s.zero(), s.zero()]).expect("mem_sing"),
        )
        .expect("mpr"),
        &Thm::eq_refl(s.zero()),
    )
    .expect("mp");
    let empty_in_t = Thm::mp(
        &inst_all(&inj_r, &[ind.wty.clone(), sing_zero.clone(), s.zero()]).expect("right"),
        &in_sing,
    )
    .expect("mp");

    // `∀x ∈ W. ∀y ∈ app(C,x). y ∈ T`.
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let hx = Formula::mem(tx.clone(), ind.wty.clone());
    let my = Formula::mem(ty.clone(), ap.apply(mot.c.clone(), tx.clone()));
    let k = Formula::and(hx.clone(), my.clone());
    let k_hx = derived::and_left(hx.clone(), my.clone());
    let k_my = derived::and_right(hx.clone(), my);

    let eq = derived::syl(&k_hx, &motive_at(env, mach, ind, mot, &tx)).expect("syl");
    let ty_c = ty.clone();
    let in_sing_x = rewrite_under(env, &eq, move |q| Formula::mem(ty_c.clone(), q), &k_my);
    let is_x = derived::hyp_mp(
        &derived::a1i(
            &derived::iff_mp(&inst_all(&ap.mem_sing, &[tx.clone(), ty.clone()]).expect("ms"))
                .expect("mp direction"),
            k.clone(),
        ),
        &in_sing_x,
    )
    .expect("mp");
    let back = hyp_eq_symm(env, &is_x);
    let in_w = rewrite_under(env, &back, |q| Formula::mem(q, ind.wty.clone()), &k_hx);
    let in_t = derived::hyp_mp(
        &derived::a1i(
            &inst_all(&inj_l, &[ind.wty.clone(), sing_zero, ty.clone()]).expect("left"),
            k.clone(),
        ),
        &in_w,
    )
    .expect("mp");

    let inner = gen_under(yv, &hx, &derived::uncurry(&in_t).expect("uncurry"));
    let covers = Thm::gen(xv, &inner);
    let out = derived::and_intro(&covers, &empty_in_t);
    let want = derived::inductive::motive::cod(env, s, &ind.wty, &mot.c, &t);
    assert!(derived::establishes(&out, &want), "COD is not what was built");
    (t, out)
}

/// **Non-vacuity.** A three-constructor enumeration at the motive `λx. {x}`,
/// whose value differs at all three constructors. Every hypothesis is
/// discharged, and what comes out is closed: the eliminator's value at each
/// constructor is *that constructor's own minor premise*, and the three are
/// provably different sets — so nothing here is satisfied by a recursor that
/// computes to a constant, nor by a target that swallows everything.
#[test]
fn the_dependent_recursor_computes_to_the_minor_at_three_distinct_motive_values() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    let spec = DeclSpec {
        params: 0,
        ctors: (0..3).map(|_| CtorSpec { args: vec![], recs: 0, order: vec![] , rec_doms: Vec::new() }).collect(),
    };
    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration");
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("dependent recursor");

    let ap = &mach.wt.sums.ap;
    let es: Vec<Term> = (0..3).map(|i| ind.ctors[i].term.clone()).collect();
    let mot = singleton_motive(env, &mach, &ind);
    let (t_target, cod_thm) = cod_for_motive(env, &mach, &ind, &mot);

    // `DEPᵢ` at `Sᵢ := eᵢ`: `eᵢ ∈ app(C, eᵢ)`, since `app(C,eᵢ) = {eᵢ}`.
    let deps: Vec<Thm> = (0..3)
        .map(|i| {
            let in_w = nullary_in_carrier(env, &ind, i);
            let eq = Thm::mp(&motive_at(env, &mach, &ind, &mot, &es[i]), &in_w).expect("mp");
            let refl = Thm::mp(
                &derived::iff_mpr(
                    &inst_all(&ap.mem_sing, &[es[i].clone(), es[i].clone()]).expect("ms"),
                )
                .expect("mpr"),
                &Thm::eq_refl(es[i].clone()),
            )
            .expect("mp");
            let back = derived::eq_symm(env, &eq).expect("symm");
            let hole = env.fresh_var();
            let (l, r) = back.concl().as_eq().expect("eq");
            let leib =
                Thm::eq_leibniz(l, r, hole, Formula::mem(es[i].clone(), Term::var(hole)));
            Thm::mp(&Thm::mp(&leib, &back).expect("mp"), &refl).expect("mp")
        })
        .collect();

    let dep_all = deps
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .expect("DEP");
    let pre = derived::and_intro(&cod_thm, &dep_all);

    // Instantiate the schemas at this motive, these minors and this target.
    let mut quant = vec![dr.motive];
    quant.extend(dr.minors.iter().copied());
    quant.push(dr.target);
    let mut args = vec![mot.c.clone()];
    args.extend(es.iter().cloned());
    args.push(t_target.clone());
    let at = |th: &Thm| inst_all(&derived::gen_all(&quant, th), &args).expect("instantiable");

    let typing = Thm::mp(&at(&dr.typing), &pre).expect("the typing obligation, discharged");
    assert!(typing.hyps().is_empty() && closed(typing.concl()), "typing should be closed");

    // The ι rules: `app(drec, eᵢ) = eᵢ`, three different values.
    let drec = {
        let mut f = Formula::eq(dr.rec.clone(), dr.rec.clone());
        for (v, a) in quant.iter().zip(&args) {
            f = f.subst(*v, a);
        }
        f.as_eq().expect("an equation").0
    };
    for (i, e) in es.iter().enumerate() {
        let iota = Thm::mp(&at(&dr.iota[i]), &pre).expect("ι, discharged");
        assert!(iota.hyps().is_empty() && closed(iota.concl()), "ι should be closed");
        let want = Formula::eq(ap.apply(drec.clone(), e.clone()), e.clone());
        assert_eq!(*iota.concl(), want, "ι does not compute to this constructor's own minor");
    }

    // The motive really is dependent: `app(C,e₀)`, `app(C,e₁)` and `app(C,e₂)`
    // are three provably distinct sets.
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        let d = ind.distinct(env, &mach, i, j).expect("distinctness");
        let inj = derived::singleton_inj(env, ap.sets.up, &ap.mem_sing).expect("singleton_inj");
        let at_ij = inst_all(&inj, &[es[i].clone(), es[j].clone()]).expect("at these two");
        let contra = derived::syl(&at_ij, &inst_all(&d, &[]).unwrap_or_else(|| d.clone()))
            .expect("distinct constructors have distinct singletons");
        assert!(contra.hyps().is_empty());
    }
}

/// `⊢ H → app(x,a) = app(y,a)` from `⊢ H → x = y`.
fn hyp_app_congr(env: &mut Env, ap: &derived::funcs::Apply, h_eq: &Thm, a: &Term) -> Thm {
    let (h, eq) = h_eq.concl().as_imp().expect("imp");
    let (x, y) = eq.as_eq().expect("eq");
    let hole = env.fresh_var();
    let left = ap.apply(x.clone(), a.clone());
    let leib = Thm::eq_leibniz(
        x,
        y,
        hole,
        Formula::eq(left.clone(), ap.apply(Term::var(hole), a.clone())),
    );
    let refl = derived::a1i(&Thm::eq_refl(left), h.clone());
    let step = derived::hyp_mp(&derived::a1i(&leib, h), h_eq).expect("mp");
    derived::hyp_mp(&step, &refl).expect("mp")
}

/// Lean's `cons` minor premise for the motive `λx. {x}`: the curried graph
/// `λ(y : β₀) (t : W) (v : app(C,t)). cons(y,t)`, three lambda levels with the
/// innermost domain **depending on `t`** — which is what lets the beta chain run
/// under exactly `DEP_cons`'s own antecedent.
struct ConsMinor {
    term: Term,
    /// One `(abbreviation axiom, beta rule)` per level, outermost first.
    levels: Vec<(Thm, Thm)>,
    doms: Vec<Term>,
}

fn cons_minor(env: &mut Env, mach: &Machine, ind: &Inductive, mot: &Motive, b0: FnSym) -> ConsMinor {
    let ap = &mach.wt.sums.ap;
    let (yv, tv, vv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, tt) = (Term::var(yv), Term::var(tv));
    let body = ind.ctor_term(mach, 1, std::slice::from_ref(&ty), std::slice::from_ref(&tt)).expect("cons");

    let (ci, ci_ax) = define_abbrev(env, &[yv, tv, vv], &body).expect("inner body");
    let (lam_ci, lam_ci_ax) = derived::funcs::lambda_n(env, ap, ci).expect("inner graph");
    let ci_beta = derived::funcs::beta_conditional_n(env, ap, ci, lam_ci, &lam_ci_ax).expect("β");

    let inner_dom = ap.apply(mot.c.clone(), tt.clone());
    let (cm, cm_ax) = define_abbrev(
        env,
        &[yv, tv],
        &Term::apply(lam_ci, vec![ty.clone(), tt.clone(), inner_dom]),
    )
    .expect("middle body");
    let (lam_cm, lam_cm_ax) = derived::funcs::lambda_n(env, ap, cm).expect("middle graph");
    let cm_beta = derived::funcs::beta_conditional_n(env, ap, cm, lam_cm, &lam_cm_ax).expect("β");

    let (cq, cq_ax) =
        define_abbrev(env, &[yv], &Term::apply(lam_cm, vec![ty, ind.wty.clone()])).expect("outer");
    let (lam_cq, lam_cq_ax) = derived::funcs::lambda(env, ap, cq).expect("outer graph");
    let cq_beta = derived::funcs::beta_conditional(env, ap, cq, lam_cq, &lam_cq_ax).expect("β");

    let beta0 = Term::apply(b0, vec![]);
    ConsMinor {
        term: Term::apply(lam_cq, vec![beta0.clone()]),
        levels: vec![(cq_ax, cq_beta), (cm_ax, cm_beta), (ci_ax, ci_beta)],
        doms: vec![beta0, ind.wty.clone()],
    }
}

/// `⊢ ctx → app(app(app(S_cons, y), t), v) = cons(y,t)`, given the three
/// memberships the binders' domains ask for.
#[allow(clippy::too_many_arguments)]
fn cons_minor_beta(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    mot: &Motive,
    sc: &ConsMinor,
    ctx: &Formula,
    ks: [&Thm; 3],
    y: &Term,
    t: &Term,
    v: &Term,
) -> Thm {
    let ap = &mach.wt.sums.ap;
    let inner_dom = ap.apply(mot.c.clone(), t.clone());
    let args: [Vec<Term>; 3] = [
        vec![sc.doms[0].clone(), y.clone()],
        vec![y.clone(), sc.doms[1].clone(), t.clone()],
        vec![y.clone(), t.clone(), inner_dom, v.clone()],
    ];
    let unfold_args: [Vec<Term>; 3] = [
        vec![y.clone()],
        vec![y.clone(), t.clone()],
        vec![y.clone(), t.clone(), v.clone()],
    ];
    let binders = [y.clone(), t.clone(), v.clone()];

    let mut chain = derived::a1i(&Thm::eq_refl(sc.term.clone()), ctx.clone());
    for level in 0..3 {
        let stepped = hyp_app_congr(env, ap, &chain, &binders[level]);
        let beta = derived::hyp_mp(
            &derived::a1i(
                &inst_all(&sc.levels[level].1, &args[level]).expect("β at these arguments"),
                ctx.clone(),
            ),
            ks[level],
        )
        .expect("mp");
        let unfold = derived::a1i(
            &inst_all(&sc.levels[level].0, &unfold_args[level]).expect("the abbreviation"),
            ctx.clone(),
        );
        let half = hyp_eq_trans(env, &stepped, &beta);
        chain = hyp_eq_trans(env, &half, &unfold);
    }
    let _ = ind;
    chain
}

/// **Non-vacuity, recursive.** `List`-shaped, at the same everywhere-different
/// motive `λx. {x}`, with Lean's `cons` minor the real curried graph
/// `λ y t v. cons(y,t)`. Every hypothesis is discharged and the eliminator
/// computes to the **identity**: `drec(nil) = nil` and
/// `drec(cons(y,t)) = cons(y,t)`, two provably different values. This is the
/// case the `⋃img(C)` obstruction is about — the guard has to fire through a
/// live recursive call for `drec(t)` to be usable at `app(C,t)`.
#[test]
fn the_dependent_recursor_computes_through_a_live_recursive_call() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let (ind, b0) = list_like(env, &mut mach);
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("dependent recursor");

    let s = mach.wt.sums.clone();
    let ap = &s.ap;
    let mot = singleton_motive(env, &mach, &ind);
    let (t_target, cod_thm) = cod_for_motive(env, &mach, &ind, &mot);
    let sc = cons_minor(env, &mach, &ind, &mot, b0);
    let nil = ind.ctors[0].term.clone();

    // `DEP_nil`: `nil ∈ app(C, nil)`.
    let dep_nil = {
        let in_w = nullary_in_carrier(env, &ind, 0);
        let eq = Thm::mp(&motive_at(env, &mach, &ind, &mot, &nil), &in_w).expect("mp");
        let refl = Thm::mp(
            &derived::iff_mpr(&inst_all(&ap.mem_sing, &[nil.clone(), nil.clone()]).unwrap())
                .expect("mpr"),
            &Thm::eq_refl(nil.clone()),
        )
        .expect("mp");
        let back = derived::eq_symm(env, &eq).expect("symm");
        let (l, r) = back.concl().as_eq().expect("eq");
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(l, r, hole, Formula::mem(nil.clone(), Term::var(hole)));
        Thm::mp(&Thm::mp(&leib, &back).expect("mp"), &refl).expect("mp")
    };

    // `DEP_cons`, under its own antecedent.
    let (yv, tv, vv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ty, tt, tv_t) = (Term::var(yv), Term::var(tv), Term::var(vv));
    let atoms = [
        Formula::mem(ty.clone(), Term::apply(b0, vec![])),
        Formula::mem(tt.clone(), ind.wty.clone()),
        Formula::mem(tv_t.clone(), ap.apply(mot.c.clone(), tt.clone())),
    ];
    let ctx = conj_of(&atoms).expect("three atoms");
    let ks: Vec<Thm> = (0..3)
        .map(|j| derived::conj_proj(&atoms, j).expect("projection"))
        .collect();
    let dep_cons = {
        let beta = cons_minor_beta(
            env, &mach, &ind, &mot, &sc, &ctx,
            [&ks[0], &ks[1], &ks[2]], &ty, &tt, &tv_t,
        );
        let cons_t = ind.ctor_term(&mach, 1, std::slice::from_ref(&ty), std::slice::from_ref(&tt)).expect("cons");
        // `cons(y,t) ∈ W`, then `app(C, cons) = {cons}` and `cons ∈ {cons}`.
        let mem_rule = inst_all(&ind.ctors[1].mem, &[ty.clone(), tt.clone()]).expect("Ctor::mem");
        let ty_ax = &ind.ty_ax;
        let (ind_t, w_t) = ty_ax.concl().as_eq().expect("carrier equation");
        let hole = env.fresh_var();
        let back = Thm::eq_leibniz(
            w_t.clone(),
            ind_t.clone(),
            hole,
            Formula::mem(tt.clone(), Term::var(hole)),
        );
        let t_in_ind = derived::hyp_mp(
            &derived::a1i(
                &Thm::mp(&back, &derived::eq_symm(env, ty_ax).expect("symm")).expect("mp"),
                ctx.clone(),
            ),
            &ks[1],
        )
        .expect("mp");
        let cons_in_ind = derived::hyp_mp(
            &derived::a1i(&mem_rule, ctx.clone()),
            &derived::hyp_and(&ks[0], &t_in_ind).expect("and"),
        )
        .expect("mp");
        let hole2 = env.fresh_var();
        let fwd = Thm::eq_leibniz(
            ind_t,
            w_t,
            hole2,
            Formula::mem(cons_t.clone(), Term::var(hole2)),
        );
        let cons_in_w = derived::hyp_mp(
            &derived::a1i(&Thm::mp(&fwd, ty_ax).expect("mp"), ctx.clone()),
            &cons_in_ind,
        )
        .expect("mp");
        let eq_c = derived::hyp_mp(
            &derived::a1i(&motive_at(env, &mach, &ind, &mot, &cons_t), ctx.clone()),
            &cons_in_w,
        )
        .expect("mp");
        let refl = derived::a1i(
            &Thm::mp(
                &derived::iff_mpr(
                    &inst_all(&ap.mem_sing, &[cons_t.clone(), cons_t.clone()]).unwrap(),
                )
                .expect("mpr"),
                &Thm::eq_refl(cons_t.clone()),
            )
            .expect("mp"),
            ctx.clone(),
        );
        let back_c = hyp_eq_symm(env, &eq_c);
        let cons_c = cons_t.clone();
        let in_motive =
            rewrite_under(env, &back_c, move |q| Formula::mem(cons_c.clone(), q), &refl);
        let beta_back = hyp_eq_symm(env, &beta);
        let body = rewrite_under(
            env,
            &beta_back,
            |q| Formula::mem(q, ap.apply(mot.c.clone(), cons_t.clone())),
            &in_motive,
        );
        let mut out = body;
        for v in [vv, tv, yv] {
            out = Thm::gen(v, &out);
        }
        out
    };
    let want_dep = derived::inductive::motive::dep_minor(env, &mach, &ind, 1, &mot.c, &sc.term)
        .expect("DEP_cons");
    assert!(derived::establishes(&dep_cons, &want_dep), "DEP_cons is not what was built");

    let pre = derived::and_intro(&cod_thm, &derived::and_intro(&dep_nil, &dep_cons));

    // Instantiate and discharge.
    let mut quant = vec![dr.motive];
    quant.extend(dr.minors.iter().copied());
    quant.push(dr.target);
    let args = vec![mot.c.clone(), nil.clone(), sc.term.clone(), t_target];
    let at = |th: &Thm| inst_all(&derived::gen_all(&quant, th), &args).expect("instantiable");
    let drec = {
        let mut f = Formula::eq(dr.rec.clone(), dr.rec.clone());
        for (v, a) in quant.iter().zip(&args) {
            f = f.subst(*v, a);
        }
        f.as_eq().expect("eq").0
    };

    let typing = Thm::mp(&at(&dr.typing), &pre).expect("typing");
    assert!(typing.hyps().is_empty() && closed(typing.concl()));

    // `drec(nil) = nil` — closed, and Lean's own minor.
    let iota_nil = Thm::mp(&at(&dr.iota[0]), &pre).expect("ι nil");
    assert_eq!(
        *iota_nil.concl(),
        Formula::eq(ap.apply(drec.clone(), nil.clone()), nil.clone())
    );
    assert!(closed(iota_nil.concl()));

    // `drec(cons(y,t)) = S_cons y t (drec t) = cons(y,t)` — the recursive call
    // is live, and the guard fires because `drec t ∈ app(C,t)` really holds.
    let iota_cons = Thm::mp(&at(&dr.iota[1]), &pre).expect("ι cons");
    let hyp2 = conj_of(&[atoms[0].clone(), atoms[1].clone()]).expect("two atoms");
    let k_y = derived::conj_proj(&[atoms[0].clone(), atoms[1].clone()], 0).unwrap();
    let k_t = derived::conj_proj(&[atoms[0].clone(), atoms[1].clone()], 1).unwrap();
    let rec_t = ap.apply(drec.clone(), tt.clone());
    let k_v = derived::hyp_mp(
        &hyp_inst(&derived::a1i(&typing, hyp2.clone()), std::slice::from_ref(&tt)),
        &k_t,
    )
    .expect("the induction hypothesis, from the typing theorem");
    let collapse = cons_minor_beta(
        env, &mach, &ind, &mot, &sc, &hyp2, [&k_y, &k_t, &k_v], &ty, &tt, &rec_t,
    );
    let at_cons = hyp_inst(&derived::a1i(&iota_cons, hyp2.clone()), &[ty.clone(), tt.clone()]);
    let fired = derived::hyp_mp(
        &at_cons,
        &derived::hyp_and(&k_y, &k_t).expect("and"),
    )
    .expect("mp");
    let identity = hyp_eq_trans(env, &fired, &collapse);
    let cons_t = ind.ctor_term(&mach, 1, std::slice::from_ref(&ty), std::slice::from_ref(&tt)).expect("cons");
    assert!(
        derived::establishes(
            &identity,
            &Formula::imp(hyp2, Formula::eq(ap.apply(drec, cons_t.clone()), cons_t.clone()))
        ),
        "the eliminator should be the identity at this motive"
    );

    // And the two values really are different, so nothing computed to a constant.
    let d = ind.distinct(env, &mach, 0, 1).expect("distinctness");
    assert!(inst_all(&d, &[ty, tt]).is_some());
}

// ─────────────────────────────────────────────────────────────────────────────
// Structural induction at a function-typed recursive argument
// ─────────────────────────────────────────────────────────────────────────────

/// `RTree = leaf | node (children : Bool → RTree)` — the declaration whose
/// recursive argument is a **function**.
fn rtree_spec(env: &mut Env, mach: &mut Machine) -> DeclSpec {
    let s = mach.wt.sums.clone();
    mach.syms.ensure(env, &s, 4).expect("the sum symbols");
    let boolean = mach.syms.finord(&s, 2).expect("finord(2)");
    let (bool_sym, _) = define_abbrev(env, &[], &boolean).expect("Bool");
    DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::with_rec_doms(Vec::new(), vec![vec![bool_sym]])],
    )
}

/// `leaf | plain (r : ind) | node (g : Bool → ind) | both (r : ind) (g : Bool → ind)`
/// — three shapes of recursive argument in one declaration, the fourth
/// constructor **mixed**. Two constructors cannot tell the two grains apart.
fn mixed_spec(env: &mut Env, mach: &mut Machine) -> DeclSpec {
    let s = mach.wt.sums.clone();
    mach.syms.ensure(env, &s, 4).expect("the sum symbols");
    let boolean = mach.syms.finord(&s, 2).expect("finord(2)");
    let (bool_sym, _) = define_abbrev(env, &[], &boolean).expect("Bool");
    DeclSpec::new(
        0,
        vec![
            CtorSpec::nullary(),
            CtorSpec::new(Vec::new(), 1),
            CtorSpec::with_rec_doms(Vec::new(), vec![vec![bool_sym]]),
            CtorSpec::with_rec_doms(Vec::new(), vec![vec![], vec![bool_sym]]),
        ],
    )
}

/// **Three function-typed slots at three distinct domains**, so that the push
/// at each one is at *its own* `β₀ⱼ(p⃗)`.
///
/// Two slots catch a permutation and nothing else: `j ↦ min(j,1)` is the
/// identity on `{0,1}`, and every per-slot index in `Inductive::minor_args`,
/// `rec_slot_betas` and `rec_telescopes` is a slot-to-position correspondence a
/// clamp would survive. The three domains are three *declarations* of the same
/// shape rather than one used three times, so what separates them is their
/// defining symbols and not an arity.
///
/// **Measured: the clamp survived this crate's whole suite without this.** The
/// `RTree` and mixed fixtures have one function-typed slot each, so `j` is
/// always `0` in both and `min(j,1)` cannot be seen. It was caught only in
/// `mini`, by a frontier cell three constructions downstream, which is the
/// wrong place for a `derived` index bug to be found.
#[test]
fn each_function_typed_slot_is_pushed_onto_its_own_argument_type() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let s = mach.wt.sums.clone();
    mach.syms.ensure(env, &s, 4).expect("the sum symbols");
    let doms: Vec<FnSym> = (0..3).map(|_| const_unit_beta(env, &mach, 0)).collect();
    let spec = DeclSpec::new(
        0,
        vec![
            CtorSpec::nullary(),
            CtorSpec::with_rec_doms(
                Vec::new(),
                doms.iter().map(|d| vec![*d]).collect::<Vec<_>>(),
            ),
        ],
    );
    let ind = Inductive::build(env, &mut mach, &spec).expect("three function-typed slots");
    let px = mach.push(env).expect("the push operator");

    let betas = ind.rec_slot_betas(1);
    assert_eq!(betas.len(), 3, "three slots");
    for (j, d) in doms.iter().enumerate() {
        assert_eq!(
            betas[j],
            Some(Term::apply(*d, Vec::new())),
            "slot {j}'s β₀(p⃗) is not its own domain"
        );
    }
    // Three *distinct* argument types, which is what makes the check above a
    // check: at one shared domain a clamp and the identity agree.
    assert_ne!(betas[0], betas[1]);
    assert_ne!(betas[1], betas[2]);
    assert_ne!(betas[0], betas[2]);

    let xs: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let got = ind.minor_args(env, &mach, 1, &xs).expect("the minor's arguments");
    let want: Vec<Term> = (0..3)
        .map(|j| px.of(xs[j].clone(), Term::apply(doms[j], Vec::new())))
        .collect();
    assert_eq!(got, want, "a slot was pushed onto another slot's argument type");
    // The clamp, spelled out: it agrees at the first two slots and not the third.
    let clamped: Vec<Term> = (0..3)
        .map(|j| px.of(xs[j].clone(), Term::apply(doms[j.min(1)], Vec::new())))
        .collect();
    assert_eq!(got[..2], clamped[..2], "the clamp must be invisible at two slots");
    assert_ne!(got, clamped, "the third slot is what separates a clamp from the identity");
}

/// **A `γ` two binders deep has no `β₀(p⃗)` at all**, so the dependent premises
/// are not stated rather than stated falsely.
///
/// The declaration is *expressible* — `Inductive::build` goes through, the
/// telescope is a two-level `Σ` nest and the fibre summand is its type — and
/// the map between `fs(Σ(z::γ),W)` and Lean's own function space is then a
/// **currying**, which `crate::sigma::push` refuses on both operators. So
/// `Inductive::rec_slot_betas` has nothing to answer with, `minor_args` fails
/// closed, and every premise stated through it disappears together.
///
/// **This fixture exists because two mutations survived the whole suite without
/// it**, and both for the same reason: nothing anywhere had a `γ` deeper than
/// one, so `rec_slot_betas`' depth guard and `minor_args`' choice of *which*
/// per-slot question to key off were both unmeasured. Dropping the depth guard,
/// or keying `minor_args` off the telescope instead of off
/// `rec_slot_domains`, now fails here. `mini`'s frontier test pins the same
/// shape from the other side — a currying is refused two constructions earlier,
/// at the spec walk — which is why no *corpus* cell reaches this and why the
/// guard needed a fixture of `derived`'s own.
#[test]
fn a_recursive_argument_at_telescope_depth_two_is_refused_rather_than_misstated() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let s = mach.wt.sums.clone();
    mach.syms.ensure(env, &s, 4).expect("the sum symbols");
    let a = const_unit_beta(env, &mach, 0);
    let b = const_unit_beta(env, &mach, 1);
    let spec = DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::with_rec_doms(Vec::new(), vec![vec![a, b]])],
    );
    let ind = Inductive::build(env, &mut mach, &spec).expect("the declaration is expressible");

    // The slot *is* function-typed — this is not a plain declaration wearing a
    // depth-two label — and it has no argument type to be pushed onto.
    assert!(ind.rec_slot_domains(1)[0].is_some(), "the slot is not function-typed");
    assert_eq!(ind.rec_telescopes[1][0].as_ref().expect("a telescope").betas.len(), 2);
    assert_eq!(ind.rec_slot_betas(1)[0], None, "a depth-two γ has no β₀(p⃗)");

    let x = Term::var(env.fresh_var());
    assert!(
        ind.minor_args(env, &mach, 1, std::slice::from_ref(&x)).is_none(),
        "minor_args answered at a slot with no β₀(p⃗)"
    );
    let (tc, su) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    assert!(
        derived::inductive::motive::dep_minor(env, &mach, &ind, 1, &tc, &su).is_none(),
        "DEP₁ was stated at a grain no interpreted minor premise can meet"
    );
    // …and the plain constructor beside it is unaffected: the refusal is per
    // slot, not per declaration.
    assert!(
        derived::inductive::motive::dep_minor(env, &mach, &ind, 0, &tc, &su).is_some(),
        "the nullary constructor's premise went with it"
    );
}

/// **The induction step of a function-typed recursive argument**, rebuilt from
/// the kernel's own constructors.
///
/// Two things it pins that no plain declaration can: the recursive argument is
/// typed at `fs(A₀, W)` and not at `W`, and the induction hypothesis is
/// **pointwise over `A₀`** — `∀z. (z ∈ A₀ → φ(app(t,z)))` — and not `φ(t)`,
/// which is not even a statement about a carrier element. And the principle
/// goes through, which is where `recarg_eta` at the general fibre is spent.
#[test]
fn the_induction_step_of_a_function_typed_argument_is_pointwise() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let spec = rtree_spec(env, &mut mach);
    let ind = Inductive::build(env, &mut mach, &spec).expect("RTree");
    let s = mach.wt.sums.clone();
    let ap = &s.ap;

    // `A₀ = Σ(z::[Bool])`, off the constructor-term funnel.
    let doms = ind.ctor_slot_domains(1);
    assert_eq!(doms.len(), 1);
    let a0 = doms[0].clone().expect("node's slot is function-typed");
    assert_ne!(a0, mach.syms.finord(&s, 1).expect("finord(1)"), "the fibre is not finord");

    let zv = env.fresh_var();
    let phi = Formula::mem(Term::var(zv), s.unit());
    let step = rect_step(env, &mach, &ind, 1, zv, &phi).expect("step");

    let (tv, zz) = (env.fresh_var(), env.fresh_var());
    let (t, tz) = (Term::var(tv), Term::var(zz));
    let ante = conj_of(&[
        Formula::mem(t.clone(), s.fs.of(a0.clone(), ind.wty.clone())),
        Formula::forall(
            zz,
            Formula::imp(
                Formula::mem(tz.clone(), a0.clone()),
                phi.subst(zv, &ap.apply(t.clone(), tz.clone())),
            ),
        ),
    ])
    .expect("two atoms");
    let concl = phi
        .subst(zv, &ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&t)).expect("node(t)"));
    assert_eq!(
        step,
        Formula::forall(tv, Formula::imp(ante, concl)),
        "the induction step is not the pointwise one"
    );

    // The two spellings a plain declaration would have used, both wrong here.
    assert_ne!(
        step,
        Formula::forall(
            tv,
            Formula::imp(
                conj_of(&[
                    Formula::mem(t.clone(), ind.wty.clone()),
                    phi.subst(zv, &t),
                ])
                .expect("two atoms"),
                phi.subst(zv, &ind.ctor_term(&mach, 1, &[], &[t]).expect("node(t)")),
            ),
        ),
        "the step reads the recursive argument as a carrier element"
    );

    // And the principle itself goes through.
    let rule = decl_rect(env, &mach, &ind, zv, &phi).expect("induction over RTree");
    let hyp = conj_of(&[
        rect_step(env, &mach, &ind, 0, zv, &phi).expect("step 0"),
        rect_step(env, &mach, &ind, 1, zv, &phi).expect("step 1"),
    ])
    .expect("two steps");
    let goal = Formula::forall(
        zv,
        Formula::imp(Formula::mem(Term::var(zv), ind.wty.clone()), phi.clone()),
    );
    assert!(derived::establishes(&rule, &Formula::imp(hyp, goal)));
}

/// **η for the recursive-argument function at the general fibre** — every
/// `f ∈ fs(Sum_m(A⃗), S)` *is* the dispatcher over its own `m` restrictions.
///
/// The right-hand side is rebuilt through [`Inductive::recfun_of`], the same
/// funnel `ctor_term` uses, so an η rule about a dispatcher no constructor is
/// built from would fail here.
#[test]
fn the_recursive_argument_function_at_a_general_fibre_is_its_own_restrictions() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let spec = mixed_spec(env, &mut mach);
    let ind = Inductive::build(env, &mut mach, &spec).expect("the declaration");
    let s = mach.wt.sums.clone();
    let fs_ext = mach.fs_ext(env).expect("function extensionality");

    // The mixed constructor: `m = 2`, both slots functions, `A₀ = 1 ≠ A₁`.
    let doms = ind.ctor_slot_domains(3);
    assert_eq!(doms.len(), 2);
    let (a0, a1) = (doms[0].clone().expect("A₀"), doms[1].clone().expect("A₁"));
    assert_eq!(a0, s.unit(), "a mixed constructor's plain slot is a function out of 1");
    assert_ne!(a0, a1, "the two summands are the same set");

    let eta = recarg_eta(env, &mach, &ind, 3, &fs_ext).expect("η at the general fibre");
    let (sv, fv) = (env.fresh_var(), env.fresh_var());
    let (t_s, tf) = (Term::var(sv), Term::var(fv));
    let at = inst_all(&eta, &[t_s.clone(), tf.clone()]).expect("η at S, f");

    let brs: Vec<Term> = (0..2)
        .map(|j| {
            let br = mach.syms.branch(env, &s, j).expect("the restriction at depth j");
            br.of(tf.clone(), doms[j].clone().expect("a domain"))
        })
        .collect();
    let want = Formula::imp(
        Formula::mem(tf.clone(), s.fs.of(ind.recargs[3].domain.clone(), t_s)),
        Formula::eq(tf.clone(), ind.recfun_of(&mach, 3, &brs).expect("the dispatcher")),
    );
    assert_eq!(*at.concl(), want, "η's statement is not the rebuilt one");
    assert!(at.hyps().is_empty(), "η carries a sequent hypothesis");

    // The plain spelling — the `m` *values* — is a different term here.
    let vals: Vec<Term> = (0..2)
        .map(|j| {
            s.ap.apply(tf.clone(), mach.syms.inj(j, s.point()).expect("Injⱼ(•)"))
        })
        .collect();
    assert_ne!(
        ind.recfun_of(&mach, 3, &brs).expect("restrictions"),
        ind.recfun_of(&mach, 3, &vals).expect("values"),
        "the general η rule collapsed to the plain one"
    );
}

/// **The two grains are not the same**, and the mixed constructor is what
/// separates them.
///
/// `Inductive::rec_slot_domains` — what Lean's minor premise takes at a slot —
/// says the mixed constructor's first slot is **plain**;
/// `Inductive::ctor_slot_domains` — what `ctor_term`'s `j`-th argument ranges
/// over — says it is a function out of `1`. Both are right, about different
/// questions, and `rect_step` reads the second. Three constructors would agree
/// under either reading; it takes the fourth.
#[test]
fn the_constructor_grain_and_the_minor_premise_grain_differ_at_a_mixed_constructor() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let spec = mixed_spec(env, &mut mach);
    let ind = Inductive::build(env, &mut mach, &spec).expect("the declaration");
    let s = mach.wt.sums.clone();
    let ap = &s.ap;

    // Agreement on the three unmixed constructors …
    for i in 0..3 {
        let (c, r) = (ind.ctor_slot_domains(i), ind.rec_slot_domains(i));
        assert_eq!(c.len(), r.len(), "constructor {i}: the two grains disagree on arity");
        assert_eq!(
            c.iter().map(|d| d.is_some()).collect::<Vec<_>>(),
            r.iter().map(|d| d.is_some()).collect::<Vec<_>>(),
            "constructor {i} is not where the grains part company"
        );
    }
    // … and disagreement on the fourth.
    let (c, r) = (ind.ctor_slot_domains(3), ind.rec_slot_domains(3));
    assert_eq!(r[0], None, "Lean's minor premise takes a carrier element here");
    assert_eq!(c[0], Some(s.unit()), "the constructor term takes a function out of 1");
    assert_eq!(c[1], r[1], "the function-typed slot is the same set under both");
    assert!(ind.ctor_slot_domains(9).is_empty(), "out of range is empty");

    // `rect_step` reads the **constructor** grain: its first recursive binder is
    // typed at `fs(1, W)` and its first ih is pointwise, not `φ(t₀)`.
    let zv = env.fresh_var();
    let phi = Formula::mem(Term::var(zv), s.unit());
    let step = rect_step(env, &mach, &ind, 3, zv, &phi).expect("the mixed step");
    let (t0v, t1v, z0, z1) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (t0, t1) = (Term::var(t0v), Term::var(t1v));
    let pointwise = |zz: kernel::FreeVar, t: &Term, a: &Term| {
        Formula::forall(
            zz,
            Formula::imp(
                Formula::mem(Term::var(zz), a.clone()),
                phi.subst(zv, &ap.apply(t.clone(), Term::var(zz))),
            ),
        )
    };
    let (a0, a1) = (c[0].clone().expect("A₀"), c[1].clone().expect("A₁"));
    let ante = conj_of(&[
        Formula::mem(t0.clone(), s.fs.of(a0.clone(), ind.wty.clone())),
        Formula::mem(t1.clone(), s.fs.of(a1.clone(), ind.wty.clone())),
        pointwise(z0, &t0, &a0),
        pointwise(z1, &t1, &a1),
    ])
    .expect("four atoms");
    let concl =
        phi.subst(zv, &ind.ctor_term(&mach, 3, &[], &[t0.clone(), t1.clone()]).expect("both"));
    assert_eq!(
        step,
        Formula::forall(t0v, Formula::forall(t1v, Formula::imp(ante, concl))),
        "the mixed step is not the constructor-grain one"
    );

    // The answer the *minor premise* grain would have given: a bare `t₀ ∈ W`
    // and a bare `φ(t₀)`, which is what a `rec_slot_domains`-keyed `rect_step`
    // produces and which no `ctor_term` can consume.
    let wrong = conj_of(&[
        Formula::mem(t0.clone(), ind.wty.clone()),
        Formula::mem(t1.clone(), s.fs.of(a1.clone(), ind.wty.clone())),
        phi.subst(zv, &t0),
        pointwise(z1, &t1, &a1),
    ])
    .expect("four atoms");
    assert_ne!(
        step,
        Formula::forall(
            t0v,
            Formula::forall(
                t1v,
                Formula::imp(
                    wrong,
                    phi.subst(
                        zv,
                        &ind.ctor_term(&mach, 3, &[], &[t0, t1]).expect("both"),
                    ),
                ),
            ),
        ),
        "the step was keyed off the minor-premise grain"
    );

    // And the principle goes through at all four constructors at once.
    assert!(decl_rect(env, &mach, &ind, zv, &phi).is_some(), "induction over the mixed shape");
}

/// **The dependent recursor at a function-typed recursive argument** — `#37`
/// piece 2's deliverable, at `RTree`.
///
/// Four things it pins that no plain declaration can:
///
/// * Lean's dependent minor premise `DEP₁` takes the field's own **function**
///   `g ∈ fs(A₀, W)` and a **family** of induction hypotheses
///   `∀z ∈ A₀. app(v,z) ∈ app(C, app(g,z))` — the motive at the recursive
///   argument each hypothesis belongs to, one per point of `A₀`;
/// * the ι rule's antecedent is `g ∈ fs(A₀, W)` and not `g ∈ W`;
/// * the induction hypothesis it hands the minor is the **composite**
///   `comp(drec, g, A₀)`, not `app(drec, g)`, which is not well typed;
/// * and the typing obligation is unchanged — `∀z ∈ W. app(drec,z) ∈ app(C,z)`
///   — which is the point: the widening is in the premises, not the conclusion.
///
/// **What this does not do**: it does not discharge `PRE` at a witness, so it
/// is not on its own a "derived about nothing" guard the way `genrec.rs`'s
/// `hyp_is_discharged_at_a_function_typed_declaration` is for `HYP`. It pins
/// `COD` as *literally* `motive::cod`'s generic formula, with nothing
/// declaration-specific in it; the satisfiability of the other half is
/// `the_dependent_premises_are_satisfiable_at_a_function_typed_argument`
/// below, which was scoped as needing one `funcs::lambda`, one
/// `ext::lam_in_funspace` and `S⃗ := •` and needed all three — plus a repair to
/// `motive::cod_at_funspace`, which the scope took for a working theorem and
/// which returned `None` at every input.
#[test]
fn the_dependent_recursor_at_a_function_typed_argument() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let spec = rtree_spec(env, &mut mach);
    let ind = Inductive::build(env, &mut mach, &spec).expect("RTree");
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("the dependent recursor no longer declines");

    let s = mach.wt.sums.clone();
    let ap = &s.ap;
    let tc = Term::var(dr.motive);
    let a0 = ind.ctor_slot_domains(1)[0].clone().expect("A₀");

    // **`β₀(p⃗)` is the argument type of the very telescope whose `Σ` is `A₀`**,
    // and `push` is the apparatus's own operator — not a second one of the same
    // shape, which is what makes the applied minor below a statement about the
    // function `mini` binds rather than about a term nothing relates to it.
    let tel = ind.rec_telescopes[1][0].clone().expect("node's slot telescope");
    assert_eq!(tel.ty_of(Vec::new()), a0, "A₀ is not this telescope's Σ");
    let beta0 = Term::apply(tel.betas[0], Vec::new());
    let px = mach.push(env).expect("the push operator");

    // ── `DEP₁`, rebuilt ─────────────────────────────────────────────────────
    let (gv, vv, zz) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tv, tz) = (Term::var(gv), Term::var(vv), Term::var(zz));
    let (pg, pv) = (px.of(tg.clone(), beta0.clone()), px.of(tv.clone(), beta0.clone()));
    let ante = conj_of(&[
        Formula::mem(tg.clone(), s.fs.of(a0.clone(), ind.wty.clone())),
        Formula::forall(
            zz,
            Formula::imp(
                Formula::mem(tz.clone(), a0.clone()),
                Formula::mem(
                    ap.apply(tv.clone(), tz.clone()),
                    ap.apply(tc.clone(), ap.apply(tg.clone(), tz.clone())),
                ),
            ),
        ),
    ])
    .expect("two atoms");
    let want_dep = Formula::forall(
        gv,
        Formula::forall(
            vv,
            Formula::imp(
                ante.clone(),
                Formula::mem(
                    ap.apply(ap.apply(Term::var(dr.minors[1]), pg.clone()), pv.clone()),
                    ap.apply(
                        tc.clone(),
                        ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&tg)).expect("node(g)"),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(
        dr.guards.dep_parts[1], want_dep,
        "DEP₁ is not Lean's dependent minor premise at a function-typed field"
    );

    // **The applied minor is at Lean's grain and the antecedent is not.** `g`
    // and `v` are bound at `fs(A₀,W)` and pointwise over `A₀`; `S₁` is a
    // function on `⟦Bool → RTree⟧`, so what it is applied to is the *pushed*
    // pair, and stating it at `g`/`v` would be a formula about a function
    // outside its domain — false at a general motive, not merely unproved.
    assert_ne!(pg, tg, "push at the field is the identity");
    assert_ne!(pv, tv, "push at the induction hypothesis is the identity");
    for (raw_g, raw_v, what) in
        [(&tg, &pv, "the field"), (&pg, &tv, "the hypothesis"), (&tg, &tv, "both")]
    {
        assert_ne!(
            dr.guards.dep_parts[1],
            Formula::forall(
                gv,
                Formula::forall(
                    vv,
                    Formula::imp(
                        ante.clone(),
                        Formula::mem(
                            ap.apply(
                                ap.apply(Term::var(dr.minors[1]), raw_g.clone()),
                                raw_v.clone(),
                            ),
                            ap.apply(
                                tc.clone(),
                                ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&tg))
                                    .expect("node(g)"),
                            ),
                        ),
                    ),
                ),
            ),
            "DEP₁ applies S₁ at derived's own grain at {what}"
        );
    }

    // The flat spelling a plain declaration would have used: one hypothesis
    // typed at `app(C, g)`, which says nothing about the field's values.
    assert_ne!(
        dr.guards.dep_parts[1],
        Formula::forall(
            gv,
            Formula::forall(
                vv,
                Formula::imp(
                    conj_of(&[
                        Formula::mem(tg.clone(), ind.wty.clone()),
                        Formula::mem(tv.clone(), ap.apply(tc.clone(), tg.clone())),
                    ])
                    .expect("two atoms"),
                    Formula::mem(
                        ap.apply(ap.apply(Term::var(dr.minors[1]), tg.clone()), tv.clone()),
                        ap.apply(
                            tc.clone(),
                            ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&tg))
                                .expect("node(g)"),
                        ),
                    ),
                ),
            ),
        ),
        "DEP₁ read the recursive argument as a carrier element"
    );

    // ── the typing obligation, unchanged ────────────────────────────────────
    let zv = env.fresh_var();
    let tzv = Term::var(zv);
    assert!(
        derived::establishes(
            &dr.typing,
            &Formula::imp(
                dr.premise.clone(),
                Formula::forall(
                    zv,
                    Formula::imp(
                        Formula::mem(tzv.clone(), ind.wty.clone()),
                        Formula::mem(
                            ap.apply(dr.rec.clone(), tzv.clone()),
                            ap.apply(tc.clone(), tzv.clone()),
                        ),
                    ),
                ),
            ),
        ),
        "the typing obligation is not what came out"
    );

    // ── the ι rule of `node`, rebuilt ───────────────────────────────────────
    let ih = derived::wrec::comp_of(fix.rc.comp, dr.rec.clone(), tg.clone(), a0.clone());
    // The ι rule's right-hand side is the *same* applied minor `DEP₁` states,
    // at the same grain — the ih slot is the composite, and what `S₁` receives
    // is that composite **pushed** onto `β₀(p⃗)`.
    let p_ih = px.of(ih.clone(), beta0.clone());
    let want_iota = Formula::imp(
        dr.premise.clone(),
        Formula::forall(
            gv,
            Formula::imp(
                Formula::mem(tg.clone(), s.fs.of(a0.clone(), ind.wty.clone())),
                Formula::eq(
                    ap.apply(
                        dr.rec.clone(),
                        ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&tg))
                            .expect("node(g)"),
                    ),
                    ap.apply(
                        ap.apply(Term::var(dr.minors[1]), pg.clone()),
                        p_ih.clone(),
                    ),
                ),
            ),
        ),
    );
    assert!(
        derived::establishes(&dr.iota[1], &want_iota),
        "the dependent ι rule is not the rebuilt one"
    );
    assert_ne!(ih, ap.apply(dr.rec.clone(), tg.clone()), "the ih is a bare application");
    assert_ne!(p_ih, ih, "the ι rule hands the minor the unpushed composite");

    // The nullary constructor is untouched: no antecedent past `PRE`.
    let (ante0, _) = dr.iota[0].concl().as_imp().expect("ι₀ is an implication");
    assert_eq!(ante0, dr.premise, "ι₀ gained an antecedent");

    // `COD` is the generic formula and nothing about this declaration — so the
    // one premise that is not discharged outright somewhere is `DEP`.
    assert_eq!(
        dr.guards.cod,
        derived::inductive::motive::cod(
            env,
            &s,
            &ind.wty,
            &tc,
            &Term::var(dr.target),
        ),
        "COD picked up something declaration-specific at a function-typed field"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// `PRE` is satisfiable — the dependent premises are not about nothing
// ─────────────────────────────────────────────────────────────────────────────

/// From `⊢ x = y` and either `⊢ φ(x)` or `⊢ H → φ(x)`, the same statement at
/// `y`. `cond` says which of the two shapes `prev` has.
fn along<F: Fn(Term) -> Formula>(
    env: &mut Env,
    eq: &Thm,
    hole: F,
    prev: &Thm,
    cond: bool,
) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let h = env.fresh_var();
    let step = Thm::mp(&Thm::eq_leibniz(x, y, h, hole(Term::var(h))), eq).expect("leibniz");
    if cond {
        derived::syl(prev, &step).expect("syl")
    } else {
        Thm::mp(&step, prev).expect("mp")
    }
}

/// `⊢ • x₀ … x_{l-1} = •` — the empty set applied to anything at all is empty.
/// `None` on an empty argument list, where there is nothing to collapse.
fn spine_collapses(env: &mut Env, mach: &Machine, args: &[Term]) -> Option<Thm> {
    let s = &mach.wt.sums;
    let ap = &s.ap;
    let mut cur = inst_all(&mach.wt.app_empty, std::slice::from_ref(args.first()?))?;
    for x in &args[1..] {
        let (lhs, _) = cur.concl().as_eq()?;
        let spine = ap.apply(lhs.clone(), x.clone());
        let lift = along(
            env,
            &cur,
            {
                let (spine, x) = (spine.clone(), x.clone());
                move |q| Formula::eq(spine.clone(), ap.apply(q, x.clone()))
            },
            &Thm::eq_refl(spine),
            false,
        );
        cur = derived::eq_trans(env, &lift, &inst_all(&mach.wt.app_empty, std::slice::from_ref(x))?)?;
    }
    Some(cur)
}

/// The witness motive `C := λx ∈ W. 1`, with everything needed to compute it.
///
/// A dependent premise is worth nothing unless some motive satisfies it, and
/// the cheapest motive that is genuinely a *function on the carrier* — rather
/// than a constant of the metalanguage, which `⟦·⟧` has no room for — is the
/// graph of `x ↦ 1` over `W`. It is a function into `{1}`, so
/// [`derived::inductive::motive::cod_at_funspace`] discharges `COD` at it, and
/// `app(C,x) = 1` at every `x ∈ W`, so every `DEPᵢ` comes down to `• ∈ 1`.
struct Witness {
    /// `C = lam(W)`.
    c: Term,
    /// `T = ⋃{1} ∪ {∅}` — [`cod_at_funspace`]'s own target at `V := {1}`.
    t: Term,
    /// `⊢ COD(C, T)`.
    cod: Thm,
    /// `⊢ ∀w. (w ∈ W → • ∈ app(C, w))` — the one fact every `DEPᵢ` spends.
    pt_in_motive: Thm,
}

fn witness_motive(env: &mut Env, mach: &Machine, ind: &Inductive) -> Witness {
    let s = mach.wt.sums.clone();
    let ap = &s.ap;
    let (pt, one) = (s.point(), s.unit());

    let xv = env.fresh_var();
    let (body, body_ax) = define_abbrev(env, &[xv], &one).expect("the constant body `1`");
    let (lam, lam_ax) = derived::funcs::lambda(env, ap, body).expect("the lambda graph");
    let beta = derived::funcs::beta_conditional(env, ap, body, lam, &lam_ax).expect("beta");
    let c = Term::apply(lam, vec![ind.wty.clone()]);
    let v = derived::singleton(ap.sets.up, one.clone());
    let t = derived::inductive::motive::cod_target(&s, &v);

    // `⊢ ∀x. (x ∈ W → body(x) ∈ V)`: the body is `1`, and `1 ∈ {1}`.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let one_in_v = Thm::mp(
        &derived::iff_mpr(&inst_all(&ap.mem_sing, &[one.clone(), one.clone()]).expect("mem_sing"))
            .expect("mpr"),
        &Thm::eq_refl(one.clone()),
    )
    .expect("1 ∈ {1}");
    let body_z = inst_all(&body_ax, std::slice::from_ref(&tz)).expect("body(z) = 1");
    let body_back = derived::eq_symm(env, &body_z).expect("symm");
    let at_z = along(
        env,
        &body_back,
        {
            let v = v.clone();
            move |q| Formula::mem(q, v.clone())
        },
        &one_in_v,
        false,
    );
    let body_in = Thm::gen(zv, &derived::a1i(&at_z, Formula::mem(tz, ind.wty.clone())));
    assert_eq!(
        *body_in.concl(),
        derived::ext::body_in(env, body, &ind.wty, &v),
        "the witness's body typing drifted from `lam_in_funspace`'s hypothesis"
    );
    let in_fs = Thm::mp(
        &inst_all(
            &derived::ext::lam_in_funspace(env, ap, &s.prod, &s.fs, body, lam, &lam_ax)
                .expect("lam_in_funspace"),
            &[ind.wty.clone(), v.clone()],
        )
        .expect("instantiate"),
        &body_in,
    )
    .expect("C ∈ fs(W,V)");
    let cod = Thm::mp(
        &inst_all(
            &derived::inductive::motive::cod_at_funspace(env, mach, ind).expect("cod_at_funspace"),
            &[c.clone(), v.clone()],
        )
        .expect("instantiate"),
        &in_fs,
    )
    .expect("COD at the witness");

    // `⊢ ∀w. (w ∈ W → • ∈ app(C,w))`, the one fact each `DEPᵢ` spends.
    let wv = env.fresh_var();
    let tw = Term::var(wv);
    let h_w = Formula::mem(tw.clone(), ind.wty.clone());
    let k_val = derived::recursion::hyp::hyp_eq_trans(
        env,
        &inst_all(&beta, &[ind.wty.clone(), tw.clone()]).expect("beta at w"),
        &derived::a1i(
            &inst_all(&body_ax, std::slice::from_ref(&tw)).expect("body(w) = 1"),
            h_w.clone(),
        ),
    )
    .expect("app(C,w) = 1");
    let val_back = derived::recursion::hyp::hyp_eq_symm(env, &k_val).expect("symm");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        one.clone(),
        ap.apply(c.clone(), tw.clone()),
        hole,
        Formula::mem(pt.clone(), Term::var(hole)),
    );
    let pt_in_motive = Thm::gen(
        wv,
        &derived::hyp_mp(
            &derived::syl(&val_back, &leib).expect("syl"),
            &derived::a1i(&s.unit_mem, h_w),
        )
        .expect("• ∈ app(C,w)"),
    );
    Witness { c, t, cod, pt_in_motive }
}

/// `⊢ DEPᵢ(C, •)` at the witness motive — **Lean's `i`-th dependent minor
/// premise, satisfied**.
///
/// `Sᵢ := •` makes the minor's value `∅` whatever it is applied to
/// ([`spine_collapses`], one `app_empty` per argument), and the witness motive
/// makes `app(C, ctorᵢ(y⃗,t⃗))` the one-point set — which needs
/// `ctorᵢ(y⃗,t⃗) ∈ W`, and *that* is the only place the premise's antecedent is
/// used. So the derivation says exactly what a non-vacuity witness has to say:
/// the antecedent is satisfiable, and what it delivers is the constructor's own
/// typing rule.
///
/// The conclusion is checked against
/// [`derived::inductive::motive::dep_minor`] rather than rebuilt by hand, so a
/// witness that drifted from the premise it is supposed to witness fails here.
fn dep_at_empty_minor(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    wit: &Witness,
    i: usize,
) -> Thm {
    let s = mach.wt.sums.clone();
    let ap = &s.ap;
    let ctor = &ind.spec.ctors[i];
    let (k, m) = (ctor.args.len(), ctor.recs);
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let yvs: Vec<kernel::FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let tvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let vvs: Vec<kernel::FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();
    let subs = ind.minor_subs(mach, i, &ts).expect("the minor premise's slots");
    let cd = ind.ctor_slot_domains(i);
    let rd = ind.rec_slot_domains(i);

    // `DEPᵢ`'s antecedent, atom by atom — the recursive ones at the constructor
    // term's grain and the induction hypotheses at the minor premise's.
    let mut atoms: Vec<Formula> = (0..k)
        .map(|j| {
            let mut a = ps.clone();
            a.extend(ys[..j].iter().cloned());
            Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
        })
        .collect();
    for j in 0..m {
        atoms.push(match &cd[j] {
            None => Formula::mem(ts[j].clone(), ind.wty.clone()),
            Some(a) => Formula::mem(ts[j].clone(), s.fs.of(a.clone(), ind.wty.clone())),
        });
    }
    for j in 0..m {
        atoms.push(derived::inductive::motive::ih_at_motive(
            env,
            &s,
            &wit.c,
            &subs[j],
            &vs[j],
            rd[j].as_ref(),
        ));
    }
    let ctx = conj_of(&atoms);
    let cond = ctx.is_some();
    let ctor_t = ind.ctor_term(mach, i, &ys, &ts).expect("the constructor term");

    // ── `ctorᵢ(y⃗,t⃗) ∈ W`, under the antecedent ─────────────────────────────
    let ty_at = inst_all(&ind.ty_ax, &ps).expect("ind(p⃗) = W");
    let mut ctor_args = ps.clone();
    ctor_args.extend(ys.iter().cloned());
    ctor_args.extend(ts.iter().cloned());
    let mem_rule = inst_all(&ind.ctors[i].mem, &ctor_args).expect("the constructor's typing rule");
    let k_mem = match &ctx {
        None => mem_rule,
        Some(h) => {
            // The rule types the fields at `ind(p⃗)`; the premise has `W`, and at
            // a function-typed slot the rewrite goes under the function space.
            let back = derived::eq_symm(env, &ty_at).expect("W = ind(p⃗)");
            let mut supplied: Vec<Thm> = (0..k)
                .map(|j| derived::conj_proj(&atoms, j).expect("project"))
                .collect();
            for j in 0..m {
                let field = derived::conj_proj(&atoms, k + j).expect("project");
                let (t_c, d, fs) = (ts[j].clone(), cd[j].clone(), s.fs.clone());
                supplied.push(along(
                    env,
                    &back,
                    move |q| {
                        Formula::mem(
                            t_c.clone(),
                            match &d {
                                None => q,
                                Some(a) => fs.of(a.clone(), q),
                            },
                        )
                    },
                    &field,
                    true,
                ));
            }
            let folded = supplied[..supplied.len() - 1]
                .iter()
                .rev()
                .fold(supplied.last().expect("non-empty").clone(), |acc, t| {
                    derived::hyp_and(t, &acc).expect("conjoin")
                });
            derived::hyp_mp(&derived::a1i(&mem_rule, h.clone()), &folded).expect("the typing rule")
        }
    };
    let ctor_c = ctor_t.clone();
    let k_in_w = along(
        env,
        &ty_at,
        move |q| Formula::mem(ctor_c.clone(), q),
        &k_mem,
        cond,
    );

    // ── `• ∈ app(C, ctorᵢ)`, and the minor's value is `•` ───────────────────
    let at_ctor =
        inst_all(&wit.pt_in_motive, std::slice::from_ref(&ctor_t)).expect("the witness at the ctor");
    let k_pt = match &ctx {
        None => Thm::mp(&at_ctor, &k_in_w).expect("mp"),
        Some(_) => derived::hyp_mp(&derived::a1i(&at_ctor, ctx.clone().expect("ctx")), &k_in_w)
            .expect("mp"),
    };

    // **The minor is applied at Lean's own grain** — `Inductive::minor_args`,
    // `push(·, β₀ⱼ(p⃗))` at a function-typed slot. `Sᵢ := •` collapses whatever
    // it is applied to, so the witness does not care *which* term stands in
    // each argument position; rebuilding the spine through the same funnel
    // `dep_minor` uses is what keeps this a check of the premise rather than of
    // `app_empty`.
    let a_subs = ind.minor_args(env, mach, i, &subs).expect("Lean's grain, at the fields");
    let a_vs = ind.minor_args(env, mach, i, &vs).expect("Lean's grain, at the hypotheses");
    let mut spine: Vec<Term> = Vec::new();
    let (mut pi, mut ri) = (0usize, 0usize);
    for sl in &ctor.order {
        match sl {
            Slot::Plain => {
                spine.push(ys[pi].clone());
                pi += 1;
            }
            Slot::Rec => {
                spine.push(a_subs[ri].clone());
                ri += 1;
            }
        }
    }
    spine.extend(a_vs.iter().cloned());
    let stated = match spine_collapses(env, mach, &spine) {
        None => k_pt,
        Some(eq) => {
            let motive_at = ap.apply(wit.c.clone(), ctor_t.clone());
            let back = derived::eq_symm(env, &eq).expect("symm");
            along(
                env,
                &back,
                move |q| Formula::mem(q, motive_at.clone()),
                &k_pt,
                cond,
            )
        }
    };

    let mut quant = yvs;
    quant.extend(tvs);
    quant.extend(vvs);
    let out = derived::gen_all(&quant, &stated);
    assert_eq!(
        *out.concl(),
        derived::inductive::motive::dep_minor(env, mach, ind, i, &wit.c, &s.point())
            .expect("DEPᵢ"),
        "the witness drifted from the premise it is supposed to satisfy"
    );
    assert!(out.hyps().is_empty(), "the witness carries a sequent hypothesis");
    out
}

/// `⊢ PRE` at the witness, and [`DepRecursor::typing`] fired at it.
///
/// Returns the witness, the `DEPᵢ` theorems one at a time, and the recursor's
/// typing obligation with **no hypothesis left**.
fn pre_at_witness(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    dr: &derived::inductive::DepRecursor,
) -> (Witness, Vec<Thm>, Thm) {
    let wit = witness_motive(env, mach, ind);
    let deps: Vec<Thm> =
        (0..ind.spec.ctors.len()).map(|i| dep_at_empty_minor(env, mach, ind, &wit, i)).collect();
    let dep = deps[..deps.len() - 1]
        .iter()
        .rev()
        .fold(deps.last().expect("non-empty").clone(), |acc, t| derived::and_intro(t, &acc));
    let pre = derived::and_intro(&wit.cod, &dep);

    let mut vars = vec![dr.motive];
    vars.extend(dr.minors.iter().copied());
    vars.push(dr.target);
    let mut args = vec![wit.c.clone()];
    args.extend(std::iter::repeat_n(mach.wt.sums.point(), dr.minors.len()));
    args.push(wit.t.clone());
    let at = inst_all(&derived::gen_all(&vars, &dr.typing), &args).expect("the witness's instance");
    let (ante, _) = at.concl().as_imp().expect("the obligation is `PRE → …`");
    assert_eq!(
        ante,
        *pre.concl(),
        "the witness satisfies something other than the premise the recursor carries"
    );
    let fired = Thm::mp(&at, &pre).expect("PRE at the witness");
    (wit, deps, fired)
}

/// **`PRE` is satisfiable at a function-typed recursive argument** — the guard
/// against deriving something about nothing, at `RTree`, and the link the
/// statement test above leaves unmeasured.
///
/// `COD` is discharged for any motive by `cod_at_funspace`, so the premise that
/// could have been vacuous is `DEP₁`, whose antecedent asks for a whole
/// **function** `g ∈ fs(A₀,W)` and a **family** of induction hypotheses. What
/// is exhibited is a motive that satisfies it: `C := λx ∈ W. 1` and `S⃗ := •`,
/// at which the minor's value collapses by `app_empty` exactly as
/// `genrec.rs`'s `empty_minor_at` collapses it — the same argument at
/// `app(C, ctorᵢ)` rather than at a flat `T`.
///
/// Three things are pinned rather than one, because a witness can be satisfied
/// and still be about nothing: `DEP₁` is *literally* the premise the recursor
/// carries at those values; the motive really is a **dependent** one, a graph
/// on `W` and not a metalanguage constant; and the typing obligation comes out
/// with no hypothesis left, so the recursor's conclusion is an outright theorem
/// at some motive.
#[test]
fn the_dependent_premises_are_satisfiable_at_a_function_typed_argument() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let spec = rtree_spec(env, &mut mach);
    let ind = Inductive::build(env, &mut mach, &spec).expect("RTree");
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("the dependent recursor");
    let s = mach.wt.sums.clone();
    let ap = &s.ap;
    let (wit, deps, fired) = pre_at_witness(env, &mach, &ind, &dr);

    // `DEP₁` — the premise with the function-typed slot — is satisfied, and it
    // is the recursor's own `DEP₁` at those values and not a lookalike.
    assert_eq!(
        *deps[1].concl(),
        dr.guards.dep_parts[1]
            .clone()
            .subst(dr.motive, &wit.c)
            .subst(dr.minors[1], &s.point()),
        "the satisfied premise is not `DEP₁`"
    );
    assert!(deps[1].hyps().is_empty(), "`DEP₁` at the witness carries a hypothesis");

    // The motive is a genuine function on the carrier, not a constant: it is a
    // set, it is in a function space, and `app(C, ·)` is not `C`.
    assert!(closed(&Formula::mem(wit.c.clone(), s.fs.of(ind.wty.clone(), wit.t.clone()))));
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    assert_ne!(ap.apply(wit.c.clone(), tz.clone()), wit.c, "the motive ignores its argument");

    // And the obligation itself, with `PRE` gone: a **closed** theorem, so
    // every one of `C`, `S⃗` and `T` really was instantiated.
    let goal = dr.typing.concl().as_imp().expect("the obligation is `PRE → …`").1;
    let want = goal
        .clone()
        .subst(dr.motive, &wit.c)
        .subst(dr.minors[0], &s.point())
        .subst(dr.minors[1], &s.point())
        .subst(dr.target, &wit.t);
    assert_ne!(want, goal, "the witness substituted nothing");
    assert!(closed(&want), "the witness left a variable free in the obligation");
    assert!(
        derived::establishes(&fired, &want),
        "the typing obligation did not come out unconditional at the witness"
    );
}

/// **The dependent recursor at a mixed constructor** — `both (r : ind) (g : Bool → ind)`,
/// the shape the value recursor took and the dependent one declined.
///
/// The whole of the difficulty is that `DEP₃` has to be stated at **both**
/// grains at once: its recursive binder `t₀` is the *constructor term's*
/// argument, a function out of `1`, while the minor premise Lean writes takes
/// an element of the carrier — so the induction hypothesis is typed at
/// `app(C, app(t₀,•))` and the minor is applied at `app(t₀,•)`. Four
/// constructors, because at three the two grains agree under either reading and
/// nothing here would be discriminated.
///
/// Three things are pinned, one per slot shape the declaration carries:
///
/// * the mixed constructor's **plain** slot — `t₀ ∈ fs(1,W)` in the antecedent,
///   `app(t₀,•)` everywhere else, and its ih flat rather than pointwise;
/// * its **function-typed** slot — `t₁ ∈ fs(A₁,W)`, a pointwise family of
///   induction hypotheses, and the composite `comp(drec,t₁,A₁)` in the ι rule;
/// * and constructor `1`, a plain recursive argument inside a plain
///   constructor, which must be untouched by any of it.
#[test]
fn the_dependent_recursor_at_a_mixed_constructor() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let spec = mixed_spec(env, &mut mach);
    let ind = Inductive::build(env, &mut mach, &spec).expect("the declaration");
    assert!(ind.has_mixed_ctor(), "the fixture is not mixed");
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("the dependent recursor no longer declines a mixed constructor");

    let s = mach.wt.sums.clone();
    let ap = &s.ap;
    let (pt, one) = (s.point(), s.unit());
    let tc = Term::var(dr.motive);
    let cd = ind.ctor_slot_domains(3);
    let a1 = cd[1].clone().expect("A₁");
    assert_eq!(cd[0], Some(one.clone()), "the plain slot's fibre summand is not `1`");
    assert_eq!(ind.rec_slot_domains(3)[0], None, "the plain slot is not plain to Lean");

    // ── `DEP₃`, rebuilt at both grains ──────────────────────────────────────
    let (t0v, t1v, v0v, v1v, zz) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (t0, t1, v0, v1, tz) = (
        Term::var(t0v),
        Term::var(t1v),
        Term::var(v0v),
        Term::var(v1v),
        Term::var(zz),
    );
    let sub0 = ap.apply(t0.clone(), pt.clone());
    // The **function-typed** slot's own telescope, and the apparatus's `push`:
    // what `S₃` receives there is `push(·, β₁(p⃗))`, while the mixed
    // constructor's plain slot is a carrier element and is not pushed at all.
    // Two slot shapes in one minor premise, and only one of them crosses.
    let tel1 = ind.rec_telescopes[3][1].clone().expect("both's function-typed slot");
    assert_eq!(tel1.ty_of(Vec::new()), a1, "A₁ is not this telescope's Σ");
    let beta1 = Term::apply(tel1.betas[0], Vec::new());
    let px = mach.push(env).expect("the push operator");
    let (p_t1, p_v1) = (px.of(t1.clone(), beta1.clone()), px.of(v1.clone(), beta1.clone()));
    let ante = conj_of(&[
        Formula::mem(t0.clone(), s.fs.of(one.clone(), ind.wty.clone())),
        Formula::mem(t1.clone(), s.fs.of(a1.clone(), ind.wty.clone())),
        Formula::mem(v0.clone(), ap.apply(tc.clone(), sub0.clone())),
        Formula::forall(
            zz,
            Formula::imp(
                Formula::mem(tz.clone(), a1.clone()),
                Formula::mem(
                    ap.apply(v1.clone(), tz.clone()),
                    ap.apply(tc.clone(), ap.apply(t1.clone(), tz.clone())),
                ),
            ),
        ),
    ])
    .expect("four atoms");
    let applied = derived::inductive::applied_minor(
        ap,
        &spec.ctors[3].order,
        &Term::var(dr.minors[3]),
        &[],
        &[sub0.clone(), p_t1.clone()],
        &[v0.clone(), p_v1.clone()],
    );
    let ctor_t = ind
        .ctor_term(&mach, 3, &[], &[t0.clone(), t1.clone()])
        .expect("both(t₀,t₁)");
    let want = [t0v, t1v, v0v, v1v].iter().rev().fold(
        Formula::imp(
            ante,
            Formula::mem(applied.clone(), ap.apply(tc.clone(), ctor_t.clone())),
        ),
        |acc, v| Formula::forall(*v, acc),
    );
    assert_eq!(
        dr.guards.dep_parts[3], want,
        "DEP₃ is not Lean's dependent minor premise at a mixed constructor"
    );

    // The two single-grain readings, both wrong: the minor applied at `t₀`
    // itself, and the plain slot's ih read pointwise like the other one.
    let both_plain = derived::inductive::applied_minor(
        ap,
        &spec.ctors[3].order,
        &Term::var(dr.minors[3]),
        &[],
        &[t0.clone(), p_t1.clone()],
        &[v0.clone(), p_v1.clone()],
    );
    assert_ne!(applied, both_plain, "the mixed constructor was read as plain throughout");
    // …and the third reading, which is the one this round removed: the
    // function-typed slot handed to `S₃` at `derived`'s grain rather than at
    // Lean's. The plain slot is *not* pushed, so a push applied uniformly per
    // constructor rather than per slot fails here too.
    let unpushed = derived::inductive::applied_minor(
        ap,
        &spec.ctors[3].order,
        &Term::var(dr.minors[3]),
        &[],
        &[sub0.clone(), t1.clone()],
        &[v0.clone(), v1.clone()],
    );
    assert_ne!(applied, unpushed, "the function-typed slot was applied at derived's grain");
    let all_pushed = derived::inductive::applied_minor(
        ap,
        &spec.ctors[3].order,
        &Term::var(dr.minors[3]),
        &[],
        &[px.of(sub0.clone(), beta1.clone()), p_t1.clone()],
        &[px.of(v0.clone(), beta1.clone()), p_v1.clone()],
    );
    assert_ne!(applied, all_pushed, "the plain slot of a mixed constructor was pushed too");
    assert_ne!(
        derived::inductive::motive::ih_at_motive(env, &s, &tc, &sub0, &v0, None),
        derived::inductive::motive::ih_at_motive(env, &s, &tc, &t0, &v0, Some(&one)),
        "the plain slot's ih is indistinguishable from a pointwise one"
    );

    // ── the ι rule of the mixed constructor ─────────────────────────────────
    let ih1 = derived::wrec::comp_of(fix.rc.comp, dr.rec.clone(), t1.clone(), a1.clone());
    let rhs = derived::inductive::applied_minor(
        ap,
        &spec.ctors[3].order,
        &Term::var(dr.minors[3]),
        &[],
        &[sub0.clone(), p_t1.clone()],
        &[ap.apply(dr.rec.clone(), sub0.clone()), px.of(ih1.clone(), beta1.clone())],
    );
    let want_iota = Formula::imp(
        dr.premise.clone(),
        Formula::forall(
            t0v,
            Formula::forall(
                t1v,
                Formula::imp(
                    conj_of(&[
                        Formula::mem(t0.clone(), s.fs.of(one.clone(), ind.wty.clone())),
                        Formula::mem(t1.clone(), s.fs.of(a1.clone(), ind.wty.clone())),
                    ])
                    .expect("two atoms"),
                    Formula::eq(ap.apply(dr.rec.clone(), ctor_t), rhs.clone()),
                ),
            ),
        ),
    );
    assert!(
        derived::establishes(&dr.iota[3], &want_iota),
        "the dependent ι rule of a mixed constructor is not the rebuilt one"
    );
    // The plain slot's ih is an application and the function-typed one is not.
    assert_ne!(ih1, ap.apply(dr.rec.clone(), t1.clone()), "the second ih is a bare application");
    assert_ne!(
        ap.apply(dr.rec.clone(), sub0),
        derived::wrec::comp_of(fix.rc.comp, dr.rec.clone(), t0.clone(), one.clone()),
        "the first ih is a composite"
    );

    // ── the plain constructor is untouched ──────────────────────────────────
    let rv = env.fresh_var();
    let tr = Term::var(rv);
    let wv = env.fresh_var();
    let tw = Term::var(wv);
    assert_eq!(
        dr.guards.dep_parts[1],
        Formula::forall(
            rv,
            Formula::forall(
                wv,
                Formula::imp(
                    conj_of(&[
                        Formula::mem(tr.clone(), ind.wty.clone()),
                        Formula::mem(tw.clone(), ap.apply(tc.clone(), tr.clone())),
                    ])
                    .expect("two atoms"),
                    Formula::mem(
                        ap.apply(ap.apply(Term::var(dr.minors[1]), tr.clone()), tw.clone()),
                        ap.apply(
                            tc.clone(),
                            ind.ctor_term(&mach, 1, &[], std::slice::from_ref(&tr))
                                .expect("plain(r)"),
                        ),
                    ),
                ),
            ),
        ),
        "a plain recursive argument picked up the mixed constructor's spelling"
    );

    // ── and `PRE` is satisfiable at this shape too ──────────────────────────
    let (wit, deps, fired) = pre_at_witness(env, &mach, &ind, &dr);
    assert_eq!(
        *deps[3].concl(),
        dr.guards.dep_parts[3]
            .clone()
            .subst(dr.motive, &wit.c)
            .subst(dr.minors[3], &pt),
        "the satisfied premise is not `DEP₃`"
    );
    assert!(fired.hyps().is_empty(), "the obligation carries a hypothesis at the witness");
}

/// **`COD` is discharged outright, for any motive that is a function** —
/// [`derived::inductive::motive::cod_at_funspace`], which had no test in this
/// crate and returned `None` at every input until this round.
///
/// Two independent defects, not the one the notes record: `k` was associated
/// `h ∧ (mx ∧ my)` where the two `gen_under`s peel one antecedent each and want
/// `(h ∧ mx) ∧ my`, **and** the union injection was lifted under `k` with
/// `a1i` before being handed to `syl`, which wants it bare. Either alone makes
/// the `?` fire, so a reader who fixed only the association would have found it
/// still dead.
///
/// What it says is that the target policy has nothing left to choose: for
/// *any* `V` the motive is a function into, `⋃V ∪ {∅}` satisfies `COD`.
#[test]
fn cod_is_discharged_for_any_motive_that_is_a_function() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    let spec = rtree_spec(env, &mut mach);
    let ind = Inductive::build(env, &mut mach, &spec).expect("RTree");
    let s = mach.wt.sums.clone();

    let th = derived::inductive::motive::cod_at_funspace(env, &mach, &ind)
        .expect("cod_at_funspace no longer returns None");
    let (cv, vv) = (env.fresh_var(), env.fresh_var());
    let (tc, tv) = (Term::var(cv), Term::var(vv));
    assert!(
        derived::establishes(
            &inst_all(&th, &[tc.clone(), tv.clone()]).expect("instantiate"),
            &Formula::imp(
                Formula::mem(tc.clone(), s.fs.of(ind.wty.clone(), tv.clone())),
                derived::inductive::motive::cod(
                    env,
                    &s,
                    &ind.wty,
                    &tc,
                    &derived::inductive::motive::cod_target(&s, &tv),
                ),
            ),
        ),
        "cod_at_funspace is not the statement its module header advertises"
    );
    // It is a schema in the motive and in the codomain alike — nothing about
    // this declaration beyond its carrier appears in it.
    assert!(th.hyps().is_empty(), "cod_at_funspace carries a sequent hypothesis");
}

// ─────────────────────────────────────────────────────────────────────────────
// **No nullary constructor** — the shape `t_policy` has no target for
// ─────────────────────────────────────────────────────────────────────────────
//
// Every fixture above starts with `CtorSpec::nullary()`, so none of them
// exercises the population the checker's target policy declines: a declaration
// with *no* nullary constructor at all. On `init-prelude` that is five
// recursors and 286 ι firings — `Lean.ParserDescr` 169, `Decidable` 81,
// `Lean.Syntax.Preresolved` / `Except` / `EStateM.Result` 12 each.
//
// The claim under test is that this is not a construction question at all:
// `DepRecursor`'s target is a **free variable** with `COD(C,T)` as a premise,
// discharged outright by `motive::cod_at_funspace` at `T := ⋃V ∪ {∅}`, so there
// is nothing for a policy to site at a nullary constructor. These two cells are
// the witnesses, at the two shapes the corpus actually has.

/// `Decidable`-shaped: **two constructors, one field each, neither nullary**,
/// one parameter, no recursion — the shape of four of the five (`Decidable` 81,
/// `Lean.Syntax.Preresolved` 12, `Except` 12, `EStateM.Result` 12; 117 firings
/// of 286).
#[test]
fn the_dependent_recursor_is_derived_with_no_nullary_constructor() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;
    // `β₀(p) = p` — `Decidable.isTrue : p → Decidable p` types its field at the
    // parameter itself, so the fixture is parameter-**live** and not merely
    // parameter-arity.
    let b = param_beta(env, 1, 0, 0);
    let spec = DeclSpec::new(
        1,
        vec![CtorSpec::new(vec![b], 0), CtorSpec::new(vec![b], 0)],
    );
    assert!(
        spec.ctors.iter().all(|c| !(c.args.is_empty() && c.recs == 0)),
        "the fixture's point: no constructor is nullary"
    );
    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration");
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("dependent recursor with no nullary constructor");

    let ap = &mach.wt.sums.ap;
    let tc = Term::var(dr.motive);

    // The typing obligation, rebuilt.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let want = Formula::imp(
        dr.premise.clone(),
        Formula::forall(
            zv,
            Formula::imp(
                Formula::mem(tz.clone(), ind.wty.clone()),
                Formula::mem(ap.apply(dr.rec.clone(), tz.clone()), ap.apply(tc, tz)),
            ),
        ),
    );
    assert!(derived::establishes(&dr.typing, &want), "the typing obligation");

    // Both ι rules, at Lean's own minors. Two constructors of the same shape,
    // so the pin has to name *which* minor each rule is about — an ι rule that
    // reached for `S₀` in both places would satisfy a one-sided check.
    assert_eq!(dr.iota.len(), 2);
    for i in 0..2 {
        let yv = env.fresh_var();
        let ty = Term::var(yv);
        let concl = Formula::eq(
            ap.apply(
                dr.rec.clone(),
                ind.ctor_term(&mach, i, std::slice::from_ref(&ty), &[]).expect("ctor"),
            ),
            ap.apply(Term::var(dr.minors[i]), ty.clone()),
        );
        let ante = Formula::mem(ty, Term::apply(b, vec![Term::var(ind.params[0])]));
        let want = Formula::imp(
            dr.premise.clone(),
            Formula::forall(yv, Formula::imp(ante, concl)),
        );
        assert!(derived::establishes(&dr.iota[i], &want), "the ι rule of constructor {i}");
        // …and not about the other minor.
        assert_ne!(dr.minors[i], dr.minors[1 - i]);
    }
}

/// `Lean.ParserDescr`-shaped: **thirteen constructors, none nullary, and
/// recursive** — 169 of the 286 firings, and the head of the population.
///
/// Faithful in the four respects the construction can see: `n = 13`, every
/// constructor takes at least one field, the field counts are the corpus's own
/// `[1,2,3,3,4,1,2,2,1,3,4,4,3]`, and two constructors carry recursive slots on
/// the **interleaved** `Rec, Plain, Rec, Plain` mask that `spec.rs`'s header
/// cites `ParserDescr.sepBy` and `sepBy1` for. It is not the real declaration —
/// the field *types* here are all `1` — and it is not meant to be; what it
/// exercises is arity, the absence of a nullary constructor, and live recursion
/// at once, none of which any other fixture in this file has.
#[test]
fn the_dependent_recursor_is_derived_at_thirteen_constructors_none_nullary() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    // Field counts as declared, and `sepBy`/`sepBy1`'s interleaved mask on the
    // two four-field constructors.
    let counts = [1usize, 2, 3, 3, 4, 1, 2, 2, 1, 3, 4, 4, 3];
    let mut ctors = Vec::with_capacity(13);
    for (i, k) in counts.iter().enumerate() {
        if i == 4 || i == 11 {
            // `sepBy : Rec, Plain, Rec, Plain` — two fields, two recursive.
            let args: Vec<FnSym> = (0..2).map(|j| const_unit_beta(env, &mach, j)).collect();
            ctors.push(
                CtorSpec::with_order(
                    args,
                    2,
                    vec![Slot::Rec, Slot::Plain, Slot::Rec, Slot::Plain],
                )
                .expect("the sepBy mask"),
            );
        } else {
            let args: Vec<FnSym> = (0..*k).map(|j| const_unit_beta(env, &mach, j)).collect();
            ctors.push(CtorSpec::new(args, 0));
        }
    }
    let spec = DeclSpec::new(0, ctors);
    assert_eq!(spec.ctors.len(), 13);
    assert!(
        spec.ctors.iter().all(|c| !(c.args.is_empty() && c.recs == 0)),
        "no constructor is nullary — the whole point"
    );
    assert!(spec.ctors.iter().any(|c| c.recs > 0), "and the declaration is recursive");

    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration");
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor at thirteen constructors");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("dependent recursor at thirteen constructors, none nullary");

    assert_eq!(dr.iota.len(), 13);
    assert_eq!(dr.minors.len(), 13);
    assert!(dr.typing.hyps().is_empty());
    assert!(dr.iota.iter().all(|t| t.hyps().is_empty()));

    // The recursive constructor's ι rule, rebuilt in full — which is the one
    // place a thirteen-constructor fixture could still be vacuous. Two live
    // recursive calls, and the minor premise applied in the declared
    // `Rec, Plain, Rec, Plain` order rather than fields-then-recs.
    let ap = &mach.wt.sums.ap;
    let (y0, y1) = (env.fresh_var(), env.fresh_var());
    let (t0, t1) = (env.fresh_var(), env.fresh_var());
    let ys = [Term::var(y0), Term::var(y1)];
    let ts = [Term::var(t0), Term::var(t1)];
    let ctor = ind.ctor_term(&mach, 4, &ys, &ts).expect("sepBy at these arguments");
    let ihs = [ap.apply(dr.rec.clone(), ts[0].clone()), ap.apply(dr.rec.clone(), ts[1].clone())];
    let rhs = derived::inductive::applied_minor(
        ap,
        &ind.spec.ctors[4].order,
        &Term::var(dr.minors[4]),
        &ys,
        &ts,
        &ihs,
    );
    let concl = Formula::eq(ap.apply(dr.rec.clone(), ctor), rhs);
    let betas = &ind.spec.ctors[4].args;
    let ante = conj_of(&[
        Formula::mem(ys[0].clone(), Term::apply(betas[0], vec![])),
        Formula::mem(ys[1].clone(), Term::apply(betas[1], vec![ys[0].clone()])),
        Formula::mem(ts[0].clone(), ind.wty.clone()),
        Formula::mem(ts[1].clone(), ind.wty.clone()),
    ])
    .expect("four atoms");
    let want = Formula::imp(
        dr.premise.clone(),
        Formula::forall(
            y0,
            Formula::forall(
                y1,
                Formula::forall(t0, Formula::forall(t1, Formula::imp(ante, concl))),
            ),
        ),
    );
    assert!(
        derived::establishes(&dr.iota[4], &want),
        "constructor 4's ι rule is not the interleaved mask with both calls live"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// **Parameters that are actually used** — the axis this suite had in its
// arities and not in its bodies
// ─────────────────────────────────────────────────────────────────────────────
//
// The gap here is **arity**, and only arity. Of 321 unindexed declarations in
// `vendor/arena-tests/good/`, 110 have `np = 0`, 106 have `np = 1`, and
// **105 have `np ≥ 2`** — 71 at two, 29 at three, and five above that, up to
// `Trans` at six. All of `derived/tests/` had four fixtures at `np = 2` and
// **none at all at `np ≥ 3`** until the cell below.
//
// A reading that did *not* survive measurement, recorded so it is not
// rediscovered: that `const_unit_beta`'s constant body also made the fixtures
// blind to the parameters. It does not — `βⱼ` and `γⱼ` are opaque symbols
// *applied to* `p⃗`, so every term mentions them whatever the body is
// (`inductive.rs`'s `ctor_term_at_moves_with_the_parameters_…`). A constant
// body is invisible only to a consumer that unfolds the symbol along its
// defining equation.

/// `EStateM.Result`-shaped: **three parameters, two constructors, two fields
/// each, none nullary** — and the two fields typed at two *different*
/// parameters, so a parameter list that were dropped, truncated or permuted
/// would not produce these antecedents.
///
/// `np = 3` is the first fixture at that arity anywhere in `derived/tests/`;
/// the corpus has 34 unindexed declarations there or above.
#[test]
fn the_dependent_recursor_at_three_parameters_two_of_them_live() {
    let env = &mut Env::new();
    let fix = fixture(env);
    let mut mach = fix.mach;

    // `β₀(p₀,p₁,p₂) = p₀` and `β₁(p₀,p₁,p₂,y₀) = p₂` — the first and the last
    // parameter, so an off-by-one in the parameter spine lands on neither.
    let b0 = param_beta(env, 3, 0, 0);
    let b1 = param_beta(env, 3, 1, 2);
    let spec = DeclSpec::new(
        3,
        vec![CtorSpec::new(vec![b0, b1], 0), CtorSpec::new(vec![b0, b1], 0)],
    );
    assert!(spec.well_formed(), "βⱼ has arity np + j");
    assert!(spec.ctors.iter().all(|c| !(c.args.is_empty() && c.recs == 0)), "none nullary");

    let ind = Inductive::build(env, &mut mach, &spec).expect("declaration at three parameters");
    assert_eq!(ind.params.len(), 3);
    let gr = derived::inductive::GenRecursor::build(
        env, &mach, &ind, &fix.rc, &fix.iota, &fix.funspace,
    )
    .expect("general recursor");
    let dr = derived::inductive::DepRecursor::build(env, &mach, &ind, &gr, &fix.rc)
        .expect("dependent recursor at three parameters");

    let ap = &mach.wt.sums.ap;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    // The ι rule of constructor 1, rebuilt — antecedent included, which is
    // where the parameters appear.
    let (y0, y1) = (env.fresh_var(), env.fresh_var());
    let (ty0, ty1) = (Term::var(y0), Term::var(y1));
    let ys = [ty0.clone(), ty1.clone()];
    let concl = Formula::eq(
        ap.apply(dr.rec.clone(), ind.ctor_term(&mach, 1, &ys, &[]).expect("ctor")),
        ap.apply(ap.apply(Term::var(dr.minors[1]), ty0.clone()), ty1.clone()),
    );
    let ante = conj_of(&[
        Formula::mem(ty0.clone(), Term::apply(b0, ps.clone())),
        Formula::mem(ty1, Term::apply(b1, {
            let mut a = ps.clone();
            a.push(ty0);
            a
        })),
    ])
    .expect("two atoms");
    let want = Formula::imp(
        dr.premise.clone(),
        Formula::forall(y0, Formula::forall(y1, Formula::imp(ante, concl))),
    );
    assert!(
        derived::establishes(&dr.iota[1], &want),
        "the ι rule's antecedent is not stated at all three parameters"
    );

    // …and the parameters really are *in* it: the statement mentions each of
    // the three free parameter variables. A `β` that ignored its arguments —
    // this file's only other kind — would mention none of them.
    let mut vs = Vec::new();
    dr.iota[1].concl().free_vars(&mut vs);
    for (i, p) in ind.params.iter().enumerate() {
        assert!(vs.contains(p), "parameter {i} does not occur in the ι rule");
    }
}
