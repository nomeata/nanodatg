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
fn const_unit_beta(env: &mut Env, mach: &Machine, arity: usize) -> FnSym {
    let vars: Vec<kernel::FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let one = mach.wt.sums.unit();
    define_abbrev(env, &vars, &one).expect("β").0
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
    let concl = phi.subst(zv, &ind.ctor_term(&mach, 1, &[], &[t.clone()]).expect("node(t)"));
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
/// **What this does not do**, named rather than left to be discovered: it does
/// not discharge `PRE` at a witness, so it is not a "derived about nothing"
/// guard the way `genrec.rs`'s `hyp_is_discharged_at_a_function_typed_declaration`
/// is for `HYP`. `PRE = COD ∧ DEP`, and the assertion below pins `COD` as
/// *literally* `motive::cod`'s generic formula — the one
/// `motive::cod_at_funspace` discharges outright for any motive into any `V`,
/// with nothing declaration-specific in it. So the one unmeasured link is
/// `DEP₁`'s satisfiability at this shape. Closing it needs a motive `C` with
/// `app(C,x) = 1` on `W` (one `funcs::lambda` and one `ext::lam_in_funspace`)
/// and `S⃗ := •`, at which `applied_minor` collapses by `wt.app_empty` exactly
/// as `genrec.rs`'s `empty_minor_at` collapses it — the same argument, at
/// `app(C, ctorᵢ)` instead of at a flat `T`.
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

    // ── `DEP₁`, rebuilt ─────────────────────────────────────────────────────
    let (gv, vv, zz) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tv, tz) = (Term::var(gv), Term::var(vv), Term::var(zz));
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
                ante,
                Formula::mem(
                    ap.apply(ap.apply(Term::var(dr.minors[1]), tg.clone()), tv.clone()),
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
                        ap.apply(Term::var(dr.minors[1]), tg.clone()),
                        ih.clone(),
                    ),
                ),
            ),
        ),
    );
    assert!(
        derived::establishes(&dr.iota[1], &want_iota),
        "the dependent ι rule is not the rebuilt one"
    );
    assert_ne!(ih, ap.apply(dr.rec.clone(), tg), "the ih is a bare application");

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
