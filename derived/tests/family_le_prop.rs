//! **Class (S) with no indices** — the general clause
//! `⟦T p⃗⟧ = [⋁ᵢ ∃y⃗ᵢ. ⋀ⱼ yⱼ ∈ βᵢⱼ]`, at the three shapes it has to subsume.
//!
//! `And`, `PUnit` and a constructorless declaration are three direct clauses a
//! checker would otherwise hand-write, and they are three degenerate cases of
//! one formula: a two-field constructor, a nullary one, and no constructor at
//! all. Each is built here through `IndexSpace`/`LeCarrier`/`LeProp` and then
//! **computed**: `And`'s carrier is pinned to be `1` at inhabited parameters
//! and `0` at an empty one, `PUnit`'s to be `1` outright, and the
//! constructorless one to be `0` outright.
//!
//! Both polarities everywhere. A construction that returned the constant `1`
//! would satisfy every membership below and fail all three equations; one that
//! dropped a field from ψ would satisfy `PUnit` and fail `And` at `(0, 1)`.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::acc::Acc;
use derived::bound::Bound;
use derived::inductive::family::{CtorIndices, IndexSpace, IndexedDeclSpec, LeCarrier, LeProp};
use derived::inductive::{CtorSpec, DeclSpec, Machine};
use derived::wtype::Wtype;
use derived::{
    and_intro, conj_of, conj_proj, disj_of, exists_elim_imp, exists_intro, imp_refl, inst_all, syl,
};

struct Fix {
    mach: Machine,
    ac: Acc,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    let ac = Acc::with_apply(env, &sums.ap).expect("acc over the same pairing");
    Fix { mach, ac }
}

fn abbrev(env: &mut Env, arity: usize, body: impl Fn(&[Term]) -> Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = body(&args);
    derived::define_abbrev(env, &vars, &t).expect("an abbreviation")
}

/// A **projection** field type: `βⱼ(p⃗, y⃗<ⱼ) = p_which`, of arity `np + j`.
/// This is what `And`'s two fields are — the field's type *is* a parameter.
fn proj_field(env: &mut Env, np: usize, j: usize, which: usize) -> (FnSym, Thm) {
    abbrev(env, np + j, move |a| a[which].clone())
}

/// A non-indexed spec: `np` parameters and one `CtorSpec` per constructor.
fn nonindexed(np: usize, ctors: Vec<CtorSpec>) -> IndexedDeclSpec {
    let n = ctors.len();
    IndexedDeclSpec::new(
        DeclSpec::new(np, ctors),
        Vec::new(),
        (0..n).map(|_| CtorIndices::nonrecursive(Vec::new())).collect(),
    )
}

/// The whole class-(S)-at-zero-indices stack for `spec`.
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

/// From `⊢ a = b` and `⊢ ctx(b)` infer `⊢ ctx(a)`.
fn rw_back(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let back = derived::eq_symm(env, eq).expect("symm");
    let (b, a) = back.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(b, a, hole, ctx(Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, &back).expect("mp"), base).expect("mp")
}

/// Substitute concrete values for the parameter variables in a formula.
fn subst_params(phi: &Formula, params: &[FreeVar], vals: &[Term]) -> Formula {
    vals.iter().enumerate().fold(phi.clone(), |acc, (i, t)| acc.subst(params[i], t))
}

// ─────────────────────────────────────────────────────────────────────────────
// `And a b` — two fields, each of a parameter's type.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole interface at `And`: the index space is a point, the carrier is a
/// conditional singleton over ψ, and the `prop` lemmas are about *this* set.
#[test]
fn a_non_indexed_subsingleton_is_a_conditional_singleton() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let (b0, _) = proj_field(&mut env, 2, 0, 0);
    let (b1, _) = proj_field(&mut env, 2, 1, 1);
    let spec = nonindexed(2, vec![CtorSpec::new(vec![b0, b1], 0)]);
    assert!(spec.well_formed());
    let params: Vec<FreeVar> = (0..2).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    let (ix, lc, lp) = stack(&mut env, &mut f, &spec, &params);
    let s = f.mach.wt.sums.clone();

    // The index space is the one-point set, and says so.
    assert_eq!(ix.num_indices(), 0);
    let point = inst_all(ix.point().expect("ni = 0"), &ps).expect("at the parameters");
    assert_eq!(*point.concl(), Formula::eq(ix.idx.clone(), s.unit()));
    assert!(point.hyps().is_empty());

    // ψ is free of the subject variable — the whole content of "it is a truth
    // value and not a predicate on index tuples".
    assert!(!lp.psi.occurs_free(lc.phi_subject));
    assert_eq!(lp.set, lc.a_phi);

    // `chi_at_params` really is `conditional_singleton`'s characteristic
    // theorem: a `prop` lemma this file did *not* get from `LeProp` accepts it.
    let subset = derived::prop::cond_subset_unit(&mut env, &s, &lp.psi, &lp.set, &lp.chi_at_params)
        .expect("A_φ ⊆ 1");
    assert!(subset.hyps().is_empty());

    assert_eq!(
        *lp.intro.concl(),
        Formula::imp(lp.psi.clone(), Formula::mem(s.point(), lp.set.clone()))
    );
    assert_eq!(
        *lp.elim.concl(),
        Formula::imp(Formula::mem(s.point(), lp.set.clone()), lp.psi.clone())
    );
    assert_eq!(
        *lp.true_.concl(),
        Formula::imp(lp.psi.clone(), Formula::eq(lp.set.clone(), s.unit()))
    );
    assert_eq!(
        *lp.false_.concl(),
        Formula::imp(Formula::not(lp.psi.clone()), Formula::eq(lp.set.clone(), s.zero()))
    );
    assert!(lp.all_unconditional());

    // The carrier really is `A_φ`: no recursion, so `acc` is the identity.
    let deg = lc.degenerate.clone().expect("no recursive argument");
    let at = inst_all(&deg, &ps).expect("at the parameters");
    assert_eq!(*at.concl(), Formula::eq(lc.acc_set.clone(), lc.a_phi.clone()));

    // The intro rule at the one constructor carries its two field typings.
    assert_eq!(LeCarrier::intro_is_conditional(&spec, 0), Some(true));
}

/// **Non-vacuity, and the reason the clause is `And`.** At `a := 1, b := 1` the
/// carrier is `1`; at `a := 0, b := 1` it is `0`. A ψ that had lost either
/// field would get the second wrong.
#[test]
fn the_conjunction_carrier_computes_at_decided_parameters() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let (b0, b0_ax) = proj_field(&mut env, 2, 0, 0);
    let (b1, b1_ax) = proj_field(&mut env, 2, 1, 1);
    let spec = nonindexed(2, vec![CtorSpec::new(vec![b0, b1], 0)]);
    let params: Vec<FreeVar> = (0..2).map(|_| env.fresh_var()).collect();
    let (_ix, lc, lp) = stack(&mut env, &mut f, &spec, &params);
    let s = f.mach.wt.sums.clone();
    let (one, zero, pt) = (s.unit(), s.zero(), s.point());

    // ψ at concrete parameters, rebuilt here so its shape is pinned and not
    // merely used. The `∃` binders are de Bruijn, so any fresh choice of
    // `y₀,y₁` reproduces `LeProp`'s formula exactly iff the order agrees.
    let shape = |env: &mut Env, vals: &[Term]| -> (Formula, Formula, FreeVar, FreeVar, Term) {
        let (y0, y1) = (env.fresh_var(), env.fresh_var());
        let (t0, t1) = (Term::var(y0), Term::var(y1));
        let d0 = Term::apply(b0, vals.to_vec());
        let mut a1 = vals.to_vec();
        a1.push(t0.clone());
        let body = conj_of(&[
            Formula::mem(t0, d0.clone()),
            Formula::mem(t1, Term::apply(b1, a1)),
            Formula::eq(pt.clone(), pt.clone()),
        ])
        .expect("three conjuncts");
        let psi = Formula::exists(y0, Formula::exists(y1, body.clone()));
        (psi, body, y0, y1, d0)
    };

    // ── `A_φ(1,1) = 1` ──────────────────────────────────────────────────────
    let vals_tt = vec![one.clone(), one.clone()];
    let (psi_tt, body_tt, y0, y1, d0) = shape(&mut env, &vals_tt);
    assert_eq!(psi_tt, subst_params(&lp.psi, &params, &vals_tt));
    let chi_tt = inst_all(&lp.chi, &vals_tt).expect("instantiate");
    let set_tt = Term::apply(lc.phi, vals_tt.clone());

    // `• ∈ β₀(1,1)` and `• ∈ β₁(1,1,•)`, along the two defining equations.
    let d0_eq = inst_all(&b0_ax, &vals_tt).expect("β₀(1,1) = 1");
    assert_eq!(*d0_eq.concl(), Formula::eq(d0.clone(), one.clone()));
    let in_d0 = rw_back(&mut env, &d0_eq, |h| Formula::mem(pt.clone(), h), &s.unit_mem);
    let mut a1 = vals_tt.clone();
    a1.push(pt.clone());
    let d1_eq = inst_all(&b1_ax, &a1).expect("β₁(1,1,•) = 1");
    let in_d1 = rw_back(&mut env, &d1_eq, |h| Formula::mem(pt.clone(), h), &s.unit_mem);

    // Witness both fields with `•`, then close the two binders, innermost last.
    let witness = and_intro(&in_d0, &and_intro(&in_d1, &Thm::eq_refl(pt.clone())));
    assert_eq!(*witness.concl(), body_tt.subst(y0, &pt).subst(y1, &pt));
    let step1 = exists_intro(y1, body_tt.subst(y0, &pt), pt.clone(), &witness)
        .expect("witness the second field");
    let holds =
        exists_intro(y0, Formula::exists(y1, body_tt.clone()), pt.clone(), &step1)
            .expect("witness the first field");
    assert_eq!(*holds.concl(), psi_tt);

    let is_one = Thm::mp(
        &derived::prop::cond_true(&mut env, &s, &psi_tt, &set_tt, &chi_tt).expect("cond_true"),
        &holds,
    )
    .expect("mp");
    assert_eq!(*is_one.concl(), Formula::eq(set_tt.clone(), one.clone()));
    assert!(is_one.hyps().is_empty());

    // ── `A_φ(0,1) = 0` ──────────────────────────────────────────────────────
    let vals_ft = vec![zero.clone(), one.clone()];
    let (psi_ft, body_ft, z0, z1, e0) = shape(&mut env, &vals_ft);
    assert_eq!(psi_ft, subst_params(&lp.psi, &params, &vals_ft));
    let chi_ft = inst_all(&lp.chi, &vals_ft).expect("instantiate");
    let set_ft = Term::apply(lc.phi, vals_ft.clone());

    // Nothing is in `β₀(0,1) = 0`, so the disjunct's first conjunct is
    // refutable, and the two `∃`s are eliminated into `⊥`.
    let e0_eq = inst_all(&b0_ax, &vals_ft).expect("β₀(0,1) = 0");
    assert_eq!(*e0_eq.concl(), Formula::eq(e0.clone(), zero.clone()));
    let t0 = Term::var(z0);
    let empty_at = inst_all(&s.ap.empty_ax, std::slice::from_ref(&t0)).expect("¬(y₀ ∈ 0)");
    let not_in_e0 = rw_back(
        &mut env,
        &e0_eq,
        |h| Formula::not(Formula::mem(t0.clone(), h)),
        &empty_at,
    );
    let first = conj_proj(
        &[
            Formula::mem(t0.clone(), e0.clone()),
            Formula::mem(Term::var(z1), Term::apply(b1, {
                let mut a = vals_ft.clone();
                a.push(t0.clone());
                a
            })),
            Formula::eq(pt.clone(), pt.clone()),
        ],
        0,
    )
    .expect("first conjunct");
    let refuted = syl(&first, &not_in_e0).expect("syl");
    assert_eq!(*refuted.concl(), Formula::imp(body_ft.clone(), Formula::false_()));
    let no_inner =
        exists_elim_imp(z1, &Thm::gen(z1, &refuted), &Formula::false_()).expect("close y₁");
    let no_psi =
        exists_elim_imp(z0, &Thm::gen(z0, &no_inner), &Formula::false_()).expect("close y₀");
    assert_eq!(*no_psi.concl(), Formula::not(psi_ft.clone()));

    let is_zero = Thm::mp(
        &derived::prop::cond_false(&mut env, &s, &psi_ft, &set_ft, &chi_ft).expect("cond_false"),
        &no_psi,
    )
    .expect("mp");
    assert_eq!(*is_zero.concl(), Formula::eq(set_ft.clone(), zero.clone()));
    assert!(is_zero.hyps().is_empty());

    // The two readings are of *different* sets and *different* truth values, so
    // nothing above is satisfied by a constant construction.
    assert_ne!(set_tt, set_ft);
    assert_ne!(psi_tt, psi_ft);
    assert_ne!(one, zero);
}

// ─────────────────────────────────────────────────────────────────────────────
// `PUnit` and the constructorless declaration.
// ─────────────────────────────────────────────────────────────────────────────

/// The one shape with **no antecedent at all**: `kᵢ = ni = 0`. `intro` is
/// unconditional, and the carrier is provably `1`.
#[test]
fn a_nullary_non_indexed_subsingleton_is_the_unit_set() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let spec = nonindexed(0, vec![CtorSpec::nullary()]);
    let (_ix, lc, lp) = stack(&mut env, &mut f, &spec, &[]);
    let s = f.mach.wt.sums.clone();

    assert_eq!(LeCarrier::intro_is_conditional(&spec, 0), Some(false));
    assert_eq!(*lc.intro[0].concl(), Formula::mem(s.point(), lc.a_phi.clone()));
    assert!(lc.intro[0].hyps().is_empty());

    // ψ is `• = •` — the empty conjunction, spelled the only way it can be.
    assert_eq!(lp.psi, Formula::eq(s.point(), s.point()));
    let is_one = Thm::mp(&lp.true_, &Thm::eq_refl(s.point())).expect("ψ by reflexivity");
    assert_eq!(*is_one.concl(), Formula::eq(lp.set.clone(), s.unit()));
    assert!(is_one.hyps().is_empty());

    // The membership, not just the equation.
    let mem = Thm::mp(&lp.intro, &Thm::eq_refl(s.point())).expect("mp");
    assert_eq!(*mem.concl(), Formula::mem(s.point(), lp.set.clone()));
}

/// No constructors: ψ is `⊥` and the carrier is `0`.
#[test]
fn a_constructorless_subsingleton_is_empty() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let spec = nonindexed(0, Vec::new());
    let (_ix, lc, lp) = stack(&mut env, &mut f, &spec, &[]);
    let s = f.mach.wt.sums.clone();

    assert!(lc.intro.is_empty());
    assert_eq!(lp.psi, Formula::false_());
    let is_zero = Thm::mp(&lp.false_, &imp_refl(Formula::false_())).expect("¬⊥");
    assert_eq!(*is_zero.concl(), Formula::eq(lp.set.clone(), s.zero()));
    assert!(is_zero.hyps().is_empty());

    // Emptiness as a consequence rather than a restatement: `elim` sends a
    // member to `⊥`. And it is *not* the unit set, which `PUnit` above is.
    assert_eq!(
        *lp.elim.concl(),
        Formula::imp(Formula::mem(s.point(), lp.set.clone()), Formula::false_())
    );
    assert_ne!(s.zero(), s.unit());
}

// ─────────────────────────────────────────────────────────────────────────────
// Order and nesting, at three of each.
// ─────────────────────────────────────────────────────────────────────────────

/// ψ keeps the declared **field** order inside a disjunct and the declared
/// **constructor** order between disjuncts, both right-nested. Three fields and
/// three constructors, so a permutation or a reassociation shows up.
#[test]
fn the_truth_value_keeps_the_declared_field_and_constructor_order() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let three: Vec<FnSym> = (0..3).map(|j| proj_field(&mut env, 3, j, j).0).collect();
    let c1 = vec![proj_field(&mut env, 3, 0, 1).0];
    let c2 = vec![proj_field(&mut env, 3, 0, 2).0];
    let spec = nonindexed(
        3,
        vec![
            CtorSpec::new(three.clone(), 0),
            CtorSpec::new(c1.clone(), 0),
            CtorSpec::new(c2.clone(), 0),
        ],
    );
    assert!(spec.well_formed());
    let params: Vec<FreeVar> = (0..3).map(|_| env.fresh_var()).collect();
    let (_ix, lc, lp) = stack(&mut env, &mut f, &spec, &params);
    let s = f.mach.wt.sums.clone();
    let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    assert_eq!(lc.phi_disjuncts.len(), 3);

    // The `j`-th field's typing atom, and the disjunct that closes a list of
    // them under the `∃`s — split so that the *conjunct order* can be varied
    // independently of everything else.
    let atoms_of = |betas: &[FnSym], ys: &[FreeVar]| -> Vec<Formula> {
        let ts: Vec<Term> = ys.iter().map(|v| Term::var(*v)).collect();
        (0..betas.len())
            .map(|j| {
                let mut a = ps.clone();
                a.extend(ts[..j].iter().cloned());
                Formula::mem(ts[j].clone(), Term::apply(betas[j], a))
            })
            .collect()
    };
    let close = |atoms: &[Formula], ys: &[FreeVar]| -> Formula {
        let mut all = atoms.to_vec();
        all.push(Formula::eq(s.point(), s.point()));
        let body = conj_of(&all).expect("non-empty");
        ys.iter().rev().fold(body, |acc, v| Formula::exists(*v, acc))
    };
    let disjunct =
        |betas: &[FnSym], ys: &[FreeVar]| -> Formula { close(&atoms_of(betas, ys), ys) };
    let ys3: Vec<FreeVar> = (0..3).map(|_| env.fresh_var()).collect();
    let y1 = vec![env.fresh_var()];
    let y2 = vec![env.fresh_var()];

    let want = disj_of(&[disjunct(&three, &ys3), disjunct(&c1, &y1), disjunct(&c2, &y2)])
        .expect("three disjuncts");
    assert_eq!(lp.psi, want);

    // Reversing the three field conjuncts is a different formula, so the
    // equality above is not satisfied by a rebuild that lost the field order.
    // (The field *types* cannot themselves be permuted: `βⱼ` has arity
    // `np + j`, so a swap is not even a well-formed term — which is a second,
    // stronger reason the order is not free.)
    let mut reversed = atoms_of(&three, &ys3);
    reversed.reverse();
    assert_eq!(reversed.len(), 3);
    assert_ne!(close(&reversed, &ys3), disjunct(&three, &ys3));
    let swapped = disj_of(&[disjunct(&c1, &y1), disjunct(&three, &ys3), disjunct(&c2, &y2)])
        .expect("three disjuncts");
    assert_ne!(lp.psi, swapped);

    // The nesting is to the *right*: ψ is the head disjoined with the tail of
    // the other two, which a left-nested assembly would not satisfy.
    let tail = disj_of(&[disjunct(&c1, &y1), disjunct(&c2, &y2)]).expect("two disjuncts");
    assert_eq!(want, Formula::or(disjunct(&three, &ys3), tail));
    assert_ne!(
        want,
        Formula::or(disj_of(&[disjunct(&three, &ys3), disjunct(&c1, &y1)]).expect("two"),
                    disjunct(&c2, &y2))
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The negative half.
// ─────────────────────────────────────────────────────────────────────────────

/// An **indexed** class-(S) declaration has no conditional-singleton reading,
/// and is refused rather than given a false one.
#[test]
fn an_indexed_spec_has_no_conditional_singleton_reading() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let one = s.unit();
    let pt = s.point();
    let ity = abbrev(&mut env, 0, move |_| one.clone()).0;
    let res = abbrev(&mut env, 0, move |_| pt.clone()).0;
    let spec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::nullary()]),
        vec![ity],
        vec![CtorIndices::nonrecursive(vec![res])],
    );
    assert!(spec.well_formed());
    let ix = IndexSpace::build(&mut env, &mut f.mach, &spec, &[]).expect("an index space");
    let lc = LeCarrier::build(&mut env, &f.mach, &f.ac, &spec, &ix, &[]).expect("the carrier");

    assert_eq!(ix.num_indices(), 1);
    assert!(ix.point().is_none(), "an indexed space is not the one point");
    assert!(
        LeProp::build(&mut env, &f.mach, &spec, &ix, &lc, &[]).is_none(),
        "the prop reading must be refused at ni ≥ 1"
    );
    // The indexed carrier's intro rule still carries its antecedent — the one
    // result-index typing — even though the constructor is nullary.
    assert_eq!(LeCarrier::intro_is_conditional(&spec, 0), Some(true));
    assert!(lc.intro[0].concl().as_imp().is_some());
}
