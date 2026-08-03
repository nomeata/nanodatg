//! **Each field of a class-(P) structure is inhabited by the point** —
//! `derived/src/inductive/family/trunc_fields.rs`.
//!
//! The class-(S) sibling's tests (`family_le_prop_fields.rs`) run against a
//! three-field *dependent* spec because no corpus declaration needs the ladder
//! there. On this side one does: `086_projProp3` projects `PropStructure`'s
//! index 2, so it needs `P₀ ∧ P₁ ∧ P₂` and no more — and `P₁` is the **data**
//! field `someData`, whose projection `085` is in `bad/tutorial/`. The shape
//! `the_consumer_climbs_to_a_middle_field` derives is that one.
//!
//! **Non-vacuity is the major premise.** `Pⱼ` alone cannot give `Hⱼ` — `βⱼ ⊆ 1`
//! is satisfied by `∅` — so a rule that produced the memberships from
//! propositionality would be false. That is pinned by *refuting* the major
//! premise at a declaration whose only field type is empty, which is a closed
//! theorem and not an absence.

use kernel::{Env, Formula, FnSym, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::family::{
    CtorIndices, IndexedDeclSpec, IndexedInductive, TruncCarrier, TruncFields,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine};
use derived::prop::Trunc;
use derived::sums::Sums;
use derived::tower::Tower;
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{a1i, and_intro, conj_of, conj_proj, ex_falso, hyp_mp, inst_all, syl};

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

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
    mach.syms.ensure(env, &sums, 2).expect("two summands");
    let rc = Recursor::new(env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(env, &mach.wt, &rc, &total).expect("funspace");
    Fix { tow, tr, mach, rc, iota, funspace }
}

/// An opaque field type of arity `np + j` whose body is its `which`-th
/// argument. Opaque is the point: the *symbol application* is what appears in
/// every formula below, and nothing here unfolds it.
fn field(env: &mut Env, np: usize, j: usize, which: usize) -> FnSym {
    let vars: Vec<FreeVar> = (0..np + j).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = args[which].clone();
    derived::define_abbrev(env, &vars, &t).expect("an abbreviation").0
}

/// A field type of arity `np + j` whose body is a fixed closed set.
fn const_field(env: &mut Env, np: usize, j: usize, v: Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..np + j).map(|_| env.fresh_var()).collect();
    derived::define_abbrev(env, &vars, &v).expect("an abbreviation")
}

/// Build the skeleton and its truncation.
fn stack(env: &mut Env, f: &mut Fix, spec: &DeclSpec) -> (Inductive, TruncCarrier) {
    let ind = Inductive::build(env, &mut f.mach, spec).expect("the skeleton");
    let tc = TruncCarrier::over_declaration(env, &f.mach, &f.tow, &f.tr, &ind)
        .expect("the class-(P) carrier");
    (ind, tc)
}

/// The three-field declaration the positive tests use — `β₂` really is applied
/// to both earlier fields, so erasing them is a step the derivation must take.
struct Three {
    spec: DeclSpec,
    args: [FnSym; 3],
}

fn three(env: &mut Env) -> Three {
    let args = [field(env, 1, 0, 0), field(env, 1, 1, 0), field(env, 1, 2, 1)];
    assert_ne!(args[0], args[1]);
    assert_ne!(args[1], args[2]);
    assert_ne!(args[0], args[2]);
    Three { spec: DeclSpec::new(1, vec![CtorSpec::new(args.to_vec(), 0)]), args }
}

impl Three {
    /// `βⱼ(p, x⃗<ⱼ)`.
    fn beta(&self, p: FreeVar, xs: &[Term], j: usize) -> Term {
        let mut a = vec![Term::var(p)];
        a.extend(xs[..j].iter().cloned());
        Term::apply(self.args[j], a)
    }

    /// The `Pⱼ` and the `Hⱼ` at a chosen field assignment.
    fn atoms(
        &self,
        env: &mut Env,
        s: &Sums,
        p: FreeVar,
        xs: &[Term],
    ) -> (Vec<Formula>, Vec<Formula>) {
        let subs = (0..3)
            .map(|j| kernel::thm::subset(env, self.beta(p, xs, j), s.unit()))
            .collect();
        let mems =
            (0..3).map(|j| Formula::mem(xs[j].clone(), self.beta(p, xs, j))).collect();
        (subs, mems)
    }
}

// ─────────────────────────────────────────────────────────────────────────────

/// **The statements.** `elim_psi` is the class-(P) analogue of `LeProp::elim`,
/// and the ladder and the bundle are stated at the point.
#[test]
fn the_theorems_have_the_shapes_the_header_advertises() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let d = three(&mut env);
    let (ind, tc) = stack(&mut env, &mut f, &d.spec);
    let tf = TruncFields::over_declaration(&mut env, &f.mach, &ind, &tc)
        .expect("the class-(P) field inhabitations");

    let s = f.mach.wt.sums.clone();
    let point = s.point();
    let p = ind.params[0];
    let pts = vec![point.clone(); 3];
    let (subs, mems) = d.atoms(&mut env, &s, p, &pts);
    assert_eq!(tf.subsets, subs, "Pⱼ = βⱼ(p, •⃗<ⱼ) ⊆ 1");
    assert_eq!(tf.memberships, mems, "Hⱼ = • ∈ βⱼ(p, •⃗<ⱼ)");
    assert!(tf.all_unconditional());
    assert_eq!(TruncFields::is_present(&d.spec), Some(true));

    // `elim_psi`: `⊢ ∀p. (• ∈ ‖ind(p)‖ → ∃y₀∃y₁∃y₂. ⋀ⱼ yⱼ ∈ βⱼ(p, y⃗<ⱼ))`.
    let mem_h = Formula::mem(point.clone(), tc.carrier.clone());
    let yvs: Vec<FreeVar> = (0..3).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let body = conj_of(
        &(0..3).map(|j| Formula::mem(ys[j].clone(), d.beta(p, &ys, j))).collect::<Vec<_>>(),
    )
    .expect("three atoms");
    let psi = yvs.iter().rev().fold(body, |acc, v| Formula::exists(*v, acc));
    assert_eq!(
        *tf.elim_psi.as_ref().expect("k > 0").concl(),
        Formula::forall(p, Formula::imp(mem_h.clone(), psi)),
        "the truncation's witness, unpacked into the constructor's fields"
    );

    // The ladder and the bundle.
    assert_eq!(tf.steps.len(), 3);
    for j in 0..3 {
        let want = Formula::forall(
            p,
            Formula::imp(
                mem_h.clone(),
                Formula::imp(
                    conj_of(&subs[..=j]).expect("a prefix"),
                    conj_of(&mems[..=j]).expect("a prefix"),
                ),
            ),
        );
        assert_eq!(*tf.steps[j].concl(), want, "steps[{j}] needs P₀ … P{j} and no others");
        assert!(tf.steps[j].hyps().is_empty());
    }
    assert_eq!(
        tf.inhabited.as_ref().expect("k > 0").concl(),
        tf.steps[2].concl(),
        "steps[k-1] *is* `inhabited`"
    );
}

/// **The `086` shape.** A consumer projecting a *middle* field climbs
///
/// ```text
/// P₀ ⟹ H₀ ⟹ (its own typing gives) P₁ ⟹ H₁ ⟹ P₂ ⟹ H₂
/// ```
///
/// and reaches `H₂` from the major premise, `P₀`, and the two stepwise
/// implications `Hⱼ₋₁ → Pⱼ` — from **nothing else**. The bundle cannot do it:
/// `inhabited` demands all three `Pⱼ` before producing any `Hⱼ`, which is a
/// cycle for a declaration whose later field types depend on earlier fields.
///
/// `086_projProp3` is this at `PropStructure`: index 2, so `P₀ ∧ P₁ ∧ P₂`, with
/// `P₁` the data field's — legal as a set fact and illegal as a projection,
/// which is why the two conditions have to stay apart.
#[test]
fn the_consumer_climbs_to_a_middle_field() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let d = three(&mut env);
    let (ind, tc) = stack(&mut env, &mut f, &d.spec);
    let tf = TruncFields::over_declaration(&mut env, &f.mach, &ind, &tc).expect("the fields");

    let s = f.mach.wt.sums.clone();
    let point = s.point();
    let p = ind.params[0];
    let mem_h = Formula::mem(point.clone(), tc.carrier.clone());
    let (subs, mems) = {
        let pts = vec![point.clone(); 3];
        d.atoms(&mut env, &s, p, &pts)
    };

    // What the consumer holds: the major premise, `P₀`, and one implication per
    // dependent field. Hypothetical on purpose — this is the *shape* of the
    // climb, and the point is that nothing else is used.
    let major = Thm::assume(mem_h.clone());
    let p0 = Thm::assume(subs[0].clone());
    let up1 = Thm::assume(Formula::imp(mems[0].clone(), subs[1].clone()));
    let up2 = Thm::assume(Formula::imp(mems[1].clone(), subs[2].clone()));

    let at = |t: &Thm| Thm::mp(&inst_all(t, &[Term::var(p)]).expect("at p"), &major).expect("mp");
    let h0 = Thm::mp(&at(&tf.steps[0]), &p0).expect("H₀ from P₀");
    assert_eq!(*h0.concl(), mems[0]);

    let p1 = Thm::mp(&up1, &h0).expect("P₁ from H₀");
    let h01 = Thm::mp(&at(&tf.steps[1]), &and_intro(&p0, &p1)).expect("H₀ ∧ H₁");
    let h1 = Thm::mp(&conj_proj(&mems[..2], 1).expect("project"), &h01).expect("H₁");

    let p2 = Thm::mp(&up2, &h1).expect("P₂ from H₁");
    let h012 = Thm::mp(
        &at(&tf.steps[2]),
        &and_intro(&p0, &and_intro(&p1, &p2)),
    )
    .expect("all three");
    let h2 = Thm::mp(&conj_proj(&mems, 2).expect("project"), &h012).expect("H₂");
    assert_eq!(*h2.concl(), mems[2], "⊢ • ∈ β₂(p, •, •) — the projected field's typing");

    // Exactly the four assumptions, and no others.
    let mut got: Vec<Formula> = h2.hyps().to_vec();
    let mut want =
        vec![mem_h, subs[0].clone(), Formula::imp(mems[0].clone(), subs[1].clone()),
             Formula::imp(mems[1].clone(), subs[2].clone())];
    got.sort_by_key(|f| format!("{f:?}"));
    want.sort_by_key(|f| format!("{f:?}"));
    assert_eq!(got, want, "the major premise, P₀, and the two stepwise typings");
}

/// **Non-vacuity: the major premise is what does the work.** `Pⱼ` is
/// `βⱼ ⊆ 1`, which `∅` satisfies, so a rule producing `Hⱼ` from propositionality
/// alone would be false.
///
/// At a declaration whose only field type is `∅` the carrier is empty, and
/// `inhabited` run backwards *refutes* the major premise: `P₀` is provable
/// outright (nothing is in `∅`) and `H₀` is refutable, so
/// `⊢ ¬(• ∈ ‖ind‖)` comes out closed. That is a theorem, not an absence.
#[test]
fn the_memberships_come_out_of_the_major_premise_and_nowhere_else() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let (point, zero) = (s.point(), s.zero());
    let (b0, b0_ax) = const_field(&mut env, 0, 0, zero.clone());
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0)]);
    let (ind, tc) = stack(&mut env, &mut f, &spec);
    let tf = TruncFields::over_declaration(&mut env, &f.mach, &ind, &tc).expect("the fields");

    let beta0 = Term::apply(b0, Vec::new());
    assert_eq!(tf.memberships, vec![Formula::mem(point.clone(), beta0.clone())]);

    // `P₀`: `β₀() = ∅ ⊆ 1`, by ex falso through the unfolding.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let not_in_zero = inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz)).expect("¬(z ∈ 0)");
    let hole = env.fresh_var();
    let back = derived::eq_symm(&mut env, &b0_ax).expect("∅ = β₀()");
    let not_in_b0 = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(
                zero.clone(),
                beta0.clone(),
                hole,
                Formula::not(Formula::mem(tz.clone(), Term::var(hole))),
            ),
            &back,
        )
        .expect("mp"),
        &not_in_zero,
    )
    .expect("mp");
    let p0 = Thm::gen(
        zv,
        &syl(&not_in_b0, &ex_falso(Formula::mem(tz.clone(), s.unit()))).expect("syl"),
    );
    assert_eq!(*p0.concl(), tf.subsets[0], "β₀() ⊆ 1 — the empty set is a Prop");

    // `¬H₀`, and hence the major premise refuted.
    let not_h0 = {
        let pt = point.clone();
        Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    zero.clone(),
                    beta0.clone(),
                    hole,
                    Formula::not(Formula::mem(pt.clone(), Term::var(hole))),
                ),
                &back,
            )
            .expect("mp"),
            &inst_all(&s.ap.empty_ax, std::slice::from_ref(&point)).expect("¬(• ∈ 0)"),
        )
        .expect("mp")
    };
    let mem_h = Formula::mem(point.clone(), tc.carrier.clone());
    let bundle = inst_all(tf.inhabited.as_ref().expect("k > 0"), &[]).expect("no parameters");
    // `⊢ • ∈ ‖ind‖ → H₀`, then `¬H₀` closes it.
    let h0_under = hyp_mp(&bundle, &a1i(&p0, mem_h.clone())).expect("P₀ under the premise");
    let refuted = syl(&h0_under, &not_h0).expect("⊥");
    assert_eq!(
        *refuted.concl(),
        Formula::not(mem_h),
        "⊢ ¬(• ∈ ‖ind‖) — propositionality alone gives no inhabitant"
    );
    assert!(refuted.hyps().is_empty() && closed(refuted.concl()));
}

/// `k = 0`: nothing to inhabit, and the three theorems are `None` rather than
/// an empty conjunction this kernel cannot spell.
#[test]
fn a_fieldless_structure_has_nothing_to_inhabit() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary()]);
    let (ind, tc) = stack(&mut env, &mut f, &spec);
    let tf = TruncFields::over_declaration(&mut env, &f.mach, &ind, &tc).expect("still builds");
    assert!(tf.subsets.is_empty() && tf.memberships.is_empty());
    assert!(tf.steps.is_empty() && tf.inhabited.is_none() && tf.elim_psi.is_none());
    assert_eq!(TruncFields::is_present(&spec), Some(false));
    assert!(tf.all_unconditional());
}

/// **What is refused.** Two constructors (where the statement would be
/// *false* — membership says only that *some* constructor's fields are
/// inhabited), a recursive field, and an indexed truncation, which is
/// `over_family`'s and belongs to a different carrier.
#[test]
fn two_constructors_a_recursive_field_and_an_indexed_carrier_are_refused() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let one = s.unit();

    // Two constructors.
    let (b0, _) = const_field(&mut env, 0, 0, one.clone());
    let (b1, _) = const_field(&mut env, 0, 0, one.clone());
    let two_spec =
        DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0), CtorSpec::new(vec![b1], 0)]);
    let (ind2, tc2) = stack(&mut env, &mut f, &two_spec);
    assert_eq!(TruncFields::is_present(&two_spec), None);
    assert!(
        TruncFields::over_declaration(&mut env, &f.mach, &ind2, &tc2).is_none(),
        "with two constructors the statement would be false"
    );

    // A recursive field.
    let (b2, _) = const_field(&mut env, 0, 0, one.clone());
    let rec_spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b2], 1)]);
    let (indr, tcr) = stack(&mut env, &mut f, &rec_spec);
    assert_eq!(TruncFields::is_present(&rec_spec), None);
    assert!(
        TruncFields::over_declaration(&mut env, &f.mach, &indr, &tcr).is_none(),
        "a structure Lean projects out of is never recursive"
    );

    // Another declaration's truncation.
    let d = three(&mut env);
    let (ind, tc) = stack(&mut env, &mut f, &d.spec);
    assert!(TruncFields::over_declaration(&mut env, &f.mach, &ind, &tc).is_some());
    assert!(
        TruncFields::over_declaration(&mut env, &f.mach, &ind, &tc2).is_none(),
        "the truncation has to be this declaration's"
    );

    // An **indexed** truncation. `TruncCarrier::over_family`'s `elim` speaks
    // about `‖ind(p⃗,x⃗)‖` and quantifies the indices, so it cannot be the major
    // premise of a statement with none. Witnessed rather than asserted: the
    // guard that used to say so was deleted for failing nothing.
    let (ib, _) = const_field(&mut env, 0, 0, one.clone());
    let (i0, _) = const_field(&mut env, 0, 0, one.clone());
    let (e0, _) = const_field(&mut env, 1, 0, one.clone());
    let ispec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::new(vec![ib], 0)]),
        vec![i0],
        vec![CtorIndices::nonrecursive(vec![e0])],
    );
    assert!(ispec.well_formed());
    let iind = Inductive::build(&mut env, &mut f.mach, &ispec.base).expect("the skeleton");
    let fam = IndexedInductive::build(
        &mut env, &mut f.mach, &iind, &ispec, &f.rc, &f.iota, &f.funspace,
    )
    .expect("the indexed family");
    let itc = TruncCarrier::over_family(&mut env, &f.mach, &f.tow, &f.tr, &iind, &fam.carrier)
        .expect("the indexed class-(P) carrier");
    assert!(!itc.xvs.is_empty(), "it really is indexed");
    assert!(
        TruncFields::over_declaration(&mut env, &f.mach, &iind, &itc).is_none(),
        "an indexed truncation belongs to no statement stated at `p⃗` alone"
    );
}
