//! **Each `Prop` field of a class-(T) structure is inhabited by the point** —
//! `derived/src/inductive/decl_fields.rs`, the third of the three.
//!
//! Both corpus declarations on this row are here and they exercise different
//! halves:
//!
//! * **`PProd`** — two independent field types, so every `Pⱼ` is dischargeable
//!   outright and the bundle suffices;
//! * **`PSigma`** — the second field type is `β fst`, so `P₁` is available only
//!   once `H₀` is. That is a *cycle* for the bundle, and the ladder is what
//!   breaks it. One of the two needs it and one does not, which is why both are
//!   here rather than one standing for both.
//!
//! **Non-vacuity is the major premise.** `Pⱼ` is `βⱼ ⊆ 1`, which `∅` satisfies,
//! so a rule producing `Hⱼ` from propositionality alone would be false. That is
//! pinned by *refuting* the major premise at a declaration whose only field type
//! is empty: a closed theorem, not an absence.

use kernel::{Env, Formula, FnSym, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::{CtorSpec, DeclFields, DeclSpec, Inductive, Machine};
use derived::sums::Sums;
use derived::wtype::Wtype;
use derived::{a1i, and_intro, conj_of, conj_proj, ex_falso, hyp_mp, inst_all, syl};

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

fn fixture(env: &mut Env) -> Machine {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    Machine::over(env, wt, bnd).expect("machine")
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

/// `βⱼ(p⃗, x⃗<ⱼ)`.
fn beta(args: &[FnSym], ps: &[Term], xs: &[Term], j: usize) -> Term {
    let mut a = ps.to_vec();
    a.extend(xs[..j].iter().cloned());
    Term::apply(args[j], a)
}

/// The `Pⱼ` and the `Hⱼ` at a chosen field assignment.
fn atoms(
    env: &mut Env,
    s: &Sums,
    args: &[FnSym],
    ps: &[Term],
    xs: &[Term],
) -> (Vec<Formula>, Vec<Formula>) {
    let subs = (0..xs.len())
        .map(|j| kernel::thm::subset(env, beta(args, ps, xs, j), s.unit()))
        .collect();
    let mems = (0..xs.len())
        .map(|j| Formula::mem(xs[j].clone(), beta(args, ps, xs, j)))
        .collect();
    (subs, mems)
}

// ─────────────────────────────────────────────────────────────────────────────

/// **`PProd α β`** — `mk : α → β`, two **independent** field types, so the
/// bundle is enough and the whole statement can be read off at once.
///
/// The major premise quantifies `z`: a class-(T) carrier holds W-elements, and
/// nothing in the conclusion mentions which one. That is the difference from
/// both siblings, whose premise is at the point.
#[test]
fn the_statement_is_at_plain_carrier_membership_and_an_arbitrary_element() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    // `β₀(α,β) = α`, `β₁(α,β,y₀) = β` — independent of `y₀`.
    let args = [field(&mut env, 2, 0, 0), field(&mut env, 2, 1, 1)];
    let spec = DeclSpec::new(2, vec![CtorSpec::new(args.to_vec(), 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the PProd skeleton");
    let df = DeclFields::over_declaration(&mut env, &mach, &ind).expect("the field theorems");

    let s = mach.wt.sums.clone();
    let point = s.point();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let pts = vec![point.clone(); 2];
    let (subs, mems) = atoms(&mut env, &s, &args, &ps, &pts);
    assert_eq!(df.subsets, subs, "Pⱼ = βⱼ(p⃗, •⃗<ⱼ) ⊆ 1");
    assert_eq!(df.memberships, mems, "Hⱼ = • ∈ βⱼ(p⃗, •⃗<ⱼ)");
    assert!(df.all_unconditional());
    assert_eq!(DeclFields::is_present(&spec), Some(true));

    let mem_z = Formula::mem(Term::var(df.major), ind.carrier.clone());
    let mut quant = ind.params.clone();
    quant.push(df.major);
    let want = |j: usize| {
        quant.iter().rev().fold(
            Formula::imp(
                mem_z.clone(),
                Formula::imp(
                    conj_of(&subs[..=j]).expect("a prefix"),
                    conj_of(&mems[..=j]).expect("a prefix"),
                ),
            ),
            |acc, v| Formula::forall(*v, acc),
        )
    };
    assert_eq!(df.steps.len(), 2);
    for j in 0..2 {
        assert_eq!(*df.steps[j].concl(), want(j), "steps[{j}] needs P₀ … P{j}");
        assert!(df.steps[j].hyps().is_empty() && closed(df.steps[j].concl()));
    }
    assert_eq!(
        df.inhabited.as_ref().expect("k > 0").concl(),
        df.steps[1].concl(),
        "steps[k-1] *is* `inhabited`"
    );

    // The bundle fires at an arbitrary carrier element and the two independent
    // `Pⱼ`, which is all `PProd` ever needs.
    let zt = Term::var(env.fresh_var());
    let at = inst_all(df.inhabited.as_ref().expect("k > 0"), &[ps[0].clone(), ps[1].clone(), zt.clone()])
        .expect("at the parameters and an element");
    let major = Thm::assume(Formula::mem(zt.clone(), ind.carrier.clone()));
    let p0 = Thm::assume(subs[0].clone());
    let p1 = Thm::assume(subs[1].clone());
    let out = Thm::mp(&Thm::mp(&at, &major).expect("mp"), &and_intro(&p0, &p1)).expect("mp");
    assert_eq!(*out.concl(), conj_of(&mems).expect("both"));
    let h1 = Thm::mp(&conj_proj(&mems, 1).expect("project"), &out).expect("H₁");
    assert_eq!(*h1.concl(), mems[1], "⊢ • ∈ β₁(α,β,•) — `PProd.snd`'s obligation");
}

/// **`PSigma α β`** — `mk : ∀ (fst : α), β fst`, so the second field type
/// **depends on the first** and `P₁` is `β(α, β, •) ⊆ 1`, which a consumer can
/// only reach once it has `H₀`.
///
/// With only the bundle that is a cycle: `inhabited` demands `P₀ ∧ P₁` before
/// producing any `Hⱼ`. The ladder breaks it, and this is the climb.
#[test]
fn a_dependent_second_field_has_to_climb_the_ladder() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    // `β₀(α,β) = α`, `β₁(α,β,y₀) = y₀` — genuinely applied to the first field.
    let args = [field(&mut env, 2, 0, 0), field(&mut env, 2, 1, 2)];
    let spec = DeclSpec::new(2, vec![CtorSpec::new(args.to_vec(), 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the PSigma skeleton");
    let df = DeclFields::over_declaration(&mut env, &mach, &ind).expect("the field theorems");

    let s = mach.wt.sums.clone();
    let point = s.point();
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let pts = vec![point.clone(); 2];
    let (subs, mems) = atoms(&mut env, &s, &args, &ps, &pts);
    assert_eq!(df.subsets, subs);
    assert_eq!(df.memberships, mems);

    // `β₁` really is applied to the *point* and not to a field variable — the
    // erasure the fold performs, visible in the statement.
    assert_eq!(
        df.subsets[1],
        kernel::thm::subset(&mut env, Term::apply(args[1], vec![ps[0].clone(), ps[1].clone(), point.clone()]), s.unit()),
        "P₁ is stated at β₁(α, β, •)"
    );

    // What the consumer holds: an element, `P₀`, and `H₀ → P₁`.
    let zt = Term::var(env.fresh_var());
    let major = Thm::assume(Formula::mem(zt.clone(), ind.carrier.clone()));
    let p0 = Thm::assume(subs[0].clone());
    let up1 = Thm::assume(Formula::imp(mems[0].clone(), subs[1].clone()));

    let at = |t: &Thm| {
        let a = [ps[0].clone(), ps[1].clone(), zt.clone()];
        Thm::mp(&inst_all(t, &a).expect("at the parameters"), &major).expect("mp")
    };
    let h0 = Thm::mp(&at(&df.steps[0]), &p0).expect("H₀ from P₀ alone");
    assert_eq!(*h0.concl(), mems[0]);

    let p1 = Thm::mp(&up1, &h0).expect("P₁ from H₀");
    let both = Thm::mp(&at(&df.steps[1]), &and_intro(&p0, &p1)).expect("H₀ ∧ H₁");
    let h1 = Thm::mp(&conj_proj(&mems, 1).expect("project"), &both).expect("H₁");
    assert_eq!(*h1.concl(), mems[1], "⊢ • ∈ β₁(α, β, •) — `PSigma.snd`'s obligation");

    // Exactly the three assumptions, and no others — the ordering contract as a
    // hypothesis set.
    let mut got: Vec<Formula> = h1.hyps().to_vec();
    let mut want = vec![
        Formula::mem(zt, ind.carrier.clone()),
        subs[0].clone(),
        Formula::imp(mems[0].clone(), subs[1].clone()),
    ];
    got.sort_by_key(|f| format!("{f:?}"));
    want.sort_by_key(|f| format!("{f:?}"));
    assert_eq!(got, want, "an element, P₀, and one stepwise typing");
}

/// **Non-vacuity: the major premise is what does the work.** `βⱼ ⊆ 1` is
/// satisfied by `∅`, so a rule producing `Hⱼ` from propositionality alone would
/// be false. At a declaration whose only field type is `∅` the carrier is empty,
/// and the bundle run backwards *refutes* membership in it.
#[test]
fn the_memberships_come_out_of_the_major_premise_and_nowhere_else() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let s = mach.wt.sums.clone();
    let (point, zero) = (s.point(), s.zero());
    let (b0, b0_ax) = const_field(&mut env, 0, 0, zero.clone());
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let df = DeclFields::over_declaration(&mut env, &mach, &ind).expect("the field theorems");

    let beta0 = Term::apply(b0, Vec::new());
    assert_eq!(df.memberships, vec![Formula::mem(point.clone(), beta0.clone())]);
    let back = derived::eq_symm(&mut env, &b0_ax).expect("∅ = β₀()");

    // `¬(t ∈ β₀())`, at any `t`, by carrying `¬(t ∈ ∅)` along the unfolding.
    let not_in = |env: &mut Env, t: &Term| -> Thm {
        let hole = env.fresh_var();
        Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    zero.clone(),
                    beta0.clone(),
                    hole,
                    Formula::not(Formula::mem(t.clone(), Term::var(hole))),
                ),
                &back,
            )
            .expect("mp"),
            &inst_all(&s.ap.empty_ax, std::slice::from_ref(t)).expect("¬(t ∈ 0)"),
        )
        .expect("mp")
    };

    // `P₀`: the empty set is a `Prop`.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let nz = not_in(&mut env, &tz);
    let p0 = Thm::gen(zv, &syl(&nz, &ex_falso(Formula::mem(tz, s.unit()))).expect("syl"));
    assert_eq!(*p0.concl(), df.subsets[0], "β₀() ⊆ 1");

    // `¬H₀`, and hence no element of the carrier at all.
    let not_h0 = not_in(&mut env, &point);
    let wt = Term::var(env.fresh_var());
    let mem_z = Formula::mem(wt.clone(), ind.carrier.clone());
    let at = inst_all(df.inhabited.as_ref().expect("k > 0"), std::slice::from_ref(&wt))
        .expect("no parameters, one element");
    let refuted = syl(&hyp_mp(&at, &a1i(&p0, mem_z.clone())).expect("P₀"), &not_h0).expect("⊥");
    assert_eq!(
        *refuted.concl(),
        Formula::not(mem_z),
        "⊢ ¬(z ∈ ind()) — propositionality alone gives no inhabitant"
    );
    assert!(refuted.hyps().is_empty());
}

/// `k = 0`: nothing to inhabit, and the theorems are `None` rather than an
/// empty conjunction this kernel cannot spell.
#[test]
fn a_fieldless_structure_has_nothing_to_inhabit() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let df = DeclFields::over_declaration(&mut env, &mach, &ind).expect("still builds");
    assert!(df.subsets.is_empty() && df.memberships.is_empty());
    assert!(df.steps.is_empty() && df.inhabited.is_none());
    assert_eq!(DeclFields::is_present(&spec), Some(false));
    assert!(df.all_unconditional());
}

/// **What is refused.** Two constructors — where the statement would be *false*,
/// since membership says only that *some* constructor's fields are inhabited —
/// and a recursive field. Indices are **not** a refusal here: `Inductive` is the
/// non-indexed carrier, so there is no indexed input to hand it.
#[test]
fn two_constructors_and_a_recursive_field_are_refused() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let s = mach.wt.sums.clone();
    let one = s.unit();

    let (b0, _) = const_field(&mut env, 0, 0, one.clone());
    let (b1, _) = const_field(&mut env, 0, 0, one.clone());
    let two = DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0), CtorSpec::new(vec![b1], 0)]);
    let ind2 = Inductive::build(&mut env, &mut mach, &two).expect("the skeleton");
    assert_eq!(DeclFields::is_present(&two), None);
    assert!(
        DeclFields::over_declaration(&mut env, &mach, &ind2).is_none(),
        "with two constructors the statement would be false"
    );

    let (b2, _) = const_field(&mut env, 0, 0, one.clone());
    let rec = DeclSpec::new(0, vec![CtorSpec::new(vec![b2], 1)]);
    let indr = Inductive::build(&mut env, &mut mach, &rec).expect("the skeleton");
    assert_eq!(DeclFields::is_present(&rec), None);
    assert!(
        DeclFields::over_declaration(&mut env, &mach, &indr).is_none(),
        "a structure Lean projects out of is never recursive"
    );

    // …and the positive control, so the two refusals are not vacuous.
    let (b3, _) = const_field(&mut env, 0, 0, one);
    let ok = DeclSpec::new(0, vec![CtorSpec::new(vec![b3], 0)]);
    let indo = Inductive::build(&mut env, &mut mach, &ok).expect("the skeleton");
    assert!(DeclFields::over_declaration(&mut env, &mach, &indo).is_some());
}
