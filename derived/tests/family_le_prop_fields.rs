//! **Each class-(S) field type is inhabited by the point** —
//! `derived/src/inductive/family/le_prop_fields.rs`.
//!
//! The premise `⊢ • ∈ βⱼ(p⃗, •⃗<ⱼ)` is what every class-(S) eliminator needs and
//! what `βⱼ ⊆ 1` does not give: `⊆ 1` is satisfied by the empty set. It comes
//! out of the **major premise** instead, and this file pins that it really does.
//!
//! # The trap this file exists to avoid
//!
//! `derived/tests/family_le_prop_rec.rs` discharges `LePropRecursor`'s `G` by
//! choosing `βⱼ ≡ 1` and applying `Sums::unit_mem`. That route never touches
//! carrier membership, so it would pass against a construction that had none.
//! Every field type here is instead an **opaque symbol application** — three
//! distinct ones, none syntactically `1`, and the third genuinely *depending on
//! the two fields before it* — so `unit_mem` proves nothing about any of them
//! and the only road to `• ∈ β₂(p, •, •)` runs through `• ∈ A_φ(p)`.
//!
//! Four things are pinned:
//!
//! 1. the exact statements, and that `guard`'s `G` is conjunct-for-conjunct
//!    `LePropRecursor`'s own antecedent at `y⃗ := •⃗` — six atoms, in order;
//! 2. **the route**: composed with `LeCarrier::intro`, membership witnessed by
//!    three arbitrary `u⃗` yields the memberships at `•⃗`, unconditionally, at
//!    field types where nothing else could;
//! 3. **the blocker unblocked**: `LePropRecursor::iota_at_point` fired through
//!    `guard`, from carrier membership and propositionality alone;
//! 4. `k = 0`, where both theorems are absent *and* ι carries no antecedent —
//!    the two coincide, so there is no sub-case to wire; and the negative half.

use kernel::{Env, Formula, FnSym, FreeVar, Term};

use derived::acc::Acc;
use derived::bound::Bound;
use derived::inductive::family::{
    minor_app, rec_term, CtorIndices, IndexSpace, IndexedDeclSpec, LeCarrier, LeProp,
    LePropFields, LePropRecursor,
};
use derived::inductive::{CtorSpec, DeclSpec, Machine};
use derived::point_fun::PointFun;
use derived::wtype::Wtype;
use derived::{conj_of, curry, inst_all, sums::Sums, syl, uncurry};

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

/// An opaque field type of arity `np + j` whose body is its `which`-th
/// argument. Opaque is the point: the *symbol application* is what appears in
/// every formula below, and nothing in this file unfolds it.
fn field(env: &mut Env, np: usize, j: usize, which: usize) -> FnSym {
    let vars: Vec<FreeVar> = (0..np + j).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = args[which].clone();
    derived::define_abbrev(env, &vars, &t).expect("an abbreviation").0
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

/// The three-field declaration every positive test below uses.
///
/// `β₀(p)`, `β₁(p,y₀)` and `β₂(p,y₀,y₁)` are three *different* symbols, the
/// last of which really is applied to both earlier fields — so erasing them is
/// a step the derivation has to take and cannot skip.
struct Three {
    spec: IndexedDeclSpec,
    p: FreeVar,
    args: [FnSym; 3],
}

fn three(env: &mut Env) -> Three {
    let args = [field(env, 1, 0, 0), field(env, 1, 1, 0), field(env, 1, 2, 1)];
    assert_ne!(args[0], args[1]);
    assert_ne!(args[1], args[2]);
    assert_ne!(args[0], args[2]);
    Three {
        spec: nonindexed(1, vec![CtorSpec::new(args.to_vec(), 0)]),
        p: env.fresh_var(),
        args,
    }
}

impl Three {
    /// `βⱼ(p, x⃗<ⱼ)`.
    fn beta(&self, xs: &[Term], j: usize) -> Term {
        let mut a = vec![Term::var(self.p)];
        a.extend(xs[..j].iter().cloned());
        Term::apply(self.args[j], a)
    }

    /// The `Pⱼ` and the `Hⱼ` at a chosen field assignment.
    fn atoms(&self, env: &mut Env, s: &Sums, xs: &[Term]) -> (Vec<Formula>, Vec<Formula>) {
        let subs = (0..3)
            .map(|j| kernel::thm::subset(env, self.beta(xs, j), s.unit()))
            .collect();
        let mems = (0..3).map(|j| Formula::mem(xs[j].clone(), self.beta(xs, j))).collect();
        (subs, mems)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. The statements, and that `G` is the consumer's own antecedent.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn the_two_theorems_have_the_shapes_the_header_advertises() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let t = three(&mut env);
    let (ix, lc, lp) = stack(&mut env, &mut f, &t.spec, &[t.p]);
    let s = f.mach.wt.sums.clone();
    let (point, unit) = (s.point(), s.unit());
    let pts = vec![point.clone(); 3];

    let lf = LePropFields::build(&mut env, &f.mach, &t.spec, &lp, &[t.p])
        .expect("the field inhabitations");
    assert!(lf.all_unconditional(), "both rest on nothing");
    assert_eq!(LePropFields::is_present(&t.spec), Some(true));
    assert_eq!(lf.subsets.len(), 3);
    assert_eq!(lf.memberships.len(), 3);

    // ── The three field types are distinct, and none of them is `1` ────────
    let betas: Vec<Term> = (0..3).map(|j| t.beta(&pts, j)).collect();
    assert_ne!(betas[0], betas[1]);
    assert_ne!(betas[1], betas[2]);
    assert_ne!(betas[0], betas[2]);
    for b in &betas {
        assert_ne!(*b, unit, "not syntactically `1`: `unit_mem` says nothing about it");
        assert_ne!(*b, point);
    }

    // ── The atoms, in order ────────────────────────────────────────────────
    let (subs, mems) = t.atoms(&mut env, &s, &pts);
    assert_eq!(lf.subsets, subs);
    assert_eq!(lf.memberships, mems);
    for m in &lf.memberships {
        assert_ne!(*m, Formula::mem(point.clone(), unit.clone()), "not `• ∈ 1`");
    }

    let mem_a = Formula::mem(point.clone(), lp.set.clone());
    let p_conj = conj_of(&subs).expect("three subsets");
    let chi = conj_of(&mems).expect("three memberships");

    let inhabited = inst_all(lf.inhabited.as_ref().expect("k = 3"), &[Term::var(t.p)])
        .expect("at the parameter");
    assert_eq!(
        *inhabited.concl(),
        Formula::imp(mem_a.clone(), Formula::imp(p_conj.clone(), chi.clone())),
    );
    assert!(inhabited.hyps().is_empty());

    // ── `G`: six atoms, the `Pⱼ` run first and the `Hⱼ` run second ─────────
    let mut g_atoms = subs.clone();
    g_atoms.extend(mems.iter().cloned());
    assert_eq!(g_atoms.len(), 6);
    let g = conj_of(&g_atoms).expect("six atoms");
    let guard = inst_all(lf.guard.as_ref().expect("k = 3"), &[Term::var(t.p)])
        .expect("at the parameter");
    assert_eq!(*guard.concl(), Formula::imp(mem_a.clone(), Formula::imp(p_conj.clone(), g.clone())));

    // The nesting, spelled out over more than three elements: `G` is
    // `P₀ ∧ (P₁ ∧ (P₂ ∧ (H₀ ∧ (H₁ ∧ H₂))))`, and the `Hⱼ` run is contiguous.
    assert_eq!(
        g,
        Formula::and(
            subs[0].clone(),
            Formula::and(
                subs[1].clone(),
                Formula::and(subs[2].clone(), conj_of(&mems).expect("the H run")),
            ),
        ),
    );

    // ── `G` really is `LePropRecursor`'s antecedent at `y⃗ := •⃗` ───────────
    let r = LePropRecursor::build(&mut env, &f.mach, &f.pf, &t.spec, &ix, &lc, &lp, &[t.p])
        .expect("the ni = 0 recursor");
    assert_eq!(r.fields.len(), 3);
    let tm = Term::var(r.minor);
    let mut at = vec![Term::var(t.p), tm.clone()];
    at.extend(pts.iter().cloned());
    let iota_pt = inst_all(&r.iota_at_point, &at).expect("at the parameter, `m` and `•⃗`");
    assert_eq!(
        iota_pt.concl().as_imp().expect("conditional at k = 3").0,
        g,
        "`guard` produces exactly what `iota_at_point` consumes",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. The route: carrier membership is what does the work.
// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable.** From "*some* `u⃗` inhabit the fields" and "the fields are
/// propositions", the point inhabits every field type — at three opaque,
/// pairwise-distinct types, the third of which is applied to the first two.
///
/// The composed theorem is unconditional and its conclusion mentions **only**
/// `•`, while its antecedent mentions only `u⃗`: the erasure `u⃗ ↦ •⃗` happened
/// inside, and it happened in the *types* as well as in the members, which is
/// the half a constantly-inhabited construction could not produce.
#[test]
fn the_memberships_come_out_of_the_major_premise_and_nowhere_else() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let t = three(&mut env);
    let (_, lc, lp) = stack(&mut env, &mut f, &t.spec, &[t.p]);
    let s = f.mach.wt.sums.clone();
    let point = s.point();
    let pts = vec![point.clone(); 3];

    let lf = LePropFields::build(&mut env, &f.mach, &t.spec, &lp, &[t.p])
        .expect("the field inhabitations");
    let inhabited = inst_all(lf.inhabited.as_ref().expect("k = 3"), &[Term::var(t.p)])
        .expect("at the parameter");

    // ── The major premise, from three arbitrary witnesses ──────────────────
    let us: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let mut ia = vec![Term::var(t.p)];
    ia.extend(us.iter().cloned());
    let intro = inst_all(&lc.intro[0], &ia).expect("the introduction rule at `u⃗`");
    let (_, u_mems) = t.atoms(&mut env, &s, &us);
    let u_conj = conj_of(&u_mems).expect("three typings");
    assert_eq!(
        *intro.concl(),
        Formula::imp(u_conj.clone(), Formula::mem(point.clone(), lc.a_phi.clone())),
    );

    // ── Compose ────────────────────────────────────────────────────────────
    let composed = syl(&intro, &inhabited).expect("the major premise into the field rule");
    let (subs, mems) = t.atoms(&mut env, &s, &pts);
    let p_conj = conj_of(&subs).expect("three subsets");
    let chi = conj_of(&mems).expect("three memberships");
    assert_eq!(*composed.concl(), Formula::imp(u_conj.clone(), Formula::imp(p_conj, chi.clone())));
    assert!(composed.hyps().is_empty(), "unconditional: nothing was assumed");

    // ── The erasure is visible, at all three fields ────────────────────────
    //
    // Antecedent and conclusion are the *same three positions*, at `u⃗` and at
    // `•⃗` respectively, and they differ at every one of them — including in the
    // types, which is what `β₂`'s dependency on `y₀` and `y₁` is here to show.
    for j in 0..3 {
        assert_ne!(u_mems[j], mems[j], "field {j}: witness and point are different statements");
    }
    assert_eq!(t.beta(&us, 0), t.beta(&pts, 0), "β₀ takes no field, so it is the same term");
    assert_ne!(t.beta(&us, 1), t.beta(&pts, 1), "β₁ sees y₀, so erasing it moves the type");
    assert_ne!(t.beta(&us, 2), t.beta(&pts, 2), "β₂ sees y₀ and y₁, so erasing them moves it");

    // ── And it is genuinely about *these* types ────────────────────────────
    //
    // At a different parameter the statement is a different one: the theorem
    // speaks about `βⱼ(p, •⃗<ⱼ)` and not about some constantly-inhabited set
    // chosen in advance.
    let other = inst_all(lf.inhabited.as_ref().expect("k = 3"), &[s.unit()])
        .expect("at the parameter `1`");
    assert_ne!(*other.concl(), *inhabited.concl());
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. The blocker, unblocked.
// ─────────────────────────────────────────────────────────────────────────────

/// `LePropRecursor::iota_at_point` fired from carrier membership and
/// propositionality alone — which is the premise that was missing.
///
/// The result is
/// `⊢ (u⃗ inhabit the fields) → (the fields are propositions → app(rec(m),•) = m(•,•,•))`,
/// unconditional, at a three-field declaration whose field types no other lemma
/// in this crate can inhabit.
#[test]
fn iota_fires_from_carrier_membership_and_propositionality() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let t = three(&mut env);
    let (ix, lc, lp) = stack(&mut env, &mut f, &t.spec, &[t.p]);
    let s = f.mach.wt.sums.clone();
    let point = s.point();
    let pts = vec![point.clone(); 3];

    let lf = LePropFields::build(&mut env, &f.mach, &t.spec, &lp, &[t.p])
        .expect("the field inhabitations");
    let r = LePropRecursor::build(&mut env, &f.mach, &f.pf, &t.spec, &ix, &lc, &lp, &[t.p])
        .expect("the ni = 0 recursor");

    let tm = Term::var(r.minor);
    let mut at = vec![Term::var(t.p), tm.clone()];
    at.extend(pts.iter().cloned());
    let iota_pt = inst_all(&r.iota_at_point, &at).expect("at the parameter, `m` and `•⃗`");

    // `guard` at the parameter is `⊢ • ∈ A_φ(p) → (P⃗ → G)`; ι is `⊢ G → …`.
    let guard = inst_all(lf.guard.as_ref().expect("k = 3"), &[Term::var(t.p)])
        .expect("at the parameter");
    // `⊢ M → (P⃗ → G)` and `⊢ G → …` compose by currying the two hypotheses
    // together, chaining, and uncurrying again — there is no deduction theorem.
    let fired = uncurry(&syl(&curry(&guard).expect("curry"), &iota_pt).expect("chain"))
        .expect("uncurry");

    let rec = rec_term(&s, &t.spec, &tm).expect("the recursor term");
    let minor_pt = minor_app(&s, &t.spec, 0, &tm, &pts, &[]).expect("the minor at `•⃗`");
    let (subs, _) = t.atoms(&mut env, &s, &pts);
    let p_conj = conj_of(&subs).expect("three subsets");
    let value = Formula::eq(s.ap.apply(rec.clone(), point.clone()), minor_pt.clone());
    assert_eq!(
        *fired.concl(),
        Formula::imp(
            Formula::mem(point.clone(), lp.set.clone()),
            Formula::imp(p_conj.clone(), value.clone()),
        ),
    );
    assert!(fired.hyps().is_empty());
    // The right-hand side is the minor at three points, not a constant.
    assert_eq!(
        minor_pt,
        s.ap.apply(
            s.ap.apply(s.ap.apply(tm.clone(), point.clone()), point.clone()),
            point.clone()
        ),
    );

    // …and with the major premise itself supplied by `LeCarrier::intro`.
    let us: Vec<Term> = (0..3).map(|_| Term::var(env.fresh_var())).collect();
    let mut ia = vec![Term::var(t.p)];
    ia.extend(us.iter().cloned());
    let intro = inst_all(&lc.intro[0], &ia).expect("the introduction rule at `u⃗`");
    let end_to_end = syl(&intro, &fired).expect("compose");
    let (_, u_mems) = t.atoms(&mut env, &s, &us);
    assert_eq!(
        *end_to_end.concl(),
        Formula::imp(
            conj_of(&u_mems).expect("three typings"),
            Formula::imp(p_conj, value),
        ),
    );
    assert!(end_to_end.hyps().is_empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. `k = 0`, and the negative half.
// ─────────────────────────────────────────────────────────────────────────────

/// At `k = 0` there is no field to inhabit — and `iota_at_point` has no
/// antecedent to discharge either, so the two absences coincide and no
/// sub-case has to be wired.
#[test]
fn a_fieldless_constructor_has_nothing_to_inhabit_and_nothing_to_discharge() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let spec = nonindexed(0, vec![CtorSpec::nullary()]);
    let (ix, lc, lp) = stack(&mut env, &mut f, &spec, &[]);

    let lf = LePropFields::build(&mut env, &f.mach, &spec, &lp, &[]).expect("still a value");
    assert_eq!(LePropFields::is_present(&spec), Some(false));
    assert!(lf.subsets.is_empty());
    assert!(lf.memberships.is_empty());
    assert!(lf.inhabited.is_none(), "the empty conjunction is not a formula in this kernel");
    assert!(lf.guard.is_none());
    assert!(lf.all_unconditional());

    // The consumer's side of the same coin.
    let r = LePropRecursor::build(&mut env, &f.mach, &f.pf, &spec, &ix, &lc, &lp, &[])
        .expect("the ni = 0 recursor");
    let tm = Term::var(r.minor);
    let iota_pt = inst_all(&r.iota_at_point, std::slice::from_ref(&tm)).expect("at `m`");
    assert!(
        iota_pt.concl().as_imp().is_none(),
        "no antecedent to discharge, so the absent `guard` is exactly right",
    );
    assert!(r.erase.is_none());
}

/// Six specs this construction is **not** about, each refused.
#[test]
fn indexed_multi_constructor_recursive_and_mismatched_inputs_are_refused() {
    let mut env = Env::new();
    let mut f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let unit = s.unit();

    let t = three(&mut env);
    let (_, _, lp) = stack(&mut env, &mut f, &t.spec, &[t.p]);
    assert!(LePropFields::build(&mut env, &f.mach, &t.spec, &lp, &[t.p]).is_some(), "baseline");
    assert!(
        LePropFields::build(&mut env, &f.mach, &t.spec, &lp, &[]).is_none(),
        "parameter count",
    );

    // A `LeProp` from a *different* declaration: ψ is rebuilt and compared, so
    // the field symbols and their order have to be this spec's.
    let other = three(&mut env);
    let (_, _, lp2) = stack(&mut env, &mut f, &other.spec, &[other.p]);
    assert!(
        LePropFields::build(&mut env, &f.mach, &t.spec, &lp2, &[t.p]).is_none(),
        "another declaration's prop reading",
    );

    // An **indexed** spec — `LeProp::build` refuses `ni ≥ 1`, so the only way to
    // make the call is with a spec and a reading that disagree.
    let (iota_ty, _) = derived::define_abbrev(&mut env, &[], &unit).expect("an abbreviation");
    let pv = env.fresh_var();
    let (res, _) = derived::define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("an abbreviation");
    let indexed = IndexedDeclSpec::new(
        DeclSpec::new(1, vec![CtorSpec::new(t.spec.base.ctors[0].args.clone(), 0)]),
        vec![iota_ty],
        vec![CtorIndices::nonrecursive(vec![res])],
    );
    assert_eq!(indexed.num_indices(), 1);
    assert!(LePropFields::is_present(&indexed).is_none());
    assert!(
        LePropFields::build(&mut env, &f.mach, &indexed, &lp, &[t.p]).is_none(),
        "an indexed spec",
    );

    // Two constructors: ψ is then a genuine disjunction and the statement would
    // be false — membership says only that *some* constructor's fields are
    // inhabited.
    let two = nonindexed(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let (_, _, lp3) = stack(&mut env, &mut f, &two, &[]);
    assert!(LePropFields::is_present(&two).is_none());
    assert!(
        LePropFields::build(&mut env, &f.mach, &two, &lp3, &[]).is_none(),
        "two constructors",
    );

    // No constructor at all: ψ is `⊥` and `LeProp::false_` already says `A_φ = 0`.
    let none = nonindexed(0, Vec::new());
    let (_, _, lp4) = stack(&mut env, &mut f, &none, &[]);
    assert!(
        LePropFields::build(&mut env, &f.mach, &none, &lp4, &[]).is_none(),
        "no constructor",
    );

    // A recursive field — refused for the reason `LePropRecursor` refuses it.
    let rec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::new(Vec::new(), 1)]),
        Vec::new(),
        vec![CtorIndices { result: Vec::new(), rec_args: vec![Vec::new()] }],
    );
    let (_, _, lp5) = stack(&mut env, &mut f, &rec, &[]);
    assert!(
        LePropFields::build(&mut env, &f.mach, &rec, &lp5, &[]).is_none(),
        "a recursive field",
    );
}
