//! **A projection out of a class-(T) structure, typed** — and the structure η
//! rule — `derived/src/inductive/decl_proj.rs`.
//!
//! # Three fields, and that is the point
//!
//! `πⱼ(z) = compⱼ(π₂(π₁ z))`. Reading `π₁(π₁ z)` instead lands on the `Inj₀`
//! tag, and an off-by-one in the `π₂ʲ` walk lands on a neighbour — **and no
//! declaration with fewer than three fields tells those apart.** Every fixture
//! here has three, at three *distinct* closed values, so each `πⱼ` has a
//! different right answer and a spine that slipped by one has nowhere to hide.
//!
//! # The computation rules are derived here, independently
//!
//! `DeclProj::over_declaration` takes `⊢ πⱼ(ctor₀(y⃗)) = yⱼ` as an argument and
//! **compares it against its own `proj_of`** rather than rebuilding it: the
//! consumer (`mini`'s `proj_data::computes`) owns that derivation, and a second
//! copy in shipped code is the drift the comparison exists to prevent. So this
//! file builds the chain a second time on purpose — a test helper that drifts
//! fails, and if this chain and the consumer's disagree then one of them is
//! wrong and `over_declaration` refuses the other.

use kernel::{Env, Formula, FnSym, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::{proj_of, CtorSpec, DeclProj, DeclSpec, Inductive, Machine};
use derived::recarg::RecArg;
use derived::sigma::Telescope;
use derived::wtype::Wtype;
use derived::{eq_trans, inst_all};

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

fn fixture(env: &mut Env) -> Machine {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 3).expect("three summands");
    mach
}

/// An opaque field type of arity `np + j` whose body is its `which`-th
/// argument.
fn field(env: &mut Env, np: usize, j: usize, which: usize) -> FnSym {
    let vars: Vec<FreeVar> = (0..np + j).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = args[which].clone();
    derived::define_abbrev(env, &vars, &t).expect("an abbreviation").0
}

/// `⊢ g(a) = g(b)` from `⊢ a = b`.
fn congr(env: &mut Env, g: &dyn Fn(Term) -> Term, ab: &Thm) -> Thm {
    let (a, b) = ab.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        a.clone(),
        b,
        hole,
        Formula::eq(g(a), g(Term::var(hole))),
    );
    Thm::mp(&Thm::mp(&leib, ab).expect("mp"), &Thm::eq_refl(g(ab.concl().as_eq().expect("eq").0)))
        .expect("mp")
}

/// **`⊢ πⱼ(ctor₀(y⃗)) = yⱼ`** — the chain, derived here rather than imported.
///
/// ```text
/// π₁ ⟨Inj₀(tuple), f(∅)⟩  = Inj₀(tuple)     Proj::fst
/// Inj₀(tuple)             = ⟨∅, tuple⟩      ISumSyms::inj_ax at depth 0
/// π₂ ⟨∅, tuple⟩           = tuple           Proj::snd      ← the `π₂(π₁ ·)`
/// π₂ ⟨y_q, rest⟩          = rest            Proj::snd, q < j
/// π₁ ⟨y_j, rest⟩          = y_j             Proj::fst
/// ```
fn computes(env: &mut Env, mach: &Machine, ind: &Inductive, j: usize, ys: &[Term]) -> Thm {
    let s = mach.wt.sums.clone();
    let ap = s.ap.clone();
    let ctor = ind.ctor_term(mach, 0, ys, &[]).expect("the constructor term");
    let tuple = Telescope::tuple_of(&s, ys);
    let tag = mach.syms.inj(0, tuple.clone()).expect("Inj₀");
    let recf = RecArg::of(&s, &mach.cases, &[]);

    let e_tag = inst_all(&mach.proj.fst, &[tag.clone(), recf]).expect("π₁ of the outer pair");
    assert_eq!(
        e_tag.concl().as_eq().expect("eq"),
        (mach.proj.fst_of(&ap, ctor.clone()), tag.clone()),
        "π₁(ctor₀(y⃗)) is the tag"
    );

    let unfold =
        inst_all(mach.syms.inj_ax(0).expect("inj_ax"), std::slice::from_ref(&tuple)).expect("at");
    assert_eq!(
        unfold.concl().as_eq().expect("eq").1,
        s.inl(tuple.clone()),
        "Inj₀(x) unfolds to inl(x) = ⟨∅, x⟩"
    );

    let snd = |t: Term| mach.proj.snd_of(&ap, t);
    let e_pay = {
        let a = congr(env, &snd, &e_tag);
        let b = congr(env, &snd, &unfold);
        let via = eq_trans(env, &a, &b).expect("trans");
        let step = inst_all(&mach.proj.snd, &[s.zero(), tuple.clone()]).expect("π₂ of ⟨∅,tuple⟩");
        eq_trans(env, &via, &step).expect("trans")
    };

    let mut cur = e_pay;
    for q in 0..j {
        let rest = Telescope::tuple_of(&s, &ys[q + 1..]);
        let step = inst_all(&mach.proj.snd, &[ys[q].clone(), rest]).expect("one tail");
        let lift = congr(env, &snd, &cur);
        cur = eq_trans(env, &lift, &step).expect("trans");
    }
    let fst = |t: Term| mach.proj.fst_of(&ap, t);
    let head = inst_all(
        &mach.proj.fst,
        &[ys[j].clone(), Telescope::tuple_of(&s, &ys[j + 1..])],
    )
    .expect("the head");
    let lift = congr(env, &fst, &cur);
    let out = eq_trans(env, &lift, &head).expect("trans");
    assert_eq!(
        out.concl().as_eq().expect("eq"),
        (proj_of(&ap, &mach.proj, j, ctor), ys[j].clone()),
        "the chain lands on `proj_of`'s spine and on field j"
    );
    assert!(out.hyps().is_empty());
    out
}

/// A three-field structure whose **third field type depends on the first two**,
/// so the typing at field 2 is stated at `π₀ z` and `π₁ z` and not at anything
/// simpler.
struct Three {
    spec: DeclSpec,
    args: [FnSym; 3],
}

fn three(env: &mut Env) -> Three {
    // `β₀(p) = p`, `β₁(p,y₀) = y₀`, `β₂(p,y₀,y₁) = y₁`.
    let args = [field(env, 1, 0, 0), field(env, 1, 1, 1), field(env, 1, 2, 2)];
    Three { spec: DeclSpec::new(1, vec![CtorSpec::new(args.to_vec(), 0)]), args }
}

fn build(env: &mut Env, mach: &mut Machine, spec: &DeclSpec) -> (Inductive, Vec<FreeVar>, Vec<Thm>) {
    let ind = Inductive::build(env, mach, spec).expect("the skeleton");
    let k = spec.ctors[0].args.len();
    let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let rules = (0..k).map(|j| computes(env, mach, &ind, j, &ys)).collect();
    (ind, yvs, rules)
}

// ─────────────────────────────────────────────────────────────────────────────

/// **The spine reaches field `j` and not its neighbour, at three distinct
/// values.** `π₂(π₁ ·)` and not `π₁(π₁ ·)`, and `π₂ʲ` and not `π₂^{j±1}`.
#[test]
fn the_spine_reaches_each_of_three_fields_and_no_other() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let d = three(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &d.spec).expect("the skeleton");
    let s = mach.wt.sums.clone();
    let ap = s.ap.clone();

    // Three *distinct* closed field values.
    let vs: Vec<Term> =
        (0..3).map(|i| mach.syms.inj(i, s.point()).expect("Inj_i")).collect();
    assert_ne!(vs[0], vs[1]);
    assert_ne!(vs[1], vs[2]);
    assert_ne!(vs[0], vs[2]);

    let ctor = ind.ctor_term(&mach, 0, &vs, &[]).expect("the constructor term");
    for j in 0..3 {
        let rule = computes(&mut env, &mach, &ind, j, &vs);
        assert_eq!(
            *rule.concl(),
            Formula::eq(proj_of(&ap, &mach.proj, j, ctor.clone()), vs[j].clone()),
            "π{j} computes to field {j}"
        );
        // …and to no other field: the three answers are pairwise different.
        for (i, v) in vs.iter().enumerate() {
            if i != j {
                assert_ne!(
                    *rule.concl(),
                    Formula::eq(proj_of(&ap, &mach.proj, j, ctor.clone()), v.clone())
                );
            }
        }
        assert!(closed(rule.concl()) && rule.hyps().is_empty());
    }

    // The tag is what `π₁(π₁ z)` reads, and it is not any field — which is why
    // the prefix is `π₂(π₁ ·)`.
    let wrong = mach.proj.fst_of(&ap, mach.proj.fst_of(&ap, ctor.clone()));
    let right = mach.proj.snd_of(&ap, mach.proj.fst_of(&ap, ctor));
    assert_ne!(wrong, right, "π₁(π₁ z) is the Inj₀ tag, not the payload");
}

/// **The deliverable.** `⊢ ∀p ∀z. (z ∈ ind(p) → πⱼ(z) ∈ βⱼ(p, π₀ z, …))`, and
/// the third field's type really is stated at the two projections before it.
#[test]
fn the_projection_is_typed_at_an_arbitrary_carrier_element() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let d = three(&mut env);
    let (ind, yvs, rules) = build(&mut env, &mut mach, &d.spec);
    let dp = DeclProj::over_declaration(&mut env, &mach, &ind, &yvs, &rules)
        .expect("the projection typings and η");

    let s = mach.wt.sums.clone();
    let ap = s.ap.clone();
    let p = ind.params[0];
    let tz = Term::var(dp.major);
    let pz: Vec<Term> = (0..3).map(|j| proj_of(&ap, &mach.proj, j, tz.clone())).collect();
    assert_eq!(dp.proj, pz, "the exported spine is `proj_of`'s");
    assert_eq!(dp.typed.len(), 3);

    let mem_z = Formula::mem(tz.clone(), ind.carrier.clone());
    for j in 0..3 {
        let mut a = vec![Term::var(p)];
        a.extend(pz[..j].iter().cloned());
        let want = Formula::forall(
            p,
            Formula::forall(
                dp.major,
                Formula::imp(
                    mem_z.clone(),
                    Formula::mem(pz[j].clone(), Term::apply(d.args[j], a)),
                ),
            ),
        );
        assert_eq!(*dp.typed[j].concl(), want, "typed[{j}]");
        assert!(dp.typed[j].hyps().is_empty() && closed(dp.typed[j].concl()));
    }

    // The loop's `want` at `j = 2` is stated at `β₂(p, π₀ z, π₁ z)` — two
    // *different* projections, which is what a two-field fixture could not
    // show, and the assertion above already compares against it verbatim.
    assert_ne!(pz[0], pz[1]);
    assert_ne!(pz[1], pz[2]);
}

/// **The structure η rule**, which `rect` assembles internally and drops.
/// `105_structEta` wants exactly this at its own subject, so it is stated
/// `∀z` and instantiated rather than stored at witnesses no consumer can name.
#[test]
fn the_structure_eta_rule_is_exported_and_fires() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let d = three(&mut env);
    let (ind, yvs, rules) = build(&mut env, &mut mach, &d.spec);
    let dp = DeclProj::over_declaration(&mut env, &mach, &ind, &yvs, &rules).expect("built");

    let s = mach.wt.sums.clone();
    let ap = s.ap.clone();
    let p = ind.params[0];
    let tz = Term::var(dp.major);
    let pz: Vec<Term> = (0..3).map(|j| proj_of(&ap, &mach.proj, j, tz.clone())).collect();
    let want = Formula::forall(
        p,
        Formula::forall(
            dp.major,
            Formula::imp(
                Formula::mem(tz.clone(), ind.carrier.clone()),
                Formula::eq(
                    ind.ctor_term(&mach, 0, &pz, &[]).expect("ctor₀ at the projections"),
                    tz.clone(),
                ),
            ),
        ),
    );
    assert_eq!(*dp.eta.concl(), want, "⊢ ∀p ∀z. (z ∈ ind(p) → ctor₀(π⃗ z) = z)");
    assert!(dp.eta.hyps().is_empty() && closed(dp.eta.concl()));

    // It fires at a consumer's own subject: instantiate, and the equation is
    // about that subject and nothing of this module's.
    let pv = Term::var(env.fresh_var());
    let xv = Term::var(env.fresh_var());
    let at = inst_all(&dp.eta, &[pv.clone(), xv.clone()]).expect("at the consumer's terms");
    let px: Vec<Term> = (0..3).map(|j| proj_of(&ap, &mach.proj, j, xv.clone())).collect();
    let carrier_at_p = Term::apply(ind.ty, vec![pv]);
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(xv.clone(), carrier_at_p),
            Formula::eq(ind.ctor_term(&mach, 0, &px, &[]).expect("ctor₀"), xv),
        ),
        "η at the consumer's own x — `Prod.mk (fst x) (snd x) = x`"
    );
}

/// `k = 0`: nothing to project, but η still says the carrier's one element is
/// `ctor₀()`.
#[test]
fn a_fieldless_structure_has_no_projections_but_still_has_eta() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary()]);
    let (ind, yvs, rules) = build(&mut env, &mut mach, &spec);
    let dp = DeclProj::over_declaration(&mut env, &mach, &ind, &yvs, &rules).expect("built");
    assert!(dp.typed.is_empty() && dp.proj.is_empty());
    let tz = Term::var(dp.major);
    assert_eq!(
        *dp.eta.concl(),
        Formula::forall(
            dp.major,
            Formula::imp(
                Formula::mem(tz.clone(), ind.carrier.clone()),
                Formula::eq(ind.ctor_term(&mach, 0, &[], &[]).expect("ctor₀()"), tz),
            ),
        )
    );
    assert!(dp.eta.hyps().is_empty());
}

/// **What is refused.** Two constructors — where the statement is *false*,
/// because `π₂(π₁ z)` is the packed tuple only under `Inj₀` — a recursive
/// field, and a computation rule about the wrong field.
///
/// The last is the one that matters for the interface: the rules are an
/// argument, so the comparison against `proj_of` is what stops a consumer's
/// projection term and this module's from being two different terms.
#[test]
fn two_constructors_a_recursive_field_and_a_mismatched_rule_are_refused() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let s = mach.wt.sums.clone();
    let one = s.unit();

    let d = three(&mut env);
    let (ind, yvs, rules) = build(&mut env, &mut mach, &d.spec);
    assert!(DeclProj::over_declaration(&mut env, &mach, &ind, &yvs, &rules).is_some());

    // A rule about field 1 handed in at slot 0.
    let mut swapped = rules.clone();
    swapped[0] = rules[1].clone();
    assert!(
        DeclProj::over_declaration(&mut env, &mach, &ind, &yvs, &swapped).is_none(),
        "every rule is compared against `proj_of` at its own index"
    );

    // Two constructors.
    let unit_field = |env: &mut Env| {
        derived::define_abbrev(env, &[], &one).expect("an abbreviation").0
    };
    let (b0, b1) = (unit_field(&mut env), unit_field(&mut env));
    let two = DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0), CtorSpec::new(vec![b1], 0)]);
    let ind2 = Inductive::build(&mut env, &mut mach, &two).expect("the skeleton");
    let yv = vec![env.fresh_var()];
    let r2 = vec![computes(&mut env, &mach, &ind2, 0, &[Term::var(yv[0])])];
    assert!(
        DeclProj::over_declaration(&mut env, &mach, &ind2, &yv, &r2).is_none(),
        "under Inj₁ the spine reads the wrong component, so the statement is false"
    );

    // A recursive field.
    let b2 = unit_field(&mut env);
    let rec = DeclSpec::new(0, vec![CtorSpec::new(vec![b2], 1)]);
    let indr = Inductive::build(&mut env, &mut mach, &rec).expect("the skeleton");
    let yvr = vec![env.fresh_var()];
    // A rule of the **right length**, so the refusal goes through the real path
    // rather than the arity check: `computes[j]` is about `ctor₀(y⃗)` with no
    // recursive argument, and that is not a recursive declaration's constructor
    // term at all, so the term the comparison is against cannot even be formed.
    let rr = vec![Thm::eq_refl(Term::var(yvr[0]))];
    assert!(DeclProj::over_declaration(&mut env, &mach, &indr, &yvr, &rr).is_none());
}
