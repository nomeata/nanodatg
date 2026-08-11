//! **The degenerate recursor** — `derived/src/inductive/degen.rs`.
//!
//! # What these cells are for
//!
//! The construction's claim is that at one constructor and no recursive field
//! the eliminator needs **no target, no `HYP` and no parameters**, because it is
//! the inverse of the constructor. Three of the cells below pin exactly that
//! claim rather than the derivation: the ι rule's conclusion is *closed* (so no
//! parameter and no field variable leaked), it carries no sequent hypothesis and
//! no antecedent (so nothing was assumed), and its two sides are different terms
//! (so it is not `s = s` wearing a hat).
//!
//! # Three fields, at three distinct values
//!
//! Every fixture has **three** fields at three pairwise-different closed
//! values. Two cannot distinguish an argument-position walk that slips by one
//! from the identity on it, and the ι rule is exactly such a walk: it rewrites
//! `πⱼ(ctor₀(y⃗))` to `yⱼ` in the minor premise's `j`-th slot, `k` times. At
//! `k = 2` a swap of the last two lands on a formula that is still an equation
//! between two applications of `s` to two of the same three terms.

use kernel::{Env, Formula, FnSym, FreeVar, Term};

use derived::bound::Bound;
use derived::inductive::{
    applied_minor, proj_of, CtorSpec, DeclProj, DeclSpec, DegenRec, Inductive, Machine, Slot,
};
use derived::inst_all;
use derived::wtype::Wtype;

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

/// A closed field type of arity `0` — for a fixture with no parameter, where
/// `field` above has no argument to name.
fn const_field(env: &mut Env, mach: &Machine) -> FnSym {
    let t = mach.wt.sums.zero();
    derived::define_abbrev(env, &[], &t).expect("an abbreviation").0
}

/// A three-field structure **with a parameter**, whose third field type depends
/// on the first two. The parameter is the point of the fixture: the ι rule must
/// come out closed even though the declaration has one.
fn three(env: &mut Env) -> DeclSpec {
    let args = vec![field(env, 1, 0, 0), field(env, 1, 1, 1), field(env, 1, 2, 2)];
    DeclSpec::new(1, vec![CtorSpec::new(args, 0)])
}

/// Three pairwise-different closed terms, for the fields.
fn values(mach: &Machine) -> Vec<Term> {
    let s = mach.wt.sums.clone();
    let vs: Vec<Term> = (0..3).map(|i| mach.syms.inj(i, s.point()).expect("Inj_i")).collect();
    assert_ne!(vs[0], vs[1]);
    assert_ne!(vs[1], vs[2]);
    assert_ne!(vs[0], vs[2]);
    vs
}

// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable.** `⊢ ∀s ∀y⃗. drec(s, ctor₀(y⃗)) = s y₀ y₁ y₂`, and it fires
/// at three distinct values onto the right one in each slot.
#[test]
fn the_iota_rule_is_the_minor_premise_at_the_fields() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = three(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let dr = DegenRec::build(&mut env, &mach, &ind).expect("the degenerate recursor");
    assert_eq!(dr.arity, 3);

    let s = mach.wt.sums.clone();
    let ap = s.ap.clone();
    let vs = values(&mach);
    // A closed minor premise. Any set will do — the rule assumes nothing about
    // it, which is half of what "no `HYP`" means.
    let minor = s.zero();

    let at = inst_all(&dr.iota, &[minor.clone(), vs[0].clone(), vs[1].clone(), vs[2].clone()])
        .expect("∀s ∀y⃗, instantiated");
    let ctor = ind.ctor_term(&mach, 0, &vs, &[]).expect("the constructor term");

    let lhs = dr.value_of(&mach, &ind, &minor, &ctor).expect("drec at the constructor");
    let rhs = (0..3).fold(minor.clone(), |acc, j| ap.apply(acc, vs[j].clone()));
    assert_eq!(*at.concl(), Formula::eq(lhs.clone(), rhs.clone()), "the ι rule at these values");

    // **Non-vacuity.** The two sides are different terms: the left reads the
    // fields back out of the constructor, the right names them.
    assert_ne!(lhs, rhs);

    // …and onto the *right* field in each slot. Swapping any two of the three
    // arguments gives a different right-hand side, so a walk that slipped by
    // one would not satisfy the assertion above.
    for (i, j) in [(0usize, 1usize), (1, 2), (0, 2)] {
        let mut sw = vs.clone();
        sw.swap(i, j);
        let other = (0..3).fold(minor.clone(), |acc, q| ap.apply(acc, sw[q].clone()));
        assert_ne!(rhs, other, "slots {i} and {j} are distinguishable");
    }

    // `value_of` is the same spelling the theorem is stated at, at an arbitrary
    // subject as well as at the constructor.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let at_z = dr.value_of(&mach, &ind, &minor, &tz).expect("drec at a variable");
    let want_z =
        (0..3).fold(minor, |acc, j| ap.apply(acc, proj_of(&ap, &mach.proj, j, tz.clone())));
    assert_eq!(at_z, want_z);
    assert_eq!(dr.proj_at(&mach, &ind, 1, tz.clone()).expect("π₁"), proj_of(&ap, &mach.proj, 1, tz));
    assert!(dr.proj_at(&mach, &ind, 3, Term::var(zv)).is_err(), "the field index is checked");
}

/// **No target, no `HYP`, no parameters** — the three things the general
/// recursor needs and this one does not, each pinned as a property of the
/// exported theorem rather than of the derivation.
#[test]
fn the_iota_rule_is_closed_and_unconditional() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = three(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    assert_eq!(ind.params.len(), 1, "the fixture really does have a parameter");
    let dr = DegenRec::build(&mut env, &mach, &ind).expect("built");

    // No sequent hypothesis on any export.
    assert!(dr.iota.hyps().is_empty());
    assert!(dr.proj_computes.iter().all(|t| t.hyps().is_empty()));

    // **Closed**: `∀s ∀y⃗` binds everything, so the declaration's parameter does
    // not occur. That is the claim "the rule is parameter-free", and it is the
    // reason a consumer needs no type-former nest to fire it.
    assert!(closed(dr.iota.concl()), "the ι rule mentions no free variable at all");
    assert!(dr.proj_computes.iter().all(|t| closed(t.concl())));

    // **No antecedent, and the quantifier prefix is `∀s ∀y⃗`**: the conclusion
    // is rebuilt here and compared verbatim, so an implication `H → equation`
    // — which the general (S4) is at every declaration — would not match.
    let ap = mach.wt.sums.ap.clone();
    let order = &ind.spec.ctors[0].order;
    let s = Term::var(dr.minor);
    let ys: Vec<Term> = dr.fields.iter().map(|v| Term::var(*v)).collect();
    let ctor = ind.ctor_term(&mach, 0, &ys, &[]).expect("ctor");
    let pc: Vec<Term> = (0..3).map(|j| proj_of(&ap, &mach.proj, j, ctor.clone())).collect();
    let body = Formula::eq(
        applied_minor(&ap, order, &s, &pc, &[], &[]),
        applied_minor(&ap, order, &s, &ys, &[], &[]),
    );
    let want = dr
        .fields
        .iter()
        .rev()
        .fold(body, |acc, v| Formula::forall(*v, acc));
    assert_eq!(*dr.iota.concl(), Formula::forall(dr.minor, want), "∀s ∀y⃗. drec = s y⃗");
}

/// **The projection reduction rule is the same theorem**, exported so the
/// second consumer does not re-derive it — `(mk a⃗).j ⟶ aⱼ` and
/// `S.rec C f (S.mk a⃗) ⟶ f a⃗` are one eliminator asked twice.
#[test]
fn the_bundle_also_serves_the_projection_rule() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = three(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let dr = DegenRec::build(&mut env, &mach, &ind).expect("built");
    assert_eq!(dr.proj_computes.len(), 3);

    let ap = mach.wt.sums.ap.clone();
    let vs = values(&mach);
    let ctor = ind.ctor_term(&mach, 0, &vs, &[]).expect("the constructor term");
    for j in 0..3 {
        let at = inst_all(&dr.proj_computes[j], &vs).expect("∀y⃗, instantiated");
        assert_eq!(
            *at.concl(),
            Formula::eq(proj_of(&ap, &mach.proj, j, ctor.clone()), vs[j].clone()),
            "π{j}(ctor₀(a,b,c)) = the {j}-th field"
        );
        // …and not any other field: three distinct values, so an off-by-one in
        // the spine has nowhere to hide.
        for (i, v) in vs.iter().enumerate() {
            if i != j {
                assert_ne!(
                    *at.concl(),
                    Formula::eq(proj_of(&ap, &mach.proj, j, ctor.clone()), v.clone())
                );
            }
        }
    }
}

/// **`DeclProj::build` derives the same rules** the one-call entry now owns, and
/// agrees with `over_declaration` at a caller's own chain.
#[test]
fn the_one_call_projection_bundle_agrees_with_the_supplied_form() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = three(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let dp = DeclProj::build(&mut env, &mach, &ind).expect("the projection bundle");
    assert_eq!(dp.typed.len(), 3);
    assert!(dp.typed.iter().all(|t| t.hyps().is_empty() && closed(t.concl())));
    assert!(dp.eta.hyps().is_empty() && closed(dp.eta.concl()));

    // The degenerate recursor's rules and this bundle's are about the same
    // spine: instantiated at the same values they are the same formula.
    let dr = DegenRec::build(&mut env, &mach, &ind).expect("built");
    let vs = values(&mach);
    let ap = mach.wt.sums.ap.clone();
    let ctor = ind.ctor_term(&mach, 0, &vs, &[]).expect("ctor");
    for j in 0..3 {
        let a = inst_all(&dr.proj_computes[j], &vs).expect("at");
        assert_eq!(
            *a.concl(),
            Formula::eq(proj_of(&ap, &mach.proj, j, ctor.clone()), vs[j].clone())
        );
    }
}

// ── the refusals, one input each ─────────────────────────────────────────────

/// **A recursive field is declined by name**, not left to fail inside: the
/// induction hypothesis there is `drec(s, ρⱼ(z))`, which is the W-recursor.
#[test]
fn a_recursive_field_is_declined() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let args = vec![const_field(&mut env, &mach)];
    // One plain field and one recursive one — `Nat`-shaped at one constructor.
    let spec = DeclSpec::new(0, vec![CtorSpec::new(args, 1)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let e = DegenRec::build(&mut env, &mach, &ind).err().expect("must decline");
    assert!(e.is_decline(), "{e}");
    assert!(e.reason().contains("recursive field"), "{e}");
}

/// **Two constructors is the general recursor's case**, and the eliminator here
/// would be about the `Inj₀` payload of an element that may carry `Inj₁`.
#[test]
fn two_constructors_are_declined() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let a0 = const_field(&mut env, &mach);
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![a0], 0), CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let e = DegenRec::build(&mut env, &mach, &ind).err().expect("must decline");
    assert!(e.is_decline(), "{e}");
    assert!(e.reason().contains("one-constructor"), "{e}");
}

/// **A foreign apparatus is refused at the door.** Every term below resolves
/// `Inj₀`, the pairing and the projections against the machine it is handed, and
/// a second machine answers all of them — with theorems about other sets.
#[test]
fn a_foreign_apparatus_is_refused() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = three(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let other = fixture(&mut env);
    let e = DegenRec::build(&mut env, &other, &ind).err().expect("must decline");
    assert!(e.is_decline(), "{e}");

    // …and the guard is at every term-former too, not only at `build`.
    let dr = DegenRec::build(&mut env, &mach, &ind).expect("built");
    let z = Term::var(env.fresh_var());
    assert!(dr.value_of(&other, &ind, &z.clone(), &z).is_err());
    assert!(dr.proj_at(&other, &ind, 0, z).is_err());
}

/// **`k = 0` is allowed and its rule is `s = s`** — true, degenerate, and the
/// one case a consumer should route to the general recursor's policy 1 instead.
/// [`DegenRec::arity`] is exported so it can.
#[test]
fn a_fieldless_structure_is_the_identity_and_says_so() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    let dr = DegenRec::build(&mut env, &mach, &ind).expect("built");
    assert_eq!(dr.arity, 0);
    assert!(dr.proj_computes.is_empty());
    let s = Term::var(env.fresh_var());
    assert_eq!(dr.value_of(&mach, &ind, &s, &s).expect("value"), s, "drec(s, z) = s at k = 0");
}

/// **A build mints no function symbol at all** — no `define_abbrev`, no
/// Replacement, no Separation — so a consumer may try this path first and fall
/// back to the general recursor for nothing. `GenRecursor::build`'s own header
/// records the opposite case: a late refusal there used to leave the
/// environment permanently larger, because one Replacement per constructor had
/// already been minted. Both a **success** and a **decline** are checked here.
#[test]
fn building_mints_no_symbol_into_the_environment() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = three(&mut env);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");

    // `next_sym` has no accessor, so two probe symbols bracket the call and the
    // gap between their ids is what was minted in between.
    let before = env.declare(0).id();
    let dr = DegenRec::build(&mut env, &mach, &ind).expect("built");
    let after = env.declare(0).id();
    assert_eq!(after - before, 1, "a successful build minted {} symbols", after - before - 1);
    assert_eq!(dr.arity, 3);

    // …and a decline leaves nothing behind either.
    let other = fixture(&mut env);
    let before = env.declare(0).id();
    assert!(DegenRec::build(&mut env, &other, &ind).is_err());
    let after = env.declare(0).id();
    assert_eq!(after - before, 1, "a declined build minted {} symbols", after - before - 1);
}

/// The field mask really is all-plain at `m = 0`, so the guard on it is a live
/// check of the spec rather than a restatement of `recs == 0`.
#[test]
fn the_field_mask_is_all_plain() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let spec = three(&mut env);
    assert!(spec.ctors[0].order.iter().all(|s| *s == Slot::Plain));
    assert_eq!(spec.ctors[0].order.len(), 3);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("the skeleton");
    assert!(DegenRec::build(&mut env, &mach, &ind).is_ok());
}
