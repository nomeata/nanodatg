//! The universe tower.
//!
//! Every assertion pins the **exact** conclusion, rebuilt from scratch rather
//! than read off the theorem: a lemma that is merely equivalent to the intended
//! one is useless downstream, because the next derivation matches formulas
//! syntactically. The negative assertions matter as much as the positive ones —
//! `U₀` must *not* be handed a `Level`, and the closure statements must not be
//! vacuous.

use derived::anchor::falsity;
use derived::funspace::bin_union;
use derived::tower::{Cumul, Tower};
use derived::universe as uni;
use kernel::{Env, Formula, Term, Thm};

/// A fresh constant, usable to instantiate a quantifier at.
fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

fn tower() -> (Env, Tower) {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    (env, t)
}

/// `⊢ a ∈ s`, rebuilt.
fn mem(a: &Term, s: &Term) -> Formula { Formula::mem(a.clone(), s.clone()) }

/// The two-hypothesis closure shape `(a ∈ u ∧ b ∈ u) → f(a,b) ∈ u`.
fn binary_clause(a: &Term, b: &Term, u: &Term, out: Term) -> Formula {
    Formula::imp(Formula::and(mem(a, u), mem(b, u)), mem(&out, u))
}

// ─────────────────────────────────────────────────────────────────────────────
// Level 0 — Prop, and not a universe.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀p. (p ∈ U₀ ↔ (p = 0 ∨ p = 1))`, and both truth values are in it.
#[test]
fn level_zero_is_the_two_element_set_of_truth_values() {
    let (mut env, t) = tower();
    let (zero, one) = (t.sums.zero(), t.sums.unit());
    let u0 = t.u0();

    let p = constant(&mut env);
    let inst = derived::inst_all(&t.u0_members, std::slice::from_ref(&p)).expect("instantiate");
    assert_eq!(
        *inst.concl(),
        Formula::iff(
            mem(&p, &u0),
            Formula::or(Formula::eq(p.clone(), zero.clone()), Formula::eq(p, one.clone())),
        ),
    );

    assert_eq!(*t.false_in_u0.concl(), mem(&zero, &u0));
    assert_eq!(*t.true_in_u0.concl(), mem(&one, &u0));
    // Non-vacuity of the *level*: without this `U₀` could be a singleton and
    // "φ denotes 1" would say nothing.
    assert_eq!(*t.u0_two_valued.concl(), Formula::not(Formula::eq(zero, one)));
}

/// `⊢ [φ] ∈ U₀` — every proposition's denotation is a truth value.
#[test]
fn every_proposition_denotes_a_truth_value() {
    let (mut env, t) = tower();
    // An arbitrary formula with no special properties: a bare relation between
    // two fresh constants.
    let (a, b) = (constant(&mut env), constant(&mut env));
    let phi = Formula::mem(a, b);
    let (c_sym, chi) = derived::prop::conditional_singleton(&mut env, &t.sums, &[], &phi)
        .expect("conditional_singleton");
    let c = Term::apply(c_sym, vec![]);

    let thm = t.cond_in_u0(&mut env, &phi, &c, &chi).expect("cond_in_u0");
    assert_eq!(*thm.concl(), mem(&c, &t.u0()));
}

/// `U₀` is **not** a universe, and the construction refuses to pretend it is.
#[test]
fn level_zero_is_not_a_universe() {
    let (_env, t) = tower();
    assert!(t.at(0).is_none(), "U₀ must not be handed a Level");
}

/// Proof irrelevance, for every member of `U₀` at once.
#[test]
fn every_proposition_is_a_subsingleton() {
    let (mut env, t) = tower();
    let (p, x) = (constant(&mut env), constant(&mut env));
    let inst =
        derived::inst_all(&t.u0_subsingleton, &[p.clone(), x.clone()]).expect("instantiate");
    assert_eq!(
        *inst.concl(),
        Formula::imp(
            Formula::and(mem(&p, &t.u0()), mem(&x, &p)),
            Formula::eq(x, t.sums.point()),
        ),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The tower stacks, and `ω` is in every level of it.
// ─────────────────────────────────────────────────────────────────────────────

/// `U₀ ∈ U₁ ∈ U₂ ∈ U₃`, at the terms [`Tower::level`] hands back.
#[test]
fn the_tower_stacks() {
    let (_env, t) = tower();
    for n in 1..=3 {
        let lv = t.at(n).unwrap_or_else(|| panic!("Level {n}"));
        assert_eq!(lv.set, t.level(n));
        assert_eq!(
            *lv.mem_below.concl(),
            mem(&t.level(n - 1), &t.level(n)),
            "U_{} ∈ U_{n} failed",
            n - 1
        );
    }
    // And the levels really are different terms.
    assert_ne!(t.level(0), t.level(1));
    assert_ne!(t.level(1), t.level(2));
    // Level 1 is seeded at `ω`, not at `U₀` — the whole point of the module.
    assert_eq!(t.seed(1), t.omega());
    assert_ne!(t.seed(1), t.level(0));
    assert_eq!(t.seed(2), t.level(1));
}

/// `⊢ ω ∈ Uₙ` for every `n ≥ 1`. Without this the tower is contained in `V_ω`
/// and has no infinite member at all.
#[test]
fn omega_is_a_member_of_every_universe_level() {
    let (_env, t) = tower();
    let omega = t.omega();
    for n in 1..=3 {
        let lv = t.at(n).expect("Level");
        assert_eq!(*lv.omega_mem.concl(), mem(&omega, &t.level(n)), "ω ∈ U_{n} failed");
    }
    // `ω` is the real thing, not an opaque constant: it is inductive.
    assert_eq!(*t.peano.core.zero_mem.concl(), mem(&t.sums.zero(), &omega));
}

/// `⊢ U₀ ∈ Uₙ` and `⊢ ∅ ∈ Uₙ` at every level above zero — `Prop` is a member of
/// *every* universe, not only of the one directly above it.
#[test]
fn prop_and_the_empty_set_are_in_every_level() {
    let (_env, t) = tower();
    for n in 1..=3 {
        let lv = t.at(n).expect("Level");
        assert_eq!(*lv.u0_mem.concl(), mem(&t.u0(), &t.level(n)));
        assert_eq!(*lv.empty_mem.concl(), mem(&t.sums.zero(), &t.level(n)));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The closure clauses, pinned at fresh constants.
// ─────────────────────────────────────────────────────────────────────────────

/// Every closure statement of [`derived::tower::Level`], at `U₁` and at `U₂`,
/// rebuilt from scratch and compared on the nose.
#[test]
fn the_closure_clauses_hold_at_each_level() {
    let (mut env, t) = tower();
    let sets = t.space.sets.clone();
    let (a, b) = (constant(&mut env), constant(&mut env));

    for n in 1..=2 {
        let lv = t.at(n).expect("Level");
        let u = t.level(n);
        let at2 = |thm: &Thm| {
            derived::inst_all(thm, &[a.clone(), b.clone()]).expect("instantiate at two")
        };
        let at1 = |thm: &Thm| {
            derived::inst_all(thm, std::slice::from_ref(&a)).expect("instantiate at one")
        };

        assert_eq!(
            *at2(&lv.pairing).concl(),
            binary_clause(&a, &b, &u, Term::apply(sets.up, vec![a.clone(), b.clone()])),
        );
        assert_eq!(
            *at2(&lv.opair).concl(),
            binary_clause(&a, &b, &u, derived::opair(sets.up, a.clone(), b.clone())),
        );
        assert_eq!(
            *at2(&lv.bin_union).concl(),
            binary_clause(&a, &b, &u, bin_union(&sets, a.clone(), b.clone())),
        );
        assert_eq!(
            *at2(&lv.product).concl(),
            binary_clause(&a, &b, &u, t.sums.prod.of(a.clone(), b.clone())),
        );
        assert_eq!(
            *at2(&lv.funspace).concl(),
            binary_clause(&a, &b, &u, t.sums.fs.of(a.clone(), b.clone())),
        );
        assert_eq!(
            *at1(&lv.union).concl(),
            Formula::imp(mem(&a, &u), mem(&sets.union_of(a.clone()), &u)),
        );
        assert_eq!(
            *at1(&lv.pow).concl(),
            Formula::imp(mem(&a, &u), mem(&Term::apply(t.space.pow, vec![a.clone()]), &u)),
        );
        assert_eq!(
            *at2(&lv.app).concl(),
            Formula::imp(mem(&a, &u), mem(&t.sums.ap.apply(a.clone(), b.clone()), &u)),
        );
        // Transitivity, in the applied form: `a ∈ Uₙ → (b ∈ a → b ∈ Uₙ)`.
        let trans = derived::inst_all(&lv.transitive, std::slice::from_ref(&a))
            .expect("instantiate transitive");
        let inner = Thm::ax_inst(trans.concl().as_imp().expect("an implication").1, b.clone())
            .expect("instantiate the inner ∀");
        assert_eq!(
            inner.concl().as_imp().expect("an implication").1,
            Formula::imp(mem(&b, &a), mem(&b, &u)),
        );
        // No clause is vacuous: antecedent and conclusion differ everywhere.
        for thm in [&lv.pairing, &lv.opair, &lv.bin_union, &lv.product, &lv.funspace] {
            let (ante, concl) = at2(thm).concl().as_imp().expect("an implication").clone();
            assert_ne!(ante, concl, "a closure clause came out vacuous");
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Replacement and the dependent product, at a fibre family.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A. ((A ∈ Uₙ ∧ ∀x ∈ A. b(x) ∈ Uₙ) → dprod(A) ∈ Uₙ)` — Lean's `Π` rule at
/// a level of the tower.
#[test]
fn the_pi_rule_holds_at_each_level() {
    let (mut env, t) = tower();
    let b = env.declare(1);
    let fam = t.family(&mut env, b).expect("Tower::family");

    for n in 1..=2 {
        let u = t.level(n);
        let (repl, dprod) = fam.at(&t, n).expect("Family::at");
        let big_a = constant(&mut env);
        let ante = Formula::and(mem(&big_a, &u), uni::fibres_in(&mut env, b, &big_a, &u));

        let at = derived::inst_all(&dprod, std::slice::from_ref(&big_a)).expect("instantiate");
        assert_eq!(
            *at.concl(),
            Formula::imp(ante.clone(), mem(&fam.dp.of(big_a.clone()), &u)),
        );
        let at_r = derived::inst_all(&repl, std::slice::from_ref(&big_a)).expect("instantiate");
        assert_eq!(
            *at_r.concl(),
            Formula::imp(ante, mem(&Term::apply(fam.dp.img, vec![big_a]), &u)),
        );
    }
    // A family symbol of the wrong arity is refused rather than described.
    let nullary = env.declare(0);
    assert!(t.family(&mut env, nullary).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// Non-vacuity — the tower is not degenerate.
// ─────────────────────────────────────────────────────────────────────────────

/// `U₁` is inhabited, `U₀ ≠ U₁`, and a closure antecedent is discharged at
/// concrete terms rather than left hypothetical.
#[test]
fn the_tower_is_not_degenerate() {
    let (_env, t) = tower();
    let (u0, u1) = (t.u0(), t.level(1));
    let one = t.at(1).expect("Level 1");

    // Inhabited, twice over, and by two *different* sets.
    assert_eq!(*one.mem_below.concl(), mem(&u0, &u1));
    assert_eq!(*one.omega_mem.concl(), mem(&t.omega(), &u1));

    // Not degenerate: the two levels are different sets. This is what would
    // fail if `U(·)` were the identity, and every other theorem here would
    // survive that.
    assert_eq!(*t.u0_ne_u1.concl(), Formula::not(Formula::eq(u0.clone(), u1.clone())));

    // A closure clause with its antecedent actually discharged.
    assert_eq!(*t.fs_u0_in_u1.concl(), mem(&t.sums.fs.of(u0.clone(), u0.clone()), &u1));

    // And `U₀` is genuinely `{0,1}` — the term the Prop anchor produces, not a
    // parallel copy of it.
    assert_eq!(u0, falsity::truth_values(&t.sums));
}

/// One chain of definitional extensions: the tower's `fs`, `app`, `ω` and `U`
/// all speak about the same ordered pair and the same `∅`.
#[test]
fn the_whole_tower_is_built_over_one_pairing() {
    let (_env, t) = tower();
    assert_eq!(t.space.sets.up, t.sums.ap.sets.up, "fs and app use different pairings");
    assert_eq!(t.peano.core.sets.up, t.sums.ap.sets.up, "ω uses a different pairing");
    assert_eq!(t.peano.core.empty, t.sums.ap.empty, "0 ∈ ω is about a different ∅");
    assert_eq!(t.space.pow, t.sums.pow, "fs was carved out of a different power set");
}

// ─────────────────────────────────────────────────────────────────────────────
// Cumulativity — `Uₘ ⊆ Uₙ`, and the lift rules built on it.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ Uₙ ⊆ U₍ₙ₊₁₎` at every rung, and `⊢ Uₘ ⊆ Uₙ` for every pair `m ≤ n` — as
/// the *kernel's* subset formula, since that is what downstream matches.
#[test]
fn every_level_is_contained_in_the_next() {
    let (mut env, t) = tower();
    let c = Cumul::new(&mut env, &t, 3).expect("Cumul::new");

    for n in 0..3 {
        assert_eq!(
            *c.step(n).expect("step").concl(),
            kernel::thm::subset(&mut env, t.level(n), t.level(n + 1)),
        );
    }
    for m in 0..=3 {
        for n in m..=3 {
            assert_eq!(
                *c.lift(m, n).expect("lift").concl(),
                kernel::thm::subset(&mut env, t.level(m), t.level(n)),
                "the lift from {m} to {n} is not the subset formula",
            );
        }
    }
    // Out of range, and the wrong way round, are refused rather than described.
    assert!(c.step(3).is_none());
    assert!(c.lift(0, 4).is_none());
    assert!(c.lift(2, 1).is_none());
}

/// The inclusion is **strict**: `¬(U₍ₙ₊₁₎ ⊆ Uₙ)`. Without this the whole table
/// could be a table of identities and every assertion above would survive.
#[test]
fn no_level_is_contained_in_the_one_below() {
    let (mut env, t) = tower();
    let c = Cumul::new(&mut env, &t, 3).expect("Cumul::new");
    for n in 0..3 {
        assert_eq!(
            *c.strict(n).expect("strict").concl(),
            Formula::not(kernel::thm::subset(&mut env, t.level(n + 1), t.level(n))),
        );
    }
    assert!(c.strict(3).is_none());
}

/// The base case is not special: `0` and `1`, the two members of `U₀`, arrive
/// in `U₁ = U(ω)` as *instances* of the lift. That is the `0, 1 ∈ U(ω)` the
/// direct route would have proved from `∅`-closure and pairing.
#[test]
fn both_truth_values_lift_from_level_zero_to_level_one() {
    let (mut env, t) = tower();
    let c = Cumul::new(&mut env, &t, 2).expect("Cumul::new");
    let (zero, one) = (t.sums.zero(), t.sums.unit());

    for (val, thm) in [(&zero, &t.false_in_u0), (&one, &t.true_in_u0)] {
        for n in 1..=2 {
            let up = c.raise(0, n, thm).expect("raise");
            assert_eq!(*up.concl(), mem(val, &t.level(n)));
        }
    }
    // A membership in some other set is not silently re-labelled.
    let stranger = constant(&mut env);
    let bogus = derived::inst_all(&t.mem_u, std::slice::from_ref(&stranger)).expect("x ∈ U(x)");
    assert!(c.raise(0, 1, &bogus).is_none());
}

/// The lift under a binder — the shape `Sort max(u,v)` needs, since a `Π`'s
/// fibre premise is `∀x. (x ∈ A → b(x) ∈ U)` and has to be raised wholesale.
#[test]
fn the_fibre_premise_lifts_under_its_binder() {
    let (mut env, t) = tower();
    let c = Cumul::new(&mut env, &t, 2).expect("Cumul::new");
    let b = env.declare(1);
    let big_a = constant(&mut env);

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let val = Term::apply(b, vec![tx.clone()]);
    let guard = mem(&tx, &big_a);
    let at = |n: usize| {
        Formula::forall(xv, Formula::imp(guard.clone(), mem(&val, &t.level(n))))
    };

    let mono = c.fibres_mono(xv, &guard, &val, 1, 2).expect("fibres_mono");
    assert_eq!(*mono.concl(), Formula::imp(at(1), at(2)));
    // It is the same statement `fibres_in` builds, so the `Π` rule's premise
    // really is what comes out.
    assert_eq!(at(1), uni::fibres_in(&mut env, b, &big_a, &t.level(1)));

    // The rule form, at a constant fibre whose membership is actually provable:
    // `∀x. (x ∈ A → ω ∈ U₁)` lifts to the same statement at `U₂`.
    let omega = t.omega();
    let om1 = t.at(1).expect("Level 1").omega_mem.clone();
    let premise = Thm::gen(xv, &derived::a1i(&om1, guard.clone()));
    let lifted = c.raise_fibres(xv, &guard, &omega, 1, 2, &premise).expect("raise_fibres");
    assert_eq!(
        *lifted.concl(),
        Formula::forall(xv, Formula::imp(guard.clone(), mem(&omega, &t.level(2)))),
    );
    // And refused when the premise is not the statement it claims to be.
    let bogus = Thm::gen(xv, &derived::imp_refl(guard.clone()));
    assert!(c.raise_fibres(xv, &guard, &val, 1, 2, &bogus).is_none());
}

/// The header of both rules reads "from `⊢ t ∈ Uₘ` infer `⊢ t ∈ Uₙ`", so a
/// premise that only holds *under a hypothesis* must be refused — a conclusion
/// pin alone lets one through, and `Thm::mp` then unions the caller's `Γ` into
/// a theorem the label calls unconditional.
///
/// This is the shape `mini` can actually produce: `mini/src/interp.rs`'s
/// `fs_typing` calls `Cumul::raise` on theorems obtained while a scope
/// hypothesis `x ∈ ⟦A⟧` is open, its own success check is `concl()`-only, and
/// `mini` is exempt from the boundary rule that keeps `Thm::assume` out of
/// shipped code. So the premise here is built the way mini would get one: a
/// true membership, weakened to hold under an open scope hypothesis.
#[test]
fn a_membership_that_holds_only_under_a_hypothesis_does_not_lift() {
    let (mut env, t) = tower();
    let c = Cumul::new(&mut env, &t, 2).expect("Cumul::new");
    let big_a = constant(&mut env);
    let xv = env.fresh_var();
    let scope = mem(&Term::var(xv), &big_a); // an open `x ∈ ⟦A⟧`

    // `{x ∈ A} ⊢ 0 ∈ U₀`: right conclusion, wrong sequent.
    let under_scope =
        Thm::mp(&derived::a1i(&t.false_in_u0, scope.clone()), &Thm::assume(scope.clone()))
            .expect("weaken into the scope");
    assert_eq!(*under_scope.concl(), *t.false_in_u0.concl());
    assert_eq!(under_scope.hyps(), &[scope.clone()]);
    assert!(c.raise(0, 1, &under_scope).is_none());
    // The same theorem with its hypothesis discharged still lifts, so the guard
    // is refusing the `Γ`, not the statement.
    assert!(c.raise(0, 1, &t.false_in_u0).is_some());

    // Same for the fibre form.
    let omega = t.omega();
    let om1 = t.at(1).expect("Level 1").omega_mem.clone();
    let fib = Thm::gen(xv, &derived::a1i(&om1, scope.clone()));
    let hyp = Formula::mem(t.omega(), t.level(0));
    let fib_under_hyp = Thm::mp(&derived::a1i(&fib, hyp.clone()), &Thm::assume(hyp))
        .expect("weaken the fibre premise");
    assert_eq!(*fib_under_hyp.concl(), *fib.concl());
    assert!(c.raise_fibres(xv, &scope, &omega, 1, 2, &fib_under_hyp).is_none());
    assert!(c.raise_fibres(xv, &scope, &omega, 1, 2, &fib).is_some());
}
