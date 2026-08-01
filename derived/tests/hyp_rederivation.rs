//! **SUPERSEDED.** The end-to-end comparison for the above-kernel deduction
//! layer; see the "SUPERSEDED" section of `derived/src/hyp.rs`. Result, kernel
//! calls with shared setup subtracted: hand-written 705, layer memoised 1443
//! (2.05×), layer unmemoised 1662 (2.36×) — and the hypothesis set never
//! exceeds three here, so this is the favourable case.
//!
//! **The validation**: one real, existing result derived twice — once in the
//! hand-written `⊢ H → φ` style this crate uses everywhere, once through
//! [`derived::hyp::Hyp`] — and the two conclusions compared.
//!
//! # What is re-derived
//!
//! ```text
//! ⊢ (is_universe(u) ∧ s ∈ u) → ⋃s ⊆ u
//! ```
//!
//! the `⋃s ⊆ u` step of `derived/src/universe/union.rs`'s ⋃-closure argument
//! (the block under "`⋃s ⊆ u`, by `C₁` twice along `z ∈ w ∈ s ∈ u`"). It is the
//! right size and the right shape: three nested hypothesis sets, an existential
//! witness that has to be discharged, a generalisation whose free-variable side
//! condition is exactly the one `ax_dist` enforces, and a final theorem whose
//! antecedent shape callers depend on.
//!
//! [`manual`] is that block transcribed unchanged, together with the two
//! `pub(super)` helpers it uses (`discharge` and `hyp_gen`), so that it can run
//! standalone. `union.rs` itself is not touched.
//!
//! # What is measured
//!
//! [`both_reach_the_same_theorem`] is the correctness claim: the two derivations
//! produce **the same formula**, and that formula is the one built independently
//! from `kernel::thm::subset`.
//!
//! The four `measure_*` tests exist to be run one at a time under
//! `-C instrument-coverage`, so that the execution count of each kernel rule can
//! be read off and the *baseline* (shared setup: `Sets::new`,
//! `universe_mem_mem`) subtracted. Raw totals, kernel rule invocations:
//!
//! ```text
//!   measure_baseline           1305
//!   measure_manual             2010   →  705 for the derivation
//!   measure_layer              2748   → 1443
//!   measure_layer_unmemoised   2967   → 1662
//! ```
//!
//! No driver script is checked in — the measurement is a one-off — but it is
//! reproducible from these four entry points alone.

use derived::funcs::Sets;
use derived::hyp::{order, Hyp};
use derived::universe::{is_universe, universe_mem_mem};
use derived::{a1i, and_left, and_right, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry};
use kernel::{Env, Formula, FreeVar, Term, Thm};

/// Everything both derivations need: the pairing/union symbols, `C₁` packaged
/// as `universe_mem_mem`, and the two variables the statement is about.
struct Setup {
    sets: Sets,
    mem_mem: Thm,
    tu: Term,
    ts: Term,
}

fn setup(env: &mut Env) -> Setup {
    let sets = Sets::new(env);
    let mem_mem = universe_mem_mem(env).expect("C₁ at a member of a member");
    let (uv, sv) = (env.fresh_var(), env.fresh_var());
    Setup { sets, mem_mem, tu: Term::var(uv), ts: Term::var(sv) }
}

/// The statement, built from nothing but the kernel and the universe predicate.
fn expected(env: &mut Env, s: &Setup) -> Formula {
    let us = s.sets.union_of(s.ts.clone());
    Formula::imp(
        Formula::and(is_universe(env, &s.tu), Formula::mem(s.ts.clone(), s.tu.clone())),
        kernel::thm::subset(env, us, s.tu.clone()),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// The hand-written derivation, transcribed from `universe/union.rs`.
// ─────────────────────────────────────────────────────────────────────────────

mod manual {
    use super::*;

    /// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
    /// witness `v`. Copied from `universe/union.rs`, where it is `pub(super)`.
    fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
        let (_, goal) = he_goal.concl().as_imp()?;
        let (h, _) = h_ex.concl().as_imp()?;
        let target = Formula::imp(h, goal);
        let elim = derived::exists_elim_imp(
            v,
            &Thm::gen(v, &derived::com12(&uncurry(he_goal)?)?),
            &target,
        )?;
        derived::empty::hyp_contract(&syl(h_ex, &elim)?)
    }

    /// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`. Also copied.
    fn hyp_gen(v: FreeVar, t: &Thm) -> Option<Thm> {
        let (h, phi) = t.concl().as_imp()?;
        Thm::mp(&Thm::ax_dist(v, h, phi)?, &Thm::gen(v, t))
    }

    /// `⊢ (is_universe(u) ∧ s ∈ u) → ⋃s ⊆ u`.
    pub fn union_subset(env: &mut Env, s: &Setup) -> Option<Thm> {
        let (sets, mem_mem, tu, ts) = (&s.sets, &s.mem_mem, s.tu.clone(), s.ts.clone());
        let us = sets.union_of(ts.clone());
        // BEGIN DERIVATION
        let univ_u = is_universe(env, &tu);
        let s_in_u = Formula::mem(ts.clone(), tu.clone());
        let h = Formula::and(univ_u.clone(), s_in_u.clone());
        let h_univ = and_left(univ_u.clone(), s_in_u.clone());
        let h_s = and_right(univ_u.clone(), s_in_u.clone());

        let (av, w0v) = (env.fresh_var(), env.fresh_var());
        let (ta, tw0) = (Term::var(av), Term::var(w0v));
        let a_in_us = Formula::mem(ta.clone(), us.clone());
        let q = Formula::and(h.clone(), a_in_us.clone());
        let q_h = and_left(h.clone(), a_in_us.clone());
        let q_mem = and_right(h.clone(), a_in_us.clone());

        let un_at = inst_all(&sets.un_ax, &[ts.clone(), ta.clone()])?;
        let ubody = Formula::and(
            Formula::mem(tw0.clone(), ts.clone()),
            Formula::mem(ta.clone(), tw0.clone()),
        );
        if *un_at.concl() != Formula::iff(a_in_us.clone(), Formula::exists(w0v, ubody.clone())) {
            return None
        }
        let q_ex = syl(&q_mem, &iff_mp(&un_at)?)?;

        let q1 = Formula::and(q.clone(), ubody.clone());
        let q1_q = and_left(q.clone(), ubody.clone());
        let q1_u = and_right(q.clone(), ubody.clone());
        let q1_ws = syl(
            &q1_u,
            &and_left(Formula::mem(tw0.clone(), ts.clone()), Formula::mem(ta.clone(), tw0.clone())),
        )?;
        let q1_aw = syl(
            &q1_u,
            &and_right(Formula::mem(tw0.clone(), ts.clone()), Formula::mem(ta.clone(), tw0.clone())),
        )?;
        let q1_univ = syl(&q1_q, &syl(&q_h, &h_univ)?)?;
        let q1_s = syl(&q1_q, &syl(&q_h, &h_s)?)?;

        let mm_check = |env: &mut Env, y: &Term, z: &Term| -> Option<Thm> {
            let at = inst_all(mem_mem, &[tu.clone(), y.clone(), z.clone()])?;
            let want = Formula::imp(
                Formula::and(
                    is_universe(env, &tu),
                    Formula::and(
                        Formula::mem(y.clone(), tu.clone()),
                        Formula::mem(z.clone(), y.clone()),
                    ),
                ),
                Formula::mem(z.clone(), tu.clone()),
            );
            if *at.concl() != want {
                return None
            }
            Some(at)
        };
        let mm1 = mm_check(env, &ts, &tw0)?;
        let q1_w_in_u =
            hyp_mp(&a1i(&mm1, q1.clone()), &hyp_and(&q1_univ, &hyp_and(&q1_s, &q1_ws)?)?)?;
        let mm2 = mm_check(env, &tw0, &ta)?;
        let q1_a_in_u =
            hyp_mp(&a1i(&mm2, q1.clone()), &hyp_and(&q1_univ, &hyp_and(&q1_w_in_u, &q1_aw)?)?)?;
        let q_a_in_u = discharge(w0v, &q_ex, &q1_a_in_u)?;
        let h_sub = hyp_gen(av, &uncurry(&q_a_in_u)?)?;
        // END DERIVATION
        Some(h_sub)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The same argument through the deduction layer.
// ─────────────────────────────────────────────────────────────────────────────

mod layer {
    use super::*;

    /// `⊢ (is_universe(u) ∧ s ∈ u) → ⋃s ⊆ u`.
    pub fn union_subset(env: &mut Env, s: &Setup) -> Option<Thm> {
        let (sets, mem_mem, tu, ts) = (&s.sets, &s.mem_mem, s.tu.clone(), s.ts.clone());
        let us = sets.union_of(ts.clone());
        // BEGIN DERIVATION
        let univ_u = is_universe(env, &tu);
        let s_in_u = Formula::mem(ts.clone(), tu.clone());
        let (av, w0v) = (env.fresh_var(), env.fresh_var());
        let (ta, tw0) = (Term::var(av), Term::var(w0v));
        let a_in_us = Formula::mem(ta.clone(), us.clone());
        let ubody = Formula::and(
            Formula::mem(tw0.clone(), ts.clone()),
            Formula::mem(ta.clone(), tw0.clone()),
        );

        let univ = Hyp::assume(univ_u.clone());
        let s_mem = Hyp::assume(s_in_u.clone());
        let a_mem = Hyp::assume(a_in_us.clone());
        let opened = Hyp::assume(ubody.clone());

        // `a ∈ ⋃s` unfolds to a `w ∈ s` containing `a`.
        let un_at = inst_all(&sets.un_ax, &[ts.clone(), ta.clone()])?;
        if *un_at.concl() != Formula::iff(a_in_us.clone(), Formula::exists(w0v, ubody.clone())) {
            return None
        }
        let ex_w = a_mem.rule(&iff_mp(&un_at)?)?;

        // `C₁`, at `w ∈ s ∈ u` and then at `a ∈ w ∈ u`.
        let c1 = |env: &mut Env, y: &Term, z: &Term| -> Option<Hyp> {
            let at = inst_all(mem_mem, &[tu.clone(), y.clone(), z.clone()])?;
            let want = Formula::imp(
                Formula::and(
                    is_universe(env, &tu),
                    Formula::and(
                        Formula::mem(y.clone(), tu.clone()),
                        Formula::mem(z.clone(), y.clone()),
                    ),
                ),
                Formula::mem(z.clone(), tu.clone()),
            );
            if *at.concl() != want {
                return None
            }
            Some(Hyp::lift(&at))
        };
        let w_in_u =
            c1(env, &ts, &tw0)?.mp(&univ.and_intro(&s_mem.and_intro(&opened.and_left()?)?)?)?;
        let a_in_u =
            c1(env, &tw0, &ta)?.mp(&univ.and_intro(&w_in_u.and_intro(&opened.and_right()?)?)?)?;

        // Discharge the witness, then the membership, then generalise — the
        // side condition is checked against what is left assumed.
        let sub = Hyp::obtain(w0v, &ex_w, &a_in_u)?.discharge(&a_in_us)?.gen(av)?;
        let h_sub = sub.close(&[univ_u, s_in_u])?;
        // END DERIVATION
        Some(h_sub)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Correctness, then the measurement entry points.
// ─────────────────────────────────────────────────────────────────────────────

/// The claim that makes the comparison meaningful: **the same formula**, twice.
#[test]
fn both_reach_the_same_theorem() {
    let mut env = Env::new();
    let s = setup(&mut env);
    let want = expected(&mut env, &s);

    let m = manual::union_subset(&mut env, &s).expect("the transcribed derivation closes");
    let l = layer::union_subset(&mut env, &s).expect("the layered derivation closes");

    assert_eq!(*m.concl(), want, "the transcription drifted from union.rs's statement");
    assert_eq!(*l.concl(), want, "the layered derivation proves something else");
    assert_eq!(m.concl(), l.concl(), "the two styles must agree on the nose");

    // Non-vacuity: this is a real implication about a real predicate, not `⊤`.
    let (ante, concl) = want.as_imp().expect("an implication");
    assert_ne!(ante, concl, "the statement collapsed to reflexivity");
    assert!(concl.is_forall(), "the consequent must be the ∀ that `subset` is");
}

/// The layered derivation must be insensitive to memoisation.
#[test]
fn the_layer_agrees_with_itself_unmemoised() {
    let mut env = Env::new();
    let s = setup(&mut env);
    let with = layer::union_subset(&mut env, &s).expect("memoised");
    let was = order::memo_enabled(false);
    let without = layer::union_subset(&mut env, &s).expect("unmemoised");
    order::memo_enabled(was);
    order::forget();
    assert_eq!(with.concl(), without.concl());
}

/// Shared setup only — subtract this from the two below.
#[test]
fn measure_baseline() {
    let mut env = Env::new();
    let s = setup(&mut env);
    assert!(s.mem_mem.concl().is_forall());
}

/// Setup plus the hand-written derivation.
#[test]
fn measure_manual() {
    let mut env = Env::new();
    let s = setup(&mut env);
    assert!(manual::union_subset(&mut env, &s).is_some());
}

/// Setup plus the layered derivation, memoised.
#[test]
fn measure_layer() {
    let mut env = Env::new();
    let s = setup(&mut env);
    assert!(layer::union_subset(&mut env, &s).is_some());
}

/// Setup plus the layered derivation, with the memo off.
#[test]
fn measure_layer_unmemoised() {
    let mut env = Env::new();
    let s = setup(&mut env);
    order::memo_enabled(false);
    let out = layer::union_subset(&mut env, &s);
    order::memo_enabled(true);
    order::forget();
    assert!(out.is_some());
}
