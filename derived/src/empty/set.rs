//! `∅`, derived from Tarski's Axiom A and Regularity.
//!
//! # Interface
//!
//! Writing `Trans(t)` for [`transitive`], i.e.
//! `∀a ∀b. ((b ∈ a ∧ a ∈ t) → b ∈ t)`, the exports are
//!
//! ```text
//! ⊢ ∀t. ((∃w. w ∈ t) ∧ Trans(t)) → ∃e ∀z. ¬(z ∈ e)                [empty_from_transitive]
//! ⊢ C₁ → Trans(u)                                                 [transitive_of_clause]
//! ⊢ ∃e ∀z. ¬(z ∈ e)                                               [empty_existence]
//! ⊢ ∀z. ¬(z ∈ ∅)                                                  [empty_of_exists, empty]
//! ⊢ ∀t ∀a. ((∃w. w ∈ t) ∧ Trans(t)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))
//!                                                                 [separation_from_transitive]
//! ```
//!
//! [`empty`] is the working symbol everything downstream consumes, and it is
//! [`empty_of_exists`] fed [`empty_existence`]. Callers need none of the
//! derivations below.
//!
//! **Nothing is asserted.** `Thm::ax_empty` was **deleted on 2026-07-31**,
//! taking the trusted set axioms from eight to seven; existence is derived from
//! Tarski and Regularity, and uniqueness — which is what makes the definitional
//! extension conservative — comes from Extensionality, via
//! [`crate::define_by_membership`].
//!
//! # The derivation, in three moves
//!
//! 1. **A non-empty set.** [`crate::empty::tarski_at`] puts an arbitrary `x`
//!    inside a universe `u`, so `x` itself witnesses `∃w. w ∈ u`. Nothing
//!    stronger is needed — [`crate::universe::universe_three_members`] would
//!    also serve, and costs considerably more.
//! 2. **A transitive one.** Tarski's clause `C₁`, `∀y ∈ u. ∀z ∈ y. z ∈ u`, says
//!    exactly that `u` is transitive. It is stated curried and guarded, while
//!    [`transitive`] is uncurried and conjunctive; [`transitive_of_clause`] is
//!    the shuffle between the two shapes, and the only fiddly step in the whole
//!    derivation.
//! 3. **Regularity.** [`empty_from_transitive`] is the heart: Regularity hands
//!    back an `∈`-minimal `y ∈ t`, meaning nothing is in both `y` and `t`;
//!    transitivity says everything in `y` *is* in `t`; so nothing is in `y`.
//!
//! The universe variable is then discharged by [`crate::exists_elim`], which it
//! may be because the conclusion does not mention it.
//!
//! [`empty_of_exists`] is kept separate from [`empty`] so that the *definition*
//! of `∅` can be tested against a premise it did not itself produce — including
//! a bogus one, which it must reject.
//!
//! # The sharpest statement
//!
//! [`separation_from_transitive`] is [`crate::separation::separation_existence`]
//! — which carries emptiness as an antecedent — with that antecedent traded for
//! the transitivity hypothesis. Full Separation costs one non-empty transitive
//! set and nothing else; [`empty_existence`] is that statement cashed in at
//! Tarski's universe. See [`crate::empty`] for why this was not possible before
//! the `C₁` clause existed.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, define_by_membership, ex_falso, exists_elim, exists_elim_imp,
    exists_intro_imp, exists_mono, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry,
};
use super::readers::{curry, open_forall, split_and};
use super::tarski::{tarski_at, Universe};

/// The transitivity of `t`, spelled out: `∀a ∀b. ((b ∈ a ∧ a ∈ t) → b ∈ t)`.
pub fn transitive(env: &mut Env, t: &Term) -> Formula {
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::imp(
                Formula::and(Formula::mem(tb.clone(), ta.clone()), Formula::mem(ta, t.clone())),
                Formula::mem(tb, t.clone()),
            ),
        ),
    )
}

/// `⊢ ∀t. ((∃w. w ∈ t) ∧ Trans(t)) → ∃e ∀z. ¬(z ∈ e)`.
///
/// **The heart of the `∅` derivation.** Regularity hands back an `∈`-minimal
/// `y ∈ t`, meaning nothing is in both `y` and `t`. Transitivity says everything
/// in `y` *is* in `t`. So nothing is in `y`.
///
/// [`empty_existence`] supplies the two premises from Tarski's universe. The
/// conclusion is what `Thm::ax_empty` used to assert, syntactically identical —
/// that equality was checked before the axiom was deleted.
///
/// This is exactly the step `separation.rs` names as unreachable — "a minimal
/// element of `t` is empty only when `t` is transitive" — turned into a
/// theorem, so that producing any non-empty transitive set now suffices.
pub fn empty_from_transitive(env: &mut Env) -> Option<Thm> {
    let reg = Thm::ax_regularity(env);

    let t = env.fresh_var();
    let tt = Term::var(t);
    let trans = transitive(env, &tt);

    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let inst = inst_all(&reg, std::slice::from_ref(&tt))?;
    let y_in_t = Formula::mem(ty.clone(), tt.clone());
    let clash_body =
        Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz.clone(), tt.clone()));
    let clash = Formula::exists(z, clash_body.clone());
    let body = Formula::and(y_in_t.clone(), Formula::not(clash.clone()));
    let nonempty = Formula::exists(y, y_in_t.clone());
    debug_assert_eq!(
        *inst.concl(),
        Formula::imp(nonempty.clone(), Formula::exists(y, body.clone())),
        "Regularity did not instantiate to the expected shape"
    );

    // `⊢ Trans(t) → ((z ∈ y ∧ y ∈ t) → z ∈ t)`, by instantiating twice.
    let trans_y = Thm::ax_inst(trans.clone(), ty.clone())?;
    let (_, trans_y_body) = trans_y.concl().as_imp()?;
    let trans_yz = syl(&trans_y, &Thm::ax_inst(trans_y_body, tz.clone())?)?;

    // Under `W := Trans(t) ∧ body(y)`, then `V := W ∧ z ∈ y`, derive `⊥`.
    let w = Formula::and(trans.clone(), body.clone());
    let w_trans = and_left(trans.clone(), body.clone());
    let w_body = and_right(trans.clone(), body.clone());
    let w_y_in_t = syl(&w_body, &and_left(y_in_t.clone(), Formula::not(clash.clone())))?;
    let w_not_clash = syl(&w_body, &and_right(y_in_t, Formula::not(clash)))?;
    let w_trans_yz = syl(&w_trans, &trans_yz)?;

    let zy = Formula::mem(tz.clone(), ty.clone());
    let v = Formula::and(w.clone(), zy.clone());
    let v_zy = and_right(w.clone(), zy.clone());
    let v_w = and_left(w.clone(), zy.clone());
    let v_pair = hyp_and(&v_zy, &syl(&v_w, &w_y_in_t)?)?;
    let v_zt = hyp_mp(&syl(&v_w, &w_trans_yz)?, &v_pair)?;
    let v_clash = hyp_mp(
        &a1i(&exists_intro_imp(z, clash_body, tz.clone())?, v.clone()),
        &hyp_and(&v_zy, &v_zt)?,
    )?;
    let v_false = hyp_mp(&syl(&v_w, &w_not_clash)?, &v_clash)?;

    // `⊢ W → ∀z. ¬(z ∈ y)`, then `y` witnesses the goal.
    let not_zy = Formula::not(zy);
    let w_not_zy = uncurry(&v_false)?;
    let w_all = Thm::mp(&Thm::ax_dist(z, w.clone(), not_zy.clone())?, &Thm::gen(z, &w_not_zy))?;

    let e = env.fresh_var();
    let empty_of = |s: &Term| Formula::forall(z, Formula::not(Formula::mem(tz.clone(), s.clone())));
    let goal = Formula::exists(e, empty_of(&Term::var(e)));
    let w_goal = syl(&w_all, &exists_intro_imp(e, empty_of(&Term::var(e)), ty.clone())?)?;
    debug_assert_eq!(*w_goal.concl(), Formula::imp(w, goal.clone()));

    // Discharge the witness `y`, then Regularity's premise.
    let trans_goal = Formula::imp(trans.clone(), goal.clone());
    let body_tg = com12(&uncurry(&w_goal)?)?;
    let ex_tg = exists_elim_imp(y, &Thm::gen(y, &body_tg), &trans_goal)?;
    let ne_tg = syl(&inst, &ex_tg)?;

    let out = curry(&ne_tg)?;
    debug_assert_eq!(*out.concl(), Formula::imp(Formula::and(nonempty, trans), goal));
    Some(Thm::gen(t, &out))
}

/// `⊢ C₁ → Trans(u)` — Tarski's transitivity clause, reshaped into the form
/// [`empty_from_transitive`] consumes.
///
/// The two say the same thing and are written differently. `C₁` is curried and
/// guarded, `∀y. (y ∈ u → ∀z. (z ∈ y → z ∈ u))`; [`transitive`] is uncurried
/// and conjunctive, `∀a ∀b. ((b ∈ a ∧ a ∈ u) → b ∈ u)`. All that happens here is
/// the shuffle between them: instantiate `C₁` at `a` and its inner `∀z` at `b`,
/// feed it the two conjuncts, then re-generalise. The `debug_assert` at the end
/// is what pins that the result really is [`transitive`]'s formula and not some
/// near-miss.
pub fn transitive_of_clause(env: &mut Env, univ: &Universe) -> Option<Thm> {
    let tu = Term::var(univ.u);
    let c1 = univ.transitive.clone();

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let b_in_a = Formula::mem(tb.clone(), ta.clone());
    let a_in_u = Formula::mem(ta.clone(), tu.clone());
    let ante = Formula::and(b_in_a.clone(), a_in_u.clone());
    let goal = Formula::mem(tb.clone(), tu.clone());

    // Under `W := C₁ ∧ (b ∈ a ∧ a ∈ u)`.
    let w = Formula::and(c1.clone(), ante.clone());
    let w_c1 = and_left(c1.clone(), ante.clone());
    let w_ante = and_right(c1.clone(), ante.clone());
    let w_b_in_a = syl(&w_ante, &and_left(b_in_a.clone(), a_in_u.clone()))?;
    let w_a_in_u = syl(&w_ante, &and_right(b_in_a, a_in_u))?;

    // `C₁` at `a`, discharged by `a ∈ u`; then its inner `∀z` at `b`.
    let c1_a = Thm::ax_inst(c1.clone(), ta)?;
    let (_, c1_a_body) = c1_a.concl().as_imp()?;
    let (_, inner) = c1_a_body.as_imp()?;
    let w_inner = hyp_mp(&syl(&w_c1, &c1_a)?, &w_a_in_u)?;
    let w_goal = hyp_mp(&syl(&w_inner, &Thm::ax_inst(inner, tb)?)?, &w_b_in_a)?;
    debug_assert_eq!(*w_goal.concl(), Formula::imp(w, goal.clone()));

    // Re-generalise. Neither `a` nor `b` occurs free in `C₁` — only `u` does —
    // so both distributions go through.
    let step = uncurry(&w_goal)?;
    let inner_f = Formula::imp(ante.clone(), goal.clone());
    let all_b = Thm::mp(&Thm::ax_dist(b, c1.clone(), inner_f.clone())?, &Thm::gen(b, &step))?;
    let outer_f = Formula::forall(b, inner_f);
    let out = Thm::mp(&Thm::ax_dist(a, c1.clone(), outer_f)?, &Thm::gen(a, &all_b))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(c1, transitive(env, &tu)),
        "C₁ was not curried into the shape empty_from_transitive wants"
    );
    Some(out)
}

/// `⊢ ∃e ∀z. ¬(z ∈ e)` — **the empty set exists**, derived.
///
/// This is what `Thm::ax_empty` used to assert. Three moves, no new assumption:
///
/// 1. [`tarski_at`] puts an arbitrary `x` inside a universe `u`, so `u` is
///    non-empty — `x` itself is the witness, and nothing stronger is needed.
/// 2. Tarski's clause `C₁` says `u` is transitive; [`transitive_of_clause`]
///    rewrites it into the shape below.
/// 3. [`empty_from_transitive`] turns any non-empty transitive set into an empty
///    one, by Regularity: an `∈`-minimal member of a transitive set has no
///    members at all.
///
/// The universe variable is then discharged by [`exists_elim`], which it may be
/// because the conclusion does not mention it.
///
/// Before the transitivity clause was added to `ax_tarski` on 2026-07-31 step 2
/// was unavailable, and the route to `∅` went through the recursion theorem and
/// a transitive closure. That is the whole reason the axiom existed.
pub fn empty_existence(env: &mut Env) -> Option<Thm> {
    let x = env.fresh_var();
    let (univ, ex_u) = tarski_at(env, x)?;
    let tu = Term::var(univ.u);

    let at_u = inst_all(&empty_from_transitive(env)?, std::slice::from_ref(&tu))?;
    let (ante, goal) = at_u.concl().as_imp()?;
    let (nonempty, trans) = split_and(&ante)?;

    // `⊢ Body → ∃w. w ∈ u`, with `x ∈ u` — the axiom's first clause — as witness.
    let w = env.fresh_var();
    let w_in_u = Formula::mem(Term::var(w), tu.clone());
    debug_assert_eq!(
        nonempty,
        Formula::exists(w, w_in_u.clone()),
        "empty_from_transitive's non-emptiness premise is not the expected shape"
    );
    let body_ne = syl(&univ.body_mem(), &exists_intro_imp(w, w_in_u, Term::var(x))?)?;

    // `⊢ Body → Trans(u)`, from `C₁`.
    let curried = transitive_of_clause(env, &univ)?;
    debug_assert_eq!(
        *curried.concl(),
        Formula::imp(univ.transitive.clone(), trans),
        "C₁ did not curry into the transitivity premise"
    );
    let body_trans = syl(&univ.body_transitive(), &curried)?;

    let body_goal = syl(&hyp_and(&body_ne, &body_trans)?, &at_u)?;
    let out = exists_elim(univ.u, &ex_u, &Thm::gen(univ.u, &body_goal), &goal)?;
    debug_assert_eq!(*out.concl(), goal, "empty_existence produced an unexpected shape");
    Some(out)
}

/// Introduce the symbol `∅` with `⊢ ∀z. ¬(z ∈ ∅)`, given `⊢ ∃e ∀z. ¬(z ∈ e)`.
///
/// The `∃!` that `kernel::thm::define` demands is existence plus
/// Extensionality — two sets with no members have the same members — which is
/// exactly what [`crate::define_by_membership`] packages, at the membership
/// condition `⊥`.
///
/// The premise is [`empty_existence`]'s conclusion, and [`empty`] is the two of
/// them packaged up. It is kept separate so that the *definition* of `∅` can be
/// tested against a premise it did not itself produce — including a bogus one,
/// which it must reject.
pub fn empty_of_exists(env: &mut Env, existence: &Thm) -> Option<(FnSym, Thm)> {
    let (e, z) = (env.fresh_var(), env.fresh_var());
    let (te, tz) = (Term::var(e), Term::var(z));
    let mem = Formula::mem(tz.clone(), te.clone());
    let emp = Formula::forall(z, Formula::not(mem.clone()));
    if *existence.concl() != Formula::exists(e, emp.clone()) {
        return None
    }

    // `¬(z ∈ e)` is the forward half of `z ∈ e ↔ ⊥`; the backward half is ex
    // falso. So `⊢ ∃e ∀z. ¬(z ∈ e)` is `⊢ ∃e ∀z. (z ∈ e ↔ ⊥)` in the shape
    // `define_by_membership` wants.
    let fwd = Thm::ax_inst(emp.clone(), tz.clone())?;
    let bwd = a1i(&ex_falso(mem.clone()), emp.clone());
    let iff_body = Formula::iff(mem, Formula::false_());
    let all = Thm::mp(&Thm::ax_dist(z, emp.clone(), iff_body)?, &Thm::gen(z, &hyp_and(&fwd, &bwd)?))?;
    let ex_iff = Thm::mp(&exists_mono(e, &Thm::gen(e, &all))?, existence)?;

    let (sym, ax) = define_by_membership(env, &[], &ex_iff, z, &Formula::false_())?;
    let at_z = Thm::mp(&Thm::ax_inst(ax.concl().clone(), tz.clone())?, &ax)?;
    let out = Thm::gen(z, &iff_mp(&at_z)?);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(z, Formula::not(Formula::mem(tz, Term::apply(sym, vec![])))),
        "empty_of_exists produced an unexpected shape"
    );
    Some((sym, out))
}

/// The symbol `∅`, with `⊢ ∀z. ¬(z ∈ ∅)`.
///
/// [`empty_of_exists`] fed [`empty_existence`]. **Nothing is asserted**: the
/// existence is derived from Tarski and Regularity, and uniqueness — which is
/// what makes the definitional extension conservative — comes from
/// Extensionality, via [`crate::define_by_membership`], inside
/// `empty_of_exists`.
///
/// This is what makes [`crate::separation::separation`] callable, and with it
/// the unconditional forms of `coll`, `fs` and `dprod`.
pub fn empty(env: &mut Env) -> (FnSym, Thm) {
    let existence = empty_existence(env).expect("empty: the ∅ derivation is unconditional");
    empty_of_exists(env, &existence).expect("empty: empty_existence is exactly the premise required")
}

/// `⊢ ∀t ∀a. ((∃w. w ∈ t) ∧ Trans(t)) → ∃s ∀z. (z ∈ s ↔ (z ∈ a ∧ φ(z)))`.
///
/// The full Separation scheme, for a caller-supplied `φ`, resting on nothing
/// but a non-empty transitive set. This is
/// [`crate::separation::separation_existence`] — which carries emptiness as an
/// antecedent — with that antecedent traded for the transitivity hypothesis via
/// [`empty_from_transitive`].
///
/// It is the sharpest honest statement of where the development stands:
/// Separation is one non-empty transitive set away, and nothing else is
/// missing.
pub fn separation_from_transitive(env: &mut Env, x: FreeVar, phi: &Formula) -> Option<Thm> {
    let sep = crate::separation::separation_existence(env, x, phi).ok()?;

    let a = env.fresh_var();
    let all_e = inst_all(&sep, &[Term::var(a)])?;
    let e = env.fresh_var();
    let opened = open_forall(all_e.concl(), &Term::var(e))?;
    let (emp, goal) = opened.as_imp()?;
    debug_assert_eq!(*all_e.concl(), Formula::forall(e, Formula::imp(emp, goal.clone())));

    let ex_goal = exists_elim_imp(e, &all_e, &goal)?;
    let t = env.fresh_var();
    let at_t = inst_all(&empty_from_transitive(env)?, &[Term::var(t)])?;
    let out = syl(&at_t, &ex_goal)?;
    Some(gen_all(&[t, a], &out))
}
