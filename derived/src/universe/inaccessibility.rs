//! Inaccessibility: the clause that is **not** proved for `U(x)`, and exactly
//! what it reduces to.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀x ∀y. ((y ⊆ U(x) ∧ ¬(y ∈ U(x)))
//!        → ∃u. ((is_universe(u) ∧ x ∈ u) ∧ (y ≈ u ∧ ¬(y ∈ u))))  [inaccessibility_reduction]
//! ⊢ ∀x. U(x) ∈ U(U(x))                                          [tower_step]
//! ```
//!
//! Everything up to that point is proved here, and **nothing is assumed**.
//! Callers need neither derivation.
//!
//! # What remains, and why it is left open
//!
//! Inaccessibility for `U(x)` asks that every `y ⊆ U(x)` be either a member of
//! `U(x)` or equinumerous with it. Suppose it is not a member. Then — this
//! theorem — some universe `u ∋ x` misses `y`, and since `y ⊆ U(x) ⊆ u`, that
//! `u`'s own inaccessibility forces `y ≈ u`.
//!
//! So the goal `y ≈ U(x)` is available *for the wrong set*: we have a bijection
//! `y → u`, and `U(x) ⊆ u` with `y ⊆ U(x)`. Composing the inclusions gives
//! injections `y ↪ U(x)` and `U(x) ↪ u ≈ y`, and concluding `y ≈ U(x)` from
//! injections both ways is **Cantor–Schröder–Bernstein**. That is a genuine
//! piece of mathematics — the back-and-forth construction needs the recursion
//! theorem, hence `ω` and function graphs — and not a matter of assembling a few
//! more combinators, which is why the clause is left open here rather than
//! half-attempted. Note also that `equinumerous` is a spelled-out first-order
//! formula about a bijection *set*, so every step of that argument would have to
//! be done at the level of explicit graphs ([`crate::funcs`]).
//!
//! Consequently `is_universe(U(x))` is **not** available, and [`tower_step`] —
//! a one-line corollary of [`crate::universe::mem_least_universe`] at the term
//! `U(x)` — says only that the tower `x ∈ U(x) ∈ U(U(x)) ∈ ⋯` is a membership
//! chain, not that it is a tower of *universes*. No closure property in
//! [`crate::universe`] depends on either.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::separation::hyp_syl;
use crate::{
    a1i, and_left, and_right, com12, contrapos, exists_elim_imp, exists_intro_imp, gen_all,
    hyp_and, hyp_mp, iff_mpr, imp_mono_r, inst_all, notnot_elim, syl, uncurry,
};
use super::shared::hyp_contract;
use super::predicate::is_universe;
use super::least::{in_all_universes, least_universe_mem};
use super::closure::{least_universe_transfer, universe_clauses};

/// `⊢ ∀x ∀y. ((y ⊆ U(x) ∧ ¬(y ∈ U(x)))
///        → ∃u. ((is_universe(u) ∧ x ∈ u) ∧ (y ≈ u ∧ ¬(y ∈ u))))`
///
/// **The inaccessibility clause of [`is_universe`] — the *fourth*, since `C₁`
/// was added — is not proved for `U(x)`, and this is exactly what remains.** Inaccessibility for `U(x)` asks that every
/// `y ⊆ U(x)` be either a member of `U(x)` or equinumerous with it. Suppose it
/// is not a member. Then — this theorem — some universe `u ∋ x` misses `y`, and
/// since `y ⊆ U(x) ⊆ u`, that `u`'s own inaccessibility forces `y ≈ u`.
///
/// So the goal `y ≈ U(x)` is available *for the wrong set*: we have a bijection
/// `y → u`, and `U(x) ⊆ u` with `y ⊆ U(x)`. Composing the inclusions gives
/// injections `y ↪ U(x)` and `U(x) ↪ u ≈ y`, and concluding `y ≈ U(x)` from
/// injections both ways is **Cantor–Schröder–Bernstein**. That is a genuine
/// piece of mathematics — the back-and-forth construction needs the recursion
/// theorem, hence `ω` and function graphs — and not a matter of assembling a
/// few more combinators, which is why the clause is left open here rather than
/// half-attempted. Note also that `equinumerous` is a spelled-out first-order
/// formula about a bijection *set*, so every step of that argument would have
/// to be done at the level of explicit graphs (`crate::funcs`).
///
/// Everything up to that point is proved here, and nothing is assumed.
pub fn inaccessibility_reduction(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);

    let y = env.fresh_var();
    let ty = Term::var(y);
    let sub_y_w = kernel::thm::subset(env, ty.clone(), w.clone());
    let y_in_w = Formula::mem(ty.clone(), w.clone());
    let h = Formula::and(sub_y_w.clone(), Formula::not(y_in_w.clone()));

    // The universe variable, and the clauses of a universe containing `x`.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), x_in_u.clone());
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    // `is_universe` is `C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))`. The walk lives in
    // [`universe_clauses`] and nowhere else.
    let cl = universe_clauses(env, &tu)?;
    let (c4_u, to_c4) = (cl.c4, cl.to_c4);

    // ── `H → ∃u. (A(u) ∧ ¬(y ∈ u))` ───────────────────────────────────────────
    //
    // Failing to be in the intersection means some universe misses it. `∃` is
    // `¬∀¬`, so this is the propositional `¬(A ∧ ¬B) → (A → B)` pushed under
    // the quantifier and contraposed.
    let taut = syl(
        &notnot_elim(Formula::imp(a.clone(), Formula::not(Formula::not(y_in_u.clone())))),
        &imp_mono_r(&notnot_elim(y_in_u.clone()), a.clone())?,
    )?;
    let witness_body = Formula::and(a.clone(), Formula::not(y_in_u.clone()));
    debug_assert_eq!(
        *taut.concl(),
        Formula::imp(Formula::not(witness_body.clone()), Formula::imp(a.clone(), y_in_u.clone()))
    );
    let not_phi_to_ex = contrapos(&crate::forall_mono(u, &Thm::gen(u, &taut))?)?;
    let phi_y = in_all_universes(env, &tx, &ty);
    debug_assert_eq!(
        *not_phi_to_ex.concl(),
        Formula::imp(Formula::not(phi_y.clone()), Formula::exists(u, witness_body.clone())),
        "the ¬∀ → ∃ step did not produce the expected shapes"
    );

    let h_not_in_w = and_right(sub_y_w.clone(), Formula::not(y_in_w.clone()));
    let h_not_phi = syl(&h_not_in_w, &contrapos(&iff_mpr(&least_universe_mem(lu_ax, &tx, &ty)?)?)?)?;
    let h_ex = syl(&h_not_phi, &not_phi_to_ex)?;

    // ── Under `M := H ∧ (A(u) ∧ ¬(y ∈ u))` ────────────────────────────────────
    let m = Formula::and(h.clone(), witness_body.clone());
    let m_h = and_left(h.clone(), witness_body.clone());
    let m_wit = and_right(h.clone(), witness_body.clone());
    let m_a = syl(&m_wit, &and_left(a.clone(), Formula::not(y_in_u.clone())))?;
    let m_not_y_in_u = syl(&m_wit, &and_right(a.clone(), Formula::not(y_in_u.clone())))?;

    // `M → y ⊆ u`, by composing `y ⊆ U(x)` with `U(x) ⊆ u`.
    let z = env.fresh_var();
    let tz = Term::var(z);
    let m_sub_w = syl(&m_h, &and_left(sub_y_w.clone(), Formula::not(y_in_w.clone())))?;
    let m_z_in_w = syl(&m_sub_w, &Thm::ax_inst(sub_y_w, tz.clone())?)?;
    let transfer_z = com12(&least_universe_transfer(env, lu_ax, &tx, &tz, &tu)?)?;
    let m_w_to_u = hyp_mp(&a1i(&transfer_z, m.clone()), &m_a)?;
    let m_step = hyp_syl(&m_z_in_w, &m_w_to_u)?;
    let m_sub_u = Thm::mp(
        &Thm::ax_dist(
            z,
            m.clone(),
            Formula::imp(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz, tu.clone())),
        )?,
        &Thm::gen(z, &m_step),
    )?;
    debug_assert_eq!(
        *m_sub_u.concl(),
        Formula::imp(m.clone(), kernel::thm::subset(env, ty.clone(), tu.clone())),
        "the composed inclusion is not the subset formula C₄ expects"
    );

    // `C₄(u)` at `y`, with `¬(y ∈ u)` selecting the equinumerosity disjunct.
    let c4_at_y = Thm::ax_inst(c4_u, ty.clone())?;
    let m_disj = hyp_mp(&syl(&syl(&m_a, &and_left(univ_u, x_in_u))?, &syl(&to_c4, &c4_at_y)?)?, &m_sub_u)?;
    let equi = kernel::thm::equinumerous(env, ty.clone(), tu.clone());
    debug_assert_eq!(
        *m_disj.concl(),
        Formula::imp(m.clone(), Formula::or(equi.clone(), y_in_u.clone())),
        "C₄ did not instantiate to the expected disjunction"
    );
    // `equi ∨ y ∈ u` is `¬equi → y ∈ u`; with `¬(y ∈ u)` that is `¬¬equi`.
    let m_nn = hyp_syl(&m_disj, &m_not_y_in_u)?;
    let m_equi = syl(&m_nn, &notnot_elim(equi.clone()))?;

    // ── Package the witness and discharge it ──────────────────────────────────
    let goal_body = Formula::and(a, Formula::and(equi, Formula::not(y_in_u)));
    let goal = Formula::exists(u, goal_body.clone());
    let m_goal = syl(
        &hyp_and(&m_a, &hyp_and(&m_equi, &m_not_y_in_u)?)?,
        &exists_intro_imp(u, goal_body, tu)?,
    )?;
    let h_goal_f = Formula::imp(h.clone(), goal.clone());
    let h_goal = hyp_contract(&syl(
        &h_ex,
        &exists_elim_imp(u, &Thm::gen(u, &com12(&uncurry(&m_goal)?)?), &h_goal_f)?,
    )?)?;
    debug_assert_eq!(*h_goal.concl(), Formula::imp(h, goal), "inaccessibility_reduction: wrong shape");
    Some(gen_all(&[x, y], &h_goal))
}

/// `⊢ ∀x. U(x) ∈ U(U(x))` — the step that stacks the tower `U₀ ∈ U₁ ∈ ⋯`.
///
/// A one-line corollary: [`crate::universe::mem_least_universe`] at the term `U(x)`. What it
/// does *not* say is that the tower is strictly increasing in universe-hood —
/// that needs `is_universe(U(x))`, whose fourth (inaccessibility) clause is
/// open (see [`inaccessibility_reduction`]).
pub fn tower_step(env: &mut Env, lu: FnSym, mem_lu: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let ux = Term::apply(lu, vec![tx]);
    let inst = inst_all(mem_lu, std::slice::from_ref(&ux))?;
    debug_assert_eq!(
        *inst.concl(),
        Formula::mem(ux.clone(), Term::apply(lu, vec![ux])),
        "tower_step produced an unexpected shape"
    );
    Some(Thm::gen(x, &inst))
}
