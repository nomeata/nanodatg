//! Inaccessibility for `U(x)`: the reduction, and the clause it closes.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀x ∀y. ((y ⊆ U(x) ∧ ¬(y ∈ U(x)))
//!        → ∃u. ((is_universe(u) ∧ x ∈ u) ∧ (y ≈ u ∧ ¬(y ∈ u))))  [inaccessibility_reduction]
//! ⊢ ∀x. C₄(U(x))                                       [least_universe_inaccessible]
//! ⊢ ∀x. is_universe(U(x))                              [least_universe_is_universe]
//! ⊢ ∀x. U(x) ∈ U(U(x))                                          [tower_step]
//! ```
//!
//! **Nothing is assumed** and callers need no derivation.
//!
//! # The argument
//!
//! Inaccessibility asks that every `y ⊆ U(x)` be either a member of `U(x)` or
//! equinumerous with it. Suppose it is not a member. Then — the reduction — some
//! universe `u ∋ x` misses `y`, and since `y ⊆ U(x) ⊆ u`, that `u`'s own
//! inaccessibility forces `y ≈ u`.
//!
//! That leaves the goal `y ≈ U(x)` available *for the wrong set*: a bijection
//! `y → u`, with `y ⊆ U(x) ⊆ u`. Closing the gap is
//! **Cantor–Schröder–Bernstein**, in the sandwiched form
//! [`crate::csb::equinumerous_sandwich`] — `a ⊆ b ⊆ c` and `a ≈ c` give `a ≈ b`.
//! The inclusion `U(x) ⊆ u` is
//! [`crate::universe::least_universe_transfer`] generalised over its element.
//!
//! # How this fails
//!
//! **There is no decline in this file.** Nothing here is a guard on caller data:
//! every entry takes the least-universe symbol together with its own axiom and
//! composes lemmas this module derived, so each of the four is either a theorem
//! or an [`crate::err::DerErr::Assembly`] — from [`crate::prim`], from a sibling
//! in [`crate::universe`], or from the unmigrated
//! [`crate::csb::equinumerous_sandwich`]. The shape checks that would elsewhere
//! be refusals are `debug_assert`s, because both sides of each are built here
//! and the composition that follows would reject a drift anyway.
//!
//! # What this cost, against what it was scheduled to cost
//!
//! This file used to say the remainder was "a genuine piece of mathematics — the
//! back-and-forth construction needs the recursion theorem, hence `ω` and
//! function graphs". **The recursion half of that was wrong.** The iterative
//! construction (`C₀ = a ∖ g[b]`, `C_{n+1} = g[f[Cₙ]]`, `C = ⋃ₙ Cₙ`) does need
//! `ω`; Knaster–Tarski computes the same set with **one Separation and no
//! recursion at all**, and no power set either, because the intersection of all
//! pre-fixed points can be written as a separation *condition* rather than as an
//! intersection over `𝒫a`. `crate::recursion` is not on this path and was not
//! used. See `crate::csb::fixpoint`.
//!
//! The function-graph half was right, and is where the cost went: `equinumerous`
//! is a first-order formula about a bijection **set**, so the conclusion had to
//! be an explicit graph, separated out of `crate::funspace`'s Cartesian product.
//!
//! It also turned out that the *general* two-injection statement is not what this
//! file wants. Neither injection exists here as a set — they are the inclusion
//! `y ↪ U(x)` and the converse of a bijection restricted to `U(x)` — so
//! `crate::csb` is stated as a scheme in two relation **formulas**, and
//! [`crate::csb::equinumerous_sandwich`] is the instance at `x = y` and
//! `⟨x,y⟩ ∈ e`. Building the two graphs would have been two Replacements and
//! eight more clauses about the results.
//!
//! # What this unblocks
//!
//! [`least_universe_is_universe`] conjoins `C₄` with the three clauses
//! `crate::universe::closure` already transferred, so `U(x)` **is** a
//! Grothendieck universe — and [`tower_step`] now says what its name suggests:
//! `x ∈ U(x) ∈ U(U(x)) ∈ ⋯` is a tower of *universes*, not merely a membership
//! chain. No closure property in [`crate::universe`] ever depended on either:
//! a property true of every universe transfers through the intersection on its
//! own, which is why everything downstream was reachable without this.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::err::{imported, DResult};
use crate::funcs::{or_intro_left, or_intro_right};
use crate::prim;
use crate::rules::{
    com12, contrapos, exists_elim_imp, exists_intro_imp, forall_mono, hyp_and, hyp_mp,
    hyp_or_elim, hyp_syl, iff_mpr, imp_mono_r, inst_all, inst_self, syl, uncurry,
};
use crate::{a1i, and_left, and_right, gen_all, imp_refl, notnot_elim};
use super::shared::hyp_contract;
use super::predicate::{inaccessible, is_universe};
use super::least::{in_all_universes, least_universe_mem};
use super::closure::{least_universe_transfer, universe_clauses};

/// `⊢ ∀x ∀y. ((y ⊆ U(x) ∧ ¬(y ∈ U(x)))
///        → ∃u. ((is_universe(u) ∧ x ∈ u) ∧ (y ≈ u ∧ ¬(y ∈ u))))`
///
/// **Half of the inaccessibility clause `C₄(U(x))`, and the half that needs
/// nothing but the axiom.** Inaccessibility asks that every `y ⊆ U(x)` be either
/// a member of `U(x)` or equinumerous with it. Suppose it is not a member. Then
/// — this theorem — some universe `u ∋ x` misses `y`, and since
/// `y ⊆ U(x) ⊆ u`, that `u`'s own inaccessibility forces `y ≈ u`.
///
/// That leaves the goal `y ≈ U(x)` available *for the wrong set*: a bijection
/// `y → u`, with `y ⊆ U(x) ⊆ u`. Closing the gap is Cantor–Schröder–Bernstein,
/// and it is [`least_universe_inaccessible`] that does it, by one instance of
/// [`crate::csb::equinumerous_sandwich`]. This theorem is kept separate because
/// it is the half that is pure universe theory — no graphs, no Separation, no
/// fixed points — and because it is what makes the split legible.
///
/// Nothing is assumed.
pub fn inaccessibility_reduction(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> DResult<Thm> {
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
    let not_phi_to_ex = contrapos(&forall_mono(u, &Thm::gen(u, &taut))?)?;
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
    let m_z_in_w = syl(&m_sub_w, &prim::ax_inst(sub_y_w, tz.clone())?)?;
    let transfer_z = com12(&least_universe_transfer(env, lu_ax, &tx, &tz, &tu)?)?;
    let m_w_to_u = hyp_mp(&a1i(&transfer_z, m.clone()), &m_a)?;
    let m_step = hyp_syl(&m_z_in_w, &m_w_to_u)?;
    let m_sub_u = prim::mp(
        &prim::ax_dist(
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
    let c4_at_y = prim::ax_inst(c4_u, ty.clone())?;
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
    Ok(gen_all(&[x, y], &h_goal))
}

/// `⊢ ∀x. U(x) ∈ U(U(x))` — the step that stacks the tower `U₀ ∈ U₁ ∈ ⋯`.
///
/// A one-line corollary: [`crate::universe::mem_least_universe`] at the term `U(x)`. What it
/// does *not* say is that the tower is strictly increasing in universe-hood —
/// that needs `is_universe(U(x))`, whose fourth (inaccessibility) clause is
/// open (see [`inaccessibility_reduction`]).
pub fn tower_step(env: &mut Env, lu: FnSym, mem_lu: &Thm) -> DResult<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let ux = Term::apply(lu, vec![tx]);
    let inst = inst_all(mem_lu, std::slice::from_ref(&ux))?;
    debug_assert_eq!(
        *inst.concl(),
        Formula::mem(ux.clone(), Term::apply(lu, vec![ux])),
        "tower_step produced an unexpected shape"
    );
    Ok(Thm::gen(x, &inst))
}

/// `⊢ ∀x. C₄(U(x))` — **the inaccessibility clause, for the least universe**.
///
/// Every `y ⊆ U(x)` is either equinumerous with `U(x)` or a member of it. This
/// is [`inaccessibility_reduction`] closed by
/// [`crate::csb::equinumerous_sandwich`]: the reduction hands over a universe
/// `u ∋ x` missing `y`, with `y ≈ u`, and `y ⊆ U(x) ⊆ u` sandwiches `U(x)`
/// between the two.
///
/// The inclusion `U(x) ⊆ u` is [`crate::universe::least_universe_transfer`]
/// generalised over its element — membership in the intersection transfers into
/// any particular universe containing `x`.
pub fn least_universe_inaccessible(
    env: &mut Env,
    s: &crate::csb::Csb,
    lu: FnSym,
    lu_ax: &Thm,
) -> DResult<Thm> {
    let red = inaccessibility_reduction(env, lu, lu_ax)?;
    let sandwich = imported(
        "crate::csb::equinumerous_sandwich",
        crate::csb::equinumerous_sandwich(env, s),
    )?;

    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);
    let y = env.fresh_var();
    let ty = Term::var(y);

    let sub_y_w = kernel::thm::subset(env, ty.clone(), w.clone());
    let y_in_w = Formula::mem(ty.clone(), w.clone());
    let equi_yw = kernel::thm::equinumerous(env, ty.clone(), w.clone());
    let disj = Formula::or(equi_yw.clone(), y_in_w.clone());
    let h = Formula::and(sub_y_w.clone(), Formula::not(y_in_w.clone()));

    // The witness the reduction produces, spelled exactly as it produces it.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let a = Formula::and(univ_u.clone(), Formula::mem(tx.clone(), tu.clone()));
    let equi_yu = kernel::thm::equinumerous(env, ty.clone(), tu.clone());
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let tail = Formula::and(equi_yu.clone(), Formula::not(y_in_u.clone()));
    let wit = Formula::and(a.clone(), tail.clone());
    let h_ex = inst_all(&red, &[tx.clone(), ty.clone()])?;
    debug_assert_eq!(
        *h_ex.concl(),
        Formula::imp(h.clone(), Formula::exists(u, wit.clone())),
        "least_universe_inaccessible: the reduction has an unexpected shape"
    );

    // ── Under `M := H ∧ WIT(u)` ─────────────────────────────────────────────
    let m = Formula::and(h.clone(), wit.clone());
    let m_h = and_left(h.clone(), wit.clone());
    let m_wit = and_right(h.clone(), wit.clone());
    let m_a = syl(&m_wit, &and_left(a.clone(), tail.clone()))?;
    let m_equi_yu = syl(
        &syl(&m_wit, &and_right(a.clone(), tail.clone()))?,
        &and_left(equi_yu.clone(), Formula::not(y_in_u.clone())),
    )?;
    let m_sub_y_w = syl(&m_h, &and_left(sub_y_w.clone(), Formula::not(y_in_w.clone())))?;

    // `M → U(x) ⊆ u`, by generalising the transfer lemma over its element.
    let z = env.fresh_var();
    let tz = Term::var(z);
    let transfer = com12(&least_universe_transfer(env, lu_ax, &tx, &tz, &tu)?)?;
    let m_step = hyp_mp(&a1i(&transfer, m.clone()), &m_a)?;
    let m_sub_w_u = prim::mp(
        &prim::ax_dist(
            z,
            m.clone(),
            Formula::imp(Formula::mem(tz.clone(), w.clone()), Formula::mem(tz, tu.clone())),
        )?,
        &Thm::gen(z, &m_step),
    )?;
    let sub_w_u = kernel::thm::subset(env, w.clone(), tu.clone());
    debug_assert_eq!(
        *m_sub_w_u.concl(),
        Formula::imp(m.clone(), sub_w_u.clone()),
        "least_universe_inaccessible: U(x) ⊆ u is not the subset formula the sandwich expects"
    );

    // Cantor–Schröder–Bernstein, in its sandwiched form.
    let csb_at = inst_all(&sandwich, &[ty.clone(), w.clone(), tu.clone()])?;
    debug_assert_eq!(
        *csb_at.concl(),
        Formula::imp(
            Formula::and(Formula::and(sub_y_w.clone(), sub_w_u), equi_yu),
            equi_yw.clone()
        ),
        "least_universe_inaccessible: the sandwich instantiated to an unexpected shape"
    );
    let m_equi_yw = hyp_mp(
        &a1i(&csb_at, m.clone()),
        &hyp_and(&hyp_and(&m_sub_y_w, &m_sub_w_u)?, &m_equi_yu)?,
    )?;
    let m_goal = syl(&m_equi_yw, &or_intro_left(equi_yw.clone(), y_in_w.clone()))?;

    // ── Discharge the witness, then the case split ──────────────────────────
    let h_goal = hyp_contract(&syl(
        &h_ex,
        &exists_elim_imp(u, &Thm::gen(u, &com12(&uncurry(&m_goal)?)?), &Formula::imp(h.clone(), disj.clone()))?,
    )?)?;
    let neg = uncurry(&h_goal)?;
    let pos = a1i(&or_intro_right(equi_yw, y_in_w.clone()), sub_y_w.clone());
    let split = a1i(&imp_refl(Formula::not(y_in_w)), sub_y_w.clone());
    let at_y = hyp_or_elim(&split, &pos, &neg)?;

    let c4 = inaccessible(env, &w);
    let out = Thm::gen(x, &Thm::gen(y, &at_y));
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(x, c4),
        "least_universe_inaccessible: wrong shape"
    );
    Ok(out)
}

/// `⊢ ∀x. is_universe(U(x))` — **`U(x)` is a Grothendieck universe**.
///
/// The four clauses, conjoined in the axiom's own nesting. `C₁`, `C₂` and `C₃`
/// are [`crate::universe::least_universe_transitive`],
/// [`crate::universe::least_universe_closed_sub`] and
/// [`crate::universe::least_universe_closed_pow`], each of which transfers
/// through the intersection pointwise; `C₄` is
/// [`least_universe_inaccessible`], and it is the one that needed
/// Cantor–Schröder–Bernstein.
///
/// With this, [`tower_step`] says what its name suggests: `U(x) ∈ U(U(x))` is a
/// step in a tower of *universes*.
pub fn least_universe_is_universe(
    env: &mut Env,
    s: &crate::csb::Csb,
    lu: FnSym,
    lu_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> DResult<Thm> {
    let c1 = super::closure::least_universe_transitive(env, lu, lu_ax)?;
    let c2 = super::closure::least_universe_closed_sub(env, lu, lu_ax)?;
    let c3 = super::closure::least_universe_closed_pow(env, lu, lu_ax, pow, pow_ax)?;
    let c4 = least_universe_inaccessible(env, s, lu, lu_ax)?;

    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx]);
    let parts: Vec<Thm> =
        [&c1, &c2, &c3, &c4].iter().map(|t| inst_self(x, t)).collect::<DResult<_>>()?;
    let joined = crate::and_intro(
        &parts[0],
        &crate::and_intro(&parts[1], &crate::and_intro(&parts[2], &parts[3])),
    );
    let out = Thm::gen(x, &joined);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(x, is_universe(env, &w)),
        "least_universe_is_universe: wrong shape"
    );
    Ok(out)
}
