//! Infinity, and induction, from Tarski's universe.
//!
//! # Interface
//!
//! With `𝒫` as successor and a caller-supplied base point `x`,
//!
//! ```text
//! Ind(x, u)    :=  x ∈ u ∧ ∀y. (y ∈ u → 𝒫y ∈ u)                      [inductive]
//! Least(x, n)  :=  Ind(x, n) ∧ ∀w. (Ind(x, w) → ∀q. (q ∈ n → q ∈ w))  [least_inductive]
//! ```
//!
//! the exports are
//!
//! ```text
//! ⊢ ∀x ∃u. Ind(x, u)      [inductive_set_exists]
//! ⊢ ∀x ∃n. Least(x, n)    [least_inductive_set_exists]
//! ```
//!
//! Callers need neither derivation.
//!
//! # What they are
//!
//! [`inductive_set_exists`] is **not** the axiom of Infinity, and an earlier
//! version of this comment said it was. It is inductive in the **power-set**
//! sense — `x`, `𝒫x`, `𝒫𝒫x`, … all lie in Tarski's universe around `x` (by
//! [`crate::empty::universe_power_closed`]) — with an arbitrary base point,
//! whereas Infinity is inductive under the **von Neumann successor**
//! `n ↦ n ∪ {n}` with base `∅`. The two are different statements and neither
//! follows from the other by inspection.
//!
//! The real thing is [`crate::infinity`], which proves the Jech §1 / Kunen I.2
//! form and its primitive expansion. What *this* module supplies is the
//! `𝒫`-tower, which is what `crate::recursion` builds `ω` out of — and note
//! that route was forced: Tarski's universe is **not** closed under
//! `n ↦ n ∪ {n}`, so `ω` had to be separated at `Trans(q) ∧ …` instead.
//!
//! [`least_inductive_set_exists`] is `ω` — with `𝒫` as successor and `x` in
//! place of `∅` at the bottom — carved out of that universe as
//! `{q ∈ u : ∀w. (Ind(x, w) → q ∈ w)}`. That is a legitimate use of
//! [`crate::separation::separation_nonvacuous`] because `x` itself satisfies the
//! condition, so the Separation used is the *non-vacuous* one, needs no empty
//! set, and **the argument is not circular** — which is what mattered back when
//! `∅` was still downstream of it.
//!
//! Its point is the third conjunct: any inductive `w` contains `n`, which is
//! induction. Note that neither theorem gives an empty set: every iterate points
//! upwards, and reaching the bottom is what [`crate::empty::empty_existence`]
//! does by a different route entirely.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, com12_imp, exists_elim, exists_elim_imp, exists_intro_imp,
    exists_mono, hyp_and, hyp_mp, inst_all, syl, uncurry,
};
use super::readers::{curry, hyp_contract, open_exists, split_and};
use super::tarski::{tarski_at, universe_power_closed};

/// `Ind(x, u) := x ∈ u ∧ ∀y. (y ∈ u → 𝒫y ∈ u)` — `u` is *inductive over* `x`,
/// with the power set as successor.
pub fn inductive(env: &mut Env, pow: FnSym, x: &Term, u: &Term) -> Formula {
    let y = env.fresh_var();
    let ty = Term::var(y);
    Formula::and(
        Formula::mem(x.clone(), u.clone()),
        Formula::forall(
            y,
            Formula::imp(
                Formula::mem(ty.clone(), u.clone()),
                Formula::mem(Term::apply(pow, vec![ty]), u.clone()),
            ),
        ),
    )
}

/// `Least(x, n) := Ind(x, n) ∧ ∀w. (Ind(x, w) → ∀q. (q ∈ n → q ∈ w))` — `n` is
/// inductive over `x` and contained in every set that is.
pub fn least_inductive(env: &mut Env, pow: FnSym, x: &Term, n: &Term) -> Formula {
    let (w, q) = (env.fresh_var(), env.fresh_var());
    let (tw, tq) = (Term::var(w), Term::var(q));
    let contained = Formula::forall(
        q,
        Formula::imp(Formula::mem(tq.clone(), n.clone()), Formula::mem(tq, tw.clone())),
    );
    Formula::and(
        inductive(env, pow, x, n),
        Formula::forall(w, Formula::imp(inductive(env, pow, x, &tw), contained)),
    )
}

/// `⊢ ∀x ∃n. Least(x, n)` — **the least inductive set over `x` exists**, and so
/// induction is available.
///
/// This is `ω` (with `𝒫` as successor, and `x` in place of `∅` at the bottom).
/// Tarski's universe `u` around `x` is inductive by [`inductive_set_exists`];
/// the least inductive set is carved out of it as
/// `{q ∈ u : ∀w. (Ind(x, w) → q ∈ w)}`, which is a legitimate use of
/// [`crate::separation::separation_nonvacuous`] because `x` itself satisfies
/// the condition — so the Separation used here is the *non-vacuous* one, needs
/// no empty set, and the argument is not circular.
///
/// Its point is the third conjunct: any inductive `w` contains `n`, which is
/// induction. That is the hypothesis the recursion theorem runs on, and the
/// recursion theorem is what the remaining gap needs.
pub fn least_inductive_set_exists(env: &mut Env, pow: FnSym, pow_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let (univ, ex_u) = tarski_at(env, x)?;
    let tu = Term::var(univ.u);
    let body = univ.body.clone();
    let closed = universe_power_closed(env, pow, pow_ax, &univ)?;

    // The condition to separate by: `hered(q) := ∀w. (Ind(x, w) → q ∈ w)`.
    let (q, w) = (env.fresh_var(), env.fresh_var());
    let (tq, tw) = (Term::var(q), Term::var(w));
    let ind_w = inductive(env, pow, &tx, &tw);
    let (ind_mem_w, ind_step_w) = split_and(&ind_w)?;
    let hered = Formula::forall(w, Formula::imp(ind_w.clone(), Formula::mem(tq.clone(), tw.clone())));

    // `⊢ hered(x)`: every inductive set contains `x` outright.
    let hered_x = Thm::gen(w, &and_left(ind_mem_w.clone(), ind_step_w.clone()));
    debug_assert_eq!(*hered_x.concl(), hered.subst(q, &tx), "hered(x) is not the right instance");

    // Separation at `u`, non-vacuously: `x ∈ u` and `hered(x)` supply the witness.
    let sep = crate::separation::separation_nonvacuous(env, q, &hered)?;
    let at_u = inst_all(&sep, std::slice::from_ref(&tu))?;
    let (ante, ex_s) = at_u.concl().as_imp()?;
    let v = env.fresh_var();
    let ante_body = open_exists(&ante, &Term::var(v))?;
    debug_assert_eq!(
        ante_body,
        Formula::and(Formula::mem(Term::var(v), tu.clone()), hered.subst(q, &Term::var(v))),
        "the non-vacuity premise is not the expected one"
    );
    let body_witness = hyp_and(&univ.body_mem(), &a1i(&hered_x, body.clone()))?;
    let body_ex_s = syl(&syl(&body_witness, &exists_intro_imp(v, ante_body, tx.clone())?)?, &at_u)?;

    // The separated set `s`, with its membership condition.
    let (s, y) = (env.fresh_var(), env.fresh_var());
    let (ts, ty) = (Term::var(s), Term::var(y));
    let sep_at = |r: &Term| Formula::and(Formula::mem(r.clone(), tu.clone()), hered.subst(q, r));
    let p_s = Formula::forall(y, Formula::iff(Formula::mem(ty.clone(), ts.clone()), sep_at(&ty)));
    debug_assert_eq!(ex_s, Formula::exists(s, p_s.clone()), "the separated set is not as expected");

    // Work under `M := Body ∧ P(s)`.
    let m = Formula::and(body.clone(), p_s.clone());
    let m_body = and_left(body.clone(), p_s.clone());
    let m_ps = and_right(body.clone(), p_s.clone());
    let m_at = |r: &Term| -> Option<Thm> {
        syl(&m_ps, &Thm::ax_inst(p_s.clone(), r.clone())?)
    };

    // ── (i) `x ∈ s` ──────────────────────────────────────────────────────────
    let m_x_cond = hyp_and(&syl(&m_body, &univ.body_mem())?, &a1i(&hered_x, m.clone()))?;
    let m_x_in_s = hyp_mp(&crate::hyp_iff_mpr(&m_at(&tx)?)?, &m_x_cond)?;

    // ── (ii) `∀y. (y ∈ s → 𝒫y ∈ s)` ──────────────────────────────────────────
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let y_in_s = Formula::mem(ty.clone(), ts.clone());
    let n = Formula::and(m.clone(), y_in_s.clone());
    let n_m = and_left(m.clone(), y_in_s.clone());
    let n_cond = hyp_mp(
        &syl(&n_m, &crate::hyp_iff_mp(&m_at(&ty)?)?)?,
        &and_right(m.clone(), y_in_s.clone()),
    )?;
    let n_y_in_u = syl(&n_cond, &and_left(y_in_u.clone(), hered.subst(q, &ty)))?;
    let n_hered_y = syl(&n_cond, &and_right(y_in_u.clone(), hered.subst(q, &ty)))?;

    // `𝒫y ∈ u`, from the universe's power closure.
    let (_, closed_all) = closed.concl().as_imp()?;
    let body_pow_y = syl(&closed, &Thm::ax_inst(closed_all, ty.clone())?)?;
    let n_pow_in_u = hyp_mp(&syl(&n_m, &syl(&m_body, &body_pow_y)?)?, &n_y_in_u)?;

    // `hered(𝒫y)`: under `O := N ∧ Ind(x, w)`, the successor step of `Ind(x, w)`
    // carries `y ∈ w` — which `hered(y)` gives — up to `𝒫y ∈ w`.
    let o = Formula::and(n.clone(), ind_w.clone());
    let o_n = and_left(n.clone(), ind_w.clone());
    let o_ind = and_right(n.clone(), ind_w.clone());
    let o_hered_y = syl(&o_n, &n_hered_y)?;
    let o_y_in_w = hyp_mp(
        &hyp_mp(&a1i(&Thm::ax_inst(hered.subst(q, &ty), tw.clone())?, o.clone()), &o_hered_y)?,
        &o_ind,
    )?;
    let o_ind_step = syl(&o_ind, &and_right(ind_mem_w.clone(), ind_step_w.clone()))?;
    let o_pow_in_w = hyp_mp(
        &hyp_mp(&a1i(&Thm::ax_inst(ind_step_w.clone(), ty.clone())?, o.clone()), &o_ind_step)?,
        &o_y_in_w,
    )?;
    let pow_y_in_w = Formula::mem(pow_y.clone(), tw.clone());
    let n_hered_pow = Thm::mp(
        &Thm::ax_dist(w, n.clone(), Formula::imp(ind_w.clone(), pow_y_in_w))?,
        &Thm::gen(w, &uncurry(&o_pow_in_w)?),
    )?;
    debug_assert_eq!(
        *n_hered_pow.concl(),
        Formula::imp(n.clone(), hered.subst(q, &pow_y)),
        "hered(𝒫y) was not assembled in the shape the separation condition uses"
    );

    let pow_y_in_s = Formula::mem(pow_y.clone(), ts.clone());
    let n_pow_in_s = hyp_mp(
        &syl(&n_m, &crate::hyp_iff_mpr(&m_at(&pow_y)?)?)?,
        &hyp_and(&n_pow_in_u, &n_hered_pow)?,
    )?;
    let m_all_step = Thm::mp(
        &Thm::ax_dist(y, m.clone(), Formula::imp(y_in_s, pow_y_in_s))?,
        &Thm::gen(y, &uncurry(&n_pow_in_s)?),
    )?;
    let m_ind_s = hyp_and(&m_x_in_s, &m_all_step)?;
    debug_assert_eq!(
        *m_ind_s.concl(),
        Formula::imp(m.clone(), inductive(env, pow, &tx, &ts)),
        "Ind(x, s) was not assembled in the expected shape"
    );

    // ── (iii) `∀w. (Ind(x, w) → ∀q. (q ∈ s → q ∈ w))` ────────────────────────
    let q2 = env.fresh_var();
    let tq2 = Term::var(q2);
    let q2_in_s = Formula::mem(tq2.clone(), ts.clone());
    let q2_in_w = Formula::mem(tq2.clone(), tw.clone());
    let n2 = Formula::and(m.clone(), q2_in_s.clone());
    let n2_m = and_left(m.clone(), q2_in_s.clone());
    let n2_cond = hyp_mp(
        &syl(&n2_m, &crate::hyp_iff_mp(&m_at(&tq2)?)?)?,
        &and_right(m.clone(), q2_in_s.clone()),
    )?;
    let n2_hered = syl(
        &n2_cond,
        &and_right(Formula::mem(tq2.clone(), tu.clone()), hered.subst(q, &tq2)),
    )?;
    let n2_imp =
        hyp_mp(&a1i(&Thm::ax_inst(hered.subst(q, &tq2), tw.clone())?, n2.clone()), &n2_hered)?;
    // `⊢ M → (q ∈ s → (Ind(x,w) → q ∈ w))`, swapped to `M → (Ind(x,w) → …)`.
    let m_swapped = hyp_mp(
        &a1i(&com12_imp(q2_in_s.clone(), ind_w.clone(), q2_in_w.clone()), m.clone()),
        &uncurry(&n2_imp)?,
    )?;
    let mi = Formula::and(m.clone(), ind_w.clone());
    let mi_all = Thm::mp(
        &Thm::ax_dist(q2, mi, Formula::imp(q2_in_s.clone(), q2_in_w.clone()))?,
        &Thm::gen(q2, &curry(&m_swapped)?),
    )?;
    let contained = Formula::forall(q2, Formula::imp(q2_in_s, q2_in_w));
    let m_min = Thm::mp(
        &Thm::ax_dist(w, m.clone(), Formula::imp(ind_w, contained))?,
        &Thm::gen(w, &uncurry(&mi_all)?),
    )?;

    // ── Assemble, then discharge `s` and `u` ─────────────────────────────────
    let m_least = hyp_and(&m_ind_s, &m_min)?;
    debug_assert_eq!(
        *m_least.concl(),
        Formula::imp(m, least_inductive(env, pow, &tx, &ts)),
        "Least(x, s) was not assembled in the expected shape"
    );

    let nvar = env.fresh_var();
    let goal_body = least_inductive(env, pow, &tx, &Term::var(nvar));
    let goal = Formula::exists(nvar, goal_body.clone());
    let m_goal = syl(&m_least, &exists_intro_imp(nvar, goal_body, ts)?)?;

    let body_goal_f = Formula::imp(body.clone(), goal.clone());
    let ex_bg = exists_elim_imp(s, &Thm::gen(s, &com12(&uncurry(&m_goal)?)?), &body_goal_f)?;
    let body_goal = hyp_contract(&syl(&body_ex_s, &ex_bg)?)?;

    let out = exists_elim(univ.u, &ex_u, &Thm::gen(univ.u, &body_goal), &goal)?;
    debug_assert_eq!(*out.concl(), goal, "least_inductive_set_exists produced an unexpected shape");
    Some(Thm::gen(x, &out))
}

/// `⊢ ∀x ∃u. (x ∈ u ∧ ∀y. (y ∈ u → 𝒫y ∈ u))` — **an inductive set exists**.
///
/// This is the near end of the bridge, and the point of bringing Tarski in:
/// `separation.rs` observes that closing its gap "needs a new axiom (Infinity
/// is the usual source)", and this is Infinity, derived. `x`, `𝒫x`, `𝒫𝒫x`, …
/// all lie in Tarski's universe around `x`, so the universe is inductive; see
/// [`least_inductive_set_exists`] for the `ω` inside it.
///
/// It does *not* yet give an empty set: every iterate points upwards, and
/// reaching the bottom means iterating `⋃` downwards, which needs the recursion
/// theorem. See the module documentation.
pub fn inductive_set_exists(env: &mut Env, pow: FnSym, pow_ax: &Thm) -> Option<Thm> {
    let x = env.fresh_var();
    let (univ, ex) = tarski_at(env, x)?;
    let closed = universe_power_closed(env, pow, pow_ax, &univ)?;
    let ind = hyp_and(&univ.body_mem(), &closed)?;
    let out = Thm::mp(&exists_mono(univ.u, &Thm::gen(univ.u, &ind))?, &ex)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::exists(univ.u, inductive(env, pow, &Term::var(x), &Term::var(univ.u))),
        "inductive_set_exists produced an unexpected shape"
    );
    Some(Thm::gen(x, &out))
}
