//! `ω`, the least inductive set: existence, the symbol, and the bundle.
//!
//! # Interface
//!
//! With `0 := ∅` and the two predicates
//!
//! ```text
//! Ind(z, w)     :=  z ∈ w ∧ ∀y. (y ∈ w → succ(y) ∈ w)                [inductive]
//! Least(z, m)   :=  Ind(z, m) ∧ ∀w. (Ind(z, w) → ∀q. (q ∈ m → q ∈ w))  [least_inductive]
//! ```
//!
//! the exports are
//!
//! ```text
//! ⊢ ∃m. Least(∅, m)      [omega_exists]
//! ⊢ Least(∅, ω)          [omega — introduces the symbol `ω`]
//! ```
//!
//! and [`OmegaCore`] packages `ω` with every symbol and theorem downstream
//! consumes. **Nothing here is an axiom**: `Thm::ax_tarski` supplies the
//! ambient universe, Replacement supplies Separation, `crate::empty::empty` supplies
//! `0`, and `ω` itself is one definitional extension whose uniqueness obligation
//! is discharged by Extensionality. Callers need none of the derivations below;
//! [`OmegaCore::with_sets`] is the entry point.
//!
//! # How `ω` is carved out
//!
//! Tarski's universe `u` around `∅` is the set the construction cuts inside,
//! and the cut is
//!
//! ```text
//! s := { q ∈ u : Trans(q) ∧ ∀w. (Ind(∅, w) → q ∈ w) }
//! ```
//!
//! by [`crate::separation::separation_nonvacuous`] — legitimate, and needing no
//! empty set of its own, because `∅` itself satisfies the condition. The
//! transitivity conjunct is what makes `s` closed under `succ`, by
//! [`crate::recursion::succ_subset_pow`] and [`crate::recursion::trans_succ`];
//! see [`crate::recursion::succ`] for why that detour is necessary. `Trans` is
//! scaffolding for the existence proof only — it does not appear in the
//! conclusion, and `⊢ ∀n ∈ ω. Trans(n)` is re-derived afterwards from the
//! induction principle ([`crate::recursion::omega_trans`]).
//!
//! # One chain of extensions
//!
//! Building [`OmegaCore`] twice would mint two unrelated pairings, two
//! unrelated successors and two unrelated `ω`s, and a theorem about one would
//! say nothing about the other — the same hazard [`crate::funcs::Apply`] exists
//! to avoid, and the reason [`OmegaCore::with_sets`] takes a caller-supplied
//! [`crate::funcs::Sets`].

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::{
    a1i, and_intro, and_left, and_right, com12, exists_elim_imp, hyp_and, hyp_mp, imp_mono_r,
    imp_refl, inst_all, syl, uncurry,
};
use super::succ::{succ_subset_pow, successor, trans_empty, trans_succ};

/// `Ind(z, w) := z ∈ w ∧ ∀y. (y ∈ w → succ(y) ∈ w)` — `w` is *inductive*: it
/// contains the base point and is closed under the successor.
pub fn inductive(env: &mut Env, succ: FnSym, zero: &Term, w: &Term) -> Formula {
    let y = env.fresh_var();
    let ty = Term::var(y);
    Formula::and(
        Formula::mem(zero.clone(), w.clone()),
        Formula::forall(
            y,
            Formula::imp(
                Formula::mem(ty.clone(), w.clone()),
                Formula::mem(Term::apply(succ, vec![ty]), w.clone()),
            ),
        ),
    )
}

/// `Least(z, m) := Ind(z, m) ∧ ∀w. (Ind(z, w) → ∀q. (q ∈ m → q ∈ w))` — `m` is
/// inductive and contained in every inductive set.
pub fn least_inductive(env: &mut Env, succ: FnSym, zero: &Term, m: &Term) -> Formula {
    let (w, q) = (env.fresh_var(), env.fresh_var());
    let (tw, tq) = (Term::var(w), Term::var(q));
    let contained = Formula::forall(
        q,
        Formula::imp(Formula::mem(tq.clone(), m.clone()), Formula::mem(tq, tw.clone())),
    );
    Formula::and(
        inductive(env, succ, zero, m),
        Formula::forall(w, Formula::imp(inductive(env, succ, zero, &tw), contained)),
    )
}

/// `⊢ ∃m. Least(∅, m)` — **the least inductive set exists**, i.e. `ω` exists
/// and induction over it is available.
///
/// Tarski's universe `u` around `∅` is the set the construction cuts inside,
/// and the cut is
///
/// ```text
/// s := { q ∈ u : Trans(q) ∧ ∀w. (Ind(∅, w) → q ∈ w) }
/// ```
///
/// by [`crate::separation::separation_nonvacuous`] — legitimate, and needing no
/// empty set of its own, because `∅` itself satisfies the condition. The
/// transitivity conjunct is what makes `s` closed under `succ`: `u` is *not*
/// closed under `n ↦ n ∪ {n}` in general (see the module documentation), but at
/// a transitive `n` we have `succ(n) ⊆ 𝒫n` ([`succ_subset_pow`]) and `𝒫n ∈ u`
/// ([`crate::empty::universe_power_closed`]), so Tarski's second clause puts
/// `succ(n)` back into `u`. Transitivity propagates along the way by
/// [`trans_succ`], so the conjunct survives the induction step, and it does not
/// appear in the conclusion — `Trans` is scaffolding for the existence proof
/// only, and `⊢ ∀n ∈ ω. Trans(n)` is re-derived afterwards from the induction
/// principle ([`crate::recursion::omega_trans`]).
pub fn omega_exists(
    env: &mut Env,
    pow: FnSym,
    pow_ax: &Thm,
    succ: FnSym,
    succ_ax: &Thm,
    empty_ax: &Thm,
) -> Option<Thm> {
    // Read `∅` off the theorem, insisting it says exactly what it must.
    let probe = env.fresh_var();
    let (mem_probe, fls) = inst_all(empty_ax, &[Term::var(probe)])?.concl().as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (lhs, zero) = mem_probe.as_mem()?;
    if lhs != Term::var(probe) || zero.occurs_free(probe) {
        return None
    }

    let ssp = succ_subset_pow(env, pow, pow_ax, succ, succ_ax)?;
    let tsucc = trans_succ(env, succ, succ_ax)?;

    // ── Tarski's universe around `∅` ─────────────────────────────────────────
    // Decomposed by `tarski_at_term`, never by hand: this call site used to
    // duplicate that destructuring and silently went stale when the axiom gained
    // its transitivity clause.
    let (univ, ex_u) = crate::empty::tarski_at_term(env, &zero)?;
    let uvar = univ.u;
    let tu = Term::var(uvar);
    let body = univ.body.clone();
    let closed = crate::empty::universe_power_closed(env, pow, pow_ax, &univ)?;

    // ── The separation condition ─────────────────────────────────────────────
    let (q, w) = (env.fresh_var(), env.fresh_var());
    let (tq, tw) = (Term::var(q), Term::var(w));
    let ind_w = inductive(env, succ, &zero, &tw);
    let (ind_mem_w, ind_step_w) = crate::empty::split_and(&ind_w)?;
    let hered = Formula::forall(w, Formula::imp(ind_w.clone(), Formula::mem(tq.clone(), tw.clone())));
    let trans_q = crate::empty::transitive(env, &tq);
    let cond = Formula::and(trans_q.clone(), hered.clone());

    let trans_zero = trans_empty(env, empty_ax)?;

    // `⊢ hered(∅)`: every inductive set contains the base point outright.
    let hered_zero = Thm::gen(w, &and_left(ind_mem_w.clone(), ind_step_w.clone()));
    debug_assert_eq!(*hered_zero.concl(), hered.subst(q, &zero));
    let cond_zero = and_intro(&trans_zero, &hered_zero);
    debug_assert_eq!(*cond_zero.concl(), cond.subst(q, &zero));

    // ── Separation at `u`, non-vacuously ─────────────────────────────────────
    let sep = crate::separation::separation_nonvacuous(env, q, &cond)?;
    let at_u = inst_all(&sep, std::slice::from_ref(&tu))?;
    let (ante, ex_s) = at_u.concl().as_imp()?;
    let v = env.fresh_var();
    let ante_body = crate::empty::open_exists(&ante, &Term::var(v))?;
    debug_assert_eq!(
        ante_body,
        Formula::and(Formula::mem(Term::var(v), tu.clone()), cond.subst(q, &Term::var(v))),
        "the non-vacuity premise is not the expected one"
    );
    let body_witness = hyp_and(&univ.body_mem(), &a1i(&cond_zero, body.clone()))?;
    let body_ex_s =
        syl(&syl(&body_witness, &crate::exists_intro_imp(v, ante_body, zero.clone())?)?, &at_u)?;

    // ── The separated set `s`, and its membership condition ──────────────────
    let (s, y) = (env.fresh_var(), env.fresh_var());
    let (ts, ty) = (Term::var(s), Term::var(y));
    let sep_at = |r: &Term| Formula::and(Formula::mem(r.clone(), tu.clone()), cond.subst(q, r));
    let p_s = Formula::forall(y, Formula::iff(Formula::mem(ty.clone(), ts.clone()), sep_at(&ty)));
    debug_assert_eq!(ex_s, Formula::exists(s, p_s.clone()), "the separated set is not as expected");

    let m = Formula::and(body.clone(), p_s.clone());
    let m_body = and_left(body.clone(), p_s.clone());
    let m_ps = and_right(body.clone(), p_s.clone());
    let m_at = |r: &Term| -> Option<Thm> { syl(&m_ps, &Thm::ax_inst(p_s.clone(), r.clone())?) };

    // ── (i) `∅ ∈ s` ──────────────────────────────────────────────────────────
    let m_zero_cond = hyp_and(&syl(&m_body, &univ.body_mem())?, &a1i(&cond_zero, m.clone()))?;
    let m_zero_in_s = hyp_mp(&crate::hyp_iff_mpr(&m_at(&zero)?)?, &m_zero_cond)?;

    // ── (ii) `∀y. (y ∈ s → succ(y) ∈ s)` ─────────────────────────────────────
    let succ_y = Term::apply(succ, vec![ty.clone()]);
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let y_in_s = Formula::mem(ty.clone(), ts.clone());
    let n = Formula::and(m.clone(), y_in_s.clone());
    let n_m = and_left(m.clone(), y_in_s.clone());
    let n_cond = hyp_mp(
        &syl(&n_m, &crate::hyp_iff_mp(&m_at(&ty)?)?)?,
        &and_right(m.clone(), y_in_s.clone()),
    )?;
    let n_y_in_u = syl(&n_cond, &and_left(y_in_u.clone(), cond.subst(q, &ty)))?;
    let n_cond_y = syl(&n_cond, &and_right(y_in_u.clone(), cond.subst(q, &ty)))?;
    let n_trans_y = syl(&n_cond_y, &and_left(trans_q.subst(q, &ty), hered.subst(q, &ty)))?;
    let n_hered_y = syl(&n_cond_y, &and_right(trans_q.subst(q, &ty), hered.subst(q, &ty)))?;

    // `succ(y) ∈ u`: `𝒫y ∈ u`, and `succ(y) ⊆ 𝒫y` because `y` is transitive.
    let (_, closed_all) = closed.concl().as_imp()?;
    let body_pow_y = syl(&closed, &Thm::ax_inst(closed_all, ty.clone())?)?;
    let n_pow_in_u = hyp_mp(&syl(&n_m, &syl(&m_body, &body_pow_y)?)?, &n_y_in_u)?;
    let n_sub = hyp_mp(&a1i(&inst_all(&ssp, std::slice::from_ref(&ty))?, n.clone()), &n_trans_y)?;

    let c2_p = Thm::ax_inst(univ.closed_sub.clone(), pow_y.clone())?;
    let (_, c2_p_body) = c2_p.concl().as_imp()?;
    let (_, all_sub_u) = c2_p_body.as_imp()?;
    let c2_s = syl(
        &c2_p,
        &imp_mono_r(
            &Thm::ax_inst(all_sub_u, succ_y.clone())?,
            Formula::mem(pow_y.clone(), tu.clone()),
        )?,
    )?;
    let n_c2 = syl(&n_m, &syl(&m_body, &univ.body_closed_sub())?)?;
    let n_succ_in_u = hyp_mp(&hyp_mp(&syl(&n_c2, &c2_s)?, &n_pow_in_u)?, &n_sub)?;

    // `Trans(succ y)`, and `hered(succ y)`.
    let n_trans_succ =
        hyp_mp(&a1i(&inst_all(&tsucc, std::slice::from_ref(&ty))?, n.clone()), &n_trans_y)?;

    let o = Formula::and(n.clone(), ind_w.clone());
    let o_n = and_left(n.clone(), ind_w.clone());
    let o_ind = and_right(n.clone(), ind_w.clone());
    let o_hered_y = syl(&o_n, &n_hered_y)?;
    let o_y_in_w = hyp_mp(
        &hyp_mp(&a1i(&Thm::ax_inst(hered.subst(q, &ty), tw.clone())?, o.clone()), &o_hered_y)?,
        &o_ind,
    )?;
    let o_ind_step = syl(&o_ind, &and_right(ind_mem_w.clone(), ind_step_w.clone()))?;
    let o_succ_in_w = hyp_mp(
        &hyp_mp(&a1i(&Thm::ax_inst(ind_step_w.clone(), ty.clone())?, o.clone()), &o_ind_step)?,
        &o_y_in_w,
    )?;
    let succ_y_in_w = Formula::mem(succ_y.clone(), tw.clone());
    let n_hered_succ = Thm::mp(
        &Thm::ax_dist(w, n.clone(), Formula::imp(ind_w.clone(), succ_y_in_w))?,
        &Thm::gen(w, &uncurry(&o_succ_in_w)?),
    )?;
    let n_cond_succ = hyp_and(&n_trans_succ, &n_hered_succ)?;
    debug_assert_eq!(
        *n_cond_succ.concl(),
        Formula::imp(n.clone(), cond.subst(q, &succ_y)),
        "cond(succ y) was not assembled in the shape the separation condition uses"
    );

    let succ_y_in_s = Formula::mem(succ_y.clone(), ts.clone());
    let n_succ_in_s = hyp_mp(
        &syl(&n_m, &crate::hyp_iff_mpr(&m_at(&succ_y)?)?)?,
        &hyp_and(&n_succ_in_u, &n_cond_succ)?,
    )?;
    let m_all_step = Thm::mp(
        &Thm::ax_dist(y, m.clone(), Formula::imp(y_in_s, succ_y_in_s))?,
        &Thm::gen(y, &uncurry(&n_succ_in_s)?),
    )?;
    let m_ind_s = hyp_and(&m_zero_in_s, &m_all_step)?;
    debug_assert_eq!(
        *m_ind_s.concl(),
        Formula::imp(m.clone(), inductive(env, succ, &zero, &ts)),
        "Ind(∅, s) was not assembled in the expected shape"
    );

    // ── (iii) `∀w. (Ind(∅,w) → ∀q. (q ∈ s → q ∈ w))` ─────────────────────────
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
    let n2_c = syl(
        &n2_cond,
        &and_right(Formula::mem(tq2.clone(), tu.clone()), cond.subst(q, &tq2)),
    )?;
    let n2_hered = syl(&n2_c, &and_right(trans_q.subst(q, &tq2), hered.subst(q, &tq2)))?;
    let n2_imp =
        hyp_mp(&a1i(&Thm::ax_inst(hered.subst(q, &tq2), tw.clone())?, n2.clone()), &n2_hered)?;
    let m_swapped = hyp_mp(
        &a1i(&crate::com12_imp(q2_in_s.clone(), ind_w.clone(), q2_in_w.clone()), m.clone()),
        &uncurry(&n2_imp)?,
    )?;
    let mi = Formula::and(m.clone(), ind_w.clone());
    let mi_all = Thm::mp(
        &Thm::ax_dist(q2, mi, Formula::imp(q2_in_s.clone(), q2_in_w.clone()))?,
        &Thm::gen(q2, &crate::empty::curry(&m_swapped)?),
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
        Formula::imp(m, least_inductive(env, succ, &zero, &ts)),
        "Least(∅, s) was not assembled in the expected shape"
    );

    let mvar = env.fresh_var();
    let goal_body = least_inductive(env, succ, &zero, &Term::var(mvar));
    let goal = Formula::exists(mvar, goal_body.clone());
    let m_goal = syl(&m_least, &crate::exists_intro_imp(mvar, goal_body, ts)?)?;

    let body_goal_f = Formula::imp(body.clone(), goal.clone());
    let ex_bg = exists_elim_imp(s, &Thm::gen(s, &com12(&uncurry(&m_goal)?)?), &body_goal_f)?;
    let body_goal = crate::empty::hyp_contract(&syl(&body_ex_s, &ex_bg)?)?;

    let out = crate::exists_elim(univ.u, &ex_u, &Thm::gen(univ.u, &body_goal), &goal)?;
    debug_assert_eq!(*out.concl(), goal, "omega_exists produced an unexpected shape");
    Some(out)
}

/// The symbol `ω`, with `⊢ Least(∅, ω)`.
///
/// Existence is [`omega_exists`]. Uniqueness — which is what makes the
/// definitional extension conservative, and is therefore not optional
/// bookkeeping but the very thing that licenses the symbol — is the standard
/// mutual-containment argument: two least inductive sets each contain the
/// other, because each is inductive and the other is minimal, so
/// Extensionality identifies them.
pub fn omega(
    env: &mut Env,
    pow: FnSym,
    pow_ax: &Thm,
    succ: FnSym,
    succ_ax: &Thm,
    empty_ax: &Thm,
) -> Option<(FnSym, Thm)> {
    let existence = omega_exists(env, pow, pow_ax, succ, succ_ax, empty_ax)?;
    let ext = Thm::ax_extensionality(env);

    let probe = env.fresh_var();
    let (mem_probe, fls) = inst_all(empty_ax, &[Term::var(probe)])?.concl().as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (lhs, zero) = mem_probe.as_mem()?;
    if lhs != Term::var(probe) || zero.occurs_free(probe) {
        return None
    }

    let (m, m2, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, tm2, tz) = (Term::var(m), Term::var(m2), Term::var(z));
    let least_m = least_inductive(env, succ, &zero, &tm);
    let least_m2 = least_inductive(env, succ, &zero, &tm2);
    debug_assert_eq!(
        *existence.concl(),
        Formula::exists(m, least_m.clone()),
        "omega: the existence theorem has an unexpected shape"
    );

    let (ind_m, min_m) = crate::empty::split_and(&least_m)?;
    let (ind_m2, min_m2) = crate::empty::split_and(&least_m2)?;

    // Under `H := Least(m) ∧ Least(m₂)`, each set is inductive and each is
    // minimal, so each contains the other.
    let h = Formula::and(least_m.clone(), least_m2.clone());
    let h_lm = and_left(least_m.clone(), least_m2.clone());
    let h_lm2 = and_right(least_m.clone(), least_m2.clone());
    let h_ind_m = syl(&h_lm, &and_left(ind_m.clone(), min_m.clone()))?;
    let h_min_m = syl(&h_lm, &and_right(ind_m, min_m.clone()))?;
    let h_ind_m2 = syl(&h_lm2, &and_left(ind_m2.clone(), min_m2.clone()))?;
    let h_min_m2 = syl(&h_lm2, &and_right(ind_m2, min_m2.clone()))?;

    let h_sub21 = hyp_mp(&syl(&h_min_m2, &Thm::ax_inst(min_m2, tm.clone())?)?, &h_ind_m)?;
    let h_sub12 = hyp_mp(&syl(&h_min_m, &Thm::ax_inst(min_m, tm2.clone())?)?, &h_ind_m2)?;
    let (_, all21) = h_sub21.concl().as_imp()?;
    let (_, all12) = h_sub12.concl().as_imp()?;
    let h21 = syl(&h_sub21, &Thm::ax_inst(all21, tz.clone())?)?;
    let h12 = syl(&h_sub12, &Thm::ax_inst(all12, tz.clone())?)?;

    let same = Formula::iff(Formula::mem(tz.clone(), tm2.clone()), Formula::mem(tz, tm.clone()));
    let h_all = Thm::mp(&Thm::ax_dist(z, h, same)?, &Thm::gen(z, &hyp_and(&h21, &h12)?))?;
    let h_eq = syl(&h_all, &inst_all(&ext, &[tm2.clone(), tm.clone()])?)?;

    let dist = Thm::ax_dist(m2, least_m.clone(), Formula::imp(least_m2, Formula::eq(tm2, tm)))?;
    let m_uniq = Thm::mp(&dist, &Thm::gen(m2, &uncurry(&h_eq)?))?;
    let step = hyp_and(&imp_refl(least_m.clone()), &m_uniq)?;
    let ex_uniq = Thm::mp(&crate::exists_mono(m, &Thm::gen(m, &step))?, &existence)?;
    kernel::thm::define(env, &[], m, least_m, &ex_uniq)
}

// ─────────────────────────────────────────────────────────────────────────────
// `ω` packaged: the symbols, and the theorems everything downstream consumes.
// ─────────────────────────────────────────────────────────────────────────────

/// The natural numbers as a definitional extension: every symbol below comes
/// from **one** chain of extensions, so the terms compose.
///
/// Building this twice would mint two unrelated pairings, two unrelated
/// successors and two unrelated `ω`s, and a theorem about one would say nothing
/// about the other — the same hazard [`crate::funcs::Apply::with_sets`] exists
/// to avoid, and the reason [`OmegaCore::with_sets`] takes a caller-supplied
/// [`Sets`].
#[derive(Clone)]
pub struct OmegaCore {
    /// Pairing and union.
    pub sets: Sets,
    /// `⊢ ∀a ∀z. (z ∈ {a} ↔ z = a)`.
    pub mem_sing: Thm,
    /// The power set.
    pub pow: FnSym,
    /// `⊢ ∀x ∀z. (z ∈ 𝒫x ↔ z ⊆ x)`.
    pub pow_ax: Thm,
    /// `∅`, the zero.
    pub empty: FnSym,
    /// `⊢ ∀z. ¬(z ∈ ∅)`.
    pub empty_ax: Thm,
    /// `succ(n) = n ∪ {n}`.
    pub succ: FnSym,
    /// `⊢ ∀n ∀z. (z ∈ succ(n) ↔ (z ∈ n ∨ z = n))`.
    pub succ_ax: Thm,
    /// `ω`, the least inductive set.
    pub omega: FnSym,
    /// `⊢ Least(∅, ω)`.
    pub least: Thm,
    /// `⊢ 0 ∈ ω`.
    pub zero_mem: Thm,
    /// `⊢ ∀n. (n ∈ ω → succ(n) ∈ ω)`.
    pub succ_closed: Thm,
    /// `⊢ ∀w. (Ind(∅, w) → ∀q. (q ∈ ω → q ∈ w))` — minimality, i.e. induction
    /// in its raw form.
    pub minimal: Thm,
}

impl OmegaCore {
    /// Introduce every symbol and derive every theorem, over a **caller
    /// supplied** [`Sets`] so the pairing can be shared.
    pub fn with_sets(env: &mut Env, sets: Sets) -> Option<OmegaCore> {
        let mem_sing = crate::mem_singleton(env, sets.up, &sets.up_ax)?;
        let (empty, empty_ax) = crate::empty::empty(env);
        OmegaCore::with_parts(env, sets, mem_sing, empty, empty_ax)
    }

    /// The same, over a caller-supplied pairing **and** a caller-supplied empty
    /// set.
    ///
    /// The recursion theorem talks about `app(f, 0)`, so the `0` in `ω` and the
    /// `∅` that [`crate::funcs::Apply`] uses off the domain have to be *the same
    /// symbol*. [`OmegaCore::with_sets`] mints its own, which is right when `ω`
    /// stands alone and wrong the moment application enters the picture — see
    /// [`crate::recursion::Rec::new`], which is the caller this exists for.
    ///
    /// `empty_ax` must be a proof `⊢ ∀z. ¬(z ∈ e)` for the term `e` that
    /// `empty` builds; [`omega`] re-reads it off the theorem and refuses
    /// otherwise, so a mismatched pair cannot slip through.
    pub fn with_parts(
        env: &mut Env,
        sets: Sets,
        mem_sing: Thm,
        empty: FnSym,
        empty_ax: Thm,
    ) -> Option<OmegaCore> {
        let (pow, pow_ax) = crate::power(env);
        let (succ, succ_ax) = successor(env, &sets, &mem_sing)?;
        let (omega, least) = omega(env, pow, &pow_ax, succ, &succ_ax, &empty_ax)?;

        let ind = crate::and_elim_left(&least)?;
        let zero_mem = crate::and_elim_left(&ind)?;
        let succ_closed = crate::and_elim_right(&ind)?;
        let minimal = crate::and_elim_right(&least)?;

        Some(OmegaCore {
            sets,
            mem_sing,
            pow,
            pow_ax,
            empty,
            empty_ax,
            succ,
            succ_ax,
            omega,
            least,
            zero_mem,
            succ_closed,
            minimal,
        })
    }

    /// The same, minting a fresh [`Sets`].
    pub fn new(env: &mut Env) -> Option<OmegaCore> {
        let sets = Sets::new(env);
        OmegaCore::with_sets(env, sets)
    }

    /// The term `0`, i.e. `∅`.
    pub fn zero(&self) -> Term { Term::apply(self.empty, vec![]) }

    /// The term `ω`.
    pub fn set(&self) -> Term { Term::apply(self.omega, vec![]) }

    /// The term `succ(t)`.
    pub fn succ_of(&self, t: Term) -> Term { Term::apply(self.succ, vec![t]) }

    /// `Ind(∅, w)` for a caller-supplied `w`.
    pub fn ind_of(&self, env: &mut Env, w: &Term) -> Formula {
        inductive(env, self.succ, &self.zero(), w)
    }
}
