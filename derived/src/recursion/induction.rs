//! Induction over `ω`, as a scheme and as a set statement.
//!
//! # Interface
//!
//! ```text
//! ⊢ (φ(0) ∧ ∀n. ((n ∈ ω ∧ φ(n)) → φ(succ n))) → ∀n. (n ∈ ω → φ(n))     [induction_scheme]
//! ⊢ ∀S. ((0 ∈ S ∧ ∀n. ((n ∈ ω ∧ n ∈ S) → succ(n) ∈ S))
//!          → ∀n. (n ∈ ω → n ∈ S))                                      [induction_principle]
//! ```
//!
//! the first for a caller-supplied formula `φ` in a caller-supplied variable,
//! the second its instance at `φ(x) := x ∈ S`, generalised. The set form is the
//! weaker of the two — a class-sized property has no set to be instantiated at —
//! but it is the form that quantifies, so it is the one to state. Callers need
//! neither derivation.
//!
//! # Why minimality is not already the induction principle
//!
//! [`crate::recursion::OmegaCore::minimal`] says every *inductive* set contains
//! `ω`, which is not usable as an induction principle: the step of a typical
//! property only holds *for natural numbers*, so `{x : φ(x)}` is rarely
//! inductive — and rarely a set either. The fix is the standard one: run
//! minimality at `{x ∈ ω : φ(x)}`, which Separation supplies and which is
//! inductive precisely because the step carries the `n ∈ ω` conjunct along.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, exists_elim_imp, hyp_and, hyp_mp, inst_all, syl, uncurry,
};
use super::naturals::{inductive, OmegaCore};

/// `⊢ (φ(0) ∧ ∀n. ((n ∈ ω ∧ φ(n)) → φ(succ n))) → ∀n. (n ∈ ω → φ(n))` —
/// **induction over `ω`**, as a scheme in a caller-supplied `φ`.
///
/// [`OmegaCore::minimal`] already says that every *inductive* set contains `ω`,
/// but that is not usable as an induction principle: the step of a typical
/// property only holds *for natural numbers*, so `{x : φ(x)}` is rarely
/// inductive — and it is rarely a set either. The fix is the standard one: run
/// minimality at `{x ∈ ω : φ(x)}`, which Separation supplies and which is
/// inductive precisely because the step carries the `n ∈ ω` conjunct along.
///
/// `phi` may mention `x` and nothing else that this function generates; `x` is
/// the induction variable and is bound in the result.
pub fn induction_scheme(env: &mut Env, core: &OmegaCore, x: FreeVar, phi: &Formula) -> Option<Thm> {
    let (zero, w) = (core.zero(), core.set());
    let tx = Term::var(x);
    let tvar = env.fresh_var();
    let tt = Term::var(tvar);

    let phi_zero = phi.subst(x, &zero);
    let x_in_om = Formula::mem(tx.clone(), w.clone());
    let succ_x = core.succ_of(tx.clone());
    let phi_succ = phi.subst(x, &succ_x);
    let step = Formula::forall(
        x,
        Formula::imp(Formula::and(x_in_om.clone(), phi.clone()), phi_succ.clone()),
    );
    let h = Formula::and(phi_zero.clone(), step.clone());
    let goal = Formula::forall(x, Formula::imp(x_in_om.clone(), phi.clone()));

    // `T := { x ∈ ω : φ(x) }`.
    let carved = Formula::and(x_in_om.clone(), phi.clone());
    let sep = crate::funcs::separation_full(env, x, phi, &w, &core.empty_ax).ok()?;
    let p_t = Formula::forall(x, Formula::iff(Formula::mem(tx.clone(), tt.clone()), carved));
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(tvar, p_t.clone()),
        "induction_scheme: Separation has an unexpected shape"
    );

    // Work under `K := H ∧ P(T)`.
    let k = Formula::and(h.clone(), p_t.clone());
    let k_h = and_left(h.clone(), p_t.clone());
    let k_pt = and_right(h.clone(), p_t.clone());
    let k_at = |r: &Term| -> Option<Thm> { syl(&k_pt, &Thm::ax_inst(p_t.clone(), r.clone())?) };

    // ── `0 ∈ T` ──────────────────────────────────────────────────────────────
    let k_zero_om = a1i(&core.zero_mem, k.clone());
    let k_phi_zero = syl(&k_h, &and_left(phi_zero.clone(), step.clone()))?;
    let k_zero_in_t =
        hyp_mp(&crate::hyp_iff_mpr(&k_at(&zero)?)?, &hyp_and(&k_zero_om, &k_phi_zero)?)?;

    // ── `∀x. (x ∈ T → succ(x) ∈ T)` ──────────────────────────────────────────
    let x_in_t = Formula::mem(tx.clone(), tt.clone());
    let succ_x_in_t = Formula::mem(succ_x.clone(), tt.clone());
    let l = Formula::and(k.clone(), x_in_t.clone());
    let l_k = and_left(k.clone(), x_in_t.clone());
    let l_xt = and_right(k.clone(), x_in_t.clone());
    let l_cond = hyp_mp(&syl(&l_k, &crate::hyp_iff_mp(&k_at(&tx)?)?)?, &l_xt)?;
    let l_x_om = syl(&l_cond, &and_left(x_in_om.clone(), phi.clone()))?;
    let l_succ_om = hyp_mp(
        &a1i(&inst_all(&core.succ_closed, std::slice::from_ref(&tx))?, l.clone()),
        &l_x_om,
    )?;
    let l_step = syl(&l_k, &syl(&k_h, &and_right(phi_zero, step.clone()))?)?;
    let l_phi_succ = hyp_mp(&syl(&l_step, &Thm::ax_inst(step, tx.clone())?)?, &l_cond)?;
    let l_succ_in_t = hyp_mp(
        &syl(&l_k, &crate::hyp_iff_mpr(&k_at(&succ_x)?)?)?,
        &hyp_and(&l_succ_om, &l_phi_succ)?,
    )?;
    let k_all_step = Thm::mp(
        &Thm::ax_dist(x, k.clone(), Formula::imp(x_in_t, succ_x_in_t))?,
        &Thm::gen(x, &uncurry(&l_succ_in_t)?),
    )?;

    let k_ind_t = hyp_and(&k_zero_in_t, &k_all_step)?;
    debug_assert_eq!(
        *k_ind_t.concl(),
        Formula::imp(k.clone(), inductive(env, core.succ, &zero, &tt)),
        "induction_scheme: Ind(∅, T) was not assembled in the expected shape"
    );

    // ── Minimality at `T`, then read the conclusion back off `P(T)` ──────────
    let min_t = Thm::mp(&Thm::ax_inst(core.minimal.concl().clone(), tt)?, &core.minimal)?;
    let k_contained = hyp_mp(&a1i(&min_t, k.clone()), &k_ind_t)?;
    let (_, all_q) = k_contained.concl().as_imp()?;

    let m_k = and_left(k.clone(), x_in_om.clone());
    let m_xom = and_right(k.clone(), x_in_om.clone());
    let m_in_t = hyp_mp(
        &syl(&m_k, &syl(&k_contained, &Thm::ax_inst(all_q, tx.clone())?)?)?,
        &m_xom,
    )?;
    let m_cond = hyp_mp(&syl(&m_k, &crate::hyp_iff_mp(&k_at(&tx)?)?)?, &m_in_t)?;
    let m_phi = syl(&m_cond, &and_right(x_in_om.clone(), phi.clone()))?;
    let k_goal = Thm::mp(
        &Thm::ax_dist(x, k, Formula::imp(x_in_om, phi.clone()))?,
        &Thm::gen(x, &uncurry(&m_phi)?),
    )?;

    // ── Discharge the separated set ──────────────────────────────────────────
    let target = Formula::imp(h, goal);
    let ex = exists_elim_imp(tvar, &Thm::gen(tvar, &com12(&uncurry(&k_goal)?)?), &target)?;
    let out = Thm::mp(&ex, &sep)?;
    debug_assert_eq!(*out.concl(), target, "induction_scheme: unexpected shape");
    Some(out)
}

/// `⊢ ∀S. ((0 ∈ S ∧ ∀n. ((n ∈ ω ∧ n ∈ S) → succ(n) ∈ S)) → ∀n. (n ∈ ω → n ∈ S))`
/// — induction over `ω`, in its set form.
///
/// [`induction_scheme`] at `φ(x) := x ∈ S`, generalised. The set form is the
/// weaker of the two — a class-sized property has no set to be instantiated at
/// — but it is the form that quantifies, so it is the one to state.
pub fn induction_principle(env: &mut Env, core: &OmegaCore) -> Option<Thm> {
    let (s, x) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::mem(Term::var(x), Term::var(s));
    let scheme = induction_scheme(env, core, x, &phi)?;
    Some(Thm::gen(s, &scheme))
}
