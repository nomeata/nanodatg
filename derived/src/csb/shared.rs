//! Private readers and `H → …` combinators for [`crate::csb`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! Deliberately private copies rather than imports from a neighbouring module,
//! on the reasoning `crate::universe::shared` gives: reading a formula apart is
//! untrusted and safe — no `Thm` is produced by any of it, so a helper here can
//! fail to build a theorem but never build a wrong one.
//!
//! # How these fail
//!
//! Every explicit refusal below is a [`crate::err::DerErr::Assembly`], never a
//! decline. The module is private to [`crate::csb`], so the caller of everything
//! here *is* that module: a helper handed a theorem whose conclusion is not the
//! shape its parameter name claims was handed it by a `csb` derivation that
//! built the theorem, and that derivation is the bug. Nothing here has a
//! contract an outside caller can legitimately fail to meet.
//!
//! The **thin combinators** — `hyp_contract`, `hyp_gen`, `discharge`,
//! `inst_all_imp`, `hyp_exists_mono`, `hyp_contrapos` and
//! `or_left_of_not_right` — carry `#[track_caller]`. Each is called from every
//! step of `csb`'s three big derivations, so a failure sited on its own line
//! names this file, which the reader already knew; annotated, the site is the
//! line in [`super::bijection`], [`super::fixpoint`] or [`super::sandwich`] that
//! composed the call. `forall_mono_imp` and `exists_mono_imp` are **not**
//! annotated: each has a derivation of its own, and which of its steps failed is
//! exactly what a reader needs. Nor is `open_exists`, which peels four
//! connectives off one formula and whose site says which of the four.

use kernel::{Formula, FreeVar, Term, Thm};

use crate::err::{DResult, Operand};
use crate::prim::{self, Shape};
use crate::rules::{com12, exists_elim_imp, forall_mono, hyp_syl, syl, uncurry};
use crate::{assembly, contrapos_imp, imp_refl};

/// Contraction under a hypothesis: from `⊢ H → (H → φ)` infer `⊢ H → φ`.
#[track_caller]
pub(super) fn hyp_contract(t: &Thm) -> DResult<Thm> {
    let (h, rest) = t.concl().imp_parts()?;
    let (h2, phi) = rest.imp_parts()?;
    if h != h2 {
        return Err(assembly!("hyp_contract: the two antecedents differ", Operand::thm("t", t)))
    }
    let s = Thm::ax_s(h.clone(), h.clone(), phi);
    prim::mp(&prim::mp(&s, t)?, &imp_refl(h))
}

/// Generalisation under a hypothesis: from `⊢ H → φ` infer `⊢ H → ∀v. φ`.
///
/// `v` must not occur free in `H`; [`crate::prim::ax_dist`] is what enforces it,
/// and reports the offending variable and hypothesis when it does.
#[track_caller]
pub(super) fn hyp_gen(v: FreeVar, t: &Thm) -> DResult<Thm> {
    let (h, phi) = t.concl().imp_parts()?;
    prim::mp(&prim::ax_dist(v, h, phi)?, &Thm::gen(v, t))
}

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
#[track_caller]
pub(super) fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> DResult<Thm> {
    let (_, goal) = he_goal.concl().imp_parts()?;
    let (h, _) = h_ex.concl().imp_parts()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — instantiation in implication form, for a quantified
/// formula that is only available under a hypothesis.
#[track_caller]
pub(super) fn inst_all_imp(phi: &Formula, ts: &[Term]) -> DResult<Thm> {
    let first = match ts.first() {
        Some(t) => t,
        None =>
            return Err(assembly!(
                "inst_all_imp: there is nothing to instantiate at",
                Operand::formula("phi", phi),
            )),
    };
    let mut cur = prim::ax_inst(phi.clone(), first.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().imp_parts()?;
        cur = syl(&cur, &prim::ax_inst(body, t.clone())?)?;
    }
    Ok(cur)
}

/// `⊢ (∀x.(φ → ψ)) → (∀x. φ → ∀x. ψ)` — [`crate::forall_mono`] in *implication*
/// form, which is what a step under a hypothesis needs.
///
/// The body is [`crate::forall_mono`]'s, stopped one line before it discharges
/// its own antecedent.
pub(super) fn forall_mono_imp(x: FreeVar, phi: &Formula, psi: &Formula) -> DResult<Thm> {
    let a = Formula::forall(x, Formula::imp(phi.clone(), psi.clone()));
    let a_to_body = prim::ax_inst(a.clone(), Term::var(x))?;
    let b = Formula::forall(x, phi.clone());
    let b_to_phi = prim::ax_inst(b.clone(), Term::var(x))?;

    let a_to_bpsi = com12(&syl(&b_to_phi, &com12(&a_to_body)?)?)?;
    let dist1 = prim::ax_dist(x, a, Formula::imp(b.clone(), psi.clone()))?;
    let a_to_all = prim::mp(&dist1, &Thm::gen(x, &a_to_bpsi))?;
    syl(&a_to_all, &prim::ax_dist(x, b, psi.clone())?)
}

/// `⊢ (∀x.(φ → ψ)) → (∃x. φ → ∃x. ψ)` — [`crate::exists_mono`] in *implication*
/// form.
pub(super) fn exists_mono_imp(x: FreeVar, phi: &Formula, psi: &Formula) -> DResult<Thm> {
    let contra_all = forall_mono(x, &Thm::gen(x, &contrapos_imp(phi.clone(), psi.clone())))?;
    let (np, nq) = (Formula::not(psi.clone()), Formula::not(phi.clone()));
    let chain = syl(&contra_all, &forall_mono_imp(x, &np, &nq)?)?;
    syl(&chain, &contrapos_imp(Formula::forall(x, np), Formula::forall(x, nq)))
}

/// From `⊢ H → (φ → ψ)` with `x` not free in `H`, infer
/// `⊢ H → (∃x. φ → ∃x. ψ)`.
#[track_caller]
pub(super) fn hyp_exists_mono(x: FreeVar, t: &Thm) -> DResult<Thm> {
    let (_, imp) = t.concl().imp_parts()?;
    let (phi, psi) = imp.imp_parts()?;
    syl(&hyp_gen(x, t)?, &exists_mono_imp(x, &phi, &psi)?)
}

/// From `⊢ H → (φ → ψ)` infer `⊢ H → (¬ψ → ¬φ)`.
#[track_caller]
pub(super) fn hyp_contrapos(t: &Thm) -> DResult<Thm> {
    let (_, imp) = t.concl().imp_parts()?;
    let (phi, psi) = imp.imp_parts()?;
    syl(t, &contrapos_imp(phi, psi))
}

/// From `⊢ H → (l ∨ r)` and `⊢ H → ¬r` infer `⊢ H → l`.
///
/// `l ∨ r` is `¬l → r`, so refuting `r` makes `¬l` absurd.
#[track_caller]
pub(super) fn or_left_of_not_right(h_disj: &Thm, h_notr: &Thm) -> DResult<Thm> {
    let (_, disj) = h_disj.concl().imp_parts()?;
    let (nl, _) = disj.imp_parts()?;
    let (l, _) = nl.imp_parts()?;
    // `¬l → r` chained with `r → ⊥` is `¬l → ⊥`, i.e. `¬¬l`.
    let nn = hyp_syl(h_disj, h_notr)?;
    syl(&nn, &crate::notnot_elim(l))
}

/// Instantiate the body of `∃v. φ` at `t`. `∃` is `¬∀¬`.
pub(super) fn open_exists(phi: &Formula, t: &Term) -> DResult<Formula> {
    let (all_not, fls) = phi.imp_parts()?;
    if fls != Formula::false_() {
        return Err(assembly!(
            "open_exists: the existential is not a negated universal",
            Operand::formula("phi", phi),
        ))
    }
    let (_, body) = prim::ax_inst(all_not, t.clone())?.concl().imp_parts()?;
    let (inner, fls2) = body.imp_parts()?;
    if fls2 != Formula::false_() {
        return Err(assembly!(
            "open_exists: the opened body is not a negation",
            Operand::formula("phi", phi),
            Operand::term("t", t),
        ))
    }
    Ok(inner)
}
