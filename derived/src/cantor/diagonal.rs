//! Cantor's theorem, as a scheme.
//!
//! # Interface
//!
//! ```text
//! ⊢ ¬(DOM(R,I) ∧ (SV(R) ∧ ONTO⊆(R,I)))                  [no_diagonal_surjection]
//! ⊢ ∀I ∀k. ¬(DOM ∧ (SV ∧ ONTO⊆))                    [no_surjection_onto_subsets]
//!                                    at R(x,b) := ⟨x,b⟩ ∈ k
//! ```
//!
//! The first is a **scheme**: `R` is an arbitrary two-variable formula of the
//! ambient language, so there is one theorem per `R`, built on demand. The
//! second is the closed instance at a set relation, which is what a caller
//! holding an actual function has. Callers need none of the derivation below.
//!
//! # Why the surjective form
//!
//! The usual Cantor statement is about injections `𝒫I ↪ I`, and getting from
//! "injection both ways" to "equinumerous" is Cantor–Schröder–Bernstein
//! ([`crate::csb`], which did not exist when this was written). The
//! surjective form needs none of that: the diagonal set is built directly from
//! the relation and the contradiction is one biconditional. It is also strictly
//! more useful here, because the objects `C₄` produces are surjections **onto**
//! `u`, not injections into it.
//!
//! # The diagonal, and where each clause is spent
//!
//! `D := { x ∈ I : ∀b. (R(x,b) → ¬(x ∈ b)) }`, one
//! [`crate::funcs::separation_full`]. `D ⊆ I`, so some `j` has `R(j,D)`, and
//! `j ∈ I`. Then `j ∈ D` unfolds to `j ∈ I ∧ φ(j)`, and `φ(j)` is equivalent to
//! `¬(j ∈ D)`: forwards by instantiating `φ(j)` at `D` itself, backwards because
//! single-valuedness makes `D` the *only* `b` with `R(j,b)`. So
//! `j ∈ D ↔ ¬(j ∈ D)`.
//!
//! `DOM` supplies `j ∈ I` — without it `j ∈ D` would not follow from `φ(j)`;
//! `ONTO⊆` supplies `j`; `SV` supplies the backward direction. Dropping any one
//! of the three makes the statement false.
//!
//! # How this fails
//!
//! [`no_diagonal_surjection`] **declines** on exactly two conditions, both about
//! the variables it is handed or draws: the two distinguished variables of `R`
//! must be distinct and invisible to the index set, and the four working
//! variables the environment issues must be fresh for `R` and for the index set.
//! Every other refusal below is a [`crate::err::DerErr::Assembly`] raised by
//! [`crate::prim`] — this is one long derivation, and a kernel primitive
//! rejecting a step of it is a bug in the step above.
//!
//! Neither entry carries `#[track_caller]`. Each is a construction with a
//! derivation of its own, and which internal step failed is exactly what a
//! reader needs; the sites inside this file are the diagnosis.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::err::{imported, DResult};
use crate::funcs::separation_full;
use crate::prim::{self, Shape};
use crate::rules::{
    com12, exists_elim_imp, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_syl, syl, uncurry,
};
use crate::{a1i, and_left, and_right, decline, gen_all};

use super::shared::{discharge, inst_all_imp, open_exists};
use super::clauses::{r_dom, r_onto_subsets, r_sv};

/// `⊢ ¬(DOM ∧ (SV ∧ ONTO))` for the relation `R(x,b)` at the index set `i`.
///
/// The scheme; see the module documentation for the argument. `xv` and `bv` are
/// `R`'s two distinguished free variables, and `i` must mention neither.
/// `empty` must be a proof `⊢ ∀z. ¬(z ∈ e)`; it is consumed by the Separation
/// that builds the diagonal and does not appear in the conclusion.
///
/// The conclusion is *not* generalised over anything — `R` may have arbitrary
/// further parameters, and it is the caller's business what to do with them.
pub fn no_diagonal_surjection(
    env: &mut Env,
    empty: &Thm,
    i: &Term,
    xv: FreeVar,
    bv: FreeVar,
    r: &Formula,
) -> DResult<Thm> {
    if xv == bv || i.occurs_free(xv) || i.occurs_free(bv) {
        return Err(decline!(
            "the two distinguished variables coincide, or the index set mentions one of them"
        ))
    }
    let (tx, tb) = (Term::var(xv), Term::var(bv));

    // The four working variables. Each must be invisible to `R` and to `i`, or
    // the substitutions below would capture.
    let (dv, jv, cv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    for v in [dv, jv, cv, wv] {
        if r.occurs_free(v) || i.occurs_free(v) || v == xv || v == bv {
            return Err(decline!(
                "a working variable drawn fresh from the environment already occurs in R or the index set"
            ))
        }
    }
    let (td, tj, tc) = (Term::var(dv), Term::var(jv), Term::var(cv));

    let dom = r_dom(r, xv, bv, i);
    let sv = r_sv(r, xv, bv, cv)?;
    let onto = r_onto_subsets(env, r, xv, bv, i);
    let tail = Formula::and(sv.clone(), onto.clone());
    let h = Formula::and(dom.clone(), tail.clone());
    let h_dom = and_left(dom.clone(), tail.clone());
    let h_tail = and_right(dom.clone(), tail);
    let h_sv = syl(&h_tail, &and_left(sv.clone(), onto.clone()))?;
    let h_onto = syl(&h_tail, &and_right(sv.clone(), onto.clone()))?;

    // ── The diagonal condition `φ(x) := ∀b. (R(x,b) → ¬(x ∈ b))` ─────────────
    let phi = Formula::forall(
        bv,
        Formula::imp(r.clone(), Formula::not(Formula::mem(tx.clone(), tb.clone()))),
    );

    // ── `D := { x ∈ I : φ(x) }` ──────────────────────────────────────────────
    let sep = imported(
        "crate::funcs::separation_full",
        separation_full(env, xv, &phi, i, empty),
    )?;
    let carved = Formula::and(Formula::mem(tx.clone(), i.clone()), phi.clone());
    let q = Formula::forall(xv, Formula::iff(Formula::mem(tx.clone(), td.clone()), carved.clone()));
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(dv, q.clone()),
        "separation_full did not produce the diagonal's characteristic property"
    );

    // `G := H ∧ Q(D)`, the working hypothesis.
    let g = Formula::and(h.clone(), q.clone());
    let g_h = and_left(h.clone(), q.clone());
    let g_q = and_right(h.clone(), q.clone());

    // ── `G → D ⊆ I` ──────────────────────────────────────────────────────────
    let g_iff_x = syl(&g_q, &prim::ax_inst(q.clone(), tx.clone())?)?;
    let g_x_in_i = hyp_syl(
        &hyp_iff_mp(&g_iff_x)?,
        &a1i(&and_left(Formula::mem(tx.clone(), i.clone()), phi.clone()), g.clone()),
    )?;
    let g_sub = prim::mp(
        &prim::ax_dist(
            xv,
            g.clone(),
            Formula::imp(
                Formula::mem(tx.clone(), td.clone()),
                Formula::mem(tx.clone(), i.clone()),
            ),
        )?,
        &Thm::gen(xv, &g_x_in_i),
    )?;
    debug_assert_eq!(
        *g_sub.concl(),
        Formula::imp(g.clone(), kernel::thm::subset(env, td.clone(), i.clone())),
        "the diagonal's inclusion is not the subset formula ONTO expects"
    );

    // ── `G → ∃j. R(j,D)` ─────────────────────────────────────────────────────
    let onto_at_d = prim::ax_inst(onto.clone(), td.clone())?;
    let g_ex = hyp_mp(&syl(&syl(&g_h, &h_onto)?, &onto_at_d)?, &g_sub)?;
    let (_, ex_j) = g_ex.concl().imp_parts()?;
    let pj = open_exists(&ex_j, &tj)?;
    debug_assert_eq!(ex_j, Formula::exists(jv, pj.clone()), "ONTO's ∃x did not reopen");
    debug_assert_eq!(
        pj,
        r.subst(xv, &tj).subst(bv, &td),
        "ONTO's body is not R at the reopened variables"
    );

    // ── Under `G2 := G ∧ R(j,D)` ─────────────────────────────────────────────
    let g2 = Formula::and(g.clone(), pj.clone());
    let g2_g = and_left(g.clone(), pj.clone());
    let g2_p = and_right(g.clone(), pj.clone());

    // `j ∈ I`, from DOM. Without this the diagonal's `x ∈ I` conjunct blocks the
    // backward direction below.
    let dom_at = inst_all_imp(&dom, &[tj.clone(), td.clone()])?;
    let g2_j_in_i = hyp_mp(&syl(&syl(&g2_g, &syl(&g_h, &h_dom)?)?, &dom_at)?, &g2_p)?;

    let phi_j = phi.subst(xv, &tj);
    let j_in_d = Formula::mem(tj.clone(), td.clone());
    let carved_j = Formula::and(Formula::mem(tj.clone(), i.clone()), phi_j.clone());
    let q_at_j = prim::ax_inst(q.clone(), tj.clone())?;
    debug_assert_eq!(
        q_at_j.concl().imp_parts()?.1,
        Formula::iff(j_in_d.clone(), carved_j.clone()),
        "Q did not instantiate at j to the expected biconditional"
    );
    let g2_iff_j = syl(&syl(&g2_g, &g_q)?, &q_at_j)?;

    // `G2 → ¬(j ∈ D)`: from `j ∈ D` read off `φ(j)`, instantiate it at `D`
    // itself, and feed it `⟨j,D⟩ ∈ k`.
    let g3 = Formula::and(g2.clone(), j_in_d.clone());
    let g3_g2 = and_left(g2.clone(), j_in_d.clone());
    let g3_in = and_right(g2.clone(), j_in_d.clone());
    let g3_carved = hyp_mp(&syl(&g3_g2, &hyp_iff_mp(&g2_iff_j)?)?, &g3_in)?;
    let g3_phi_j = syl(&g3_carved, &and_right(Formula::mem(tj.clone(), i.clone()), phi_j.clone()))?;
    // `φ(j)` at `D`: `R(j,D) → ¬(j ∈ D)`. `φ(j)` is a `∀`, not an
    // implication, so this is `hyp_mp` and not `hyp_syl`.
    let g3_at_d = hyp_mp(&a1i(&prim::ax_inst(phi_j.clone(), td.clone())?, g3.clone()), &g3_phi_j)?;
    let g3_step = hyp_mp(&g3_at_d, &syl(&g3_g2, &g2_p)?)?;
    let g2_not_in = uncurry(&hyp_mp(&g3_step, &g3_in)?)?;
    debug_assert_eq!(
        *g2_not_in.concl(),
        Formula::imp(g2.clone(), Formula::not(j_in_d.clone())),
        "the forward half of the diagonal did not close"
    );

    // `G2 → φ(j)`: single-valuedness makes `D` the only value of `R` at `j`, so
    // `¬(j ∈ D)` propagates to every `c` with `R(j,c)`.
    let p_jc = r.subst(xv, &tj).subst(bv, &tc);
    let g4 = Formula::and(g2.clone(), p_jc.clone());
    let g4_g2 = and_left(g2.clone(), p_jc.clone());
    let g4_p = and_right(g2.clone(), p_jc.clone());
    let sv_at = inst_all_imp(&sv, &[tj.clone(), td.clone(), tc.clone()])?;
    let g4_eq = hyp_mp(
        &syl(&syl(&g4_g2, &syl(&g2_g, &syl(&g_h, &h_sv)?)?)?, &sv_at)?,
        &hyp_and(&syl(&g4_g2, &g2_p)?, &g4_p)?,
    )?;
    let leib = Thm::eq_leibniz(
        td.clone(),
        tc.clone(),
        wv,
        Formula::not(Formula::mem(tj.clone(), Term::var(wv))),
    );
    let g4_not_c = hyp_mp(
        &hyp_mp(&a1i(&leib, g4.clone()), &g4_eq)?,
        &syl(&g4_g2, &g2_not_in)?,
    )?;
    let g2_phi_j = prim::mp(
        &prim::ax_dist(
            cv,
            g2.clone(),
            Formula::imp(p_jc, Formula::not(Formula::mem(tj.clone(), tc))),
        )?,
        &Thm::gen(cv, &uncurry(&g4_not_c)?),
    )?;
    debug_assert_eq!(
        *g2_phi_j.concl(),
        Formula::imp(g2.clone(), phi_j),
        "the backward half did not rebuild φ(j)"
    );

    // `j ∈ I ∧ φ(j)` puts `j` back into `D`, which `¬(j ∈ D)` refutes.
    let g2_in_d = hyp_mp(&hyp_iff_mpr(&g2_iff_j)?, &hyp_and(&g2_j_in_i, &g2_phi_j)?)?;
    let g2_false = hyp_mp(&g2_not_in, &g2_in_d)?;

    // ── Discharge `j`, then the diagonal ─────────────────────────────────────
    let g_false = discharge(jv, &g_ex, &g2_false)?;
    let target = Formula::imp(h.clone(), Formula::false_());
    let q_target = Thm::gen(dv, &com12(&uncurry(&g_false)?)?);
    let out = prim::mp(&exists_elim_imp(dv, &q_target, &target)?, &sep)?;
    debug_assert_eq!(*out.concl(), Formula::not(h), "no_diagonal_surjection: wrong shape");
    Ok(out)
}

/// `⊢ ∀I ∀k. ¬(DOM ∧ (SV ∧ ONTO))` — **no set surjects onto its own subsets**,
/// i.e. Cantor's theorem for a relation given as a *set* of ordered pairs.
///
/// The instance of [`no_diagonal_surjection`] at `R(x,b) := ⟨x,b⟩ ∈ k`, and
/// nothing more. `empty` must be a proof `⊢ ∀z. ¬(z ∈ e)`.
pub fn no_surjection_onto_subsets(env: &mut Env, empty: &Thm) -> DResult<Thm> {
    let (iv, kv) = (env.fresh_var(), env.fresh_var());
    let (ti, tk) = (Term::var(iv), Term::var(kv));
    let (xv, bv) = (env.fresh_var(), env.fresh_var());
    let r = kernel::thm::pair_in(env, tk, Term::var(xv), Term::var(bv));
    let out = no_diagonal_surjection(env, empty, &ti, xv, bv, &r)?;
    Ok(gen_all(&[iv, kv], &out))
}
