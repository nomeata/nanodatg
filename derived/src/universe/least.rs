//! The operator `U(x)`: the membership condition, existence, and the symbol.
//!
//! # Interface
//!
//! Writing `in_all_universes(x,z)` for the membership condition
//!
//! ```text
//! ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u)     [in_all_universes]
//! ```
//!
//! the exports are
//!
//! ```text
//! ⊢ in_all_universes(x, x)                                    [mem_all_universes_self]
//! ⊢ ∀x ∃s ∀z. (z ∈ s ↔ in_all_universes(x,z))                 [least_universe_existence]
//! ⊢ ∀x ∀z. (z ∈ U(x) ↔ in_all_universes(x,z))                 [least_universe — introduces `U`]
//! ⊢ z ∈ U(a) ↔ in_all_universes(a,z)                          [least_universe_mem], at terms
//! ⊢ ∀x ∀u₀. ((x ∈ u₀ ∧ is_universe(u₀))
//!        → ∀z. (z ∈ U(x) ↔ (z ∈ u₀ ∧ in_all_universes(x,z)))) [least_universe_independent]
//! ⊢ ∀x. x ∈ U(x)                                              [mem_least_universe]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why the intersection, and why it is well defined
//!
//! [`kernel::Thm::ax_tarski`] gives *existence* of a universe around every set,
//! never uniqueness, so it cannot be Skolemised by `kernel::thm::define`
//! directly. What is canonical is the **intersection** of all universes
//! containing `x`:
//!
//! ```text
//! U(x) := { z ∈ u₀ : ∀u. (is_universe(u) ∧ x ∈ u) → z ∈ u }
//! ```
//!
//! for any `u₀` Tarski happens to hand over. Two things have to be said about
//! that description before it defines anything.
//!
//! * **It does not depend on `u₀`.** Under the hypothesis that `u₀` *is* a
//!   universe containing `x`, the side condition `z ∈ u₀` is implied by the
//!   body — instantiate the body at `u₀` — so the separated set satisfies
//!   `∀z. (z ∈ s ↔ in_all_universes(x,z))`, in which `u₀` no longer occurs.
//!   That formula is what [`least_universe_existence`] proves, and it is why the
//!   operator is well defined rather than merely definable.
//!   [`least_universe_independent`] states the same observation in the form a
//!   reader would want to check: two different choices of `u₀` describe the same
//!   set.
//! * **`∃!` follows from Extensionality**, via
//!   [`crate::rules::define_by_membership`], which is what [`least_universe`]
//!   hands to the kernel. Nothing is added to the theory —
//!   `kernel::thm::define` is conservative — and in particular Tarski's failure
//!   to provide uniqueness is repaired by the construction rather than by an
//!   appeal to choice.
//!
//! # No empty set is needed
//!
//! The separation used is [`crate::separation::separation_nonvacuous`], which
//! needs the separated set to be inhabited and in exchange needs no empty set
//! (none is derivable at this point; see [`crate::separation`]). The witness is
//! `x` itself: `x ∈ u` holds for *every* universe containing `x`, trivially,
//! which is [`mem_all_universes_self`] — simultaneously the inhabitation witness
//! and the content of [`mem_least_universe`].

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::err::{DResult, imported};
use crate::prim;
use crate::rules::{
    com12, exists_elim_imp, exists_intro_imp, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_syl,
    iff_mp, iff_mpr, inst_all, syl, uncurry,
};
use crate::{a1i, and_left, and_right, decline, gen_all, imp_refl};
use super::shared::{and_comm_imp, hyp_contract};
use super::predicate::{is_universe, tarski_at, universe_body};

/// `∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u)` — "`z` lies in every universe
/// containing `x`". This is the membership condition of `U(x)`.
pub fn in_all_universes(env: &mut Env, x: &Term, z: &Term) -> Formula {
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ = is_universe(env, &tu);
    Formula::forall(
        u,
        Formula::imp(
            Formula::and(univ, Formula::mem(x.clone(), tu.clone())),
            Formula::mem(z.clone(), tu),
        ),
    )
}

/// `⊢ ∀u. ((is_universe(u) ∧ x ∈ u) → x ∈ u)`, i.e. `in_all_universes(x, x)`.
///
/// Trivial — it is `and_right` generalised — and it is what makes the whole
/// construction go through without an empty set: it is simultaneously the
/// inhabitation witness [`crate::separation::separation_nonvacuous`] demands
/// and the content of [`mem_least_universe`].
pub fn mem_all_universes_self(env: &mut Env, x: &Term) -> Thm {
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ = is_universe(env, &tu);
    let mem = Formula::mem(x.clone(), tu.clone());
    let out = Thm::gen(u, &and_right(univ, mem));
    debug_assert_eq!(*out.concl(), in_all_universes(env, x, x), "mem_all_universes_self: wrong shape");
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Existence of the intersection, independently of the universe Tarski hands us.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∃s ∀z. (z ∈ s ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`, at a
/// caller-chosen parameter `x` and element variable `z`.
///
/// Split out from [`least_universe_existence`] so that [`least_universe`] can
/// hand the very same `x` and `z` to [`crate::rules::define_by_membership`].
///
/// Declines when `x` and `z` are the same variable: the parameter would then be
/// captured by the element quantifier and the statement would not be the one
/// this function documents.
///
/// **Where `u₀` goes.** Separation is run inside a Tarski universe `u₀` for
/// `x`, so what it produces is `∀z. (z ∈ s ↔ (z ∈ u₀ ∧ φ(z)))`. The extra
/// conjunct is then *deleted*, because under the hypothesis that `u₀` is a
/// universe containing `x` the body `φ(z)` instantiated at `u₀` already gives
/// `z ∈ u₀`. The conclusion therefore does not mention `u₀`, which is exactly
/// the well-definedness obligation, and it is what lets the witness be
/// discharged by [`crate::rules::exists_elim_imp`] at the end.
pub fn least_universe_existence_at(env: &mut Env, x: FreeVar, z: FreeVar) -> DResult<Thm> {
    if x == z {
        return Err(decline!("the parameter variable and the element variable must be distinct"))
    }
    let (tx, tz) = (Term::var(x), Term::var(z));
    let phi = in_all_universes(env, &tx, &tz);

    // The goal, with its own witness variable.
    let s = env.fresh_var();
    let ts = Term::var(s);
    let goal_body = Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), ts.clone()), phi.clone()));
    let goal = Formula::exists(s, goal_body.clone());

    // ── Tarski's universe `u₀` around `x` ────────────────────────────────────
    let u0 = env.fresh_var();
    let tu0 = Term::var(u0);
    let ex_u0 = tarski_at(env, &tx, u0)?;
    let h = universe_body(env, &tx, &tu0);
    let univ_u0 = is_universe(env, &tu0);
    let x_in_u0 = Formula::mem(tx.clone(), tu0.clone());
    debug_assert_eq!(h, Formula::and(x_in_u0.clone(), univ_u0.clone()));

    // ── Separation inside `u₀`, at the condition `φ` ──────────────────────────
    let sep = imported(
        "crate::separation::separation_nonvacuous",
        crate::separation::separation_nonvacuous(env, z, &phi),
    )?;
    let sep_u0 = inst_all(&sep, std::slice::from_ref(&tu0))?;

    let w = env.fresh_var();
    let tw = Term::var(w);
    let sep_body = Formula::and(Formula::mem(tw.clone(), tu0.clone()), phi.subst(z, &tw));
    let sep_ante = Formula::exists(w, sep_body.clone());
    let sep_prop = Formula::forall(
        z,
        Formula::iff(
            Formula::mem(tz.clone(), ts.clone()),
            Formula::and(Formula::mem(tz.clone(), tu0.clone()), phi.clone()),
        ),
    );
    debug_assert_eq!(
        *sep_u0.concl(),
        Formula::imp(sep_ante.clone(), Formula::exists(s, sep_prop.clone())),
        "separation_nonvacuous did not instantiate to the expected shape"
    );

    // `x` itself inhabits the condition, so Separation applies without an empty
    // set: `⊢ H → ∃w. (w ∈ u₀ ∧ φ(w))`.
    let h_x_in_u0 = and_left(x_in_u0.clone(), univ_u0.clone());
    let phi_x = mem_all_universes_self(env, &tx);
    debug_assert_eq!(*phi_x.concl(), phi.subst(z, &tx));
    let h_pair = hyp_and(&h_x_in_u0, &a1i(&phi_x, h.clone()))?;
    let h_ante = syl(&h_pair, &exists_intro_imp(w, sep_body, tx.clone())?)?;
    let h_ex_s = syl(&h_ante, &sep_u0)?;

    // ── Delete the `z ∈ u₀` conjunct, under `K := H ∧ P(s)` ───────────────────
    let k = Formula::and(h.clone(), sep_prop.clone());
    let k_h = and_left(h.clone(), sep_prop.clone());
    let k_p = and_right(h.clone(), sep_prop.clone());
    let k_iff = syl(&k_p, &prim::ax_inst(sep_prop.clone(), tz.clone())?)?;

    // `K → (is_universe(u₀) ∧ x ∈ u₀)`, the antecedent `φ` wants at `u₀`.
    let k_univ = syl(&k_h, &and_comm_imp(x_in_u0.clone(), univ_u0.clone()))?;

    // Forward: drop the conjunct.
    let mem_u0 = Formula::mem(tz.clone(), tu0.clone());
    let k_fwd = hyp_syl(&hyp_iff_mp(&k_iff)?, &a1i(&and_right(mem_u0.clone(), phi.clone()), k.clone()))?;

    // Backward: `φ(z)` at `u₀` restores it.
    let phi_at_u0 = prim::ax_inst(phi.clone(), tu0.clone())?;
    let l = Formula::and(k.clone(), phi.clone());
    let l_k = and_left(k.clone(), phi.clone());
    let l_phi = and_right(k.clone(), phi.clone());
    let l_imp = hyp_mp(&a1i(&phi_at_u0, l.clone()), &l_phi)?;
    let l_mem = hyp_mp(&l_imp, &syl(&l_k, &k_univ)?)?;
    let k_restore = uncurry(&hyp_and(&l_mem, &l_phi)?)?;
    let k_bwd = hyp_syl(&k_restore, &hyp_iff_mpr(&k_iff)?)?;

    let k_iff2 = hyp_and(&k_fwd, &k_bwd)?;
    let iff_f = Formula::iff(Formula::mem(tz.clone(), ts.clone()), phi.clone());
    debug_assert_eq!(*k_iff2.concl(), Formula::imp(k.clone(), iff_f.clone()));

    // `z` is bound in `P(s)` and absent from `H`, so it generalises.
    let k_all = prim::mp(&prim::ax_dist(z, k.clone(), iff_f)?, &Thm::gen(z, &k_iff2))?;
    let k_goal = syl(&k_all, &exists_intro_imp(s, goal_body, ts)?)?;

    // ── Discharge the separated set, then the universe ────────────────────────
    let h_goal_f = Formula::imp(h.clone(), goal.clone());
    let ex_sg = exists_elim_imp(s, &Thm::gen(s, &com12(&uncurry(&k_goal)?)?), &h_goal_f)?;
    let h_goal = hyp_contract(&syl(&h_ex_s, &ex_sg)?)?;
    let ex_ug = exists_elim_imp(u0, &Thm::gen(u0, &h_goal), &goal)?;
    let out = prim::mp(&ex_ug, &ex_u0)?;
    debug_assert_eq!(*out.concl(), goal, "least_universe_existence_at produced an unexpected shape");
    Ok(out)
}

/// `⊢ ∀x ∃s ∀z. (z ∈ s ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`.
///
/// The intersection of all universes containing `x` exists, for every `x`.
pub fn least_universe_existence(env: &mut Env) -> DResult<Thm> {
    let (x, z) = (env.fresh_var(), env.fresh_var());
    Ok(Thm::gen(x, &least_universe_existence_at(env, x, z)?))
}

// ─────────────────────────────────────────────────────────────────────────────
// The operator itself.
// ─────────────────────────────────────────────────────────────────────────────

/// Introduce `U(x)`, the least universe containing `x`, with
/// `⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))`.
///
/// Existence is [`least_universe_existence_at`]; uniqueness is Extensionality,
/// via [`crate::rules::define_by_membership`]. Nothing is added to the theory —
/// `kernel::thm::define` is conservative — and in particular Tarski's failure
/// to provide uniqueness is repaired by the construction rather than by an
/// appeal to choice.
pub fn least_universe(env: &mut Env) -> DResult<(FnSym, Thm)> {
    let (x, z) = (env.fresh_var(), env.fresh_var());
    let existence = least_universe_existence_at(env, x, z)?;
    let phi = in_all_universes(env, &Term::var(x), &Term::var(z));
    crate::rules::define_by_membership(env, &[x], &existence, z, &phi)
}

/// `⊢ z ∈ U(a) ↔ ∀u. ((is_universe(u) ∧ a ∈ u) → z ∈ u)`, for given terms.
///
/// The characteristic property, ready to use at concrete terms rather than at
/// the defining variables.
pub fn least_universe_mem(lu_ax: &Thm, a: &Term, z: &Term) -> DResult<Thm> {
    inst_all(lu_ax, &[a.clone(), z.clone()])
}

/// `⊢ ∀x ∀u₀. ((x ∈ u₀ ∧ is_universe(u₀))
///        → ∀z. (z ∈ U(x) ↔ (z ∈ u₀ ∧ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))))`
///
/// **Independence of `u₀`, as a theorem.** `U(x)` is *the* set the defining
/// description produces, whichever universe Tarski happens to hand over:
/// separating the intersection condition inside any universe `u₀ ∋ x`
/// whatsoever gives `U(x)` back. The extra conjunct is free in both directions
/// — the body instantiated at `u₀` already says `z ∈ u₀`.
///
/// [`least_universe_existence_at`] uses the same observation internally, to
/// keep `u₀` out of the existence statement. This states it in the form a
/// reader would want to check: two different choices of `u₀` describe the same
/// set, namely `U(x)`.
pub fn least_universe_independent(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> DResult<Thm> {
    let (x, u0, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tu0, tz) = (Term::var(x), Term::var(u0), Term::var(z));
    let w = Term::apply(lu, vec![tx.clone()]);

    let univ_u0 = is_universe(env, &tu0);
    let x_in_u0 = Formula::mem(tx.clone(), tu0.clone());
    let h = universe_body(env, &tx, &tu0);
    debug_assert_eq!(h, Formula::and(x_in_u0.clone(), univ_u0.clone()));

    let phi_z = in_all_universes(env, &tx, &tz);
    let iff_z = least_universe_mem(lu_ax, &tx, &tz)?;
    let mem_u0 = Formula::mem(tz.clone(), tu0.clone());
    let z_in_w = Formula::mem(tz.clone(), w);

    // `H → (φ(z) → z ∈ u₀)`, the whole content of the deletion.
    let h_a = syl(&imp_refl(h.clone()), &and_comm_imp(x_in_u0, univ_u0))?;
    let h_phi_u0 = syl(&h_a, &com12(&prim::ax_inst(phi_z.clone(), tu0)?)?)?;

    // Forward, under `L := H ∧ z ∈ U(x)`.
    let l_h = and_left(h.clone(), z_in_w.clone());
    let l_zw = and_right(h.clone(), z_in_w.clone());
    let l_phi = hyp_mp(&syl(&l_h, &a1i(&iff_mp(&iff_z)?, h.clone()))?, &l_zw)?;
    let l_u0 = hyp_mp(&syl(&l_h, &h_phi_u0)?, &l_phi)?;
    let h_fwd = uncurry(&hyp_and(&l_u0, &l_phi)?)?;

    // Backward: drop the conjunct and read the characteristic property back.
    let h_bwd = a1i(&syl(&and_right(mem_u0.clone(), phi_z.clone()), &iff_mpr(&iff_z)?)?, h.clone());

    let iff_f = Formula::iff(z_in_w, Formula::and(mem_u0, phi_z));
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    debug_assert_eq!(*h_iff.concl(), Formula::imp(h.clone(), iff_f.clone()));

    // `z` occurs nowhere in `H`, so it generalises.
    let out = prim::mp(&prim::ax_dist(z, h, iff_f)?, &Thm::gen(z, &h_iff))?;
    Ok(gen_all(&[x, u0], &out))
}

/// `⊢ ∀x. x ∈ U(x)`.
///
/// Immediate from [`mem_all_universes_self`] and the characteristic property —
/// and worth stating separately, because it is what makes `U(x)` non-empty and
/// hence what made the whole construction possible without an empty set.
pub fn mem_least_universe(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> DResult<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let inst = least_universe_mem(lu_ax, &tx, &tx)?;
    let out = prim::mp(&iff_mpr(&inst)?, &mem_all_universes_self(env, &tx))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(tx.clone(), Term::apply(lu, vec![tx])),
        "mem_least_universe produced an unexpected shape"
    );
    Ok(Thm::gen(x, &out))
}
