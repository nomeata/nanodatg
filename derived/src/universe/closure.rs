//! Closure clauses, for an arbitrary universe and then for `U(x)`.
//!
//! # Interface
//!
//! For an arbitrary universe:
//!
//! ```text
//! ⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → 𝒫y ∈ u)                 [universe_power_closed]
//! ⊢ ∀u ∀y ∀z. ((is_universe(u) ∧ (y ∈ u ∧ z ∈ y)) → z ∈ u)     [universe_mem_mem]
//! ⊢ ∀u ∀y ∀z. ((is_universe(u) ∧ (y ∈ u ∧ z ⊆ y)) → z ∈ u)     [universe_sub_mem]
//! ```
//!
//! and for the intersection, with no hypothesis about `U(x)` at all:
//!
//! ```text
//! ⊢ t ∈ U(x) → ((is_universe(u) ∧ x ∈ u) → t ∈ u)   [least_universe_transfer]
//! ⊢ ∀x. C₁(U(x))                                    [least_universe_transitive]
//! ⊢ ∀x. C₂(U(x))                                    [least_universe_closed_sub]
//! ⊢ ∀x. C₃(U(x))                                    [least_universe_closed_pow]
//! ⊢ ∀x. (C₂(U(x)) ∧ C₃(U(x)))                       [least_universe_closure]
//! ```
//!
//! [`UniverseClauses`] / [`universe_clauses`] split `is_universe(u)` into its
//! four clauses together with the projections `⊢ is_universe(u) → Cᵢ(u)`.
//! Callers need none of the derivations below.
//!
//! # Go through [`universe_clauses`]
//!
//! The predicate is `C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))`, so every projection is one step
//! deeper than it was before transitivity was added on 2026-07-31. **This is the
//! only place in the module that walks that nesting.** Two hand-rolled
//! `split_and` chains elsewhere — one here, one in [`crate::recursion`] — are
//! what turned the clause insertion into two silent breakages instead of one
//! compile-time one.
//!
//! # Why the transfer needs nothing about `U(x)`
//!
//! Each of the three clause transfers is the same pointwise argument: if
//! `y ∈ U(x)` and (say) `z ⊆ y`, then for each universe `u ∋ x` we have `y ∈ u`,
//! and `C₂(u)` puts `z` in `u` as well; being in every such `u` *is* being in
//! `U(x)`. So `is_universe(U(x))` — whose fourth clause is open, see
//! [`crate::universe::inaccessibility_reduction`] — is never needed. That
//! observation is [`least_universe_transfer`], and it is the half of the
//! characteristic property every proof here uses over and over.
//!
//! [`universe_power_closed`] is the one lemma that needs two clauses at once and
//! neither alone: `C₃` puts *some* `p ∈ u` above every subset of `y`, so
//! `𝒫y ⊆ p`; `C₂` then pulls `𝒫y`, a subset of the member `p`, back into `u`.
//! Inaccessibility is not needed, so the equinumerosity formula never has to be
//! unpacked. [`least_universe_transitive`] is what countermodel A in
//! [`crate::universe`] used to refute, and it is the fact everything downstream
//! was missing: `w ∈ y ∈ U(x)` now gives `w ∈ U(x)`.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{
    com12, exists_elim_imp, exists_intro_imp, hyp_and, hyp_mp, hyp_syl, iff_mp, iff_mpr,
    imp_mono_r, inst_all, syl, uncurry,
};
use crate::{a1i, and_left, and_right, decline, gen_all};
use super::shared::{hyp_contract, open_exists, split_and};
use super::predicate::{closed_pow, closed_sub, is_universe, transitive};
use super::least::{in_all_universes, least_universe_mem};

/// The four clauses of `is_universe(u)`, each with its projection
/// `⊢ is_universe(u) → Cᵢ(u)`.
///
/// The predicate is `C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))`, so every projection is one step
/// deeper than it was before transitivity was added on 2026-07-31. **This is the
/// only place in the module that walks that nesting.** Two hand-rolled
/// `split_and` chains elsewhere — one here, one in `crate::recursion` — are what
/// turned the clause insertion into two silent breakages instead of one
/// compile-time one; go through [`universe_clauses`] rather than reproducing the
/// walk.
pub struct UniverseClauses {
    /// `∀y ∈ u. ∀z ∈ y. z ∈ u` — [`transitive`].
    pub c1: Formula,
    /// `∀y ∈ u. ∀z ⊆ y. z ∈ u` — [`closed_sub`].
    pub c2: Formula,
    /// `∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p` — [`closed_pow`].
    pub c3: Formula,
    /// `∀y ⊆ u. (y ≈ u ∨ y ∈ u)` — [`crate::universe::inaccessible`].
    pub c4: Formula,
    /// `⊢ is_universe(u) → C₁(u)`.
    pub to_c1: Thm,
    /// `⊢ is_universe(u) → C₂(u)`.
    pub to_c2: Thm,
    /// `⊢ is_universe(u) → C₃(u)`.
    pub to_c3: Thm,
    /// `⊢ is_universe(u) → C₄(u)`.
    pub to_c4: Thm,
}

/// Split `is_universe(u)` into its four clauses and the projections onto them.
///
/// Reading a formula apart produces no `Thm`; the projections are ordinary
/// `and_left`/`and_right` compositions, so a mistake here yields a rejected
/// derivation, never a wrong theorem. Every refusal is an assembly failure:
/// both the predicate and the walk over it are built right here.
pub fn universe_clauses(env: &mut Env, u: &Term) -> DResult<UniverseClauses> {
    let univ = is_universe(env, u);
    let (c1, rest) = split_and(&univ)?;
    let (c2, rest2) = split_and(&rest)?;
    let (c3, c4) = split_and(&rest2)?;

    let to_c1 = and_left(c1.clone(), rest.clone());
    let to_rest = and_right(c1.clone(), rest.clone());
    let to_c2 = syl(&to_rest, &and_left(c2.clone(), rest2.clone()))?;
    let to_rest2 = syl(&to_rest, &and_right(c2.clone(), rest2.clone()))?;
    let to_c3 = syl(&to_rest2, &and_left(c3.clone(), c4.clone()))?;
    let to_c4 = syl(&to_rest2, &and_right(c3.clone(), c4.clone()))?;

    Ok(UniverseClauses { c1, c2, c3, c4, to_c1, to_c2, to_c3, to_c4 })
}

/// `⊢ is_universe(u) → C₁(u)` and the clause itself — transitivity.
///
/// This is the clause added on 2026-07-31, and the one every closure property
/// downstream was missing. `f ∈ fs(B(a), u) ∈ u` gives `f ∈ u` by this and
/// nothing else.
pub fn universe_transitive_clause(env: &mut Env, u: &Term) -> DResult<(Formula, Thm)> {
    let cl = universe_clauses(env, u)?;
    Ok((cl.c1, cl.to_c1))
}

/// `⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → 𝒫y ∈ u)` — a universe is closed under
/// power sets.
///
/// Neither closure clause does this alone. `C₃` puts *some* `p ∈ u` above every
/// subset of `y`, so `𝒫y ⊆ p`; `C₂` then pulls `𝒫y`, a subset of the member
/// `p`, back into `u`. Inaccessibility is not needed, so the equinumerosity
/// formula never has to be unpacked.
///
/// (`crate::empty` proves the same thing in the shape its own decomposition of
/// Tarski's body wants. Restated here against [`is_universe`], which is the
/// form `U(x)` needs and the form that survives that module changing.)
pub fn universe_power_closed(env: &mut Env, pow: FnSym, pow_ax: &Thm) -> DResult<Thm> {
    let (u, y) = (env.fresh_var(), env.fresh_var());
    let (tu, ty) = (Term::var(u), Term::var(y));
    let univ_u = is_universe(env, &tu);
    let cl = universe_clauses(env, &tu)?;
    let (c2_u, c3_u, to_c2, to_c3) = (cl.c2, cl.c3, cl.to_c2, cl.to_c3);

    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let goal = Formula::mem(pow_y.clone(), tu.clone());

    // `K := is_universe(u) ∧ y ∈ u`.
    let k = Formula::and(univ_u.clone(), y_in_u.clone());
    let k_univ = and_left(univ_u.clone(), y_in_u.clone());
    let k_y = and_right(univ_u, y_in_u);

    // `C₃` at `y`, with its witness `p` and the clause it satisfies read off.
    let c3_at_y = prim::ax_inst(c3_u, ty.clone())?;
    let (_, c3_body) = c3_at_y.concl().imp_parts()?;
    let (_, ex_p) = c3_body.imp_parts()?;
    let p = env.fresh_var();
    let tp = Term::var(p);
    let bp = open_exists(&ex_p, &tp)?;
    debug_assert_eq!(ex_p, Formula::exists(p, bp.clone()), "C₃'s ∃p did not reopen");
    let (p_in_u, all_sub_p) = split_and(&bp)?;
    let k_ex_p = hyp_mp(&syl(&k_univ, &syl(&to_c3, &c3_at_y)?)?, &k_y)?;

    // ── Under `L := K ∧ (p ∈ u ∧ ∀z ⊆ y. z ∈ p)` ─────────────────────────────
    let l = Formula::and(k.clone(), bp.clone());
    let l_k = and_left(k.clone(), bp.clone());
    let l_bp = and_right(k.clone(), bp.clone());
    let l_p_in_u = syl(&l_bp, &and_left(p_in_u.clone(), all_sub_p.clone()))?;
    let l_all = syl(&l_bp, &and_right(p_in_u.clone(), all_sub_p.clone()))?;

    // `L → 𝒫y ⊆ p`: a member of `𝒫y` is a subset of `y`, and those are in `p`.
    let v = env.fresh_var();
    let tv = Term::var(v);
    let l_v_sub_p = syl(&l_all, &prim::ax_inst(all_sub_p, tv.clone())?)?;
    let pw_at_v = inst_all(pow_ax, &[ty.clone(), tv.clone()])?;
    let l_step = hyp_syl(&a1i(&iff_mp(&pw_at_v)?, l.clone()), &l_v_sub_p)?;
    let sub_f = Formula::imp(Formula::mem(tv.clone(), pow_y.clone()), Formula::mem(tv, tp.clone()));
    let l_sub = prim::mp(&prim::ax_dist(v, l.clone(), sub_f)?, &Thm::gen(v, &l_step))?;
    debug_assert_eq!(
        *l_sub.concl(),
        Formula::imp(l, kernel::thm::subset(env, pow_y.clone(), tp.clone())),
        "the subset formula is not the one C₂ expects"
    );

    // `C₂` at `p` and then at `𝒫y`: a subset of the member `p` is a member.
    let c2_at_p = prim::ax_inst(c2_u, tp)?;
    let (_, c2_body) = c2_at_p.concl().imp_parts()?;
    let (_, all_sub_u) = c2_body.imp_parts()?;
    let c2_pw = syl(&c2_at_p, &imp_mono_r(&prim::ax_inst(all_sub_u, pow_y)?, p_in_u)?)?;
    let l_c2 = syl(&l_k, &syl(&k_univ, &to_c2)?)?;
    let l_goal = hyp_mp(&hyp_mp(&syl(&l_c2, &c2_pw)?, &l_p_in_u)?, &l_sub)?;

    // Discharge the witness `p`, then contract the duplicated `K`.
    let k_goal_f = Formula::imp(k.clone(), goal.clone());
    let ex_kg = exists_elim_imp(p, &Thm::gen(p, &com12(&uncurry(&l_goal)?)?), &k_goal_f)?;
    let k_goal = hyp_contract(&syl(&k_ex_p, &ex_kg)?)?;
    debug_assert_eq!(*k_goal.concl(), Formula::imp(k, goal), "universe_power_closed: wrong shape");
    Ok(gen_all(&[u, y], &k_goal))
}

/// `⊢ t ∈ U(x) → ((is_universe(u) ∧ x ∈ u) → t ∈ u)`.
///
/// Membership in the intersection transfers into any particular universe
/// containing `x`. Half of the characteristic property, and the half both
/// closure proofs use over and over.
pub fn least_universe_transfer(
    env: &mut Env,
    lu_ax: &Thm,
    x: &Term,
    t: &Term,
    u: &Term,
) -> DResult<Thm> {
    let phi_t = in_all_universes(env, x, t);
    let iff_t = least_universe_mem(lu_ax, x, t)?;
    // The instance must be the characteristic property *for this `φ`* — a
    // caller passing an unrelated theorem is declined, not given a theorem.
    let (fwd, _) = split_and(iff_t.concl())?;
    if fwd.imp_parts()?.1 != phi_t {
        return Err(decline!(
            "the characteristic property given is not the one for this membership condition"
        ))
    }
    syl(&iff_mp(&iff_t)?, &prim::ax_inst(phi_t, u.clone())?)
}

/// `⊢ ∀u ∀y ∀z. ((is_universe(u) ∧ (y ∈ u ∧ z ∈ y)) → z ∈ u)` — `C₁` in the
/// applied form the rest of the development wants.
///
/// `C₁` is stated as `∀y ∈ u. ∀z ∈ y. z ∈ u`; this is the same fact with the
/// two memberships gathered into one antecedent, which is the shape every
/// caller needs and which saves each of them the two instantiations.
pub fn universe_mem_mem(env: &mut Env) -> DResult<Thm> {
    let (uv, yv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ty, tz) = (Term::var(uv), Term::var(yv), Term::var(zv));

    let univ_u = is_universe(env, &tu);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let z_in_y = Formula::mem(tz.clone(), ty.clone());
    let both = Formula::and(y_in_u.clone(), z_in_y.clone());
    let h = Formula::and(univ_u.clone(), both.clone());

    let h_univ = and_left(univ_u.clone(), both.clone());
    let h_mems = and_right(univ_u, both);
    let h_y = syl(&h_mems, &and_left(y_in_u.clone(), z_in_y.clone()))?;
    let h_z = syl(&h_mems, &and_right(y_in_u, z_in_y))?;

    // `C₁(u)` at `y`, then its inner `∀z` at `z`.
    let cl = universe_clauses(env, &tu)?;
    let c1_at_y = prim::ax_inst(cl.c1, ty.clone())?;
    let (_, c1_body) = c1_at_y.concl().imp_parts()?;
    let (_, all_mem_u) = c1_body.imp_parts()?;
    let h_all = hyp_mp(&syl(&h_univ, &syl(&cl.to_c1, &c1_at_y)?)?, &h_y)?;
    let out = hyp_mp(&syl(&h_all, &prim::ax_inst(all_mem_u, tz.clone())?)?, &h_z)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tz, tu)),
        "universe_mem_mem: wrong shape"
    );
    Ok(gen_all(&[uv, yv, zv], &out))
}

/// `⊢ ∀u ∀y ∀z. ((is_universe(u) ∧ (y ∈ u ∧ z ⊆ y)) → z ∈ u)` — `C₂` in the
/// applied form the rest of the development wants.
///
/// The subset companion of [`universe_mem_mem`]. `C₂` is stated as
/// `∀y ∈ u. ∀z ⊆ y. z ∈ u`; this is the same fact with the two conditions
/// gathered into one antecedent, which saves every caller the two
/// instantiations. [`crate::funspace::sub_closed`] does the same job for a
/// caller that already has `C₂` at a fixed term; this one takes
/// `is_universe(u)` instead, which is the form the closure lemmas carry.
pub fn universe_sub_mem(env: &mut Env) -> DResult<Thm> {
    let (uv, yv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ty, tz) = (Term::var(uv), Term::var(yv), Term::var(zv));

    let univ_u = is_universe(env, &tu);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let z_sub_y = kernel::thm::subset(env, tz.clone(), ty.clone());
    let both = Formula::and(y_in_u.clone(), z_sub_y.clone());
    let h = Formula::and(univ_u.clone(), both.clone());

    let h_univ = and_left(univ_u.clone(), both.clone());
    let h_mems = and_right(univ_u, both);
    let h_y = syl(&h_mems, &and_left(y_in_u.clone(), z_sub_y.clone()))?;
    let h_sub = syl(&h_mems, &and_right(y_in_u, z_sub_y))?;

    // `C\u{2082}(u)` at `y`, then its inner `\u{2200}z` at `z`.
    let cl = universe_clauses(env, &tu)?;
    let c2_at_y = prim::ax_inst(cl.c2, ty.clone())?;
    let (_, c2_body) = c2_at_y.concl().imp_parts()?;
    let (_, all_sub_u) = c2_body.imp_parts()?;
    let h_all = hyp_mp(&syl(&h_univ, &syl(&cl.to_c2, &c2_at_y)?)?, &h_y)?;
    let out = hyp_mp(&syl(&h_all, &prim::ax_inst(all_sub_u, tz.clone())?)?, &h_sub)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(tz, tu)),
        "universe_sub_mem: wrong shape"
    );
    Ok(gen_all(&[uv, yv, zv], &out))
}

/// `⊢ ∀x. C₁(U(x))` — **the intersection of all universes containing `x` is
/// transitive**.
///
/// The clause added to `ax_tarski` on 2026-07-31, transferred through the
/// intersection by exactly the argument [`least_universe_closed_sub`] uses for
/// `C₂`: if `y ∈ U(x)` and `z ∈ y`, then for each universe `u ∋ x` we have
/// `y ∈ u`, and `C₁(u)` puts `z` in `u` as well; being in every such `u` is
/// being in `U(x)`. `is_universe(U(x))` is not needed and is not available.
///
/// This is what countermodel A at the end of this file used to refute, and it
/// is the fact everything downstream was missing: `w ∈ y ∈ U(x)` now gives
/// `w ∈ U(x)`.
pub fn least_universe_transitive(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> DResult<Thm> {
    if lu.arity() != 1 {
        return Err(decline!("the least-universe symbol is not unary"))
    }
    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);

    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let mem_zy = Formula::mem(tz.clone(), ty.clone());
    let y_in_w = Formula::mem(ty.clone(), w.clone());

    // `H := y ∈ U(x) ∧ z ∈ y`.
    let h = Formula::and(y_in_w.clone(), mem_zy.clone());
    let h_y = and_left(y_in_w.clone(), mem_zy.clone());
    let h_mem = and_right(y_in_w.clone(), mem_zy);

    // A universe `u` containing `x`, held fixed until the very end.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), x_in_u.clone());
    let cl = universe_clauses(env, &tu)?;

    // `N := H ∧ A`.
    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());

    let transfer = least_universe_transfer(env, lu_ax, &tx, &ty, &tu)?;
    let n_y_in_u = hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &syl(&n_h, &h_y)?)?, &n_a)?;

    // `C₁(u)` at `y`, then its inner `∀z` at `z`.
    let c1_at_y = prim::ax_inst(cl.c1, ty.clone())?;
    let (_, c1_body) = c1_at_y.concl().imp_parts()?;
    let (_, all_mem_u) = c1_body.imp_parts()?;
    let n_univ = syl(&n_a, &and_left(univ_u, x_in_u))?;
    let n_all = hyp_mp(&syl(&syl(&n_univ, &cl.to_c1)?, &c1_at_y)?, &n_y_in_u)?;
    let n_z_in_u =
        hyp_mp(&syl(&n_all, &prim::ax_inst(all_mem_u, tz.clone())?)?, &syl(&n_h, &h_mem)?)?;

    // Generalise over `u`: it occurs nowhere in `H`.
    let z_in_u = Formula::mem(tz.clone(), tu);
    let h_phi =
        prim::mp(&prim::ax_dist(u, h.clone(), Formula::imp(a, z_in_u))?, &Thm::gen(u, &uncurry(&n_z_in_u)?))?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h, in_all_universes(env, &tx, &tz)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let h_z_in_w = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tx, &tz)?)?)?;

    // Pull the two hypotheses back apart and quantify.
    let z_in_w = Formula::mem(tz, w.clone());
    let y_mem_z = uncurry(&h_z_in_w)?;
    let (_, inner) = y_mem_z.concl().imp_parts()?;
    let (mem_f, _) = inner.imp_parts()?;
    let out = Thm::gen(
        y,
        &prim::mp(
            &prim::ax_dist(z, y_in_w.clone(), Formula::imp(mem_f, z_in_w))?,
            &Thm::gen(z, &y_mem_z),
        )?,
    );
    debug_assert_eq!(*out.concl(), transitive(env, &w), "least_universe_transitive: wrong shape");
    Ok(Thm::gen(x, &out))
}

/// `⊢ ∀x. C₂(U(x))` — the intersection of all universes containing `x` is
/// closed under subsets of its members.
///
/// Pointwise: if `y ∈ U(x)` and `z ⊆ y`, then for each universe `u` containing
/// `x` we have `y ∈ u`, and `C₂(u)` puts `z` in `u` as well. Being in every
/// such `u` is exactly being in `U(x)`.
pub fn least_universe_closed_sub(env: &mut Env, lu: FnSym, lu_ax: &Thm) -> DResult<Thm> {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);

    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let sub_zy = kernel::thm::subset(env, tz.clone(), ty.clone());
    let y_in_w = Formula::mem(ty.clone(), w.clone());

    // `H := y ∈ U(x) ∧ z ⊆ y`.
    let h = Formula::and(y_in_w.clone(), sub_zy.clone());
    let h_y = and_left(y_in_w.clone(), sub_zy.clone());
    let h_sub = and_right(y_in_w.clone(), sub_zy);

    // A universe `u` containing `x`, held fixed until the very end.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let a = Formula::and(univ_u.clone(), Formula::mem(tx.clone(), tu.clone()));
    let cl = universe_clauses(env, &tu)?;
    let (c2_u, to_c2) = (cl.c2, cl.to_c2);

    // `N := H ∧ A`.
    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());

    let transfer = least_universe_transfer(env, lu_ax, &tx, &ty, &tu)?;
    let n_y_in_w = syl(&n_h, &h_y)?;
    let n_y_in_u = hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &n_y_in_w)?, &n_a)?;

    // `C₂(u)` at `y`, then its inner `∀z` at `z`.
    let c2_at_y = prim::ax_inst(c2_u, ty.clone())?;
    let (_, c2_body) = c2_at_y.concl().imp_parts()?;
    let (_, all_sub_u) = c2_body.imp_parts()?;
    let n_univ = syl(&n_a, &and_left(univ_u, Formula::mem(tx.clone(), tu.clone())))?;
    let n_c2 = syl(&n_univ, &to_c2)?;
    let n_all = hyp_mp(&syl(&n_c2, &c2_at_y)?, &n_y_in_u)?;
    let n_z_in_u =
        hyp_mp(&syl(&n_all, &prim::ax_inst(all_sub_u, tz.clone())?)?, &syl(&n_h, &h_sub)?)?;

    // Generalise over `u`: it occurs nowhere in `H`.
    let h_a_z = uncurry(&n_z_in_u)?;
    let z_in_u = Formula::mem(tz.clone(), tu);
    let h_phi = prim::mp(&prim::ax_dist(u, h.clone(), Formula::imp(a, z_in_u))?, &Thm::gen(u, &h_a_z))?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h, in_all_universes(env, &tx, &tz)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let h_z_in_w = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tx, &tz)?)?)?;

    // Pull the two hypotheses back apart and quantify.
    let z_in_w = Formula::mem(tz, w.clone());
    let y_sub_z = uncurry(&h_z_in_w)?;
    let (_, inner) = y_sub_z.concl().imp_parts()?;
    let (sub_f, _) = inner.imp_parts()?;
    let out = Thm::gen(
        y,
        &prim::mp(
            &prim::ax_dist(z, y_in_w.clone(), Formula::imp(sub_f, z_in_w))?,
            &Thm::gen(z, &y_sub_z),
        )?,
    );
    debug_assert_eq!(*out.concl(), closed_sub(env, &w), "least_universe_closed_sub: wrong shape");
    Ok(Thm::gen(x, &out))
}

/// `⊢ ∀x. C₃(U(x))` — the intersection of all universes containing `x` keeps
/// power sets inside.
///
/// The witness the clause asks for is `𝒫y` itself: it holds every subset of
/// `y` by definition, and it is in `U(x)` because every universe containing `x`
/// contains `y` and hence, by [`universe_power_closed`], contains `𝒫y`.
pub fn least_universe_closed_pow(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> DResult<Thm> {
    let upc = universe_power_closed(env, pow, pow_ax)?;

    let x = env.fresh_var();
    let tx = Term::var(x);
    let w = Term::apply(lu, vec![tx.clone()]);

    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let h = Formula::mem(ty.clone(), w.clone());

    // A universe `u` containing `x`.
    let u = env.fresh_var();
    let tu = Term::var(u);
    let univ_u = is_universe(env, &tu);
    let x_in_u = Formula::mem(tx.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), x_in_u.clone());

    // `N := (y ∈ U(x)) ∧ A`.
    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());

    let transfer = least_universe_transfer(env, lu_ax, &tx, &ty, &tu)?;
    let n_y_in_u = hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &n_h)?, &n_a)?;
    let n_univ = syl(&n_a, &and_left(univ_u, x_in_u))?;
    let upc_at = inst_all(&upc, &[tu.clone(), ty.clone()])?;
    let n_pow_in_u = hyp_mp(&a1i(&upc_at, n), &hyp_and(&n_univ, &n_y_in_u)?)?;

    // Generalise over `u`, then read the result back as membership in `U(x)`.
    let pow_in_u = Formula::mem(pow_y.clone(), tu);
    let h_phi = prim::mp(
        &prim::ax_dist(u, h.clone(), Formula::imp(a, pow_in_u))?,
        &Thm::gen(u, &uncurry(&n_pow_in_u)?),
    )?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h.clone(), in_all_universes(env, &tx, &pow_y)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let h_pow_in_w = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tx, &pow_y)?)?)?;

    // `⊢ ∀z. (z ⊆ y → z ∈ 𝒫y)`, the other half of what the clause demands.
    let sub_zy = kernel::thm::subset(env, tz.clone(), ty.clone());
    let all_sub = Thm::gen(z, &iff_mpr(&inst_all(pow_ax, &[ty.clone(), tz.clone()])?)?);
    debug_assert_eq!(
        *all_sub.concl(),
        Formula::forall(z, Formula::imp(sub_zy.clone(), Formula::mem(tz.clone(), pow_y.clone())))
    );

    let p = env.fresh_var();
    let tp = Term::var(p);
    let goal_body = Formula::and(
        Formula::mem(tp.clone(), w.clone()),
        Formula::forall(z, Formula::imp(sub_zy, Formula::mem(tz, tp))),
    );
    let h_pair = hyp_and(&h_pow_in_w, &a1i(&all_sub, h))?;
    let out = Thm::gen(y, &syl(&h_pair, &exists_intro_imp(p, goal_body, pow_y)?)?);
    debug_assert_eq!(*out.concl(), closed_pow(env, &w), "least_universe_closed_pow: wrong shape");
    Ok(Thm::gen(x, &out))
}

/// `⊢ ∀x. (C₂(U(x)) ∧ C₃(U(x)))` — both closure clauses at once.
///
/// This is `is_universe(U(x))` minus its first and last conjuncts: the
/// predicate is `C₁ ∧ (C₂ ∧ (C₃ ∧ C₄))`, `C₁` (transitivity) is
/// [`crate::universe::least_universe_transitive`] on its own, and what is
/// proved here is `C₂ ∧ C₃`. See
/// [`crate::universe::inaccessibility_reduction`] for what stands between this and the whole
/// predicate.
pub fn least_universe_closure(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> DResult<Thm> {
    let c2 = least_universe_closed_sub(env, lu, lu_ax)?;
    let c3 = least_universe_closed_pow(env, lu, lu_ax, pow, pow_ax)?;
    let x = env.fresh_var();
    let tx = Term::var(x);
    let both = crate::and_intro(
        &inst_all(&c2, std::slice::from_ref(&tx))?,
        &inst_all(&c3, std::slice::from_ref(&tx))?,
    );
    let w = Term::apply(lu, vec![tx]);
    debug_assert_eq!(
        *both.concl(),
        Formula::and(closed_sub(env, &w), closed_pow(env, &w)),
        "least_universe_closure: wrong shape"
    );
    Ok(Thm::gen(x, &both))
}
