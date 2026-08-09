//! Closure properties of `U(x)`, from the clauses `C₂` and `C₃` on their own.
//!
//! # Interface
//!
//! ```text
//! from ⊢ C₂(u)             infer ⊢ big ∈ u → (small ⊆ big → small ∈ u)   [sub_closed]
//! from ⊢ C₂(u) and ⊢ C₃(u) infer ⊢ ∀y. (y ∈ u → 𝒫y ∈ u)                  [pow_closed]
//! ```
//!
//! Callers need neither derivation.
//!
//! # Why these are re-derived here
//!
//! [`crate::universe::universe_power_closed`] proves the same thing from
//! `is_universe(u)`, and that form *can* now be instantiated at `U(x)`:
//! `is_universe(U(x))` is a theorem
//! ([`crate::universe::least_universe_is_universe`]). These two are stated at
//! the clause level anyway — they take `C₂` and `C₃` as separate hypotheses at
//! whatever term the caller has, which is what
//! [`crate::universe::least_universe_closed_sub`] and
//! [`crate::universe::least_universe_closed_pow`] supply — and those two
//! clauses are all the argument ever used, so it is rerun against them.
//! The instantiation was measured (`tests/is_universe_route_cost.rs`) and
//! loses even with the theorem already in hand: [`pow_closed`] at `U(x)`
//! costs 306 kernel calls against 672 for deriving
//! [`crate::universe::universe_power_closed`] and instantiating it there;
//! [`sub_closed`] costs 10 against 399 via
//! [`crate::universe::universe_sub_mem`] — whose discharged instance is the
//! *uncurried* shape, which no consumer chains.
//!
//! Neither clause suffices alone for [`pow_closed`]: `C₃` puts *some* `p ∈ u`
//! above every subset of `y`, so `𝒫y ⊆ p`; `C₂` then pulls `𝒫y`, a subset of the
//! member `p`, back into `u`. Inaccessibility is never touched.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::hyp_syl;
use crate::{a1i, and_left, and_right, hyp_mp, iff_mp, inst_all, syl};
use super::glue::{discharge, open_exists, split_and};

/// From `⊢ C₂(u)`, i.e. `⊢ ∀y ∈ u. ∀z ⊆ y. z ∈ u`, infer
/// `⊢ big ∈ u → (small ⊆ big → small ∈ u)`.
pub fn sub_closed(c2: &Thm, big: &Term, small: &Term) -> Option<Thm> {
    let at_big = Thm::mp(&Thm::ax_inst(c2.concl().clone(), big.clone())?, c2)?;
    let (_, all_sub) = at_big.concl().as_imp()?;
    syl(&at_big, &Thm::ax_inst(all_sub, small.clone())?)
}

/// From `⊢ C₂(u)` and `⊢ C₃(u)` infer `⊢ ∀y. (y ∈ u → 𝒫y ∈ u)`.
///
/// Neither clause suffices alone. `C₃` puts *some* `p ∈ u` above every subset
/// of `y`, so `𝒫y ⊆ p`; `C₂` then pulls `𝒫y`, a subset of the member `p`, back
/// into `u`. Inaccessibility is never touched.
pub fn pow_closed(
    env: &mut Env,
    pow: FnSym,
    pow_ax: &Thm,
    u: &Term,
    c2: &Thm,
    c3: &Thm,
) -> Option<Thm> {
    let y = env.fresh_var();
    let ty = Term::var(y);
    let pow_y = Term::apply(pow, vec![ty.clone()]);
    let h = Formula::mem(ty.clone(), u.clone());
    let goal = Formula::mem(pow_y.clone(), u.clone());

    // `C₃` at `y`, with its witness `p` and the clause it satisfies read off.
    let c3_y = Thm::mp(&Thm::ax_inst(c3.concl().clone(), ty.clone())?, c3)?;
    let (h_chk, ex_p) = c3_y.concl().as_imp()?;
    if h_chk != h {
        return None
    }
    let p = env.fresh_var();
    let tp = Term::var(p);
    let bp = open_exists(&ex_p, &tp)?;
    debug_assert_eq!(ex_p, Formula::exists(p, bp.clone()), "C₃'s ∃p did not reopen");
    let (p_in_u, all_sub_p) = split_and(&bp)?;

    // ── Under `L := (y ∈ u) ∧ (p ∈ u ∧ ∀z ⊆ y. z ∈ p)` ───────────────────────
    let l = Formula::and(h.clone(), bp.clone());
    let l_bp = and_right(h.clone(), bp.clone());
    let l_p_in_u = syl(&l_bp, &and_left(p_in_u.clone(), all_sub_p.clone()))?;
    let l_all = syl(&l_bp, &and_right(p_in_u.clone(), all_sub_p.clone()))?;

    // `L → 𝒫y ⊆ p`: a member of `𝒫y` is a subset of `y`, and those are in `p`.
    let v = env.fresh_var();
    let tv = Term::var(v);
    let l_v_sub_p = syl(&l_all, &Thm::ax_inst(all_sub_p, tv.clone())?)?;
    let pw_at_v = inst_all(pow_ax, &[ty.clone(), tv.clone()])?;
    let l_step = hyp_syl(&a1i(&iff_mp(&pw_at_v)?, l.clone()), &l_v_sub_p)?;
    let sub_f = Formula::imp(Formula::mem(tv.clone(), pow_y.clone()), Formula::mem(tv, tp.clone()));
    let l_sub = Thm::mp(&Thm::ax_dist(v, l.clone(), sub_f)?, &Thm::gen(v, &l_step))?;
    debug_assert_eq!(
        *l_sub.concl(),
        Formula::imp(l.clone(), kernel::thm::subset(env, pow_y.clone(), tp.clone())),
        "the subset formula is not the one C₂ expects"
    );

    // `C₂` at `p` and then at `𝒫y`.
    let c2_pw = sub_closed(c2, &tp, &pow_y)?;
    let l_goal = hyp_mp(&hyp_mp(&a1i(&c2_pw, l), &l_p_in_u)?, &l_sub)?;

    let h_goal = discharge(p, &c3_y, &l_goal)?;
    debug_assert_eq!(*h_goal.concl(), Formula::imp(h, goal), "pow_closed: unexpected shape");
    Some(Thm::gen(y, &h_goal))
}
