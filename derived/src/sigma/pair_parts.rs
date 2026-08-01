//! **A member of a Cartesian product is its own two projections** —
//! `q ∈ A × B → (π₁q ∈ A ∧ π₂q ∈ B ∧ ⟨π₁q,π₂q⟩ = q)`.
//!
//! # Why this is missing and why it is needed
//!
//! [`crate::proj`] derives `π₁⟨a,b⟩ = a` and `π₂⟨a,b⟩ = b` — the thesis's ι
//! rules for the projections — but every one of its statements is *at a pair
//! that is already written as a pair*. A `Σ`-type's elimination rule has the
//! opposite shape: it is handed an element `q` of a set and must produce typed
//! components, without anybody having spelled `q` as `⟨_,_⟩`. The missing step
//! is exactly the thesis's η rule `(π₁ x, π₂ x) ≡ x` for `x : Σy:α. β`
//! (`derived/src/proj.rs` records that it derives η only at a literal pair),
//! together with the typing of the two halves.
//!
//! This file supplies it once, for the *Cartesian* product, and
//! [`super::dsum`] inherits it: a dependent `Σ` is carved out of `A × ⋃img(A)`
//! by Separation, so anything its members are is something the product's
//! members already are.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀q. (q ∈ A × B → (π₁q ∈ A ∧ (π₂q ∈ B ∧ ⟨π₁q,π₂q⟩ = q)))   [product_parts]
//! ```
//!
//! Unconditional, and the three conjuncts are stated in the order a caller
//! wants them.
//!
//! # The derivation
//!
//! [`Product::prod_ax`](crate::funspace::Product::prod_ax) says a member of
//! `A × B` is `⟨x,y⟩` for some `x ∈ A` and `y ∈ B`. Two existential
//! eliminations bring `x` and `y` into scope; under `q = ⟨x,y⟩` the two
//! computation rules [`Proj::fst`](crate::proj::Proj::fst) and
//! [`Proj::snd`](crate::proj::Proj::snd) identify `π₁q` with `x` and `π₂q`
//! with `y`, and the goal transports along those two equations. The witnesses
//! do not escape: the conclusion mentions only `q`, which is why the
//! eliminations are legal.
//!
//! # Nothing here is an axiom
//!
//! One instance of the product's characteristic property and two of the
//! projections' computation rules. No new symbol.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::{cartesian::product_cond, Product};
use crate::proj::Proj;
use crate::{
    a1i, and_left, and_right, com12, exists_elim_imp, gen_all, hyp_mp, iff_mp, inst_all, syl,
};

use super::shared::{hyp_congr, hyp_eq_symm, hyp_transport};

/// `⊢ ∀A ∀B ∀q. (q ∈ A × B → (π₁q ∈ A ∧ (π₂q ∈ B ∧ ⟨π₁q,π₂q⟩ = q)))`.
///
/// `prod` must be the product [`Proj`] and `ap` were built over — the pairing
/// symbol has to be the same one, or `⟨π₁q,π₂q⟩` names a different term from
/// the product's own pairs. That is checked against
/// [`product_cond`], not assumed.
pub fn product_parts(env: &mut Env, ap: &Apply, prod: &Product, proj: &Proj) -> Option<Thm> {
    let (av, bv, qv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tq, tx, ty) =
        (Term::var(av), Term::var(bv), Term::var(qv), Term::var(xv), Term::var(yv));

    let fst_q = proj.fst_of(ap, tq.clone());
    let snd_q = proj.snd_of(ap, tq.clone());
    let goal = Formula::and(
        Formula::mem(fst_q.clone(), ta.clone()),
        Formula::and(
            Formula::mem(snd_q.clone(), tb.clone()),
            Formula::eq(ap.sets.pair(fst_q.clone(), snd_q.clone()), tq.clone()),
        ),
    );

    // The product's membership condition, spelled with binders we control.
    let pair_xy = ap.sets.pair(tx.clone(), ty.clone());
    let inner = Formula::and(
        Formula::mem(ty.clone(), tb.clone()),
        Formula::eq(tq.clone(), pair_xy.clone()),
    );
    let outer = Formula::and(
        Formula::mem(tx.clone(), ta.clone()),
        Formula::exists(yv, inner.clone()),
    );
    let cond = Formula::exists(xv, outer.clone());
    if cond != product_cond(env, &ap.sets, &ta, &tb, &tq) {
        return None
    }

    // ── Under `K := x ∈ A ∧ (y ∈ B ∧ q = ⟨x,y⟩)`, prove the goal ────────────
    let k = Formula::and(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    let h_x_in_a = and_left(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    let rest = and_right(Formula::mem(tx.clone(), ta.clone()), inner.clone());
    let h_y_in_b = syl(
        &rest,
        &and_left(
            Formula::mem(ty.clone(), tb.clone()),
            Formula::eq(tq.clone(), pair_xy.clone()),
        ),
    )?;
    let h_q_eq = syl(
        &rest,
        &and_right(
            Formula::mem(ty.clone(), tb.clone()),
            Formula::eq(tq.clone(), pair_xy.clone()),
        ),
    )?;

    // `K → π₁q = x` and `K → π₂q = y`.
    let e1 = {
        let step = hyp_congr(env, &h_q_eq, |t| proj.fst_of(ap, t))?;
        let rule = a1i(&inst_all(&proj.fst, &[tx.clone(), ty.clone()])?, k.clone());
        crate::recursion::hyp::hyp_eq_trans(env, &step, &rule)?
    };
    let e2 = {
        let step = hyp_congr(env, &h_q_eq, |t| proj.snd_of(ap, t))?;
        let rule = a1i(&inst_all(&proj.snd, &[tx.clone(), ty.clone()])?, k.clone());
        crate::recursion::hyp::hyp_eq_trans(env, &step, &rule)?
    };

    // The three conjuncts.
    let c1 = {
        let back = hyp_eq_symm(env, &e1)?;
        let ta2 = ta.clone();
        hyp_transport(env, &back, &h_x_in_a, |t| Formula::mem(t, ta2.clone()))?
    };
    let c2 = {
        let back = hyp_eq_symm(env, &e2)?;
        let tb2 = tb.clone();
        hyp_transport(env, &back, &h_y_in_b, |t| Formula::mem(t, tb2.clone()))?
    };
    let c3 = {
        let snd_q2 = snd_q.clone();
        let step1 = hyp_congr(env, &e1, move |t| ap.sets.pair(t, snd_q2.clone()))?;
        let tx2 = tx.clone();
        let step2 = hyp_congr(env, &e2, move |t| ap.sets.pair(tx2.clone(), t))?;
        let to_pair = crate::recursion::hyp::hyp_eq_trans(env, &step1, &step2)?;
        let back = hyp_eq_symm(env, &h_q_eq)?;
        crate::recursion::hyp::hyp_eq_trans(env, &to_pair, &back)?
    };
    let under_k = crate::hyp_and(&c1, &crate::hyp_and(&c2, &c3)?)?;
    debug_assert_eq!(*under_k.concl(), Formula::imp(k.clone(), goal.clone()), "product_parts: K");

    // ── Peel the two existentials ───────────────────────────────────────────
    // `⊢ (y ∈ B ∧ q = ⟨x,y⟩) → (x ∈ A → goal)`, then over `∃y`.
    let swapped = com12(&crate::uncurry(&under_k)?)?;
    let x_goal = Formula::imp(Formula::mem(tx.clone(), ta.clone()), goal.clone());
    let over_y = exists_elim_imp(yv, &Thm::gen(yv, &swapped), &x_goal)?;

    // `⊢ (x ∈ A ∧ ∃y. …) → goal`.
    let h_x = and_left(Formula::mem(tx.clone(), ta.clone()), Formula::exists(yv, inner.clone()));
    let h_ex = and_right(Formula::mem(tx.clone(), ta.clone()), Formula::exists(yv, inner));
    let under_outer = hyp_mp(&syl(&h_ex, &over_y)?, &h_x)?;
    debug_assert_eq!(
        *under_outer.concl(),
        Formula::imp(outer, goal.clone()),
        "product_parts: outer"
    );

    let over_x = exists_elim_imp(xv, &Thm::gen(xv, &under_outer), &goal)?;
    let from_prod = syl(
        &iff_mp(&inst_all(&prod.prod_ax, &[ta.clone(), tb.clone(), tq.clone()])?)?,
        &over_x,
    )?;
    debug_assert_eq!(
        *from_prod.concl(),
        Formula::imp(Formula::mem(tq, prod.of(ta, tb)), goal),
        "product_parts: the conclusion has the wrong shape"
    );
    Some(gen_all(&[av, bv, qv], &from_prod))
}
