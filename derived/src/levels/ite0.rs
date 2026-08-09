//! The conditional term former `ite0(g,a,b)` — `a` if `g = ∅`, else `b`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀g ∀a ∀b. ((g = ∅ → ite0(g,a,b) = a) ∧ (¬(g = ∅) → ite0(g,a,b) = b))   [Ite0::ax]
//! ⊢ ∀g ∀a ∀b. (g = ∅ → ite0(g,a,b) = a)                                    [Ite0::when_zero]
//! ⊢ ∀g ∀a ∀b. (¬(g = ∅) → ite0(g,a,b) = b)                                 [Ite0::when_nonzero]
//! ```
//!
//! All **unconditional**. `∅` is the caller's — [`ite0`] takes the
//! [`crate::funcs::Apply`] whose `empty` symbol the guard compares against,
//! because a freshly minted `∅` would be a different symbol and every theorem
//! here would then be about the wrong constant. This is the `imax` conditional
//! of `LEVELPOLY.md`: `(imax ℓ ℓ')̂ = ite0(ℓ̂', ∅, ℓ̂ ∪ ℓ̂')`.
//!
//! # Derivation
//!
//! The symbol comes through [`kernel::thm::define`] from the witness
//!
//! ```text
//! ⊢ ∀g ∀a ∀b ∃!y. ((g = ∅ → y = a) ∧ (¬(g = ∅) → y = b))
//! ```
//!
//! by excluded middle on `P := (g = ∅)`. Under `P` the witness is `y := a`:
//! the first conjunct is reflexivity, the second holds vacuously, and any `y₂`
//! satisfying the pair equals `a` by its own first conjunct. Under `¬P` it is
//! `y := b`, symmetrically. The two cases close classically — `∨` is `¬· → ·`,
//! so contraposing the `P`-case into the `¬P`-case gives `¬goal → goal`, which
//! [`crate::clavius`] collapses. The defining axiom is the conjunction above at
//! `y := ite0(g,a,b)`; [`crate::and_elim_left`]/[`crate::and_elim_right`] under
//! the quantifiers split it into the two exported halves.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::{
    a1i, and_elim_left, and_elim_right, and_left, and_right, clavius, com12, contrapos, ex_falso,
    exists_intro_imp, gen_all, hyp_and, imp_mono_r, imp_refl, inst_all, syl,
};

/// The conditional apparatus: the symbol and its characteristic theorems.
pub struct Ite0 {
    /// The ternary symbol `ite0`.
    pub sym: FnSym,
    /// `⊢ ∀g ∀a ∀b. ((g = ∅ → ite0(g,a,b) = a) ∧ (¬(g = ∅) → ite0(g,a,b) = b))`.
    pub ax: Thm,
    /// `⊢ ∀g ∀a ∀b. (g = ∅ → ite0(g,a,b) = a)`.
    pub when_zero: Thm,
    /// `⊢ ∀g ∀a ∀b. (¬(g = ∅) → ite0(g,a,b) = b)`.
    pub when_nonzero: Thm,
    /// The `∅` the guard compares against — the caller's, from the [`Apply`].
    pub empty: FnSym,
}

impl Ite0 {
    /// The term `ite0(g, a, b)`.
    pub fn at(&self, g: Term, a: Term, b: Term) -> Term { Term::apply(self.sym, vec![g, a, b]) }
}

/// Introduce `ite0` over the caller's `∅` and derive the interface theorems.
pub fn ite0(env: &mut Env, ap: &Apply) -> Option<Ite0> {
    let e = Term::apply(ap.empty, vec![]);
    let (g, a, b, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, ta, tb, ty) = (Term::var(g), Term::var(a), Term::var(b), Term::var(y));

    let p = Formula::eq(tg.clone(), e.clone());
    let np = Formula::not(p.clone());
    let phi = Formula::and(
        Formula::imp(p.clone(), Formula::eq(ty.clone(), ta.clone())),
        Formula::imp(np.clone(), Formula::eq(ty.clone(), tb.clone())),
    );

    // The ∃!-body in exactly the spelling `kernel::thm::exists_unique` uses:
    // `φ ∧ ∀y₂. (φ[y₂/y] → y₂ = y)`. Locally nameless representation makes the
    // choice of `y₂` invisible once the binder closes, so `define`'s comparison
    // against its own fresh variable succeeds.
    let y2 = env.fresh_var();
    let ty2 = Term::var(y2);
    let phi_y2 = phi.subst(y, &ty2);
    let c1_y2 = Formula::imp(p.clone(), Formula::eq(ty2.clone(), ta.clone()));
    let c2_y2 = Formula::imp(np.clone(), Formula::eq(ty2.clone(), tb.clone()));
    debug_assert_eq!(
        phi_y2,
        Formula::and(c1_y2.clone(), c2_y2.clone()),
        "ite0: φ[y₂/y] does not split into the expected conjuncts"
    );
    let uniq = Formula::forall(
        y2,
        Formula::imp(phi_y2.clone(), Formula::eq(ty2.clone(), ty.clone())),
    );
    let body = Formula::and(phi.clone(), uniq);
    let goal = Formula::exists(y, body.clone());

    // ── Case `P`: witness `y := a` ───────────────────────────────────────────
    // φ(a)'s first conjunct is `P → a = a`, provable outright; the second is
    // vacuous under `P`, since `P` and `¬P` yield `⊥`.
    let hp_c1 = a1i(&a1i(&Thm::eq_refl(ta.clone()), p.clone()), p.clone());
    let p_np_false = com12(&imp_refl(np.clone()))?;
    let hp_c2 = syl(
        &p_np_false,
        &imp_mono_r(&ex_falso(Formula::eq(ta.clone(), tb.clone())), np.clone())?,
    )?;
    let hp_phi_a = hyp_and(&hp_c1, &hp_c2)?;
    // Uniqueness: any `y₂` with φ(y₂) equals `a`, by its first conjunct at `P`.
    let hp_u = com12(&and_left(c1_y2.clone(), c2_y2.clone()))?;
    let hp_uniq_a = Thm::mp(
        &Thm::ax_dist(
            y2,
            p.clone(),
            Formula::imp(phi_y2.clone(), Formula::eq(ty2.clone(), ta.clone())),
        )?,
        &Thm::gen(y2, &hp_u),
    )?;
    let hp_body_a = hyp_and(&hp_phi_a, &hp_uniq_a)?;
    debug_assert_eq!(
        *hp_body_a.concl(),
        Formula::imp(p.clone(), body.subst(y, &ta)),
        "ite0: the P-case body has an unexpected shape"
    );
    let case_p = syl(&hp_body_a, &exists_intro_imp(y, body.clone(), ta.clone())?)?;

    // ── Case `¬P`: witness `y := b` ──────────────────────────────────────────
    let hnp_c1 = syl(
        &imp_refl(np.clone()),
        &imp_mono_r(&ex_falso(Formula::eq(tb.clone(), ta.clone())), p.clone())?,
    )?;
    let hnp_c2 = a1i(&a1i(&Thm::eq_refl(tb.clone()), np.clone()), np.clone());
    let hnp_phi_b = hyp_and(&hnp_c1, &hnp_c2)?;
    let hnp_u = com12(&and_right(c1_y2, c2_y2))?;
    let hnp_uniq_b = Thm::mp(
        &Thm::ax_dist(
            y2,
            np.clone(),
            Formula::imp(phi_y2, Formula::eq(ty2, tb.clone())),
        )?,
        &Thm::gen(y2, &hnp_u),
    )?;
    let hnp_body_b = hyp_and(&hnp_phi_b, &hnp_uniq_b)?;
    debug_assert_eq!(
        *hnp_body_b.concl(),
        Formula::imp(np.clone(), body.subst(y, &tb)),
        "ite0: the ¬P-case body has an unexpected shape"
    );
    let case_np = syl(&hnp_body_b, &exists_intro_imp(y, body, tb.clone())?)?;

    // ── Excluded middle, as Clavius' law ─────────────────────────────────────
    // Contrapose the `P`-case into the `¬P`-case: `¬goal → ¬P → goal`, and
    // `(¬goal → goal) → goal` closes classically.
    let neg_to_goal = syl(&contrapos(&case_p)?, &case_np)?;
    let exu = Thm::mp(&clavius(goal), &neg_to_goal)?;

    let witness = gen_all(&[g, a, b], &exu);
    let (sym, ax) = kernel::thm::define(env, &[g, a, b], y, phi, &witness)?;

    // ── Split the defining axiom under the quantifiers ───────────────────────
    let at = inst_all(&ax, &[tg.clone(), ta.clone(), tb.clone()])?;
    let applied = Term::apply(sym, vec![tg, ta.clone(), tb.clone()]);
    debug_assert_eq!(
        *at.concl(),
        Formula::and(
            Formula::imp(p.clone(), Formula::eq(applied.clone(), ta.clone())),
            Formula::imp(np.clone(), Formula::eq(applied.clone(), tb.clone())),
        ),
        "ite0: the defining axiom has an unexpected shape"
    );
    let when_zero = gen_all(&[g, a, b], &and_elim_left(&at)?);
    let when_nonzero = gen_all(&[g, a, b], &and_elim_right(&at)?);
    debug_assert_eq!(
        *when_zero.concl(),
        Formula::forall(
            g,
            Formula::forall(
                a,
                Formula::forall(b, Formula::imp(p.clone(), Formula::eq(applied.clone(), ta))),
            ),
        ),
        "ite0: when_zero has an unexpected shape"
    );
    debug_assert_eq!(
        *when_nonzero.concl(),
        Formula::forall(
            g,
            Formula::forall(a, Formula::forall(b, Formula::imp(np, Formula::eq(applied, tb)))),
        ),
        "ite0: when_nonzero has an unexpected shape"
    );

    Some(Ite0 { sym, ax, when_zero, when_nonzero, empty: ap.empty })
}
