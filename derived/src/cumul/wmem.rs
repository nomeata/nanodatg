//! **The W-type is a member of a universe** — steps (d) and (f) of the route in
//! [`crate::cumul`], and the point of the whole module.
//!
//! # Interface
//!
//! Writing `S` for the seed, `T` for `tower(S)`, `W` for `W(A,B,U(c))`, `bnd`
//! for [`super::bounded::bnd`] and
//!
//! ```text
//! Fin(A,B)  :=  A ⊆ S ∧ ∀a. (a ∈ A → (B(a) ⊆ S ∧ B(a) ∈ ω))
//! Fin⁺(A,B) :=  A ⊆ S ∧ ∀a. (a ∈ A → (B(a) ⊆ S ∧ bnd(B(a))))
//! ```
//!
//! for the two hypotheses [`super::tower_closed`] and
//! [`super::tower_closed_bnd`] carry, [`WMem`] exports
//!
//! ```text
//! ⊢ ∀A ∀B ∀c. ((Fin(A,B) ∧ S ∈ U(c)) → W ⊆ T)                [WMem::w_sub_tower]
//! ⊢ ∀A ∀B ∀c ∀d. (((Fin(A,B) ∧ S ∈ U(c)) ∧ (S ∈ U(d) ∧ ω ∈ U(d)))
//!                     → W ∈ U(d))                            [WMem::w_in_universe]
//!
//! ⊢ ∀A ∀B ∀c. ((Fin⁺(A,B) ∧ S ∈ U(c)) → W ⊆ T)           [WMem::w_sub_tower_bnd]
//! ⊢ ∀A ∀B ∀c ∀d. (((Fin⁺(A,B) ∧ S ∈ U(c)) ∧ (S ∈ U(d) ∧ ω ∈ U(d)))
//!                     → W ∈ U(d))                        [WMem::w_in_universe_bnd]
//! ```
//!
//! Callers need neither derivation; both are three lines.
//!
//! # Why four theorems and not two — and why two of them now have no consumer
//!
//! [`derive`] never looks at the fibre condition — it reads the antecedent off
//! the `tower_closed` it is handed and carries it — so the general pair costs
//! one extra call and no extra mathematics. The `Fin` pair is
//! [`crate::wlist`]'s and [`crate::enums`]': their fibres really are von Neumann
//! naturals, and their discharge is unchanged.
//!
//! **The `Fin⁺` pair has stopped having one.** It existed for the general
//! inductive translation, whose fibre `finord(m)` is a nest of binary sums and
//! is not a member of `ω`; [`super::DeclUniverse::over_at_general`]'s step (f)
//! now spends [`crate::wpath::w_in_universe_paths`] instead, which asks nothing
//! about the fibres at all and therefore reaches an infinitely branching
//! declaration, which `bnd` cannot. `Fin` still implies `Fin⁺` (that is
//! [`super::tower_closed`]), so nothing here is *wrong*; it is unreached, and
//! [`mod@super::bounded`]'s header says where the rest of that story is.
//!
//! # Two universes, and they are not the same one
//!
//! `c` is the **bound**: `W(A,B,U(c))` is carved out of `U(c)`, and
//! [`crate::wlist`] takes `c := 1 + α`. `d` is where the W-type *lives*, and it has
//! to satisfy `ω ∈ U(d)`.
//!
//! They cannot be identified, and this is the correction the previous session
//! recorded and this one confirms by construction. At `c = d = A` the second
//! antecedent would be `ω ∈ U(A)`, and `V_ω` is a universe containing
//! `A = 1+1`, so `U(A) ⊆ V_ω` and every member of `U(A)` is finite — `ω ∈ U(A)`
//! is **refutable**. The target `W(A,B,U(A)) ∈ U(A)` that this development
//! chased for two sessions is therefore false, and the true statement needs the
//! second universe. See the closing note of [`crate::cumul`] and
//! [`crate::tower`], where the same countermodel decided `U₁ := U(ω)`.
//!
//! # Why (d) is not an induction
//!
//! `W(A,B,u)` is *defined* as the intersection of the closed subsets of `u`, so
//! `W ⊆ T` for a closed `T ⊆ u` is one instantiation of that intersection —
//! [`crate::wtype::w_induction`], W2, and nothing more. An earlier handover
//! called this "the only genuinely new mathematics left, an induction over
//! `crate::wtype::rect`"; it is neither. The new mathematics was
//! [`super::tower_closed`], W2's second antecedent.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::wtype::Wtype;
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, inst_all, syl};

use super::stages::Stages;

/// From `⊢ H → ∀v₁ … ∀vₙ. φ` infer `⊢ H → φ[t₁ … tₙ]`.
fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// The W-type inside the tower, and inside a universe.
pub struct WMem {
    /// `⊢ ∀A ∀B ∀c. ((Fin(A,B) ∧ S ∈ U(c)) → W(A,B,U(c)) ⊆ T)` — **step (d)**.
    pub w_sub_tower: Thm,
    /// `⊢ ∀A ∀B ∀c ∀d. (((Fin(A,B) ∧ S ∈ U(c)) ∧ (S ∈ U(d) ∧ ω ∈ U(d)))
    /// → W(A,B,U(c)) ∈ U(d))` — **step (f)**.
    pub w_in_universe: Thm,
    /// `⊢ ∀A ∀B ∀c. ((Fin⁺(A,B) ∧ S ∈ U(c)) → W(A,B,U(c)) ⊆ T)` — **step (d)**
    /// at the general fibre condition `bnd(B(a))`.
    pub w_sub_tower_bnd: Thm,
    /// `⊢ ∀A ∀B ∀c ∀d. (((Fin⁺(A,B) ∧ S ∈ U(c)) ∧ (S ∈ U(d) ∧ ω ∈ U(d)))
    /// → W(A,B,U(c)) ∈ U(d))` — **step (f)** at the general fibre condition.
    pub w_in_universe_bnd: Thm,
}

impl WMem {
    /// Derive all four.
    ///
    /// `tower_closed` must be [`super::tower_closed`] and `tower_closed_bnd`
    /// [`super::tower_closed_bnd`]; `tower_subset` and `tower_mem` the two
    /// exports of [`super::Inside`], and `sub` the `∀c` form of `C₂` at the
    /// same `lu`. All five are checked to rest on nothing: a hypothetical one
    /// has the conclusion the real one has, so pinning conclusions alone would
    /// let an assumption ride into a theorem advertised as unconditional.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        env: &mut Env,
        wt: &Wtype,
        st: &Stages,
        lu: FnSym,
        omega: &Term,
        tower_closed: &Thm,
        tower_closed_bnd: &Thm,
        tower_subset: &Thm,
        tower_mem: &Thm,
        sub: &Thm,
    ) -> Option<WMem> {
        if [tower_closed, tower_closed_bnd, tower_subset, tower_mem, sub]
            .iter()
            .any(|t| !t.hyps().is_empty())
        {
            return None
        }
        let (w_sub_tower, w_in_universe) =
            derive(env, wt, st, lu, omega, tower_closed, tower_subset, tower_mem, sub)?;
        let (w_sub_tower_bnd, w_in_universe_bnd) =
            derive(env, wt, st, lu, omega, tower_closed_bnd, tower_subset, tower_mem, sub)?;
        Some(WMem { w_sub_tower, w_in_universe, w_sub_tower_bnd, w_in_universe_bnd })
    }
}

/// Steps (d) and (f) over whatever fibre condition `tower_closed`'s antecedent
/// carries — the antecedent is read off it and never inspected, which is why
/// one derivation serves both forms.
#[allow(clippy::too_many_arguments)]
fn derive(
    env: &mut Env,
    wt: &Wtype,
    st: &Stages,
    lu: FnSym,
    omega: &Term,
    tower_closed: &Thm,
    tower_subset: &Thm,
    tower_mem: &Thm,
    sub: &Thm,
) -> Option<(Thm, Thm)> {
    let tower = st.tower_set();
    let seed = Term::var(st.seed);

    let (av, bv, cv, dv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) =
        (Term::var(av), Term::var(bv), Term::var(cv), Term::var(dv));
    let uc = Term::apply(lu, vec![tc.clone()]);
    let ud = Term::apply(lu, vec![td.clone()]);
    let w = wt.of(ta.clone(), tb.clone(), uc.clone());

    // ── (d) ─────────────────────────────────────────────────────────────
    let closed_at = inst_all(tower_closed, &[ta.clone(), tb.clone()])?;
    let (fin, closed) = closed_at.concl().as_imp()?;
    let s_uc = Formula::mem(seed.clone(), uc.clone());
    let h1 = Formula::and(fin.clone(), s_uc.clone());
    let h1_closed = hyp_mp(
        &a1i(&closed_at, h1.clone()),
        &and_left(fin.clone(), s_uc.clone()),
    )?;
    let h1_sub = hyp_mp(
        &a1i(&inst_all(tower_subset, std::slice::from_ref(&tc))?, h1.clone()),
        &and_right(fin, s_uc),
    )?;

    let wi = inst_all(&wt.w_induction, &[ta.clone(), tb.clone(), uc, tower.clone()])?;
    let sub_form = kernel::thm::subset(env, tower.clone(), Term::apply(lu, vec![tc.clone()]));
    if wi.concl().as_imp()?.0 != Formula::and(sub_form, closed) {
        return None
    }
    let d = hyp_mp(&a1i(&wi, h1.clone()), &hyp_and(&h1_sub, &h1_closed)?)?;
    let w_sub = kernel::thm::subset(env, w.clone(), tower.clone());
    if *d.concl() != Formula::imp(h1.clone(), w_sub.clone()) {
        return None
    }
    let w_sub_tower = gen_all(&[av, bv, cv], &d);

    // ── (f) ─────────────────────────────────────────────────────────────
    let s_ud = Formula::mem(seed, ud.clone());
    let om_ud = Formula::mem(omega.clone(), ud.clone());
    let size = Formula::and(s_ud, om_ud);
    let h = Formula::and(h1.clone(), size.clone());
    let h_d = syl(&and_left(h1.clone(), size.clone()), &d)?;
    let h_tower = hyp_mp(
        &a1i(&inst_all(tower_mem, std::slice::from_ref(&td))?, h.clone()),
        &and_right(h1, size),
    )?;
    let sub_at = inst_all(sub, &[td.clone(), tower])?;
    let f = hyp_mp(
        &hyp_inst(&hyp_mp(&a1i(&sub_at, h.clone()), &h_tower)?, std::slice::from_ref(&w))?,
        &h_d,
    )?;
    if *f.concl() != Formula::imp(h, Formula::mem(w, ud)) {
        return None
    }
    Some((w_sub_tower, gen_all(&[av, bv, cv, dv], &f)))
}
