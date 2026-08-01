//! **Step 3 — W2**: the W-type is the least closed subset of its bound.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀C. ((C ⊆ u ∧ closed(A,B,C)) → W(A,B,u) ⊆ C)          [w_induction]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why this is short and W1 is not
//!
//! This is the half of the intersection that comes for free. `z ∈ W(A,B,u)`
//! unfolds to `z ∈ u ∧ ∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S)`, so `W ⊆ C` for a
//! closed `C ⊆ u` is one instantiation of that inner `∀S` at `S := C`. All the
//! work of the intersection is in the *other* direction —
//! [`super::sup_mem`] — where `⟨a,f⟩` has to be shown to lie in every closed
//! subset at once.
//!
//! W2 is nonetheless the workhorse of everything downstream: [`super::rect`]'s
//! structural induction is this lemma applied to the set of `z` satisfying the
//! induction predicate, and [`super::inversion`]'s W3 applies it to the set of
//! `z` that are `sup`s.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::sums::Sums;
use crate::{and_right, com12, gen_all, iff_mp, inst_all, syl};

use super::condition::{closed, w_cond};

/// **W2, induction.**
/// `⊢ ∀A ∀B ∀u ∀C. ((C ⊆ u ∧ closed(A,B,C)) → ∀z. (z ∈ W(A,B,u) → z ∈ C))`
///
/// Immediate from the definition: `C` is one of the sets being intersected, so
/// the condition carried by every member of `W(A,B,u)` applies at `C`. The
/// whole proof is one universal instantiation plus a swap of antecedents.
///
/// **No `C ⊆ W` antecedent**, which matters: `C` need only be a closed subset
/// of the *bound*. Everything downstream — [`crate::wtype::w_inversion`] and [`crate::wtype::w_rect`] —
/// nonetheless instantiates it at a subset of `W`, because that is what makes
/// `closed(A,B,C)` provable; see the note on [`crate::wtype::w_inversion`].
pub fn w_induction(env: &mut Env, s: &Sums, w: FnSym, w_ax: &Thm) -> Option<Thm> {
    let (av, bv, uv, cv, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tc, tz) =
        (Term::var(av), Term::var(bv), Term::var(uv), Term::var(cv), Term::var(z));

    let cond = w_cond(env, s, &ta, &tb, &tu, &tz);
    let mem_u = Formula::mem(tz.clone(), tu.clone());
    let w_t = Term::apply(w, vec![ta.clone(), tb.clone(), tu.clone()]);
    let mem_w = Formula::mem(tz.clone(), w_t);

    let at = inst_all(w_ax, &[ta.clone(), tb.clone(), tu.clone(), tz.clone()])?;
    if *at.concl() != Formula::iff(mem_w.clone(), Formula::and(mem_u.clone(), cond.clone())) {
        return None
    }
    let to_cond = syl(&iff_mp(&at)?, &and_right(mem_u, cond.clone()))?;

    let h = Formula::and(
        kernel::thm::subset(env, tc.clone(), tu.clone()),
        closed(env, s, &ta, &tb, &tc),
    );
    let mem_c = Formula::mem(tz.clone(), tc.clone());

    // The condition, instantiated at `C` — this is the entire content of W2.
    let cond_at = Thm::ax_inst(cond, tc)?;
    let (_, body) = cond_at.concl().as_imp()?;
    if body != Formula::imp(h.clone(), mem_c.clone()) {
        return None
    }

    let h_z = com12(&syl(&to_cond, &cond_at)?)?;
    let out = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(mem_w.clone(), mem_c.clone()))?,
        &Thm::gen(z, &h_z),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::forall(z, Formula::imp(mem_w, mem_c))),
        "w_induction: unexpected shape"
    );
    Some(gen_all(&[av, bv, uv, cv], &out))
}
