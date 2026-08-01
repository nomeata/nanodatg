//! **A2** — `acc(A,R)` is the least step-closed subset of `A`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀R ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → ∀z. (z ∈ acc(A,R) → z ∈ C))
//!                                                            [acc_induction]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why this is short and A1 is not
//!
//! This is the half of the intersection that comes for free, exactly as
//! [`crate::wtype::w_induction`] is. `z ∈ acc(A,R)` unfolds to
//! `z ∈ A ∧ ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → z ∈ C)`, so `acc ⊆ C` for a
//! step-closed `C ⊆ A` is one instantiation of that inner `∀C` at this very
//! `C`. All the work of the intersection is in the other direction —
//! [`crate::acc::acc_intro`] — where `x` has to be shown to lie in every
//! step-closed subset at once.
//!
//! This is nevertheless the workhorse: [`crate::acc::acc_rect`]'s well-founded
//! induction is this lemma applied to `{z ∈ acc : φ(z)}`, and
//! [`crate::acc::acc_intro`] uses it to move the induction hypothesis from
//! `acc` into an arbitrary `C`.
//!
//! **No `C ⊆ acc` antecedent**: `C` need only be a step-closed subset of `A`.
//! Everything downstream nonetheless instantiates it at a subset of `acc`,
//! because that is what makes `step_closed(A,R,C)` provable.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::{and_right, com12, gen_all, iff_mp, inst_all, syl};

use super::condition::{acc_cond, step_closed};

/// **A2, induction.**
/// `⊢ ∀A ∀R ∀C. ((C ⊆ A ∧ step_closed(A,R,C)) → ∀z. (z ∈ acc(A,R) → z ∈ C))`
///
/// Immediate from the definition: `C` is one of the sets being intersected, so
/// the condition carried by every member of `acc(A,R)` applies at `C`. The
/// whole proof is one universal instantiation plus a swap of antecedents.
///
/// `acc_ax` must **establish** the defining biconditional: its conclusion is
/// pinned below, and it must be unconditional, because this header promises
/// `⊢ …` and every step after the instantiation is a [`crate::syl`] or a
/// [`Thm::mp`], each of which would silently union the caller's `Γ` in.
pub fn acc_induction(env: &mut Env, up: FnSym, acc: FnSym, acc_ax: &Thm) -> Option<Thm> {
    if !acc_ax.hyps().is_empty() {
        return None
    }
    let (av, rv, cv, z) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tc, tz) = (Term::var(av), Term::var(rv), Term::var(cv), Term::var(z));

    let cond = acc_cond(env, up, &ta, &tr, &tz);
    let mem_a = Formula::mem(tz.clone(), ta.clone());
    let acc_t = Term::apply(acc, vec![ta.clone(), tr.clone()]);
    let mem_acc = Formula::mem(tz.clone(), acc_t);

    let at = inst_all(acc_ax, &[ta.clone(), tr.clone(), tz.clone()])?;
    if *at.concl() != Formula::iff(mem_acc.clone(), Formula::and(mem_a.clone(), cond.clone())) {
        return None
    }
    let to_cond = syl(&iff_mp(&at)?, &and_right(mem_a, cond.clone()))?;

    let h = Formula::and(
        kernel::thm::subset(env, tc.clone(), ta.clone()),
        step_closed(env, up, &ta, &tr, &tc),
    );
    let mem_c = Formula::mem(tz.clone(), tc.clone());

    // The condition, instantiated at `C` — this is the entire content of A2.
    let cond_at = Thm::ax_inst(cond, tc)?;
    let (_, body) = cond_at.concl().as_imp()?;
    if body != Formula::imp(h.clone(), mem_c.clone()) {
        return None
    }

    let h_z = com12(&syl(&to_cond, &cond_at)?)?;
    let out = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(mem_acc.clone(), mem_c.clone()))?,
        &Thm::gen(z, &h_z),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::forall(z, Formula::imp(mem_acc, mem_c))),
        "acc_induction: unexpected shape"
    );
    Some(gen_all(&[av, rv, cv], &out))
}
