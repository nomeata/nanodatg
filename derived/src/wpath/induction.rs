//! **P2** — `paths` is the least set closed under the two path rules.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀Q ∀C. ((C ⊆ Bnd ∧ path_closed(C)) → ∀p. (p ∈ paths → p ∈ C))
//!                                                          [paths_induction]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why this is short and P1 is not
//!
//! This is the half of the intersection that comes for free, exactly as
//! [`crate::acc::acc_induction`] and [`crate::wtype::w_induction`] are:
//! `p ∈ paths` unfolds to `p ∈ Bnd ∧ ∀C. ((C ⊆ Bnd ∧ path_closed(C)) → p ∈ C)`,
//! so `paths ⊆ C` at a closed `C ⊆ Bnd` is one instantiation of that inner `∀C`
//! at this very `C`. All the work is in the other direction —
//! [`super::paths_intro`] — where the conclusion of each rule has to be shown to
//! lie in every closed subset at once.
//!
//! It is nevertheless the workhorse: [`super::paths_inversion`] is this lemma at
//! `C := { p ∈ paths : p arises from a rule }`, and that is the only nontrivial
//! consumer in the module.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::wtype::Wtype;
use crate::{and_right, com12, gen_all, iff_mp, inst_all, syl};

use super::condition::{path_closed, path_cond, At};

/// **P2, induction.**
/// `⊢ ∀A ∀B ∀u ∀Q ∀C. ((C ⊆ Bnd ∧ path_closed(C)) → ∀p. (p ∈ paths → p ∈ C))`
///
/// Immediate from the definition: `C` is one of the sets being intersected, so
/// the condition carried by every member of `paths` applies at `C`. The whole
/// proof is one universal instantiation plus a swap of antecedents.
///
/// `paths_ax` must **establish** the defining biconditional: its conclusion is
/// pinned below, and it must be unconditional, because this header promises
/// `⊢ …` and every step after the instantiation would otherwise union a `Γ` in.
pub fn paths_induction(
    env: &mut Env,
    wt: &Wtype,
    paths: FnSym,
    paths_ax: &Thm,
) -> Option<Thm> {
    if !paths_ax.hyps().is_empty() {
        return None
    }
    let s = wt.sums.clone();
    let (av, bv, uv, qv, cv, pv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let (tc, tp) = (Term::var(cv), Term::var(pv));

    let cond = path_cond(env, &s, &at, &tp);
    let mem_bnd = Formula::mem(tp.clone(), at.bnd.clone());
    let term = Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);
    let mem_paths = Formula::mem(tp.clone(), term);

    let ax = inst_all(
        paths_ax,
        &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), tp.clone()],
    )?;
    if *ax.concl() != Formula::iff(mem_paths.clone(), Formula::and(mem_bnd.clone(), cond.clone()))
    {
        return None
    }
    let to_cond = syl(&iff_mp(&ax)?, &and_right(mem_bnd, cond.clone()))?;

    let h = Formula::and(
        kernel::thm::subset(env, tc.clone(), at.bnd.clone()),
        path_closed(env, &s, &at, &tc),
    );
    let mem_c = Formula::mem(tp.clone(), tc.clone());

    // The condition, instantiated at `C` — the entire content of P2.
    let cond_at = Thm::ax_inst(cond, tc)?;
    let (_, body) = cond_at.concl().as_imp()?;
    if body != Formula::imp(h.clone(), mem_c.clone()) {
        return None
    }

    let h_p = com12(&syl(&to_cond, &cond_at)?)?;
    let out = Thm::mp(
        &Thm::ax_dist(pv, h.clone(), Formula::imp(mem_paths.clone(), mem_c.clone()))?,
        &Thm::gen(pv, &h_p),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::forall(pv, Formula::imp(mem_paths, mem_c))),
        "paths_induction: unexpected shape"
    );
    Some(gen_all(&[av, bv, uv, qv, cv], &out))
}
