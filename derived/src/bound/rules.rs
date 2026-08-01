//! **Step 6** — the three W-type rules, with the bound antecedent gone.
//!
//! # Interface
//!
//! Write `T(A,B,c)` for `A ∈ U(c) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(c))` — the typing
//! side conditions any caller has anyway — and `W` for `W(A,B,U(c))`:
//!
//! ```text
//! ⊢ ∀c ∀A ∀B. (T(A,B,c) → ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W) → ⟨a,f⟩ ∈ W)))  [sup_mem_at]
//! ⊢ ∀c ∀A ∀B. (T(A,B,c) → ∀w. (w ∈ W → ∃a. (a ∈ A ∧ ∃f. (…))))             [w_inversion_at]
//! ⊢ T(A,B,c) → (ind_step → ∀z. (z ∈ W → φ(z)))                             [w_rect_at]
//! ```
//!
//! [`At`] bundles the terms and theorems each of them needs;
//! [`discharge_closed`] is the single move all three share. Callers need none
//! of the derivations below.
//!
//! # What this file actually does
//!
//! Nothing new is derived. [`crate::wtype`] proves all three rules with
//! `closed(A,B,u)` as an explicit antecedent, and
//! [`super::least_universe_closed`] proves that antecedent at `u := U(c)` from
//! `T(A,B,c)`. Each rule here is therefore one composition — that is
//! [`discharge_closed`] — and the value is in the *statement*, not the proof:
//! the caller is left holding only conditions it can discharge.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};
use crate::sums::Sums;
use crate::wtype::{closed, Wtype};
use crate::{gen_all, inst_all, syl};

use super::closure::fibres_in;

/// From `⊢ closed(A,B,U(c)) → φ` infer
/// `⊢ (A ∈ U(c) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(c))) → φ`.
///
/// The one move that turns a conditional W-type rule into an unconditional
/// one. The antecedent of `thm` is checked to be `closed(A,B,U(c))` on the
/// nose — a theorem about some other bound, or about some other `A` and `B`,
/// is rejected rather than mis-discharged.
/// The three terms every rule here is stated at: the universe seed `c`, and the
/// W-type's `A` and `B`.
///
/// Bundled because they always travel together, and because passing them
/// positionally is how a rule ends up proved about the wrong `A`.
pub struct At<'t> {
    /// The seed of the least universe `U(c)`.
    pub c: &'t Term,
    /// The W-type's index set `A`.
    pub a: &'t Term,
    /// The W-type's fibre family `B`.
    pub b: &'t Term,
}

pub fn discharge_closed(
    env: &mut Env,
    s: &Sums,
    lu: FnSym,
    least_closed: &Thm,
    at: &At<'_>,
    thm: &Thm,
) -> Option<Thm> {
    let (c, a, b) = (at.c, at.a, at.b);
    if lu.arity() != 1 {
        return None
    }
    let w = Term::apply(lu, vec![c.clone()]);
    let (ante, _) = thm.concl().as_imp()?;
    if ante != closed(env, s, a, b, &w) {
        return None
    }
    let lc = inst_all(least_closed, &[c.clone(), a.clone(), b.clone()])?;
    let want = Formula::and(Formula::mem(a.clone(), w.clone()), fibres_in(env, s, a, b, &w));
    if *lc.concl() != Formula::imp(want, ante) {
        return None
    }
    syl(&lc, thm)
}

/// **W1, unconditionally.**
/// `⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a. (a ∈ A → B(a) ∈ U(c)))
///      → ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), W(A,B,U(c))) → ⟨a,f⟩ ∈ W(A,B,U(c)))))`
///
/// [`crate::wtype::sup_mem`] at `u := U(c)`, with its `closed(A,B,u)`
/// antecedent discharged by [`crate::bound::least_universe_closed`]. This is `sup`'s typing
/// rule as a client would want to state it: the hypotheses are that the
/// constructor set and every fibre are sets of the universe, and nothing else.
pub fn sup_mem_at(
    env: &mut Env,
    wt: &Wtype,
    lu: FnSym,
    least_closed: &Thm,
) -> Option<Thm> {
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let inst = inst_all(&wt.sup_mem, &[ta.clone(), tb.clone(), w])?;
    let out = discharge_closed(env, &wt.sums, lu, least_closed, &At { c: &tc, a: &ta, b: &tb }, &inst)?;
    Some(gen_all(&[cv, av, bv], &out))
}

/// **W3, unconditionally.**
/// `⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a. (a ∈ A → B(a) ∈ U(c)))
///      → ∀w. (w ∈ W(A,B,U(c)) → ∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a), W) ∧ w = ⟨a,f⟩))))`
///
/// [`crate::wtype::w_inversion`] at `u := U(c)`. `inversion` must be that
/// theorem — it mints a symbol per call, so it is passed in rather than
/// rebuilt.
pub fn w_inversion_at(
    env: &mut Env,
    wt: &Wtype,
    lu: FnSym,
    least_closed: &Thm,
    inversion: &Thm,
) -> Option<Thm> {
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let inst = inst_all(inversion, &[ta.clone(), tb.clone(), w])?;
    let out = discharge_closed(env, &wt.sums, lu, least_closed, &At { c: &tc, a: &ta, b: &tb }, &inst)?;
    Some(gen_all(&[cv, av, bv], &out))
}

/// **Structural induction, unconditionally.**
///
/// ```text
/// ⊢ (A ∈ U(c) ∧ ∀a. (a ∈ A → B(a) ∈ U(c)))
///     → (ind_step → ∀z. (z ∈ W(A,B,U(c)) → φ(z)))
/// ```
///
/// [`crate::wtype::w_rect`] is a *construction taking a formula* and is stated
/// at caller-chosen variables `A`, `B`, `u`; this replaces `u` by `U(c)`
/// throughout — in `φ` as well, which is why the substitution goes through a
/// generalisation — and discharges the bound. `uv` must be the variable
/// `w_rect` was given as its bound, and `a` and `b` the terms it was given for
/// `A` and `B`.
pub fn w_rect_at(
    env: &mut Env,
    s: &Sums,
    lu: FnSym,
    least_closed: &Thm,
    rect: &Thm,
    uv: FreeVar,
    at: &At<'_>,
) -> Option<Thm> {
    let (c, a, b) = (at.c, at.a, at.b);
    if lu.arity() != 1 || c.occurs_free(uv) || a.occurs_free(uv) || b.occurs_free(uv) {
        return None
    }
    let w = Term::apply(lu, vec![c.clone()]);
    let all_u = Thm::gen(uv, rect);
    let inst = Thm::mp(&Thm::ax_inst(all_u.concl().clone(), w)?, &all_u)?;
    discharge_closed(env, s, lu, least_closed, at, &inst)
}
