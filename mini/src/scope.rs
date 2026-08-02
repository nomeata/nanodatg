//! Binder open and close — the hypothesis discipline (MINI-DESIGN.md §4).
//!
//! # Interface
//!
//! **This is the only module that names `Thm::assume` or `Thm::implies_intr`**
//! (invariant I1). Everything else obtains a hypothesis by asking an open
//! [`Scope`] for the one it already holds.
//!
//! Mini-lean's `openType` pushes a type on the telescope. Mini's counterpart
//! also acquires the typing hypothesis, once, at the open:
//!
//! ```text
//!   open   ⟦A⟧ = dom      →   w fresh,  hyp = w ∈ dom,  assumed = {hyp} ⊢ hyp
//!   under the binder      →   ⟦bvar 0⟧ = w   and its typing is `assumed`
//!   close                 →   Γ ∪ {hyp} ⊢ φ   ↦   Γ ⊢ ∀w. (w ∈ dom → φ)
//! ```
//!
//! The typing of `bvar i` is therefore a stored theorem, at **zero derivation
//! cost and with no acquisition per consumer** — which is the whole point of
//! the sequent judgement, and what replaces nanoda's `local_premises` guessing
//! and its `CondEq`/`guard_and_generalise_at` layer. [`Closed::discharge`] *is*
//! `guard_and_generalise_at`, performed by two kernel rules instead of a
//! formula-surgery module.
//!
//! The `∀w. (w ∈ A → φ)` shape `discharge` produces is the shape the library
//! consumes: `lam_in_funspace_n`, `lam_in_dprod_n`, `lam_ext_n`, `dprod_ext_n`,
//! `cond_ext_n` and `prop::cond_intro` all take their under-the-binder premise
//! in exactly this form. Nothing is ever re-proved against a merged hypothesis
//! set.
//!
//! # R6′, the enforceable invariant
//!
//! * **I1 — single introduction point.** `Thm::assume` / `Thm::implies_intr`
//!   appear only here. Grep-enforceable with a path allowlist, exactly as
//!   `ci/check-boundary.sh` rule 6 is a path ban today. (Rule 6 does not scan
//!   `mini/`, so it does not fire on this file; if the scan is ever widened,
//!   this module is the allowlist entry.)
//! * **I2 — hypotheses are scoped.** At every point of execution,
//!   `thm.hyps() ⊆ {hyp of each open scope}`, and scopes are opened and closed
//!   LIFO. Enforced by [`ScopeToken`] being neither `Clone` nor `Copy` and
//!   being consumed by [`Scopes::close`], by that method's LIFO assertion, and
//!   by [`Scopes::hyps_are_scoped`] as a `debug_assert` at the close.
//! * **I3 — no panicking generalisation.** `Thm::gen` is never called; the
//!   fallible [`kernel::Thm::gen_checked`] is the only entry, and its `None` is
//!   reported as an internal error rather than a user-visible rejection,
//!   because by I2 it cannot happen.
//! * **I4 — persistence requires emptiness.** See [`crate::ev::Sealed`].
//!
//! # Why `gen_checked` cannot fail here
//!
//! `w` is minted fresh at the open, so it occurs in no other scope's
//! hypothesis. `discharge` first removes this scope's own hypothesis with
//! `implies_intr`; whatever remains in `Γ` belongs to strictly outer scopes by
//! I2, and none of them mention `w`. The `Result` is therefore an assertion
//! with a message, not a control-flow path.

use crate::ev::{Ev, Gap};
use kernel::{Env, Formula, FreeVar, Term, Thm};

/// One open binder.
#[derive(Debug, Clone)]
pub struct Scope {
    /// `⟦A⟧`, the interpreted domain, computed once at the open.
    dom: Term,
    /// The kernel variable interpreting `bvar 0` under this scope.
    w: FreeVar,
    /// `w ∈ ⟦A⟧`.
    hyp: Formula,
    /// `{w ∈ ⟦A⟧} ⊢ w ∈ ⟦A⟧`.
    assumed: Thm,
}

impl Scope {
    pub fn var(&self) -> FreeVar { self.w }
    pub fn term(&self) -> Term { Term::var(self.w) }
    pub fn domain(&self) -> &Term { &self.dom }
    pub fn hyp(&self) -> &Formula { &self.hyp }
    /// The typing of `bvar 0` under this scope: `Γ ⊢ w ∈ ⟦A⟧`, already proved.
    pub fn assumption(&self) -> &Thm { &self.assumed }
}

/// Proof that a scope was opened, and the obligation to close it.
///
/// Neither `Clone` nor `Copy`, and consumed by [`Scopes::close`], so a scope
/// cannot be closed twice and cannot be forgotten silently.
#[derive(Debug)]
pub struct ScopeToken {
    /// The stack depth *below* this scope; closing requires it to be the top.
    depth: usize,
    /// Blocks `Clone`/`Copy` from ever being derived by accident, and blocks
    /// `Send`, which is what would let a token escape to another thread.
    _not_clone: std::marker::PhantomData<*const ()>,
}

/// A scope that has been popped, holding what discharging needs.
#[derive(Debug, Clone)]
pub struct Closed {
    scope: Scope,
}

impl Closed {
    /// From `Γ ∪ {w ∈ ⟦A⟧} ⊢ φ` produce `Γ ⊢ ∀w. (w ∈ ⟦A⟧ → φ)`.
    ///
    /// `Err` is an internal error (I2 makes it unreachable), never a rejection
    /// of the input file.
    pub fn discharge(&self, thm: &Thm) -> Result<Thm, String> {
        let imp = Thm::implies_intr(&self.scope.hyp, thm);
        Thm::gen_checked(self.scope.w, &imp).ok_or_else(|| {
            format!(
                "scope discipline violated (I2): the bound variable is free in a \
                 remaining hypothesis after discharging {:?}; remaining Γ has {} formula(s)",
                self.scope.hyp,
                imp.hyps().len()
            )
        })
    }

    /// [`Closed::discharge`] on an [`Ev`], propagating a gap unchanged.
    pub fn discharge_ev(&self, ev: Ev) -> Result<Ev, String> {
        match ev {
            Ev::Proved(t) => self.discharge(&t).map(Ev::Proved),
            Ev::Gap(g) => Ok(Ev::Gap(g)),
        }
    }

    pub fn scope(&self) -> &Scope { &self.scope }
    pub fn assumption(&self) -> &Thm { &self.scope.assumed }
    pub fn var(&self) -> FreeVar { self.scope.w }
    pub fn domain(&self) -> &Term { &self.scope.dom }
}

/// The LIFO stack of open binders. `stack.last()` is `bvar 0`.
#[derive(Debug, Default)]
pub struct Scopes {
    stack: Vec<Scope>,
}

impl Scopes {
    pub fn new() -> Scopes { Scopes::default() }

    pub fn len(&self) -> usize { self.stack.len() }
    pub fn is_empty(&self) -> bool { self.stack.is_empty() }

    /// `⟦bvar i⟧` and its typing. `None` when `i` is out of range, which is a
    /// malformed expression rather than a scope error.
    pub fn get(&self, i: u32) -> Option<&Scope> {
        let n = self.stack.len();
        if (i as usize) < n {
            Some(&self.stack[n - 1 - i as usize])
        } else {
            None
        }
    }

    /// The typing of `bvar i`: the scope's own `assume`d theorem, at zero cost.
    pub fn typing_of_bvar(&self, i: u32) -> Ev {
        match self.get(i) {
            Some(s) => Ev::Proved(s.assumption().clone()),
            // A `bvar` with no scope cannot arise from a well-formed
            // expression; the shape zone is the only caller that can be under
            // symbolic levels with no interpretation to open against.
            None => Ev::missing(Gap::SymbolicLevel),
        }
    }

    /// `openType`: mint `w`, assume `w ∈ dom`, push.
    ///
    /// **The one call to `Thm::assume` in the whole program.**
    pub fn open(&mut self, env: &mut Env, dom: Term) -> ScopeToken {
        let w = env.fresh_var();
        let hyp = Formula::mem(Term::var(w), dom.clone());
        let assumed = Thm::assume(hyp.clone());
        let depth = self.stack.len();
        self.stack.push(Scope { dom, w, hyp, assumed });
        ScopeToken { depth, _not_clone: std::marker::PhantomData }
    }

    /// Pop. The token forces pairing; the assertion forces LIFO order.
    pub fn close(&mut self, tok: ScopeToken) -> Closed {
        assert_eq!(
            tok.depth + 1,
            self.stack.len(),
            "scopes must be closed innermost-first (I2): closing the scope at depth {} while {} \
             are open",
            tok.depth,
            self.stack.len()
        );
        let scope = self.stack.pop().expect("token implies a scope");
        Closed { scope }
    }

    /// The hypotheses I2 permits a live `Thm` to carry.
    pub fn open_hyps(&self) -> Vec<&Formula> { self.stack.iter().map(|s| &s.hyp).collect() }

    /// I2, as a predicate: `thm.hyps() ⊆ {hyp of each open scope}`.
    ///
    /// Checked with `debug_assert` at every close rather than on every rule,
    /// because a violation can only be *introduced* by an `assume` and can only
    /// be *observed* once the introducing scope is gone.
    pub fn hyps_are_scoped(&self, thm: &Thm) -> bool {
        thm.hyps().iter().all(|h| self.stack.iter().any(|s| &s.hyp == h))
    }

    /// Close and check I2 of the theorem being discharged, in one step. This is
    /// the pairing every caller in the checker should use.
    pub fn close_checked(&mut self, tok: ScopeToken, thm: &Thm) -> Closed {
        let closed = self.close(tok);
        debug_assert!(
            {
                let outer = Thm::implies_intr(closed.scope.hyp(), thm);
                self.hyps_are_scoped(&outer)
            },
            "I2 violated: a theorem carries a hypothesis belonging to no open scope"
        );
        closed
    }
}

/// The one sanctioned use of `Thm::assume` outside [`Scopes::open`]: tests in
/// sibling modules that need a hypothetical theorem to pin a guard against.
/// Keeping it here keeps I1 a single-file property.
#[cfg(test)]
pub(crate) mod test_support {
    use kernel::{Formula, Thm};
    pub(crate) fn assume(phi: Formula) -> Thm { Thm::assume(phi) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::Term;

    fn dom(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

    /// The shape `discharge` produces is the shape the library consumes.
    #[test]
    fn discharge_produces_the_forall_arrow_shape() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let tok = sc.open(&mut env, a.clone());
        let w = sc.get(0).unwrap().var();
        // Under the binder, the typing of `bvar 0` is free.
        let body = sc.typing_of_bvar(0);
        let body = body.thm().unwrap().clone();
        assert_eq!(body.concl(), &Formula::mem(Term::var(w), a.clone()));
        assert_eq!(body.hyps().len(), 1);

        let closed = sc.close_checked(tok, &body);
        let out = closed.discharge(&body).unwrap();
        assert!(out.hyps().is_empty(), "discharging the only scope must empty Γ");
        let hyp = Formula::mem(Term::var(w), a);
        assert_eq!(out.concl(), &Formula::forall(w, Formula::imp(hyp.clone(), hyp)));
    }

    /// Nested scopes discharge to a nested `∀`-`→` family, and the inner
    /// hypothesis does not leak past its own close.
    #[test]
    fn nested_scopes_discharge_outwards() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let b = dom(&mut env);
        let t1 = sc.open(&mut env, a.clone());
        let t2 = sc.open(&mut env, b.clone());
        let (x, y) = (sc.get(1).unwrap().var(), sc.get(0).unwrap().var());
        // A theorem mentioning both hypotheses: `{x∈A, y∈B} ⊢ y∈B`.
        let inner = sc.get(0).unwrap().assumption().clone();
        let both = Thm::mp(
            &Thm::implies_intr(sc.get(1).unwrap().hyp(), &inner),
            sc.get(1).unwrap().assumption(),
        )
        .expect("mp");
        assert_eq!(both.hyps().len(), 2);
        assert!(sc.hyps_are_scoped(&both));

        let c2 = sc.close_checked(t2, &both);
        let step = c2.discharge(&both).unwrap();
        assert_eq!(step.hyps().len(), 1, "only the outer hypothesis may remain");
        assert!(sc.hyps_are_scoped(&step));

        let c1 = sc.close_checked(t1, &step);
        let done = c1.discharge(&step).unwrap();
        assert!(done.hyps().is_empty());
        // `⊢ ∀x. (x ∈ A → ∀y. (y ∈ B → y ∈ B))` — the nested `∀`-`→` family the
        // n-ary lemmas take as their under-the-binder premise.
        let hy = Formula::mem(Term::var(y), b);
        let hx = Formula::mem(Term::var(x), a);
        let expected =
            Formula::forall(x, Formula::imp(hx, Formula::forall(y, Formula::imp(hy.clone(), hy))));
        assert_eq!(done.concl(), &expected);
    }

    /// I2's LIFO half. Closing an outer scope while an inner one is open is a
    /// programming error, not a rejection, so it aborts.
    #[test]
    #[should_panic(expected = "innermost-first")]
    fn closing_out_of_order_is_caught() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let b = dom(&mut env);
        let t1 = sc.open(&mut env, a);
        let _t2 = sc.open(&mut env, b);
        let _ = sc.close(t1);
    }

    /// The `bvar` typing costs one vector index and no derivation — the case
    /// that is 5 186 of nanoda's `has_type` misses.
    #[test]
    fn bvar_typing_is_the_stored_assumption() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let b = dom(&mut env);
        let t1 = sc.open(&mut env, a.clone());
        let t2 = sc.open(&mut env, b.clone());
        // `bvar 0` is the innermost, `bvar 1` the next one out.
        assert_eq!(sc.get(0).unwrap().domain(), &b);
        assert_eq!(sc.get(1).unwrap().domain(), &a);
        assert_eq!(
            sc.typing_of_bvar(1).thm().unwrap().concl(),
            &Formula::mem(Term::var(sc.get(1).unwrap().var()), a)
        );
        assert!(sc.typing_of_bvar(2).gap().is_some(), "an out-of-range bvar has no typing");
        let _ = sc.close(t2);
        let _ = sc.close(t1);
    }

    /// Gaps ride through the close untouched: a missing derivation under a
    /// binder must not become a *different* missing derivation outside it.
    #[test]
    fn discharge_propagates_a_gap() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let tok = sc.open(&mut env, a);
        let closed = sc.close(tok);
        let out = closed.discharge_ev(Ev::missing(Gap::FunEta)).unwrap();
        assert_eq!(out.gap(), Some(&Gap::FunEta));
    }
}
