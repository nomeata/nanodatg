//! Binder open and close — the hypothesis discipline for `checker/`.
//!
//! # Interface
//!
//! **This is the only module in `checker/` that names `Thm::assume` or
//! `Thm::implies_intr`** (invariant I1, checked by `ci/check-boundary.sh`).
//! Everything else obtains a hypothesis by asking an open [`Scope`] for the one
//! it already holds.
//!
//! ```text
//!   open   ⟦A⟧ = dom      →   w fresh,  hyp = w ∈ dom,  assumed = {hyp} ⊢ hyp
//!   under the binder      →   the local's typing *is* `assumed`
//!   close                 →   Γ ∪ {hyp} ⊢ φ   ↦   Γ ⊢ ∀w. (w ∈ dom → φ)
//! ```
//!
//! [`Closed::discharge`] produces the `∀w. (w ∈ A → φ)` shape the library
//! consumes: `lam_in_funspace_n`, `lam_in_dprod_n`, `lam_ext_n`, `dprod_ext_n`,
//! `cond_ext_n` and `prop::cond_intro` all take their under-the-binder premise
//! in exactly that form.
//!
//! # Status: no production caller yet, and that is deliberate
//!
//! `tg.rs` today expresses an assumption as an **antecedent inside the formula**
//! (`CondEq`: `⊢ conj(h⃗) → a = b`, with a ledger counting the ones that escape
//! to a boundary undischarged). That is a complete and working scheme, and this
//! module does not change it. It exists because the evidence-threading work that
//! follows replaces the antecedent surgery with the sequent's own `Γ`, and
//! because `ci/check-boundary.sh` R6′ needs a named place for the introduction
//! rule to live — a ban with no sanctioned alternative is what made rule 6 wrong.
//!
//! Nothing here is speculative in shape: it is a port of `mini/src/scope.rs`,
//! which drives mini's interpreter over the same corpus. The duplication is
//! real and is not ideal — the natural shared home is `derived/`, which models
//! type theory and knows nothing of Lean syntax — but `checker` does not depend
//! on `mini`, and moving it into `derived/` is a change to a crate this work is
//! not allowed to touch. Collapse the two when both are in one pair of hands.
//!
//! # R6′, the enforceable invariant
//!
//! * **I1 — single introduction point.** `Thm::assume` / `Thm::implies_intr`
//!   appear only here. Grep-enforced with a path allowlist.
//! * **I2 — hypotheses are scoped.** At every point of execution,
//!   `thm.hyps() ⊆ {hyp of each open scope}`, and scopes are opened and closed
//!   LIFO. Enforced by [`ScopeToken`] being neither `Clone` nor `Copy` and being
//!   consumed by [`Scopes::close`], by that method's LIFO assertion, and by
//!   [`Scopes::hyps_are_scoped`] as a `debug_assert` at the close.
//! * **I3 — no panicking generalisation.** `Thm::gen` is called nowhere in this
//!   crate; [`kernel::Thm::gen_checked`] is the only entry. Grep-enforced.
//! * **I4 — persistence requires emptiness.** See [`crate::sealed::Sealed`].
//!
//! # Why `gen_checked` cannot fail here
//!
//! `w` is minted fresh at the open, so it occurs in no other scope's hypothesis.
//! `discharge` first removes this scope's own hypothesis with `implies_intr`;
//! whatever remains in `Γ` belongs to strictly outer scopes by I2, and none of
//! them mention `w`. The `Result` is therefore an assertion with a message, not
//! a control-flow path.

use kernel::{Env, Formula, FreeVar, Term, Thm};

/// One open binder.
#[derive(Debug, Clone)]
pub struct Scope {
    /// `⟦A⟧`, the interpreted domain, computed once at the open.
    dom: Term,
    /// The kernel variable interpreting the bound occurrence under this scope.
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
    /// The typing of the bound occurrence: `Γ ⊢ w ∈ ⟦A⟧`, already proved.
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
                "scope discipline violated (I2): the bound variable is free in a remaining \
                 hypothesis after discharging {:?}; remaining Γ has {} formula(s)",
                self.scope.hyp,
                imp.hyps().len()
            )
        })
    }

    pub fn scope(&self) -> &Scope { &self.scope }
    pub fn assumption(&self) -> &Thm { &self.scope.assumed }
    pub fn var(&self) -> FreeVar { self.scope.w }
    pub fn domain(&self) -> &Term { &self.scope.dom }
}

/// The LIFO stack of open binders. `stack.last()` is the innermost.
#[derive(Debug, Default)]
pub struct Scopes {
    stack: Vec<Scope>,
}

impl Scopes {
    pub fn new() -> Scopes { Scopes::default() }

    pub fn len(&self) -> usize { self.stack.len() }
    pub fn is_empty(&self) -> bool { self.stack.is_empty() }

    /// The `i`-th scope counted from the innermost. `None` when `i` is out of
    /// range, which is a malformed expression rather than a scope error.
    pub fn get(&self, i: usize) -> Option<&Scope> {
        let n = self.stack.len();
        if i < n {
            Some(&self.stack[n - 1 - i])
        } else {
            None
        }
    }

    /// Mint `w`, assume `w ∈ dom`, push.
    ///
    /// **The one call to `Thm::assume` in the whole crate.**
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
    /// the pairing every caller should use.
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

    fn dom(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

    /// The shape `discharge` produces is the shape the library consumes.
    #[test]
    fn discharge_produces_the_forall_arrow_shape() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let tok = sc.open(&mut env, a.clone());
        let w = sc.get(0).unwrap().var();
        let body = sc.get(0).unwrap().assumption().clone();
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
        // `{x∈A, y∈B} ⊢ y∈B`, a theorem mentioning both hypotheses.
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

    /// A scope's assumption is a *hypothetical* theorem, and therefore is not
    /// something a store may keep. This is the join between I1 and I4.
    #[test]
    fn a_scopes_assumption_does_not_seal() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let tok = sc.open(&mut env, a);
        let assumed = sc.get(0).unwrap().assumption().clone();
        assert!(crate::sealed::Sealed::new(assumed.clone()).is_err());
        let closed = sc.close_checked(tok, &assumed);
        let discharged = closed.discharge(&assumed).unwrap();
        assert!(
            crate::sealed::Sealed::new(discharged).is_ok(),
            "once discharged it is unconditional, and may be stored"
        );
    }
}
