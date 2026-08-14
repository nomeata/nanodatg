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
//! # Status: no production caller yet, and the consumer that is named
//!
//! Grepping `checker/` for `crate::scope`, `Scopes`, `ScopeToken`, `Closed`,
//! `discharge`, `hyps_are_scoped` and `open_hyps` finds no caller outside this
//! file except two **tests** reaching for [`test_support::assume`]
//! (`sealed.rs`, `tg.rs`). No shipped code opens a scope.
//!
//! `tg.rs` today expresses an assumption as an **antecedent inside the formula**
//! (`CondEq`: `⊢ conj(h⃗) → a = b`, with a ledger counting the ones that escape
//! to a boundary undischarged), with `guard_and_generalise_at` re-implementing
//! at the formula level exactly what `implies_intr` + `gen` do at the kernel
//! level. That is a complete and working scheme, and this module does not
//! change it.
//!
//! The consumer is named and staged, not hoped for: **THREADING-CENSUS.md §2,
//! stage 1, "binder open/close"** — the stage after the one that landed
//! 2026-08-01 — whose plumbing is "a context stack beside `dbj_level_counter`
//! in `TcCtx` (open pushes `(local, ⟦w⟧ ∈ ⟦A⟧ evidence)`, close pops and
//! discharges), readable by the backend, replacing `local_premises`' term-scan
//! guess", and whose measurable is the escape count. `ci/check-boundary.sh` R6′
//! also needs a named place for the introduction rule to live: it fails if this
//! file stops calling `Thm::assume`, because a ban with no sanctioned
//! alternative is what made rule 6 wrong.
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
//!   LIFO. The **LIFO half** is enforced: [`ScopeToken`] is neither `Clone` nor
//!   `Copy`, [`Scopes::close`] consumes it, and that method asserts the depth.
//!
//!   The **set half is not checked at the close**, and that is a decision, not
//!   an omission. "Each open scope" is a property of the whole execution, not
//!   of the stack being closed: a theorem may legitimately carry a hypothesis
//!   belonging to a *different* [`Scopes`]. Mini measured this on the same code
//!   — it runs about fifteen `Scopes` concurrently, and asserting the subset at
//!   every close fails 19 of its unit tests, all of them correct code
//!   (`mini/src/scope.rs`, `a_discharge_may_carry_another_stacks_hypothesis`).
//!   `checker/` has no production `Scopes` at all yet and so has measured
//!   nothing, which is the weaker position, not the stronger one: putting the
//!   assertion on the close here would assert of stage 1 something stage 1 has
//!   not yet decided. So the checked close is
//!   [`test_support::close_single_stack`], where the precondition — one stack
//!   for the whole derivation — is the caller's to guarantee.
//!
//!   **When stage 1 may promote it back onto [`Scopes::close`]**: if the
//!   context stack lands as exactly one `Scopes` per `TcCtx`, and `derived/`
//!   stays barred from `Thm::assume` by R6′ (so no construction can open a
//!   stack of its own the way mini's do), then checker really is single-stack
//!   and the assertion belongs on the close, with the corpus as its
//!   measurement. Until then it is a claim nobody has checked.
//!
//!   What holds I2 in production today is the pair of consequences a violation
//!   must have. `gen_checked` in [`Closed::discharge`] refuses to strand a
//!   hypothesis mentioning the variable being generalised (I3). And nothing may
//!   *persist* carrying a hypothesis: [`crate::sealed::Sealed`] is the store
//!   funnel (I4), stack-agnostic, backed at the in-flight caches by
//!   `certify::is_unconditional` and `certify::hypothesis_free`. Neither notices
//!   the specific failure `close_single_stack` catches — a scope closed without
//!   its theorem being discharged out of it — because such a hypothesis never
//!   mentions the variable being generalised; that gap is why the check exists
//!   at all rather than being deleted as redundant.
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

/// **The ambient context's own typing of a local, as a hypothesis**:
/// `{⟦w⟧ ∈ ⟦A⟧} ⊢ ⟦w⟧ ∈ ⟦A⟧`.
///
/// The second sanctioned `Thm::assume` in this crate, and it is here rather
/// than at its caller for exactly the reason I1 exists: a hypothesis must enter
/// a derivation at a place that can be read and argued about.
///
/// # What the caller owes, and it is not a formality
///
/// `hyp` must be a member of `⟦Γ⟧` for the `Γ` of the judgement being stated —
/// the interpreted typing of a local the checker *already had open* when the
/// query started. Carneiro's Theorem 6.7 reads `Γ ⊢ e ≡ e'` as *for all
/// `γ ∈ ⟦Γ⟧`, `⟦Γ ⊢ e⟧γ = ⟦Γ ⊢ e'⟧γ`*, so under that precondition the sequent
/// this produces is the judgement's own statement. Without it, it is an
/// assumption about a variable nothing quantifies over.
///
/// The precondition is discharged by *positive witness*, not by a side
/// condition on levels: `crate::tg::TgBackend::close_at_boundary` compares the
/// atom against the interpreted typings of the locals on
/// `TcCtx::open_dbj_levels` at the query's entry, and passes only atoms that
/// are literally one of them. A local the query opened for itself is not on
/// that list, so its premise stays where it was and is still owed to the binder
/// rule that opened it.
///
/// # Why this does not weaken I1
///
/// `assume` asserts nothing about `hyp`: what comes back records the
/// hypothesis in the theorem's own `hyps()`, where every downstream gate can
/// see it. In particular `certify::is_unconditional` — which the checker's
/// reduction memos and its equality cache are gated on — is
/// `hyps().is_empty()`, so a theorem produced here is excluded from exactly the
/// stores that are keyed on something not mentioning `Γ`. Nothing is smuggled
/// past a cache by calling this; the worst a wrong caller can do is state a
/// weaker theorem than it meant to.
pub fn assume_ambient(hyp: Formula) -> Thm { Thm::assume(hyp) }

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

    /// I2's set half, **as a predicate for one stack**:
    /// `thm.hyps() ⊆ {hyp of each scope open on this stack}`.
    ///
    /// A violation can only be *introduced* by an `assume` and can only be
    /// *observed* once the introducing scope is gone, so the close is the point
    /// where asking is useful. It is not asked *at* the close by
    /// [`Scopes::close`]: see the module header, and
    /// [`test_support::close_single_stack`], which is where the question has a
    /// caller that can guarantee its precondition.
    pub fn hyps_are_scoped(&self, thm: &Thm) -> bool {
        thm.hyps().iter().all(|h| self.open_hyps().contains(&h))
    }
}

/// What sibling modules' **tests** may reach into this one for.
#[cfg(test)]
pub(crate) mod test_support {
    use super::{Closed, ScopeToken, Scopes};
    use kernel::{Formula, Thm};

    /// The one sanctioned use of `Thm::assume` outside [`Scopes::open`]: tests
    /// that need a hypothetical theorem to pin a guard against. Keeping it here
    /// keeps I1 a single-file property.
    pub(crate) fn assume(phi: Formula) -> Thm { Thm::assume(phi) }

    /// **Close, and assert that nothing was stranded — for a derivation that
    /// threads exactly one [`Scopes`].**
    ///
    /// After `implies_intr` removes this scope's own hypothesis, every formula
    /// left in `Γ` must belong to a scope still open *on this stack*. That is
    /// I2's set half specialised to a single-stack derivation, and it catches
    /// the mistake the invariant exists for: a scope closed without its theorem
    /// being discharged out of it leaves a hypothesis no later discharge can
    /// reach, and [`Closed::discharge`]'s `gen_checked` does not see it, because
    /// such a hypothesis does not mention the variable being generalised.
    ///
    /// **It is here, and not on [`Scopes::close`], because the precondition is
    /// a property of the derivation and not of the program** — see the module
    /// header for the measurement (mini, 19 unit tests) and for the condition
    /// under which THREADING-CENSUS §2 stage 1 may move it onto `close`. The
    /// two directions are pinned by
    /// `a_stranded_hypothesis_is_caught_on_a_single_stack` and
    /// `gen_checked_does_not_see_a_stranded_hypothesis`.
    pub(crate) fn close_single_stack(sc: &mut Scopes, tok: ScopeToken, thm: &Thm) -> Closed {
        let closed = sc.close(tok);
        let outer = Thm::implies_intr(closed.scope().hyp(), thm);
        assert!(
            sc.hyps_are_scoped(&outer),
            "I2 violated on a single-stack derivation: after discharging this scope, Γ is {:?}, \
             and the scopes still open hold {:?} — the difference can never be discharged",
            outer.hyps(),
            sc.open_hyps()
        );
        closed
    }
}

#[cfg(test)]
mod tests {
    use super::test_support::close_single_stack;
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

        let closed = close_single_stack(&mut sc, tok, &body);
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

        let c2 = close_single_stack(&mut sc, t2, &both);
        let step = c2.discharge(&both).unwrap();
        assert_eq!(step.hyps().len(), 1, "only the outer hypothesis may remain");
        assert!(sc.hyps_are_scoped(&step));

        let c1 = close_single_stack(&mut sc, t1, &step);
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
        let closed = close_single_stack(&mut sc, tok, &assumed);
        let discharged = closed.discharge(&assumed).unwrap();
        assert!(
            crate::sealed::Sealed::new(discharged).is_ok(),
            "once discharged it is unconditional, and may be stored"
        );
    }

    /// Set up the failure I2's set half exists for: the inner scope is closed
    /// **without** its theorem being discharged out of it, so `y ∈ B` is
    /// stranded in `Γ` with no scope left that could ever remove it.
    fn strand_a_hypothesis(env: &mut Env, sc: &mut Scopes) -> (ScopeToken, Thm) {
        let a = dom(env);
        let b = dom(env);
        let t1 = sc.open(env, a);
        let t2 = sc.open(env, b);
        let inner = sc.get(0).unwrap().assumption().clone();
        // Closed, and the `Closed` dropped: nobody discharges `inner` out of it.
        let _ = sc.close(t2);
        assert_eq!(inner.hyps().len(), 1, "the stranded hypothesis is still on the theorem");
        assert!(!sc.hyps_are_scoped(&inner), "and it belongs to no scope still open");
        (t1, inner)
    }

    /// The check fires — on a single-stack derivation, where its precondition
    /// holds. This is what [`test_support::close_single_stack`] is *for*.
    #[test]
    #[should_panic(expected = "I2 violated on a single-stack derivation")]
    fn a_stranded_hypothesis_is_caught_on_a_single_stack() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let (t1, inner) = strand_a_hypothesis(&mut env, &mut sc);
        let _ = close_single_stack(&mut sc, t1, &inner);
    }

    /// …and it is not redundant with I3: on exactly the same derivation, the
    /// plain `close`/`discharge` pair succeeds and hands back a theorem still
    /// carrying the stranded hypothesis. `gen_checked` cannot see it, because
    /// `y ∈ B` does not mention `x`. Deleting the check would lose this.
    #[test]
    fn gen_checked_does_not_see_a_stranded_hypothesis() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let (t1, inner) = strand_a_hypothesis(&mut env, &mut sc);
        let out = sc
            .close(t1)
            .discharge(&inner)
            .expect("gen_checked succeeds: the stranded hypothesis is not about `x`");
        assert!(sc.is_empty(), "every scope has been closed");
        assert_eq!(
            out.hyps().len(),
            1,
            "yet `Γ` is non-empty with nothing left open to discharge it — the silent failure"
        );
    }
}
