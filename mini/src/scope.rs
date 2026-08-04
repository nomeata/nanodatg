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
//! # Not every hypothesis is a binder's typing
//!
//! [`Scopes::assume`] takes an arbitrary [`Formula`] and discharges it to
//! `φ → ψ` with no generalisation. It exists because a *premise stated by
//! `derived`* need not be a membership: `derived::acc::ind_step`'s induction
//! hypothesis is `∀y. (y ∈ A → (⟨y,x⟩ ∈ R → (y ∈ acc(A,R) ∧ φ(y))))`, and
//! `Acc.rec` at `u₁ = 0` has to **use** it — the eliminator stands on the side
//! of that implication where the antecedent is held, not owed. Every mini-side
//! step it then feeds (`cond_app`, `cond_intro`, `beta_spine`, `point_of_proof`)
//! takes and returns a plain `Γ ⊢ t ∈ S`, so the honest place for the
//! hypothesis is `Γ`; the alternative is a `K → …` variant of each of them.
//!
//! An assumption is **not** a binder: it has no domain, no variable and no `∀`
//! on discharge. It is kept on a stack of its own so that [`Scopes::get`],
//! [`Scopes::len`] and every `bvar` index keep counting binders only, and the
//! two stacks are checked to interleave properly at each close.
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
//!   being consumed by [`Scopes::close`], and by that method's LIFO assertion.
//!   **"Each open scope" is not one stack.** Mini runs about fifteen
//!   [`Scopes`] concurrently — the checker holds one for the Lean binders it is
//!   under, and each construction that needs a binder of its own (`acc`,
//!   `rec_dep`, `quot_classes`, `rec_prop::subset_of_unit`, …) opens a local
//!   one — and a theorem discharged out of one of them legitimately still
//!   carries hypotheses belonging to the others. So the *set* half of I2 is
//!   a property of the whole execution and cannot be read off the stack being
//!   closed; [`Scopes::hyps_are_scoped`] answers it for one stack only.
//!   `a_discharge_may_carry_another_stacks_hypothesis` is the measurement:
//!   asserting it at [`Scopes::close`] fails 19 unit tests, all of them
//!   correct code. So the checked close lives in
//!   [`test_support::close_single_stack`], where its precondition — one stack
//!   for the whole derivation — is a property the test can guarantee; on that
//!   precondition it does fire, and
//!   `a_stranded_hypothesis_is_caught_on_a_single_stack` is the theorem it
//!   catches, which `gen_checked` lets through.
//!
//!   What *is* checked in production is the pair of consequences that a
//!   violation must have. `gen_checked` in [`Closed::discharge`] refuses to
//!   strand a hypothesis mentioning the variable being generalised (I3 below).
//!   And nothing may *persist* with a hypothesis: [`crate::ev::Sealed`] is the
//!   store funnel (I4), so a hypothesis that escaped its discharge is caught
//!   there whichever stack it came from — counted, on every corpus run, as the
//!   `unsealed` column that the closed corpus holds at zero.
//!
//!   **An abandoned [`ScopeToken`] is contained by [`Scopes::close`] itself,
//!   not by a convention.** Five helpers take the caller's stack —
//!   `rec_acc::preds`, `rec_acc_value::minor_fn`,
//!   `rec_acc_ih::ih_in_minor_domain`, `rec_acc_ih::row_in_fibre`,
//!   `rec_acc_iota::row_agrees` — and each opens a scope and then has some
//!   twenty `?` paths between the open and the close, every one of which drops
//!   the token with the scope still on the stack. That is sound, and the
//!   argument is not "every caller happens to use a fresh local stack": it is
//!   that a caller which *did* go on to close would hit [`Scopes::close`]'s
//!   own LIFO assertion, because an abandoned scope leaves `stack.len()` one
//!   too high for every token still outstanding. The failure mode is an abort
//!   naming the invariant, which is what
//!   `an_abandoned_token_is_caught_at_the_next_close` pins — with the token
//!   *dropped* rather than merely held out of order, since that is the shape
//!   these helpers produce and the one where nothing in the type system is
//!   left to complain. What the callers do supply is that the abort never
//!   happens: every stack these five are handed is a `Scopes::new()` local to
//!   the function that owns it, and every `None` they return is
//!   `?`-propagated straight out of that function, so the stack is dropped
//!   rather than closed. Both halves are needed — the convention makes it
//!   correct, `close` makes a lapse loud.
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

/// One assumed formula that is not a binder's typing.
#[derive(Debug, Clone)]
struct Assumption {
    /// The formula assumed.
    hyp: Formula,
    /// How many binders were open when it was assumed — the interleaving check.
    under: usize,
}

/// Proof that a formula was assumed, and the obligation to discharge it.
///
/// The counterpart of [`ScopeToken`] for [`Scopes::assume`], and separate from
/// it so that a binder cannot be closed with an assumption's token or the
/// reverse.
#[derive(Debug)]
pub struct AssumeToken {
    /// The assumption stack's depth *below* this one.
    depth: usize,
    _not_clone: std::marker::PhantomData<*const ()>,
}

/// The LIFO stack of open binders. `stack.last()` is `bvar 0`.
///
/// Assumed formulas live on a second stack — see the module header — so that a
/// `bvar` index is unaffected by whatever a derivation assumes under it.
#[derive(Debug, Default)]
pub struct Scopes {
    stack: Vec<Scope>,
    assumed: Vec<Assumption>,
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

    /// Assume an arbitrary formula: `{φ} ⊢ φ`, to be discharged by
    /// [`Scopes::discharge_assumption`] into `φ → ψ`.
    ///
    /// **The second and last call to `Thm::assume`.** Unlike [`Scopes::open`]
    /// this introduces no variable and no domain, so it is not a binder and
    /// nothing about `bvar` indexing moves; what it is for is a premise a
    /// `derived` statement puts on the left of an implication that is not a
    /// membership. See the module header.
    pub fn assume(&mut self, phi: Formula) -> (AssumeToken, Thm) {
        let depth = self.assumed.len();
        let assumed = Thm::assume(phi.clone());
        self.assumed.push(Assumption { hyp: phi, under: self.stack.len() });
        (AssumeToken { depth, _not_clone: std::marker::PhantomData }, assumed)
    }

    /// From `Γ ∪ {φ} ⊢ ψ` produce `Γ ⊢ φ → ψ`.
    ///
    /// No generalisation: an assumption has no variable to bind, which is the
    /// whole difference from [`Closed::discharge`].
    pub fn discharge_assumption(&mut self, tok: AssumeToken, thm: &Thm) -> Thm {
        assert_eq!(
            tok.depth + 1,
            self.assumed.len(),
            "assumptions must be discharged innermost-first (I2): discharging the one at depth \
             {} while {} are open",
            tok.depth,
            self.assumed.len()
        );
        let a = self.assumed.pop().expect("token implies an assumption");
        Thm::implies_intr(&a.hyp, thm)
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
        // The two stacks interleave: an assumption made under this binder must
        // be discharged before it, or `gen_checked` would be asked to bind a
        // variable that is free in a hypothesis still live.
        assert!(
            self.assumed.last().is_none_or(|a| a.under <= tok.depth),
            "a formula assumed under this binder is still open (I2)"
        );
        let scope = self.stack.pop().expect("token implies a scope");
        Closed { scope }
    }

    /// The hypotheses I2 permits a live `Thm` to carry.
    pub fn open_hyps(&self) -> Vec<&Formula> {
        self.stack.iter().map(|s| &s.hyp).chain(self.assumed.iter().map(|a| &a.hyp)).collect()
    }

    /// I2's set half, as a predicate — **for this stack only**.
    ///
    /// `false` is not a violation: a theorem legitimately carries hypotheses
    /// belonging to *other* live [`Scopes`], and this stack cannot see them.
    /// That is why the checked close is [`test_support::close_single_stack`]
    /// and not a method here — see the module header, and
    /// `a_discharge_may_carry_another_stacks_hypothesis`.
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
    /// that need a hypothetical theorem to pin a guard against. Keeping it
    /// here keeps I1 a single-file property.
    pub(crate) fn assume(phi: Formula) -> Thm { Thm::assume(phi) }

    /// **Close, and assert that nothing was stranded — for a derivation that
    /// threads exactly one [`Scopes`].**
    ///
    /// After `implies_intr` removes this scope's own hypothesis, every formula
    /// left in `Γ` must belong to a scope that is still open *on this stack*.
    /// That is I2's set half specialised to a single-stack derivation, and it
    /// catches the mistake the invariant exists for: a scope closed without its
    /// theorem being discharged out of it leaves a hypothesis that no later
    /// discharge can reach, and `gen_checked` does not see it, because such a
    /// hypothesis does not mention the variable being generalised.
    ///
    /// **It is here, and not on [`Scopes::close`], because the precondition is
    /// a property of the derivation and not of the program.** Mini runs about
    /// fifteen `Scopes` concurrently and a theorem may legitimately carry
    /// another stack's hypotheses; asserting this at every close fails 19 unit
    /// tests, all of them correct code. See the module header, and the two
    /// tests that pin both directions —
    /// `a_stranded_hypothesis_is_caught_on_a_single_stack` and
    /// `a_discharge_may_carry_another_stacks_hypothesis`.
    ///
    /// In production the same failure is caught at the far end instead:
    /// nothing may persist carrying a hypothesis ([`crate::ev::Sealed`], I4),
    /// which is stack-agnostic and is the `unsealed` column the closed corpus
    /// holds at zero.
    pub(crate) fn close_single_stack(sc: &mut Scopes, tok: ScopeToken, thm: &Thm) -> Closed {
        let closed = sc.close(tok);
        let outer = Thm::implies_intr(closed.scope().hyp(), thm);
        assert!(
            sc.hyps_are_scoped(&outer),
            "I2 violated on a single-stack derivation: after discharging this scope, Γ is \
             {:?}, and the scopes still open hold {:?} — the difference can never be \
             discharged",
            outer.hyps(),
            sc.open_hyps()
        );
        closed
    }
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

        let closed = test_support::close_single_stack(&mut sc, tok, &body);
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

        let c2 = test_support::close_single_stack(&mut sc, t2, &both);
        let step = c2.discharge(&both).unwrap();
        assert_eq!(step.hyps().len(), 1, "only the outer hypothesis may remain");
        assert!(sc.hyps_are_scoped(&step));

        let c1 = test_support::close_single_stack(&mut sc, t1, &step);
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

    /// An assumed formula discharges to `φ → ψ` with **no** `∀`, and it does
    /// not move a `bvar` index: `get(0)` is still the binder it was.
    #[test]
    fn an_assumption_discharges_to_an_implication_and_is_not_a_binder() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let tok = sc.open(&mut env, a.clone());
        let w = sc.get(0).unwrap().var();
        let phi = Formula::mem(Term::var(w), dom(&mut env));
        let (atok, assumed) = sc.assume(phi.clone());
        // The binder is still `bvar 0`; the assumption is on the other stack.
        assert_eq!(sc.len(), 1);
        assert_eq!(sc.get(0).unwrap().var(), w);
        let body = derived::and_intro(sc.get(0).unwrap().assumption(), &assumed);
        assert_eq!(body.hyps().len(), 2);
        assert!(sc.hyps_are_scoped(&body));

        let step = sc.discharge_assumption(atok, &body);
        assert_eq!(step.hyps().len(), 1, "only the binder's hypothesis may remain");
        let closed = test_support::close_single_stack(&mut sc, tok, &step);
        let out = closed.discharge(&step).unwrap();
        assert!(out.hyps().is_empty());
        let hyp = Formula::mem(Term::var(w), a);
        assert_eq!(
            out.concl(),
            &Formula::forall(
                w,
                Formula::imp(
                    hyp.clone(),
                    Formula::imp(phi.clone(), Formula::and(hyp, phi)),
                )
            ),
        );
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

    /// **An abandoned token is caught by the next close on the same stack.**
    ///
    /// This is the containment behind the five `sc: &mut Scopes` helpers,
    /// which drop their token on some twenty `?` paths each. `closing_out_of_
    /// order_is_caught` above pins the same assertion with both tokens still
    /// held; here the inner token is *gone* — which is the shape those helpers
    /// actually produce, and the one where nothing in the type system is left
    /// to complain. The stack is one deeper than every outstanding token
    /// expects, so the outer close aborts naming I2 instead of handing back a
    /// theorem generalised over the wrong variable.
    #[test]
    #[should_panic(expected = "innermost-first")]
    fn an_abandoned_token_is_caught_at_the_next_close() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let b = dom(&mut env);
        let t1 = sc.open(&mut env, a);
        // The helper's failure path: opened, and the token dropped on the spot.
        let _ = sc.open(&mut env, b);
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

    /// **A hypothesis stranded on this stack is caught** — the half of I2 that
    /// `gen_checked` does not see, and the reason the checked close exists at
    /// all.
    ///
    /// Two scopes, and the inner one is closed *without* its theorem being
    /// discharged out of it. The theorem still carries `y ∈ B`, and `y` is a
    /// scope that no longer exists, so nothing can ever discharge it — yet
    /// generalising over the *outer* `x` succeeds, because `y ∈ B` does not
    /// mention `x`. Plain `close`/`discharge` therefore hands back
    /// `{y ∈ B} ⊢ ∀x. (x ∈ A → …)`, an undischargeable hypothesis with no
    /// complaint; the assertion is what names it. Two scopes, because with one
    /// the stranded hypothesis is the one being discharged.
    #[test]
    #[should_panic(expected = "I2 violated on a single-stack derivation")]
    fn a_stranded_hypothesis_is_caught_on_a_single_stack() {
        let mut env = Env::new();
        let mut sc = Scopes::new();
        let a = dom(&mut env);
        let b = dom(&mut env);
        let t1 = sc.open(&mut env, a);
        let t2 = sc.open(&mut env, b);
        let inner = sc.get(0).unwrap().assumption().clone();
        let both = derived::and_intro(sc.get(1).unwrap().assumption(), &inner);
        // The mistake: the inner scope is popped, and `both` is not discharged
        // out of it.
        let _ = sc.close(t2);
        let _ = test_support::close_single_stack(&mut sc, t1, &both);
    }

    /// **A discharge may carry another stack's hypothesis, and that is not a
    /// violation of I2.**
    ///
    /// This is `rec_prop::subset_of_unit` in miniature, and it is the reason
    /// the checked close is test-side rather than on [`Scopes::close`]. That
    /// function opens a [`Scopes`] of its own over `⟦βⱼ⟧` — a domain
    /// mentioning the *checker's* binders — and discharges a theorem that
    /// still carries the checker's scope hypotheses, for the checker's own
    /// stack to discharge later. A close that asserted
    /// `thm.hyps() ⊆ {hyp of each scope open on this stack}` would reject it:
    /// measured, that assertion fails 19 unit tests, every one of them correct
    /// code, because mini runs about fifteen `Scopes` concurrently.
    ///
    /// The two stacks are needed to say it: with one stack the two halves of
    /// I2 — "this stack's scopes" and "every open scope" — coincide, and a
    /// per-stack check passes for the wrong reason.
    #[test]
    fn a_discharge_may_carry_another_stacks_hypothesis() {
        let mut env = Env::new();
        let a = dom(&mut env);
        let mut outer = Scopes::new();
        let tx = outer.open(&mut env, a.clone());
        let x = outer.get(0).unwrap().var();
        let hx = outer.get(0).unwrap().hyp().clone();
        // `{x ∈ A} ⊢ x ∈ A`, held across the local construction below.
        let carried = outer.get(0).unwrap().assumption().clone();

        // The construction: a stack of its own, over a domain that mentions
        // `x`, closed and discharged while `outer` is still open.
        let mut local = Scopes::new();
        let b = Term::apply(env.declare(1), vec![Term::var(x)]);
        let ty = local.open(&mut env, b);
        let body = derived::and_intro(local.get(0).unwrap().assumption(), &carried);
        assert_eq!(body.hyps().len(), 2, "one hypothesis from each stack");
        assert!(
            !local.hyps_are_scoped(&body),
            "the local stack cannot see `x ∈ A`, so its predicate is false — and the \
             theorem is correct all the same"
        );

        let out = local.close(ty).discharge(&body).expect("the local scope discharges");
        assert_eq!(
            out.hyps(),
            std::slice::from_ref(&hx),
            "…and hands `x ∈ A` back to the stack that owns it"
        );
        assert!(outer.hyps_are_scoped(&out), "which is where it is in scope");

        let done = outer.close(tx).discharge(&out).expect("and there it discharges");
        assert!(done.hyps().is_empty(), "nothing is stranded");
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
