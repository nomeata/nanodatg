//! **SUPERSEDED.** Part of the above-kernel deduction layer; see the
//! "SUPERSEDED" section of `derived/src/hyp.rs`. The `gen` side condition and
//! `obtain` below are the two operations that carry over unchanged to the
//! in-kernel design. Kept as the experiment.
//!
//! The quantifier operations on [`Hyp`], including the free-variable side
//! condition checked against the hypothesis set.
//!
//! # Interface
//!
//! ```text
//!   a.gen(x)                    Γ ⊢ φ ⟹ Γ ⊢ ∀x.φ,  provided x ∉ FV(Γ)
//!   a.inst(t)                   Γ ⊢ ∀x.φ ⟹ Γ ⊢ φ[t/x]
//!   a.inst_all(&[t₀..tₙ])       the same, n+1 leading quantifiers at once
//!   a.exists_intro(v, φ, t)     Γ ⊢ φ[t/v] ⟹ Γ ⊢ ∃v.φ
//!   Hyp::obtain(v, &ex, &body)  Δ ⊢ ∃v.E,  Γ∪{E} ⊢ ψ ⟹ Γ∪Δ ⊢ ψ
//! ```
//!
//! # `gen` is where carrying the set pays for itself
//!
//! When this was written, `kernel::Thm::gen` needed no side condition, because a
//! `Thm` had no hypotheses and so there was no `Γ` for `x` to be free in. **That
//! is no longer true and must not be repeated**: `Thm` is a sequent now, `gen`
//! carries `x ∉ FV(Γ)`, `kernel::Thm::gen_checked` reports a violation as `None`
//! and `kernel::Thm::gen` **panics** on it. The condition is merely *vacuous* on
//! a hypothesis-free theorem, which is a fact about those callers rather than a
//! property of the rule — `kernel/README.md`, "What a `Thm` asserts", says so
//! explicitly.
//!
//! A `Hyp` has always had hypotheses, so the side condition was always live
//! here — and it is exactly the check `kernel::Thm::ax_dist` enforces on the
//! antecedent, which is what this operation goes through. That this layer got
//! the condition right, and the kernel later grew the same one, is the part
//! worth keeping.
//!
//! Callers in this crate currently rediscover that each time: they arrange for
//! the quantified variable not to occur in the conjunction they chose as `H`,
//! satisfy themselves of it by inspection, and call `ax_dist`. Here the
//! hypothesis set *is* the thing to check against, so the check is one line and
//! is made every time.
//!
//! # `obtain` is the other half
//!
//! Existential elimination is the operation this crate has hand-rolled most
//! often: `universe/union.rs`, `ext/shared.rs`, `funspace/`, `sums/` and
//! `cantor/` each keep a private `discharge`, all with the same body and the
//! same comment about not breaking when a neighbour is reshaped. All of them
//! take a *fixed* `H`, so the caller must have arranged for the existential and
//! the body to already share it. [`Hyp::obtain`] does not need that: it
//! discharges the opened body from the hypothesis set, merges what is left with
//! whatever the existential was proved under, and checks `v` against the result.

use kernel::{FreeVar, Term, Thm};

use super::{order, Hyp};

impl Hyp {
    /// `Γ ⊢ φ` gives `Γ ⊢ ∀x. φ`, **provided `x` is free in no hypothesis**.
    ///
    /// Returns `None` when the side condition fails. That is the whole point:
    /// generalising a variable a hypothesis still constrains is unsound in a
    /// system with contexts, and a `Hyp` has one.
    pub fn gen(&self, x: FreeVar) -> Option<Hyp> {
        if self.hyps().iter().any(|h| h.occurs_free(x)) {
            return None
        }
        // `ax_dist` re-checks this against `conj(Γ)` itself; the check above is
        // the same condition stated where a caller can act on it, and it is what
        // makes the rejection mean "a hypothesis mentions `x`" rather than
        // "`ax_dist` said no".
        let dist = Thm::ax_dist(x, order::conj(self.hyps()), self.concl().clone())?;
        self.same_hyps(Thm::mp(&dist, &Thm::gen(x, self.thm()))?)
    }

    /// `Γ ⊢ ∀x. φ` gives `Γ ⊢ φ[t/x]`.
    pub fn inst(&self, t: Term) -> Option<Hyp> {
        self.rule(&Thm::ax_inst(self.concl().clone(), t)?)
    }

    /// Instantiate several leading quantifiers, outermost first.
    pub fn inst_all(&self, ts: &[Term]) -> Option<Hyp> {
        let mut cur = self.clone();
        for t in ts {
            cur = cur.inst(t.clone())?;
        }
        Some(cur)
    }

    /// `Γ ⊢ φ[t/v]` gives `Γ ⊢ ∃v. φ`.
    ///
    /// `φ` and `v` are supplied because the instance does not determine them —
    /// `φ[t/v]` has forgotten which occurrences of `t` were the variable. The
    /// premise is checked against `φ[t/v]`, so a wrong `φ` is rejected.
    pub fn exists_intro(&self, v: FreeVar, phi: &kernel::Formula, t: Term) -> Option<Hyp> {
        if *self.concl() != phi.subst(v, &t) {
            return None
        }
        self.rule(&crate::exists_intro_imp(v, phi.clone(), t)?)
    }

    /// Existential elimination, with the witness discharged from the hypothesis
    /// set: from `Δ ⊢ ∃v. E` and `Γ ∪ {E} ⊢ ψ` infer `Γ ∪ Δ ⊢ ψ`.
    ///
    /// `E` is read off `ex`'s conclusion by opening it at `v`, so the caller
    /// names the witness variable and nothing else; `body` must have that opened
    /// formula among its hypotheses, or this returns `None`.
    ///
    /// `v` must be free in neither the resulting hypothesis set nor `ψ` — the
    /// side condition that stops a witness-dependent conclusion escaping the
    /// witness's scope. It is checked here against the merged set, and again
    /// inside [`crate::exists_elim_imp`].
    pub fn obtain(v: FreeVar, ex: &Hyp, body: &Hyp) -> Option<Hyp> {
        let e = open_exists(ex.concl(), &Term::var(v))?;
        let discharged = body.discharge(&e)?;
        let (hs, imp, existential) = Hyp::merge(&discharged, ex)?;
        if hs.iter().any(|h| h.occurs_free(v)) {
            return None
        }
        let psi = body.concl().clone();
        if psi.occurs_free(v) {
            return None
        }

        // `⊢ K → (E → ψ)` becomes `⊢ ∀v. (E → (K → ψ))`, which eliminates the
        // existential at the target `K → ψ`; discharging `K` twice contracts.
        let target = kernel::Formula::imp(order::conj(&hs), psi);
        let all = Thm::gen(v, &crate::com12(&imp)?);
        let elim = crate::exists_elim_imp(v, &all, &target)?;
        let twice = crate::syl(&existential, &elim)?;
        Hyp::wrap(hs, crate::empty::hyp_contract(&twice).ok()?)
    }
}

/// Open the body of `∃v. φ` at `t`, as a formula operation. `∃` is `¬∀¬`.
///
/// Goes through `ax_inst` because a `Forall`'s body is not reachable from
/// outside the kernel; the resulting theorem is discarded and only its shape is
/// read, so this builds nothing that is kept.
fn open_exists(phi: &kernel::Formula, t: &Term) -> Option<kernel::Formula> {
    let fls = kernel::Formula::false_();
    let (all_not, f1) = phi.as_imp()?;
    if f1 != fls {
        return None
    }
    let (_, opened) = Thm::ax_inst(all_not, t.clone())?.concl().as_imp()?;
    let (body, f2) = opened.as_imp()?;
    if f2 != fls {
        return None
    }
    Some(body)
}
