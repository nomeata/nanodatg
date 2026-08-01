//! **SUPERSEDED.** Part of the above-kernel deduction layer; see the
//! "SUPERSEDED" section of `derived/src/hyp.rs`. Kept as the experiment.
//!
//! The propositional operations on [`Hyp`].
//!
//! # Interface
//!
//! ```text
//! ── binary: the hypothesis sets union-merge ──────────────────────────────────
//!   a.mp(&b)            Γ ⊢ φ→ψ,  Δ ⊢ φ            ⟹ Γ∪Δ ⊢ ψ
//!   a.syl(&b)           Γ ⊢ φ→ψ,  Δ ⊢ ψ→χ          ⟹ Γ∪Δ ⊢ φ→χ
//!   a.and_intro(&b)     Γ ⊢ φ,    Δ ⊢ ψ            ⟹ Γ∪Δ ⊢ φ∧ψ
//!   a.iff_intro(&b)     Γ ⊢ φ→ψ,  Δ ⊢ ψ→φ          ⟹ Γ∪Δ ⊢ φ↔ψ
//!   a.or_elim(&l, &r)   Γ ⊢ φ∨ψ, Δ ⊢ φ→χ, Ε ⊢ ψ→χ  ⟹ Γ∪Δ∪Ε ⊢ χ
//!
//! ── unary: the hypothesis set is untouched ───────────────────────────────────
//!   a.and_left()        Γ ⊢ φ∧ψ  ⟹ Γ ⊢ φ
//!   a.and_right()       Γ ⊢ φ∧ψ  ⟹ Γ ⊢ ψ
//!   a.iff_mp()          Γ ⊢ φ↔ψ  ⟹ Γ ⊢ φ→ψ
//!   a.iff_mpr()         Γ ⊢ φ↔ψ  ⟹ Γ ⊢ ψ→φ
//!   a.rule(&Thm)        Γ ⊢ φ  and  ⊢ φ→ψ  ⟹ Γ ⊢ ψ
//!   a.contrapos()       Γ ⊢ φ→ψ  ⟹ Γ ⊢ ¬ψ→¬φ
//!   a.not_elim()        Γ ⊢ ¬¬φ  ⟹ Γ ⊢ φ
//!   a.absurd(&χ)        Γ ⊢ ⊥    ⟹ Γ ⊢ χ
//! ```
//!
//! # How the invariant is preserved
//!
//! Each binary operation calls [`Hyp::merge`] first, which re-proves both
//! premises against `Γ ∪ Δ` and hands back two theorems with a common
//! antecedent — exactly the shape the fixed-hypothesis rules in `lib.rs`
//! consume. The rule is then applied unchanged and the result re-wrapped, which
//! re-checks the antecedent. Each unary operation composes with a *closed*
//! implication and goes through [`Hyp::same_hyps`], which re-checks it too.
//!
//! Reading a conclusion apart — [`split_and`] below — produces no [`Thm`], so a
//! misreading yields `None`, never a wrong theorem.

use kernel::{Formula, Thm};

use super::{order, Hyp};

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`, into its conjuncts.
///
/// A local copy, on the same reasoning [`crate::universe`] and [`crate::ext`]
/// give for keeping theirs: it builds nothing, so a duplicate cannot diverge
/// into an unsoundness, and a layer this central should not break when a
/// neighbouring module reshapes its own private helpers.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, not_psi) = inner.as_imp()?;
    let (psi, fls2) = not_psi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

impl Hyp {
    /// `Γ ⊢ φ → ψ` and `Δ ⊢ φ` give `Γ ∪ Δ ⊢ ψ`.
    pub fn mp(&self, arg: &Hyp) -> Option<Hyp> {
        let (hs, imp, a) = Hyp::merge(self, arg)?;
        Hyp::wrap(hs, crate::hyp_mp(&imp, &a)?)
    }

    /// `Γ ⊢ φ → ψ` and `Δ ⊢ ψ → χ` give `Γ ∪ Δ ⊢ φ → χ`.
    pub fn syl(&self, next: &Hyp) -> Option<Hyp> {
        let (hs, ab, bc) = Hyp::merge(self, next)?;
        Hyp::wrap(hs, crate::separation::hyp_syl(&ab, &bc)?)
    }

    /// `Γ ⊢ φ` and `Δ ⊢ ψ` give `Γ ∪ Δ ⊢ φ ∧ ψ`.
    pub fn and_intro(&self, other: &Hyp) -> Option<Hyp> {
        let (hs, p, q) = Hyp::merge(self, other)?;
        Hyp::wrap(hs, crate::hyp_and(&p, &q)?)
    }

    /// `Γ ⊢ φ → ψ` and `Δ ⊢ ψ → φ` give `Γ ∪ Δ ⊢ φ ↔ ψ`.
    ///
    /// `φ ↔ ψ` is `(φ → ψ) ∧ (ψ → φ)`, so this is [`Hyp::and_intro`] with the
    /// halves in the order the encoding fixes; it exists so callers need not
    /// know which order that is.
    pub fn iff_intro(&self, other: &Hyp) -> Option<Hyp> {
        let (a, b) = self.concl().as_imp()?;
        let (b2, a2) = other.concl().as_imp()?;
        if a != a2 || b != b2 {
            return None
        }
        let out = self.and_intro(other)?;
        debug_assert_eq!(*out.concl(), Formula::iff(a, b), "iff_intro: wrong shape");
        Some(out)
    }

    /// Case analysis: `Γ ⊢ φ ∨ ψ`, `Δ ⊢ φ → χ` and `Ε ⊢ ψ → χ` give
    /// `Γ ∪ Δ ∪ Ε ⊢ χ`.
    ///
    /// `φ ∨ ψ` is `¬φ → ψ`, and the collapse is Clavius' law; see
    /// [`crate::hyp_or_elim`], which is what this calls once all three premises
    /// have been brought to a common antecedent. Every "the case split is run as
    /// Clavius' law" comment in this crate is a hand-rolled instance of this.
    pub fn or_elim(&self, left: &Hyp, right: &Hyp) -> Option<Hyp> {
        let (hs, disj, l, r) = Hyp::merge3(self, left, right)?;
        Hyp::wrap(hs, crate::hyp_or_elim(&disj, &l, &r)?)
    }

    /// `Γ ⊢ φ ∧ ψ` gives `Γ ⊢ φ`.
    pub fn and_left(&self) -> Option<Hyp> {
        let (phi, psi) = split_and(self.concl())?;
        self.same_hyps(crate::syl(self.thm(), &crate::and_left(phi, psi))?)
    }

    /// `Γ ⊢ φ ∧ ψ` gives `Γ ⊢ ψ`.
    pub fn and_right(&self) -> Option<Hyp> {
        let (phi, psi) = split_and(self.concl())?;
        self.same_hyps(crate::syl(self.thm(), &crate::and_right(phi, psi))?)
    }

    /// `Γ ⊢ φ ↔ ψ` gives `Γ ⊢ φ → ψ`.
    pub fn iff_mp(&self) -> Option<Hyp> {
        self.same_hyps(crate::hyp_iff_mp(self.thm())?)
    }

    /// `Γ ⊢ φ ↔ ψ` gives `Γ ⊢ ψ → φ`.
    pub fn iff_mpr(&self) -> Option<Hyp> {
        self.same_hyps(crate::hyp_iff_mpr(self.thm())?)
    }

    /// Apply a *closed* implication: `Γ ⊢ φ` and `⊢ φ → ψ` give `Γ ⊢ ψ`.
    ///
    /// The cheap path, and the one most uses want — a lemma proved elsewhere is
    /// a `Thm`, not a `Hyp`, and running it through [`Hyp::lift`] and
    /// [`Hyp::mp`] would rebuild the merge machinery for a set that cannot have
    /// changed. One [`crate::syl`], four kernel calls.
    pub fn rule(&self, r: &Thm) -> Option<Hyp> {
        self.same_hyps(crate::syl(self.thm(), r)?)
    }

    /// `Γ ⊢ φ → ψ` gives `Γ ⊢ ¬ψ → ¬φ`.
    pub fn contrapos(&self) -> Option<Hyp> {
        let (phi, psi) = self.concl().as_imp()?;
        let bridge = crate::a1i(&crate::contrapos_imp(phi, psi), order::conj(self.hyps()));
        self.same_hyps(crate::hyp_mp(&bridge, self.thm())?)
    }

    /// `Γ ⊢ ¬¬φ` gives `Γ ⊢ φ`. Classical.
    pub fn not_elim(&self) -> Option<Hyp> {
        let (not_phi, fls) = self.concl().as_imp()?;
        let (phi, fls2) = not_phi.as_imp()?;
        if fls != Formula::false_() || fls2 != Formula::false_() {
            return None
        }
        self.rule(&crate::notnot_elim(phi))
    }

    /// `Γ ⊢ ⊥` gives `Γ ⊢ χ` for any `χ`.
    pub fn absurd(&self, chi: &Formula) -> Option<Hyp> {
        if *self.concl() != Formula::false_() {
            return None
        }
        self.rule(&crate::ex_falso(chi.clone()))
    }
}
