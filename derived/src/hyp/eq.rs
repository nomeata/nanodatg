//! **SUPERSEDED.** Part of the above-kernel deduction layer; see the
//! "SUPERSEDED" section of `derived/src/hyp.rs`. Kept as the experiment.
//!
//! The equality operations on [`Hyp`].
//!
//! # Interface
//!
//! ```text
//!   Hyp::eq_refl(t)             {} ⊢ t = t
//!   a.symm(env)                 Γ ⊢ a=b ⟹ Γ ⊢ b=a
//!   a.trans(env, &b)            Γ ⊢ a=b,  Δ ⊢ b=c        ⟹ Γ∪Δ ⊢ a=c
//!   a.leibniz(w, &φ)            Γ ⊢ a=b ⟹ Γ ⊢ φ[a/w] → φ[b/w]
//!   a.subst(w, &φ, &b)          Γ ⊢ a=b,  Δ ⊢ φ[a/w]     ⟹ Γ∪Δ ⊢ φ[b/w]
//!   a.congr_arg(env, f, args, i)  Γ ⊢ a=b ⟹ Γ ⊢ f(..a..) = f(..b..)
//! ```
//!
//! # Why these are not just `eq_symm` and friends
//!
//! [`crate::eq_symm`], [`crate::eq_trans`] and [`crate::congr_arg`] all consume
//! a *proved* equation. In a derivation of any size the equations are only
//! available under assumptions, which is why `ext/shared.rs` keeps
//! `hyp_leibniz`, `hyp_congr`, `hyp_eq_trans` and `hyp_eq_symm` — the same four
//! operations, at one fixed hypothesis. These are those four with the
//! restriction lifted: `trans` and `subst` union-merge, so the two equations
//! need not have been proved under the same assumptions.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use super::{order, Hyp};

impl Hyp {
    /// `{} ⊢ t = t`.
    pub fn eq_refl(t: Term) -> Hyp { Hyp::lift(&Thm::eq_refl(t)) }

    /// `Γ ⊢ a = b` gives `Γ ⊢ b = a`.
    pub fn symm(&self, env: &mut Env) -> Option<Hyp> {
        let (a, b) = self.concl().as_eq()?;
        self.rule(&crate::eq_symm_imp(env, a, b))
    }

    /// `Γ ⊢ a = b` and `Δ ⊢ b = c` give `Γ ∪ Δ ⊢ a = c`.
    pub fn trans(&self, env: &mut Env, next: &Hyp) -> Option<Hyp> {
        let (a, b1) = self.concl().as_eq()?;
        let (b2, c) = next.concl().as_eq()?;
        if b1 != b2 {
            return None
        }
        let (hs, ab, bc) = Hyp::merge(self, next)?;
        // Leibniz on `b = c` with the hole in `a = ·`.
        let w = env.fresh_var();
        let leib = Thm::eq_leibniz(b1, c, w, Formula::eq(a, Term::var(w)));
        let under = crate::a1i(&leib, order::conj(&hs));
        Hyp::wrap(hs, crate::hyp_mp(&crate::hyp_mp(&under, &bc)?, &ab)?)
    }

    /// `Γ ⊢ a = b` gives `Γ ⊢ φ[a/w] → φ[b/w]` — Leibniz under the hypotheses.
    pub fn leibniz(&self, w: FreeVar, phi: &Formula) -> Option<Hyp> {
        let (a, b) = self.concl().as_eq()?;
        let leib = Thm::eq_leibniz(a, b, w, phi.clone());
        let under = crate::a1i(&leib, order::conj(self.hyps()));
        self.same_hyps(crate::hyp_mp(&under, self.thm())?)
    }

    /// `Γ ⊢ a = b` and `Δ ⊢ φ[a/w]` give `Γ ∪ Δ ⊢ φ[b/w]` — rewriting.
    pub fn subst(&self, w: FreeVar, phi: &Formula, at: &Hyp) -> Option<Hyp> {
        self.leibniz(w, phi)?.mp(at)
    }

    /// `Γ ⊢ a = b` gives `Γ ⊢ f(t₀..a..tₙ) = f(t₀..b..tₙ)`, replacing argument
    /// `idx`.
    ///
    /// `args` must already have `a` at `idx`; that is checked. Congruence in
    /// every argument at once is [`crate::congr`] and is not lifted here,
    /// because it consumes a slice of proved equations and the useful lifted
    /// form — a slice of `Hyp`s, merged — has no caller yet.
    pub fn congr_arg(&self, env: &mut Env, f: FnSym, args: &[Term], idx: usize) -> Option<Hyp> {
        let (a, b) = self.concl().as_eq()?;
        if idx >= args.len() || args.get(idx) != Some(&a) {
            return None
        }
        let lhs = Term::apply(f, args.to_vec());
        let x = env.fresh_var();
        let mut hole = args.to_vec();
        hole[idx] = Term::var(x);
        // `φ(x) := f(..a..) = f(..x..)`, so Leibniz turns reflexivity at `a`
        // into the equation at `b`.
        let leib = Thm::eq_leibniz(a, b, x, Formula::eq(lhs.clone(), Term::apply(f, hole)));
        self.rule(&crate::mpd_const(&leib, &Thm::eq_refl(lhs))?)
    }
}
