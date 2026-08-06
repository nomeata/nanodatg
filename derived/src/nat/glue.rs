//! Equational and inductive glue for the arithmetic on `ω`.
//!
//! # Interface
//!
//! ```text
//! Chain::start(t)                     a running `⊢ t = t`
//! Chain::then(env, ⊢ b = c)           extends `⊢ a = b` to `⊢ a = c`
//! Chain::then_rev(env, ⊢ c = b)       the same, with the step read backwards
//! congr1(env, f, ⊢ a = b)             `⊢ f(a) = f(b)`
//! congr2_l / congr2_r                 the same at a binary symbol
//! induct(env, core, x, φ, base, step) `⊢ ∀x. (x ∈ ω → φ(x))`
//! ```
//!
//! # Why this file exists
//!
//! Every arithmetic lemma below is a chain of rewrites assembled under an
//! induction hypothesis. The kernel *has* hypotheses ([`Thm::assume`] /
//! [`Thm::implies_intr`]), and every derived rule this file calls propagates
//! them through [`Thm::mp`]'s union, so the natural-deduction shape is
//! available and there is no need for the combinator gymnastics
//! [`crate::recursion::hyp`] needs. What is missing is only the bookkeeping:
//! a chain of `eq_trans` calls written out by hand is unreadable at ten links,
//! and the induction scheme wants its two premises assembled in one particular
//! shape. Both are mechanical, and both are here so that no arithmetic file
//! repeats them.
//!
//! Nothing here is trusted and nothing here builds a `Thm` other than through
//! the kernel's own rules.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::recursion::induction::induction_scheme;
use crate::recursion::naturals::OmegaCore;
use crate::{and_intro, congr_arg, eq_symm, eq_trans};

/// A running equation `Γ ⊢ a = b`, extended on the right.
///
/// The point of the wrapper is that the *left* end never changes, so a
/// ten-link chain reads as ten steps rather than as ten nested `eq_trans`
/// calls whose intermediate terms have to be spelled out.
///
/// The links are **collected and folded at the end** rather than composed as
/// they arrive. That is not a performance choice: `eq_trans` needs a fresh
/// variable and therefore `&mut Env`, and a builder that took the environment
/// on every link could not have its links *computed* inline — every step of
/// every chain below is itself a congruence needing the same `&mut Env`, and
/// the borrow checker refuses the two at once. Deferring the folds to
/// [`Chain::done`] makes the natural spelling compile.
pub struct Chain {
    head: Thm,
    links: Vec<(Thm, bool)>,
}

impl Chain {
    /// Start at `⊢ t = t`.
    pub fn start(t: Term) -> Chain { Chain::from(Thm::eq_refl(t)) }

    /// Start from an equation already in hand.
    pub fn from(thm: Thm) -> Chain { Chain { head: thm, links: Vec::new() } }

    /// Extend `Γ ⊢ a = b` by `Δ ⊢ b = c`.
    pub fn then(mut self, step: Thm) -> Chain {
        self.links.push((step, false));
        self
    }

    /// Extend `Γ ⊢ a = b` by `Δ ⊢ c = b`, read backwards.
    pub fn then_rev(mut self, step: Thm) -> Chain {
        self.links.push((step, true));
        self
    }

    /// Fold the links into one equation.
    pub fn done(self, env: &mut Env) -> Option<Thm> {
        let mut acc = self.head;
        for (step, rev) in self.links {
            let s = if rev { eq_symm(env, &step)? } else { step };
            acc = eq_trans(env, &acc, &s)?;
        }
        Some(acc)
    }
}

/// From `Γ ⊢ a = b` and a **template** `t(x)` infer `Γ ⊢ t(a) = t(b)`.
///
/// [`crate::congr_arg`] rewrites one argument of one symbol; this rewrites at
/// an arbitrary position, named by putting a fresh variable there. The kernel
/// exposes no way to take a `Term` apart — `TermData` is `pub(crate)` — so a
/// context has to be *built* with its hole rather than found in a finished
/// term, which is the right discipline anyway: the caller says which occurrence
/// it means instead of hoping there is only one.
///
/// `x` must not occur in `a` or `b`.
pub fn congr_tmpl(env: &mut Env, x: FreeVar, tmpl: &Term, ab: &Thm) -> Option<Thm> {
    let _ = &env;
    let (a, b) = ab.concl().as_eq()?;
    if a.occurs_free(x) || b.occurs_free(x) {
        return None
    }
    let lhs = crate::subst_term(tmpl, &[(x, a.clone())]);
    let phi = Formula::eq(lhs.clone(), tmpl.clone());
    let leib = Thm::eq_leibniz(a, b, x, phi);
    let step = Thm::mp(&leib, ab)?;
    Thm::mp(&step, &Thm::eq_refl(lhs))
}

/// From `Γ ⊢ a = b` infer `Γ ⊢ f(a) = f(b)`, at a unary symbol.
pub fn congr1(env: &mut Env, f: FnSym, ab: &Thm) -> Option<Thm> {
    let (a, _) = ab.concl().as_eq()?;
    congr_arg(env, f, &[a], 0, ab)
}

/// From `Γ ⊢ a = b` infer `Γ ⊢ f(a, r) = f(b, r)`.
pub fn congr2_l(env: &mut Env, f: FnSym, ab: &Thm, r: &Term) -> Option<Thm> {
    let (a, _) = ab.concl().as_eq()?;
    congr_arg(env, f, &[a, r.clone()], 0, ab)
}

/// From `Γ ⊢ a = b` infer `Γ ⊢ f(l, a) = f(l, b)`.
pub fn congr2_r(env: &mut Env, f: FnSym, l: &Term, ab: &Thm) -> Option<Thm> {
    let (a, _) = ab.concl().as_eq()?;
    congr_arg(env, f, &[l.clone(), a], 1, ab)
}

/// `⊢ ∀x. (x ∈ ω → φ(x))` from `⊢ φ(0)` and `⊢ ∀x. ((x ∈ ω ∧ φ(x)) → φ(succ x))`.
///
/// A thin assembly over [`induction_scheme`]: it is that theorem's antecedent
/// that has to be built in exactly the right shape, and getting it wrong is a
/// `None` from `mp` a hundred lines from the mistake.
pub fn induct(
    env: &mut Env,
    core: &OmegaCore,
    x: FreeVar,
    phi: &Formula,
    base: &Thm,
    step: &Thm,
) -> Option<Thm> {
    let scheme = induction_scheme(env, core, x, phi)?;
    Thm::mp(&scheme, &and_intro(base, step))
}

/// Assemble the step premise of [`induct`] from a natural-deduction proof.
///
/// `body` is handed `⊢ x ∈ ω` and `⊢ φ(x)` — both under the hypothesis
/// `x ∈ ω ∧ φ(x)`, which this function then discharges — and must return
/// `φ(succ x)`.
pub fn induct_step<F>(
    core: &OmegaCore,
    x: FreeVar,
    phi: &Formula,
    body: F,
) -> Option<Thm>
where
    F: FnOnce(&Thm, &Thm) -> Option<Thm>,
{
    let tx = Term::var(x);
    let x_om = Formula::mem(tx, core.set());
    let h = Formula::and(x_om, phi.clone());
    let assumed = Thm::assume(h.clone());
    let x_om_thm = crate::and_elim_left(&assumed)?;
    let phi_thm = crate::and_elim_right(&assumed)?;
    let out = body(&x_om_thm, &phi_thm)?;
    let discharged = Thm::implies_intr(&h, &out);
    Thm::gen_checked(x, &discharged)
}
