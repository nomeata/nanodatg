//! `‖α‖` — propositional truncation, as a third conditional singleton.
//!
//! # Interface
//!
//! [`Trunc::new`] introduces the symbol and derives every theorem; the fields
//! *are* the theorems, so a caller reads them off the struct and never calls
//! anything below directly. Writing `‖a‖` for [`Trunc::of`], `1` for the unit
//! type, `0` for `∅` and `•` for the point:
//!
//! ```text
//! ‖a‖ := [∃x. x ∈ a]
//!
//! ⊢ ∀a ∀z. (z ∈ ‖a‖ ↔ (z ∈ 1 ∧ ∃x. x ∈ a))                     [Trunc::trunc_ax]
//! ⊢ ∀a ∀w. (w ∈ a → • ∈ ‖a‖)                                   [Trunc::intro]
//! ⊢ ∀a. (• ∈ ‖a‖ → ∃x. x ∈ a)                                  [Trunc::elim]
//! ⊢ ∀a ∀z. (z ∈ ‖a‖ → z ∈ 1)                    i.e. ‖a‖ ⊆ 1   [Trunc::subset]
//! ⊢ ∀a ∀x ∀y. ((x ∈ ‖a‖ ∧ y ∈ ‖a‖) → x = y)                    [Trunc::irrel]
//! ⊢ ‖1‖ = 1        ⊢ ‖0‖ = 0        ⊢ ¬(‖0‖ = ‖1‖)             [unit, zero, distinct]
//! ```
//!
//! # Why this is the whole of `‖·‖`
//!
//! The thesis interprets propositional truncation as
//! `⟦‖α‖⟧ = [⟦α⟧ ≠ ∅]` — a *truth value*, not a quotient — and both its term
//! formers interpret to the point: `⟦|e|⟧ = •` and `⟦rec_‖‖ f⟧ = •`
//! (thesis.txt:2109–2114). So the only thing there is to construct is the set,
//! and it is one instance of [`super::conditional_singleton`] at the formula
//! `∃x. x ∈ a`, exactly as `eq_set` and `and_set` are instances at `a = b` and
//! `• ∈ p ∧ • ∈ q`.
//!
//! That also settles what `intro` and `elim` have to say. `|e| = •` is typed by
//! [`Trunc::intro`]: an inhabitant of `a` puts `•` in `‖a‖`. The large
//! eliminator does not exist — truncation is *not* eliminable into arbitrary
//! types, which is the point of it — and the small one is
//! [`Trunc::elim`] composed with the caller's own reasoning, since the
//! conclusion of a `Prop`-valued eliminator is itself a subsingleton. There is
//! no recursor set to build.
//!
//! # Where it is used
//!
//! `‖·‖` is one of the eight menagerie types of §5.1 (thesis.txt:1900), and
//! thesis.txt:1696 makes it the reduction target of every `Prop`-valued
//! recursive inductive: §5.2's small-eliminator rule (thesis.txt:1813–1815)
//! wraps a W-type in it. Nothing in `derived/` consumes it yet; it is here so
//! that the `Prop`-valued half of §5.2 has its target already built.
//!
//! # Non-vacuity
//!
//! A subsingleton development is exactly where a vacuous result hides: every
//! lemma above would still be provable if `‖·‖` were the constant `1`, or the
//! constant `0`. Both polarities are therefore pinned at concrete sets —
//! `‖1‖ = 1` and `‖0‖ = 0`, via [`super::cond_true`] and [`super::cond_false`]
//! — and [`Trunc::distinct`] records that those two answers are *different
//! sets*, which is what makes `• ∈ ‖a‖` say something about `a`.
//!
//! # `‖a‖ ∈ U₀`
//!
//! Not derived here, because it needs no new derivation: `‖a‖` is a conditional
//! singleton, so [`crate::tower::Tower::cond_in_u0`] applies to it verbatim,
//! given `[Trunc::trunc_ax]` instantiated at `a`.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::sums::Sums;
use crate::{eq_symm, exists_intro_imp, gen_all, inst_all, syl};

use super::cond::{
    cond_elim, cond_false, cond_intro, cond_subset_unit, cond_subsingleton, cond_true,
    conditional_singleton,
};

/// Propositional truncation `‖a‖ = [∃x. x ∈ a]`, with every theorem about it.
///
/// Built over a **caller-supplied** [`Sums`], never a fresh one: the unit set
/// `1` and the point `•` come from it, and two `Sums` would mean two unrelated
/// `1`s and no theorem here would compose with the caller's. This is the same
/// discipline [`super::Props`] follows.
pub struct Trunc {
    /// `trunc(a) = ‖a‖`.
    pub trunc: FnSym,
    /// `⊢ ∀a ∀z. (z ∈ ‖a‖ ↔ (z ∈ 1 ∧ ∃x. x ∈ a))` — the characteristic theorem.
    pub trunc_ax: Thm,
    /// `⊢ ∀a ∀w. (w ∈ a → • ∈ ‖a‖)` — the typing of `|e|`.
    pub intro: Thm,
    /// `⊢ ∀a. (• ∈ ‖a‖ → ∃x. x ∈ a)` — soundness: the truncation is not
    /// vacuously inhabited.
    pub elim: Thm,
    /// `⊢ ∀a ∀z. (z ∈ ‖a‖ → z ∈ 1)`, i.e. `‖a‖ ⊆ 1`: a truncation is a `Prop`.
    pub subset: Thm,
    /// `⊢ ∀a ∀x ∀y. ((x ∈ ‖a‖ ∧ y ∈ ‖a‖) → x = y)` — proof irrelevance.
    pub irrel: Thm,
    /// `⊢ ‖1‖ = 1` — **non-vacuity**, positive polarity.
    pub unit: Thm,
    /// `⊢ ‖0‖ = 0` — **non-vacuity**, negative polarity.
    pub zero: Thm,
    /// `⊢ ¬(‖0‖ = ‖1‖)` — the two answers are different sets.
    pub distinct: Thm,
}

impl Trunc {
    /// Introduce `‖·‖` over `s` and derive every theorem, from the axioms up.
    ///
    /// Returns `None` if `s`'s stored theorems are not the ones this expects —
    /// in particular if `s.zero_empty` is not literally `¬(∃x. x ∈ 0)` for the
    /// `∅` that `s.zero()` names, which is what discharges [`Trunc::zero`].
    pub fn new(env: &mut Env, s: &Sums) -> Option<Trunc> {
        let a = env.fresh_var();
        let ta = Term::var(a);
        // The bound variable of the truncation's condition. It is fixed once,
        // here, because every later use of `∃x. x ∈ t` has to be *syntactically*
        // the formula the symbol was defined with.
        let x = env.fresh_var();
        let inhabited = |t: &Term| Formula::exists(x, Formula::mem(Term::var(x), t.clone()));

        let phi = inhabited(&ta);
        let (trunc, trunc_ax) = conditional_singleton(env, s, &[a], &phi)?;
        let of = |t: Term| Term::apply(trunc, vec![t]);

        let c_a = of(ta.clone());
        let chi_a = inst_all(&trunc_ax, std::slice::from_ref(&ta))?;

        // `w ∈ a → ∃x. x ∈ a`, composed with `φ → • ∈ [φ]`: the witness is the
        // element itself, so `intro` is stated at an element rather than at the
        // existential a caller would otherwise have to build.
        let wv = env.fresh_var();
        let witness = exists_intro_imp(x, Formula::mem(Term::var(x), ta.clone()), Term::var(wv))?;
        let intro = gen_all(&[a, wv], &syl(&witness, &cond_intro(s, &phi, &c_a, &chi_a)?)?);

        let elim = Thm::gen(a, &cond_elim(s, &phi, &c_a, &chi_a)?);
        let subset = Thm::gen(a, &cond_subset_unit(env, s, &phi, &c_a, &chi_a)?);
        let irrel = Thm::gen(a, &cond_subsingleton(env, s, &phi, &c_a, &chi_a)?);

        // ── Non-vacuity, both polarities ────────────────────────────────────
        let (zero, one) = (s.zero(), s.unit());
        let (c_zero, c_one) = (of(zero.clone()), of(one.clone()));

        let phi_one = inhabited(&one);
        let chi_one = inst_all(&trunc_ax, std::slice::from_ref(&one))?;
        let one_inhabited = Thm::mp(
            &exists_intro_imp(x, Formula::mem(Term::var(x), one.clone()), s.point())?,
            &s.unit_mem,
        )?;
        let unit = Thm::mp(&cond_true(env, s, &phi_one, &c_one, &chi_one)?, &one_inhabited)?;

        let phi_zero = inhabited(&zero);
        if *s.zero_empty.concl() != Formula::not(phi_zero.clone()) {
            return None
        }
        let chi_zero = inst_all(&trunc_ax, std::slice::from_ref(&zero))?;
        let zero_thm =
            Thm::mp(&cond_false(env, s, &phi_zero, &c_zero, &chi_zero)?, &s.zero_empty)?;

        let distinct = distinct(env, s, &zero_thm, &unit, &c_zero, &c_one)?;

        Some(Trunc { trunc, trunc_ax, intro, elim, subset, irrel, unit, zero: zero_thm, distinct })
    }

    /// The term `‖a‖`, the denotation of `‖α‖`.
    pub fn of(&self, a: Term) -> Term { Term::apply(self.trunc, vec![a]) }
}

/// `⊢ ¬(‖0‖ = ‖1‖)` — **the non-vacuity lemma**.
///
/// Two Leibniz rewrites on top of [`crate::sums::tags_distinct`]: `‖0‖ = 0` and
/// `‖1‖ = 1` carry `¬(0 = 1)` to `¬(‖0‖ = ‖1‖)`. Without it, every other
/// theorem in this file would survive `‖·‖` being constant, and "`•` inhabits
/// `‖a‖` exactly when `a` is inhabited" would say nothing.
fn distinct(
    env: &mut Env,
    s: &Sums,
    zero_thm: &Thm,
    unit: &Thm,
    c_zero: &Term,
    c_one: &Term,
) -> Option<Thm> {
    let (zero, one) = (s.zero(), s.unit());
    if *s.tags_distinct.concl() != Formula::not(Formula::eq(zero.clone(), one.clone())) {
        return None
    }

    // `⊢ ¬(0 = 1)` with `0` rewritten to `‖0‖`, then `1` to `‖1‖`.
    let h0 = env.fresh_var();
    let step0 = Thm::eq_leibniz(
        zero,
        c_zero.clone(),
        h0,
        Formula::not(Formula::eq(Term::var(h0), one.clone())),
    );
    let left = Thm::mp(&Thm::mp(&step0, &eq_symm(env, zero_thm)?)?, &s.tags_distinct)?;

    let h1 = env.fresh_var();
    let step1 = Thm::eq_leibniz(
        one,
        c_one.clone(),
        h1,
        Formula::not(Formula::eq(c_zero.clone(), Term::var(h1))),
    );
    let out = Thm::mp(&Thm::mp(&step1, &eq_symm(env, unit)?)?, &left)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(c_zero.clone(), c_one.clone())),
        "trunc distinct: unexpected shape"
    );
    Some(out)
}
