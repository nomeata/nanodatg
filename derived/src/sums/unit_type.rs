//! The unit type `1`, the empty type `0`, and the fact the two tags differ.
//!
//! # Interface
//!
//! ```text
//! ⊢ • ∈ 1                                  [unit_mem]
//! ⊢ ∀x. (x ∈ 1 → x = •)                    [unit_eta]
//! ⊢ ¬(∃x. x ∈ 0)                           [zero_empty]
//! ⊢ ¬(∅ = 1)                               [tags_distinct]
//! ```
//!
//! with `0 = • = ∅` and `1 = {∅}`. Callers need none of the derivations below;
//! all four are reached through [`super::Sums`], which stores them as fields.
//!
//! # Why `tags_distinct` is here and not assumed
//!
//! `inl(a) = ⟨∅, a⟩` and `inr(b) = ⟨1, b⟩`, so the whole sum construction rests
//! on the two tags being *different sets*. Were they equal,
//! [`super::sum_disjoint`] would be a statement about one tag and would prove
//! nothing. It is cheap — if `∅` were `{∅}` then `∅ ∈ {∅}` would carry across
//! the equation to `∅ ∈ ∅`, which the empty set refutes — but it is the one
//! place the *choice* of tags matters, so it is derived and tested rather than
//! taken on trust.
//!
//! [`unit_eta`] is the η-rule in embryo: a set-theoretic function into `1` is
//! determined, because every value it can take is `•`. [`zero_empty`] is
//! nothing new, just [`crate::empty::empty`]'s theorem in `¬∃` shape.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::{
    eq_symm_imp, iff_mp, iff_mpr, inst_all, mpd_const, notnot_intro, singleton, syl,
};

use super::shared::carry_mem;

/// `⊢ • ∈ 1` — the point inhabits the unit type.
///
/// `1` is `{∅}` and `•` is `∅`, so this is membership in a singleton at its own
/// element: reflexivity, cashed through [`crate::mem_singleton`].
pub fn unit_mem(ap: &Apply) -> Option<Thm> {
    let e = Term::apply(ap.empty, vec![]);
    let ms = inst_all(&ap.mem_sing, &[e.clone(), e.clone()])?;
    let out = Thm::mp(&iff_mpr(&ms)?, &Thm::eq_refl(e.clone()))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(e.clone(), singleton(ap.sets.up, e)),
        "unit_mem: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀x. (x ∈ 1 → x = •)` — the unit type is a subsingleton.
///
/// This is the η-rule in embryo: a set-theoretic function into `1` is
/// determined, because every value it can take is `•`.
pub fn unit_eta(env: &mut Env, ap: &Apply) -> Option<Thm> {
    let e = Term::apply(ap.empty, vec![]);
    let x = env.fresh_var();
    let tx = Term::var(x);
    let ms = inst_all(&ap.mem_sing, &[e.clone(), tx.clone()])?;
    let out = Thm::gen(x, &iff_mp(&ms)?);
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), singleton(ap.sets.up, e.clone())),
                Formula::eq(tx, e)
            )
        ),
        "unit_eta: unexpected shape"
    );
    Some(out)
}

/// `⊢ ¬(∃x. x ∈ 0)` — the empty type has no inhabitants.
///
/// Nothing new: `⊢ ∀z. ¬(z ∈ ∅)` is [`crate::empty::empty`]'s theorem, and
/// `∃` is `¬∀¬`, so `¬∃x. x ∈ ∅` *is* `¬¬∀z. ¬(z ∈ ∅)` — one double-negation
/// introduction away.
pub fn zero_empty(ap: &Apply) -> Thm {
    let phi = ap.empty_ax.concl().clone();
    Thm::mp(&notnot_intro(phi), &ap.empty_ax).expect("zero_empty: double negation applies")
}

/// `⊢ ¬(∅ = 1)` — the two tags of the sum are different sets.
///
/// **The lemma disjointness stands on.** If `∅` were `{∅}` then `∅ ∈ {∅}`
/// would carry across the equation to `∅ ∈ ∅`, which the empty set refutes.
/// Were the two tags equal, [`super::sum_disjoint`] would be a statement about one
/// tag and would prove nothing.
pub fn tags_distinct(env: &mut Env, ap: &Apply, unit_mem: &Thm) -> Option<Thm> {
    let e = Term::apply(ap.empty, vec![]);
    let u = singleton(ap.sets.up, e.clone());

    // ⊢ {∅} = ∅ → (∅ ∈ {∅} → ∅ ∈ ∅), discharged by `unit_mem`.
    let carry = carry_mem(env, e.clone(), u.clone(), e.clone());
    let to_self = mpd_const(&carry, unit_mem)?;
    // ⊢ ¬(∅ ∈ ∅), so the antecedent is refuted.
    let not_self = inst_all(&ap.empty_ax, std::slice::from_ref(&e))?;
    let ne = syl(&to_self, &not_self)?; // ⊢ ¬({∅} = ∅)

    // Turn it around: `∅ = {∅} → {∅} = ∅` composes with the negation.
    let out = syl(&eq_symm_imp(env, e.clone(), u.clone()), &ne)?;
    debug_assert_eq!(*out.concl(), Formula::not(Formula::eq(e, u)), "tags_distinct: unexpected shape");
    Some(out)
}
