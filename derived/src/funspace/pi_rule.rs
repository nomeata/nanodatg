//! The general non-dependent `Π` typing rule: `fs(a,b) ∈ U(c)` for **any** two
//! members, and the Cartesian product that gets there.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → prod(a,b) ∈ U(c))          [product_in_universe_of]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → prod(a,b) ∈ U(c))   [product_in_universe]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))     [funspace_in_universe_pair]
//! ```
//!
//! The last two carry **no hypothesis about `U(c)`** — in particular not
//! `is_universe(U(c))`, whose inaccessibility clause is still open. Callers
//! need none of the derivations below.
//!
//! # What changed
//!
//! [`super::funspace_in_universe_of`] has always proved
//! `(a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c)`; the antecedent was the whole of what was
//! missing, and until 2026-07-31 it was not merely missing but **false** — see
//! countermodel B at the end of [`crate::universe`]. With the transitivity
//! clause `C₁` in `ax_tarski` and `⋃`-closure derived
//! ([`crate::universe::universe_union_closed`]), binary-union closure is
//! [`crate::universe::least_universe_bin_union`], and the antecedent
//! discharges.
//!
//! So [`funspace_in_universe_pair`] **retires the restriction to the diagonal**
//! `fs(a,a) ∈ U(a)` that [`super::funspace_in_universe`] was stuck at, and it
//! is the shape Lean's non-dependent `Π` rule wants: two types in a universe,
//! their function space in the same universe.
//!
//! [`product_in_universe`] is the same discharge applied one rung lower —
//! `prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` and `C₂` — and it is what the dependent case
//! ([`crate::ext::dprod_in_universe_of`]) consumes.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::{a1i, gen_all, hyp_mp, inst_all, syl};

use super::cartesian::Product;
use super::closure::{pow_closed, sub_closed};
use super::in_universe::Space;
use super::pow_pow::bin_union;
use super::space::Funspace;

/// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → prod(a,b) ∈ U(c))` — the product lands in any
/// universe containing the union of its factors.
///
/// Two power sets above `a ∪ b`, then [`super::product_subset_pow_pow`] and
/// `C₂`. This is the first half of [`super::funspace_in_universe_of`], stated
/// on its own because the dependent case needs the product and not the function
/// space.
pub fn product_in_universe_of(
    env: &mut Env,
    s: &Space,
    p: &Product,
    prod_pp: &Thm,
) -> Option<Thm> {
    let (a, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc) = (Term::var(a), Term::var(b), Term::var(c));
    let w = s.universe_of(tc.clone());

    let c2 = inst_all(&s.c2, std::slice::from_ref(&tc))?;
    let c3 = inst_all(&s.c3, std::slice::from_ref(&tc))?;
    let pc = pow_closed(env, s.pow, &s.pow_ax, &w, &c2, &c3)?;

    let un = bin_union(&s.sets, ta.clone(), tb.clone());
    let pu = Term::apply(s.pow, vec![un.clone()]);
    let ppu = Term::apply(s.pow, vec![pu.clone()]);
    let h_pu = inst_all(&pc, std::slice::from_ref(&un))?;
    let h = h_pu.concl().as_imp()?.0;
    if h != Formula::mem(un, w.clone()) {
        return None
    }
    let h_ppu = syl(&h_pu, &inst_all(&pc, std::slice::from_ref(&pu))?)?;

    let prod_t = p.of(ta.clone(), tb.clone());
    let prod_sub = inst_all(prod_pp, &[ta.clone(), tb.clone()])?;
    if *prod_sub.concl() != kernel::thm::subset(env, prod_t.clone(), ppu.clone()) {
        return None
    }
    let out = hyp_mp(
        &syl(&h_ppu, &sub_closed(&c2, &ppu, &prod_t)?)?,
        &a1i(&prod_sub, h.clone()),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(prod_t, w)),
        "product_in_universe_of: wrong shape"
    );
    Some(gen_all(&[a, b, c], &out))
}

/// Discharge an `(a ∪ b) ∈ U(c)` antecedent with
/// [`crate::universe::least_universe_bin_union`].
///
/// `general` must be `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → φ(a,b) ∈ U(c))` and
/// `bin_union_closed` `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))`,
/// both for the same `U` and the same pairing; the result is
/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → φ(a,b) ∈ U(c))`.
///
/// Shared by [`product_in_universe`] and [`funspace_in_universe_pair`], which
/// differ only in what `φ` is.
fn discharge_union(
    env: &mut Env,
    s: &Space,
    sets: &Sets,
    general: &Thm,
    bin_union_closed: &Thm,
) -> Option<Thm> {
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = s.universe_of(tc.clone());
    let un = bin_union(sets, ta.clone(), tb.clone());

    let mems = Formula::and(
        Formula::mem(ta.clone(), w.clone()),
        Formula::mem(tb.clone(), w.clone()),
    );
    let bu_at = inst_all(bin_union_closed, &[tc.clone(), ta.clone(), tb.clone()])?;
    if *bu_at.concl() != Formula::imp(mems.clone(), Formula::mem(un.clone(), w.clone())) {
        return None
    }
    let gen_at = inst_all(general, &[ta, tb, tc])?;
    let (ante, goal) = gen_at.concl().as_imp()?;
    if ante != Formula::mem(un, w.clone()) {
        return None
    }
    let out = syl(&bu_at, &gen_at)?;
    debug_assert_eq!(*out.concl(), Formula::imp(mems, goal), "discharge_union: wrong shape");
    Some(gen_all(&[cv, av, bv], &out))
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → prod(a,b) ∈ U(c))` — **`U(c)` is
/// closed under Cartesian products**.
///
/// [`product_in_universe_of`] with its antecedent discharged by
/// [`crate::universe::least_universe_bin_union`].
pub fn product_in_universe(
    env: &mut Env,
    s: &Space,
    p: &Product,
    general: &Thm,
    bin_union_closed: &Thm,
) -> Option<Thm> {
    let sets = s.sets.clone();
    let out = discharge_union(env, s, &sets, general, bin_union_closed)?;
    // Pin the conclusion to the product, so a `general` about something else is
    // refused rather than silently described as a product theorem.
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = s.universe_of(tc.clone());
    let at = inst_all(&out, &[tc, ta.clone(), tb.clone()])?;
    if at.concl().as_imp()?.1 != Formula::mem(p.of(ta, tb), w) {
        return None
    }
    Some(out)
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c))` — **the general
/// non-dependent `Π` typing rule**.
///
/// [`super::funspace_in_universe_of`] with its antecedent discharged by
/// [`crate::universe::least_universe_bin_union`]. This is the statement that
/// retires the restriction to the diagonal `fs(a,a) ∈ U(a)`
/// ([`super::funspace_in_universe`]): the function space of any two members of
/// `U(c)` is a member of `U(c)`.
pub fn funspace_in_universe_pair(
    env: &mut Env,
    s: &Space,
    fs: &Funspace,
    general: &Thm,
    bin_union_closed: &Thm,
) -> Option<Thm> {
    let sets = s.sets.clone();
    let out = discharge_union(env, s, &sets, general, bin_union_closed)?;
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = s.universe_of(tc.clone());
    let at = inst_all(&out, &[tc, ta.clone(), tb.clone()])?;
    if at.concl().as_imp()?.1 != Formula::mem(fs.of(ta, tb), w) {
        return None
    }
    Some(out)
}
