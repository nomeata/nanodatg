//! Closure under the **binary** union `a ∪ b`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → (a ∪ b) ∈ u)  [universe_bin_union]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))            [least_universe_bin_union]
//! ```
//!
//! writing `a ∪ b` for [`crate::funspace::bin_union`], i.e. `⋃{a,b}` — a
//! composition of existing symbols, so there is no new definitional extension
//! and no new proof obligation about the *term*.
//!
//! # Why this is now two lines of composition
//!
//! `a ∪ b` **is** `⋃{a,b}`, so binary-union closure is unordered-pairing
//! closure followed by `⋃`-closure, and nothing else. Pairing has been
//! available since [`super::universe_pairing`]; the union half is
//! [`super::universe_union_closed`]. Both are stated at an arbitrary universe,
//! so both transfer through the intersection, and the `U(c)` form is the same
//! composition one level down.
//!
//! This is the antecedent [`crate::funspace::funspace_in_universe_of`] and
//! [`crate::ext::dprod_in_universe_of`] were carrying, and discharging it is
//! what turns the diagonal restriction `fs(a,a) ∈ U(a)` into the general
//! non-dependent `Π` rule; see
//! [`crate::funspace::funspace_in_universe_pair`].

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Sets;
use crate::funspace::bin_union;
use crate::{a1i, and_left, gen_all, hyp_and, hyp_mp, inst_all, syl};

use super::predicate::is_universe;

/// `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → (a ∪ b) ∈ u)` — **every
/// universe is closed under binary union**.
///
/// `{a,b} ∈ u` by [`super::universe_pairing`], then `⋃{a,b} ∈ u` by
/// [`super::universe_union_closed`]. Both arguments are rebuilt at our own
/// terms and compared, so a mismatched pair of theorems yields `None`.
pub fn universe_bin_union(
    env: &mut Env,
    sets: &Sets,
    pairing: &Thm,
    union_closed: &Thm,
) -> Option<Thm> {
    let (uv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(uv), Term::var(av), Term::var(bv));
    let pair = Term::apply(sets.up, vec![ta.clone(), tb.clone()]);
    let un = bin_union(sets, ta.clone(), tb.clone());
    debug_assert_eq!(un, sets.union_of(pair.clone()), "a ∪ b is not ⋃{{a,b}}");

    let univ_u = is_universe(env, &tu);
    let mems = Formula::and(
        Formula::mem(ta.clone(), tu.clone()),
        Formula::mem(tb.clone(), tu.clone()),
    );
    let h = Formula::and(univ_u.clone(), mems.clone());
    let h_univ = and_left(univ_u.clone(), mems.clone());

    let pairing_at = inst_all(pairing, &[tu.clone(), ta.clone(), tb.clone()])?;
    if *pairing_at.concl() != Formula::imp(h.clone(), Formula::mem(pair.clone(), tu.clone())) {
        return None
    }
    let uc_at = inst_all(union_closed, &[tu.clone(), pair.clone()])?;
    if *uc_at.concl()
        != Formula::imp(
            Formula::and(is_universe(env, &tu), Formula::mem(pair.clone(), tu.clone())),
            Formula::mem(un.clone(), tu.clone()),
        )
    {
        return None
    }
    let out = hyp_mp(&a1i(&uc_at, h.clone()), &hyp_and(&h_univ, &pairing_at)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(un, tu)),
        "universe_bin_union: wrong shape"
    );
    Some(gen_all(&[uv, av, bv], &out))
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))` — **`U(c)` is closed
/// under binary union**, with no hypothesis at all.
///
/// The same composition one level down: [`super::least_universe_pairing`] then
/// [`super::least_universe_union`], both of which are already unconditional
/// because they transfer through the intersection. `is_universe(U(c))` is
/// nowhere needed.
///
/// This is the exact statement `crate::funspace` and `crate::ext` record as the
/// missing ingredient, and it was **refutable** before the transitivity clause
/// was added to `ax_tarski` on 2026-07-31 — see countermodel B at the end of
/// [`crate::universe`], which puts `{W₁}` and `𝒫{W₂}` in a universe whose
/// binary union is outside it.
pub fn least_universe_bin_union(
    env: &mut Env,
    lu: FnSym,
    sets: &Sets,
    least_pairing: &Thm,
    least_union: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let pair = Term::apply(sets.up, vec![ta.clone(), tb.clone()]);
    let un = bin_union(sets, ta.clone(), tb.clone());

    let a_in = Formula::mem(ta.clone(), w.clone());
    let b_in = Formula::mem(tb.clone(), w.clone());
    let h = Formula::and(a_in, b_in);

    let pairing_at = inst_all(least_pairing, &[tc.clone(), ta.clone(), tb.clone()])?;
    if *pairing_at.concl() != Formula::imp(h.clone(), Formula::mem(pair.clone(), w.clone())) {
        return None
    }
    let union_at = inst_all(least_union, &[tc.clone(), pair.clone()])?;
    if *union_at.concl()
        != Formula::imp(
            Formula::mem(pair, w.clone()),
            Formula::mem(un.clone(), w.clone()),
        )
    {
        return None
    }
    let out = syl(&pairing_at, &union_at)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(un, w)),
        "least_universe_bin_union: wrong shape"
    );
    Some(gen_all(&[cv, av, bv], &out))
}
