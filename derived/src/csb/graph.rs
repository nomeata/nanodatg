//! Cantor–Schröder–Bernstein at two **set** graphs.
//!
//! # Interface
//!
//! With `INJECTION(f,a,b)` the [`injection`](super::clauses::injection) of
//! [`super::clauses`] — `kernel::thm::equinumerous`'s body with the *onto*
//! clause deleted, in the same described-pair spelling — and `≈` that
//! `equinumerous`:
//!
//! ```text
//! ⊢ ∀a ∀b ∀f ∀g. ((INJECTION(f,a,b) ∧ INJECTION(g,b,a)) → a ≈ b)
//!                                                       [schroeder_bernstein]
//! ```
//!
//! Callers need no derivation; the statement above is the whole contract, and
//! [`injection`](super::clauses::injection) is how a caller builds its half of
//! it.
//!
//! # What this file actually does
//!
//! **A reassociation, and nothing else.** [`super::csb_scheme`] proves the
//! theorem at two arbitrary two-variable formulas, and the set relations
//! `⟨x,y⟩ ∈ f` and `⟨y,x⟩ ∈ g` are one instance of it. The scheme lists its eight
//! clauses in one flat right-nested conjunction; a caller holding two
//! *injections* holds them as two conjunctions of four. Turning the second shape
//! into the first is the whole content here.
//!
//! That the clauses line up at all is worth one sentence: `G` runs from `b` to
//! `a`, so its four clauses are [`super::clauses`]'s four builders with the two
//! distinguished variables and the two sets swapped — which is exactly what
//! `INJECTION(g,b,a)` is. No translation layer, and in particular no converse
//! graph, is built anywhere.
//!
//! # Why this is not the form the waiting consumer uses
//!
//! `crate::universe::inaccessibility` has `y ⊆ U(x) ⊆ u` and a bijection
//! `y ≈ u`, and neither of the two injections it needs exists as a *set* in its
//! hands: they are the inclusion `y ↪ U(x)` and the converse of that bijection
//! restricted to `U(x)`. Building them would be two Replacements and eight more
//! clauses to prove about the results. [`super::sandwich`] instantiates the
//! scheme at the two *formulas* instead. This file is therefore the general
//! statement rather than the one on the critical path.

use kernel::{Env, Formula, Term, Thm};

use crate::{and_left, and_right, conj_of, conj_proj, gen_all, hyp_and, syl};

use super::bijection::{csb_clauses, csb_scheme};
use super::prereq::Csb;

/// `⊢ ∀a ∀b ∀f ∀g. ((INJECTION(f,a,b) ∧ INJECTION(g,b,a)) → a ≈ b)` —
/// **Cantor–Schröder–Bernstein**.
///
/// Nothing is assumed: the four sets are universally quantified and the only
/// hypothesis is the two injections. See the module header for why this is a
/// reassociation of [`csb_scheme`] and not a second proof.
pub fn schroeder_bernstein(env: &mut Env, s: &Csb) -> Option<Thm> {
    let (a, b, f, g) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf, tg) = (Term::var(a), Term::var(b), Term::var(f), Term::var(g));
    let (xv, bv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(bv));

    let f_rel = kernel::thm::pair_in(env, tf.clone(), tx.clone(), ty.clone());
    let g_rel = kernel::thm::pair_in(env, tg.clone(), ty, tx);

    let atoms = csb_clauses(env, &f_rel, &g_rel, xv, bv, &ta, &tb)?;
    let scheme = csb_scheme(env, s, &f_rel, &g_rel, xv, bv, &ta, &tb)?;

    // The caller's two halves, and the check that they really are the scheme's
    // eight clauses split down the middle.
    let inj_f = super::clauses::injection(env, &tf, &ta, &tb)?;
    let inj_g = super::clauses::injection(env, &tg, &tb, &ta)?;
    debug_assert_eq!(
        inj_f,
        conj_of(&atoms[0..4])?,
        "schroeder_bernstein: INJECTION(f,a,b) is not the scheme's first four clauses"
    );
    debug_assert_eq!(
        inj_g,
        conj_of(&atoms[4..8])?,
        "schroeder_bernstein: INJECTION(g,b,a) is not the scheme's last four clauses"
    );

    let p = Formula::and(inj_f.clone(), inj_g.clone());
    let p_f = and_left(inj_f.clone(), inj_g.clone());
    let p_g = and_right(inj_f, inj_g);
    let parts: Vec<Thm> = (0..8)
        .map(|i| {
            if i < 4 {
                syl(&p_f, &conj_proj(&atoms[0..4], i)?)
            } else {
                syl(&p_g, &conj_proj(&atoms[4..8], i - 4)?)
            }
        })
        .collect::<Option<_>>()?;
    let mut acc = parts[7].clone();
    for part in parts[..7].iter().rev() {
        acc = hyp_and(part, &acc)?;
    }
    debug_assert_eq!(
        *acc.concl(),
        Formula::imp(p.clone(), conj_of(&atoms)?),
        "schroeder_bernstein: the two injections do not reassemble into the scheme's hypothesis"
    );

    let out = gen_all(&[a, b, f, g], &syl(&acc, &scheme)?);
    let body = Formula::imp(p, kernel::thm::equinumerous(env, ta, tb));
    let want = Formula::forall(
        a,
        Formula::forall(b, Formula::forall(f, Formula::forall(g, body))),
    );
    debug_assert_eq!(*out.concl(), want, "schroeder_bernstein: wrong shape");
    Some(out)
}
