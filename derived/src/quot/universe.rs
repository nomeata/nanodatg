//! **`⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))`** — the quotient is small.
//!
//! # The route, and why it is three lines
//!
//! `quot(A,R)` is carved by Separation out of `𝒫A`
//! ([`super::classes::quot_symbol`]), so the left conjunct of its defining
//! biconditional gives `quot(A,R) ⊆ 𝒫A` for nothing. `U(c)` is closed under the
//! power set and under subsets-of-members (`C₂`), and those two close it:
//!
//! ```text
//! A ∈ U(c)              given
//! 𝒫A ∈ U(c)             pow_all
//! quot(A,R) ⊆ 𝒫A        the Separation's own left conjunct
//! ───────────────────────────────────────────── C₂  sub_all
//! quot(A,R) ∈ U(c)
//! ```
//!
//! **Nothing about `R` is needed**, which is worth being explicit about: the
//! bound is on the *carrier*, and a quotient by a larger relation is a smaller
//! set. Nor is anything about `A` beyond its membership — no equivalence
//! property, no `Fin`, no size argument. This is the cheapest universe theorem
//! in the crate and the contrast with [`crate::cumul::DeclUniverse`] is the
//! point: a W-type needs a cumulative hierarchy because it is not a subset of
//! anything already in hand, and a quotient is.
//!
//! # One power set, not two — the thesis's bound is coarse
//!
//! `thesis.txt:2355` places the quotient in the **double** powerset of `ᾱ`. One
//! suffices here and the difference is not an improvement in the argument but a
//! difference in what the object is: a class `class(A,R,x)` is a *subset of `A`*
//! ([`super::classes::class_subset`]), so the quotient is a set of subsets of
//! `A` and lands in `𝒫A`. The thesis's `𝒫𝒫ᾱ` is a bound on a construction that
//! carries the classes as sets of pairs or as an image; it is coarse rather than
//! wrong. **Do not widen this to match it** — the extra `𝒫` would cost a second
//! closure step for no statement anyone wants.
//!
//! # `c ≥ 1`, and rung 0 is not merely unproved
//!
//! The statement is about `U(c)`, the least universe over a seed, and every rung
//! of [`crate::tower`] from 1 upward is of that form. **Rung 0 is not**, and the
//! theorem is false there: `U₀ = {0,1}`, `quot(1,R) = 1` for the one-point
//! carrier, and `{1} ∈ U₀` is refutable. That is not a gap to be closed —
//! `QUOT-MODEL.md` §2 establishes that at `Sort 0` the interpretation is the
//! **identity**, `⟦Quot α r⟧ = ⟦α⟧`, and `derived/src/quot/` is not consulted at
//! all. So the `c ≥ 1` restriction is where the two branches meet, not a
//! weakness of this route.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))                  [quot_in_universe]
//! ⊢ ∀A ∀R. quot(A,R) ⊆ 𝒫A                                    [quot_subset_pow]
//! ```
//!
//! # Why the two closure theorems are arguments
//!
//! `U(·)`'s closure clauses live in [`crate::tower`], which is a large
//! apparatus this module otherwise does not need — and there is more than one
//! `𝒫` symbol in a typical `Env` ([`crate::cumul::Chain`]'s header records
//! three). So `pow_all` and `sub_all` are handed in and their statements
//! **rebuilt and compared** against this `Sums`' own `𝒫` and the caller's `U(·)`,
//! exactly as [`crate::bound::Bound::over`] takes `lu` and `lu_ax`. A theorem
//! about somebody else's power set is refused rather than composed.
//!
//! # Nothing here is an axiom
//!
//! No symbol is introduced and no Separation is performed; both theorems are
//! consequences of `quot_ax` and the two closure clauses.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::sums::Sums;
use crate::{and_left, gen_all, hyp_mp, iff_mp, inst_all, syl};

use super::classes::quot_cond;
use super::shared::sums_unconditional;

/// `⊢ ∀A ∀R. quot(A,R) ⊆ 𝒫A` — a class is a subset of `A`, so the quotient is a
/// set of them.
///
/// The left conjunct of [`super::classes::quot_symbol`]'s biconditional, under
/// one `∀`. The subset formula is rebuilt and compared in release: it is the
/// whole of what this advertises.
pub fn quot_subset_pow(
    env: &mut Env,
    s: &Sums,
    class: FnSym,
    quot: FnSym,
    quot_ax: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[quot_ax]) {
        return None
    }
    let (av, rv, cv, xv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tc) = (Term::var(av), Term::var(rv), Term::var(cv));
    let pow_a = Term::apply(s.pow, vec![ta.clone()]);
    let quot_t = Term::apply(quot, vec![ta.clone(), tr.clone()]);

    // The biconditional, rebuilt — this is what ties `quot_ax` to *this* `quot`,
    // *this* `class` and *this* power set all at once.
    let cond = quot_cond(class, &ta, &tr, &tc, xv);
    let mem_pow = Formula::mem(tc.clone(), pow_a.clone());
    let at = inst_all(quot_ax, &[ta.clone(), tr.clone(), tc.clone()])?;
    if *at.concl()
        != Formula::iff(
            Formula::mem(tc.clone(), quot_t.clone()),
            Formula::and(mem_pow.clone(), cond.clone()),
        )
    {
        return None
    }
    let body = syl(&iff_mp(&at)?, &and_left(mem_pow, cond))?;
    let out = Thm::gen(cv, &body);
    if *out.concl() != kernel::thm::subset(env, quot_t, pow_a) {
        return None
    }
    Some(gen_all(&[av, rv], &out))
}

/// **`⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))`** — the quotient of a small
/// carrier is small, at every rung `c ≥ 1`.
///
/// `pow_all` must be `⊢ ∀c ∀y. (y ∈ U(c) → 𝒫y ∈ U(c))` and `sub_all`
/// `⊢ ∀c ∀y. (y ∈ U(c) → ∀z. (z ⊆ y → z ∈ U(c)))`, both at the caller's `lu`
/// and at **this** `Sums`' power set — [`crate::tower::Tower`]'s `pow` and
/// `sub`, or [`crate::cumul::Chain`]'s `pow_all` and `sub_all`. Both statements
/// are rebuilt and compared, and both must rest on nothing; see the header for
/// why they are arguments.
///
/// `None` on a hypothetical or foreign input, and on a `quot_ax` that is not
/// this `quot`'s.
#[allow(clippy::too_many_arguments)]
pub fn quot_in_universe(
    env: &mut Env,
    s: &Sums,
    class: FnSym,
    quot: FnSym,
    quot_ax: &Thm,
    lu: FnSym,
    pow_all: &Thm,
    sub_all: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[pow_all, sub_all]) {
        return None
    }
    let sub_pow = quot_subset_pow(env, s, class, quot, quot_ax)?;

    let (av, rv, cv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tc) = (Term::var(av), Term::var(rv), Term::var(cv));
    let u_c = Term::apply(lu, vec![tc.clone()]);
    let pow_a = Term::apply(s.pow, vec![ta.clone()]);
    let quot_t = Term::apply(quot, vec![ta.clone(), tr.clone()]);

    // `⊢ A ∈ U(c) → 𝒫A ∈ U(c)`, checked against the statement rebuilt here.
    let pow_at = inst_all(pow_all, &[tc.clone(), ta.clone()])?;
    if *pow_at.concl()
        != Formula::imp(
            Formula::mem(ta.clone(), u_c.clone()),
            Formula::mem(pow_a.clone(), u_c.clone()),
        )
    {
        return None
    }

    // `⊢ 𝒫A ∈ U(c) → ∀z. (z ⊆ 𝒫A → z ∈ U(c))`, likewise.
    let sub_at = inst_all(sub_all, &[tc.clone(), pow_a.clone()])?;
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let want_sub = Formula::imp(
        Formula::mem(pow_a.clone(), u_c.clone()),
        Formula::forall(
            zv,
            Formula::imp(
                kernel::thm::subset(env, tz.clone(), pow_a.clone()),
                Formula::mem(tz, u_c.clone()),
            ),
        ),
    );
    if *sub_at.concl() != want_sub {
        return None
    }

    // Compose: `A ∈ U(c)` gives `𝒫A ∈ U(c)`, then `C₂` at `quot(A,R)`.
    let chained = syl(&pow_at, &sub_at)?;
    let (_, all) = chained.concl().as_imp()?;
    let at_quot = syl(&chained, &Thm::ax_inst(all, quot_t.clone())?)?;
    let sub_at_ar = inst_all(&sub_pow, &[ta.clone(), tr.clone()])?;
    let out = hyp_mp(&at_quot, &crate::a1i(&sub_at_ar, Formula::mem(ta.clone(), u_c.clone())))?;

    if !crate::establishes(
        &out,
        &Formula::imp(Formula::mem(ta, u_c.clone()), Formula::mem(quot_t, u_c)),
    ) {
        return None
    }
    Some(gen_all(&[av, rv, cv], &out))
}
