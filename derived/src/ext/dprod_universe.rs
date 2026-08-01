//! Lean's Π typing rule: a dependent product lands in a universe.
//!
//! # Interface
//!
//! Writing `U(c)` for [`crate::universe::least_universe`] and `img(A)` for the
//! fibre image of the [`crate::ext::DProd`], the exports are
//!
//! ```text
//! ⊢ ∀A ∀c. ((A ∪ ⋃img(A)) ∈ U(c) → dprod(A) ∈ U(c))   [dprod_in_universe_of]
//! ⊢ ∀A. dprod(A) ∈ U(A ∪ ⋃img(A))                     [dprod_in_universe]
//! ```
//!
//! The second is **unconditional**. Callers need neither derivation; the two
//! statements are the whole contract.
//!
//! # What is delivered and what is not
//!
//! Everything above the base set is already available, and each step is one of
//! the two closure properties [`crate::universe`] proves for `U(x)`:
//!
//! ```text
//! dprod(A) ⊆ fs(A, ⋃img(A))          — `DProd::dprod_sub`, unconditional
//! fs(a,b)  ⊆ 𝒫(prod(a,b))            — `funspace_subset_pow_prod`
//! prod(a,b) ⊆ 𝒫𝒫(a ∪ b)              — `product_subset_pow_pow`
//! ```
//!
//! so [`crate::funspace::funspace_in_universe_of`] already carries the middle
//! two and [`dprod_in_universe_of`] adds the first with one more `C₂`. What is
//! left is a **single** membership: `(A ∪ ⋃img(A)) ∈ U(c)`.
//!
//! The form the checker wants is
//!
//! ```text
//! (A ∈ U(c) ∧ ∀x ∈ A. b(x) ∈ U(c))  →  dprod(A) ∈ U(c)
//! ```
//!
//! and it is **delivered by [`super::dprod_in_universe_pair`]**, not here.
//! Discharging `(A ∪ ⋃img(A)) ∈ U(c)` from that hypothesis needs three things,
//! all of which now exist:
//!
//!   * closure under Replacement, to put `img(A) = { b(x) : x ∈ A }` in `U(c)`
//!     — [`crate::universe::least_universe_replacement`];
//!   * closure under `⋃`, to put `⋃img(A)` there —
//!     [`crate::universe::least_universe_union`];
//!   * closure under binary union, since `a ∪ b` is `⋃{a,b}` —
//!     [`crate::universe::least_universe_bin_union`]. Pairing itself was
//!     already available ([`crate::universe::least_universe_pairing`], the
//!     inaccessibility argument run in an arbitrary universe and transferred
//!     through the intersection); stripping the outer `⋃` is the part that had
//!     to be built.
//!
//! This file is unchanged and keeps the reduction, which is what
//! `dprod_in_universe_pair` and `crate::checker` both consume.
//!
//! **Read the date on the paragraph that used to stand here.** Until 2026-07-31
//! `ax_tarski` had no transitivity clause, and all three were *refutable*: the
//! countermodels at the end of [`crate::universe`] gave a `U({W})` with
//! `{W} ∈ U({W})` and `⋃{W} = W ∉ U({W})`, and refuted binary union,
//! `prod(a,b) ∈ U(c)` and `fs(a,b) ∈ U(c)` as well. Those models violate the new
//! `C₁` clause, so nothing above is refutable any more, and all three have since
//! been proved. What made that possible: `U(x)` is transitive
//! ([`crate::universe::least_universe_transitive`]), and a subset of a universe
//! that is the surjective image of a member is a member
//! ([`crate::cantor::image_in_universe`]). Assembling those two into `⋃`-closure
//! ([`crate::universe::universe_union_closed`]) is what unlocked the rest; none
//! of it ever waited on [`crate::universe::inaccessibility_reduction`].
//!
//! No axiom is added to route around any of it. What is delivered *here* is the
//! reduction — [`dprod_in_universe_of`], exactly as strong as
//! `funspace_in_universe_of` and no weaker — together with the one instance
//! whose antecedent discharges itself: at `c := A ∪ ⋃img(A)` the antecedent
//! becomes `x ∈ U(x)`, which is [`crate::universe::mem_least_universe`]. So
//! [`dprod_in_universe`] is **unconditional**. It is the dependent analogue of
//! [`crate::funspace::funspace_in_universe`], and reached by the same move: not
//! by closing `U` under the union, but by choosing the universe *after* the
//! union is formed.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::Funspace;
use crate::{a1i, gen_all, hyp_mp, inst_all, syl};
use super::dprod::{base_of, DProd};

/// `⊢ ∀A ∀c. ((A ∪ ⋃img(A)) ∈ U(c) → dprod(A) ∈ U(c))` — the dependent product
/// lands in any universe its base set does.
///
/// `dprod(A)` is a subset of `fs(A, ⋃img(A))` outright ([`DProd::dprod_sub`],
/// unconditional), so `C₂` — closure under subsets of members — carries it in
/// as soon as the function space is there, and that is
/// [`crate::funspace::funspace_in_universe_of`] verbatim. **The antecedent is
/// the same one that lemma carries**; nothing is lost and nothing new is
/// assumed. See the section comment for why it cannot be discharged from
/// `A ∈ U(c)` and `∀x ∈ A. b(x) ∈ U(c)`.
///
/// `c2` must be `⊢ ∀x. C₂(U(x))`
/// ([`crate::universe::least_universe_closed_sub`]) and `fs_in_u`
/// `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))`, for the same `lu` and the
/// same `fsp`; `dp` must be the [`DProd`] built over `ap` and `fsp`. All of that
/// is checked — the two theorems are rebuilt at our own terms and compared — so
/// a mismatched stack is refused rather than silently described.
pub fn dprod_in_universe_of(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    dp: &DProd,
    lu: FnSym,
    c2: &Thm,
    fs_in_u: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let (av, cv) = (env.fresh_var(), env.fresh_var());
    let (ta, tc) = (Term::var(av), Term::var(cv));
    let w = Term::apply(lu, vec![tc.clone()]); // U(c)

    let u = base_of(ap, dp.img, &ta); // ⋃img(A)
    let un = crate::funspace::bin_union(&ap.sets, ta.clone(), u.clone()); // A ∪ ⋃img(A)
    let fs_t = fsp.of(ta.clone(), u.clone());
    let dp_t = dp.of(ta.clone());
    let h = Formula::mem(un, w.clone());

    // `H → fs(A,⋃img(A)) ∈ U(c)`, which is the whole of the function-space chain.
    let fs_at = inst_all(fs_in_u, &[ta.clone(), u, tc.clone()])?;
    if *fs_at.concl() != Formula::imp(h.clone(), Formula::mem(fs_t.clone(), w.clone())) {
        return None
    }

    // `C₂(U(c))`, and the subset step it licenses.
    let c2_at = inst_all(c2, std::slice::from_ref(&tc))?;
    if *c2_at.concl() != crate::universe::closed_sub(env, &w) {
        return None
    }
    let sc = crate::funspace::sub_closed(&c2_at, &fs_t, &dp_t)?;

    let sub = inst_all(&dp.dprod_sub, std::slice::from_ref(&ta))?;
    if *sub.concl() != kernel::thm::subset(env, dp_t.clone(), fs_t) {
        return None
    }

    let out = hyp_mp(&syl(&fs_at, &sc)?, &a1i(&sub, h.clone()))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(dp_t, w)),
        "dprod_in_universe_of: unexpected shape"
    );
    Some(gen_all(&[av, cv], &out))
}

/// `⊢ ∀A. dprod(A) ∈ U(A ∪ ⋃img(A))` — **unconditional**: every dependent
/// product lands in a universe, named explicitly.
///
/// [`dprod_in_universe_of`] does the work; all that is left is to instantiate
/// its universe parameter at the very set its antecedent is about. The
/// antecedent then reads `(A ∪ ⋃img(A)) ∈ U(A ∪ ⋃img(A))`, which is
/// [`crate::universe::mem_least_universe`], and it discharges itself.
///
/// This is the dependent analogue of
/// [`crate::funspace::funspace_in_universe`], and it is reached the same way:
/// the binary union that blocks the general form is not closed over but stepped
/// around, by choosing the universe after the union has been formed. What it
/// does *not* give is membership in a universe fixed in advance — going from
/// `U(A ∪ ⋃img(A))` to a prescribed `U(c)` needs `U(c)` to be a universe, whose
/// inaccessibility clause is open, and is in any case what
/// [`dprod_in_universe_of`] already states directly.
pub fn dprod_in_universe(
    env: &mut Env,
    ap: &Apply,
    dp: &DProd,
    lu: FnSym,
    mem_lu: &Thm,
    general: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let av = env.fresh_var();
    let ta = Term::var(av);
    let un = crate::funspace::bin_union(&ap.sets, ta.clone(), base_of(ap, dp.img, &ta));
    let w = Term::apply(lu, vec![un.clone()]);

    let self_mem = inst_all(mem_lu, std::slice::from_ref(&un))?;
    if *self_mem.concl() != Formula::mem(un.clone(), w.clone()) {
        return None
    }

    let inst = inst_all(general, &[ta.clone(), un])?;
    let out = Thm::mp(&inst, &self_mem)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::mem(dp.of(ta), w),
        "dprod_in_universe: unexpected shape"
    );
    Some(Thm::gen(av, &out))
}
