//! The collection `coll(f,a) = { y : ⟨a,y⟩ ∈ f }`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀f ∀a. ∃s ∀y. (y ∈ s ↔ ⟨a,y⟩ ∈ f)                     [value_collection]
//! ⊢ ∀f ∀a ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f)                 [collection — introduces `coll`]
//! ⊢ ∀f ∀a. ((∃y. ⟨a,y⟩ ∈ f) → ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f))
//!                                                         [collection_conditional]
//! ```
//!
//! The first two are **unconditional**. Separation supplies the set once a
//! superset is known, and [`crate::funcs::snd_in_union2`] is that superset — the
//! very same inclusion also erases the `y ∈ ⋃⋃f` conjunct Separation leaves
//! behind, so the condition comes out clean. `empty` must be a proof
//! `⊢ ∀z. ¬(z ∈ e)`; it is consumed and does not appear in the conclusion.
//!
//! [`collection_conditional`] is [`collection`]'s theorem weakened by plain
//! weakening. It is retained because it is the shape the beta-reduction
//! derivations consume: they establish inhabitation anyway (the pair
//! `⟨a, t(a)⟩` witnesses it), and matching against an implication is what their
//! existing steps expect.
//!
//! # The default disjunct that is gone
//!
//! A definitional extension has to be *total*, and for as long as the vacuous
//! case of Separation was out of reach the only way to get totality was a
//! default disjunct: the condition actually defined read
//!
//! ```text
//! y ∈ coll(f,a)  ↔  ⟨a,y⟩ ∈ f  ∨  (¬∃y. ⟨a,y⟩ ∈ f  ∧  y ∈ f)
//! ```
//!
//! so that `coll(f,a)` degenerated to `f` when there was nothing to collect, and
//! the characteristic theorem had to be conditional on inhabitation to hide that
//! away. With `∅` available the empty case has a name,
//! [`crate::funcs::separation_full`] produces the set outright, and the disjunct
//! is gone: `coll(f,a)` *is* the collection, empty or not.
//!
//! # How this fails
//!
//! **Nothing here declines.** Each of the three is handed the characteristic
//! theorem of the rung below it — `snd_in_uu` from
//! [`crate::funcs::snd_in_union2`], then [`value_collection`]'s, then
//! [`collection`]'s — and the checks on those theorems are the toolkit's own:
//! [`crate::rules::inst_all`] declines one with fewer leading quantifiers than
//! the terms supplied for it, [`crate::rules::hyp_and`] and
//! [`crate::rules::hyp_syl`] decline two premises that do not sit under the same
//! hypothesis, and [`crate::funcs::separation_full`] owns every check on
//! `empty`. Everything else — the kernel calls behind [`crate::prim`], and the
//! three `debug_assert_eq!`s comparing a formula this file built against the one
//! it intended — is this file checking its **own** work, so a failure there is a
//! [`crate::err::DerErr::Assembly`] and a bug here rather than in the caller.
//!
//! None of the three is `#[track_caller]`: each is a construction with a
//! derivation of its own, and which internal step stopped is exactly what a
//! reader needs.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::err::DResult;
use crate::prim;
use crate::rules::{
    define_by_membership, exists_mono, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_syl, inst_all,
};
use crate::{a1i, and_right, gen_all, imp_refl};
use super::sets::Sets;
use super::separation::separation_full;

/// `⊢ ∀f ∀a. ∃s ∀y. (y ∈ s ↔ ⟨a,y⟩ ∈ f)`.
///
/// The collection `{ y : ⟨a,y⟩ ∈ f }` is a set. Separation supplies it once a
/// superset is known, and [`crate::funcs::snd_in_union2`] is that superset: the very same
/// inclusion also erases the `y ∈ ⋃⋃f` conjunct Separation leaves behind, so
/// the condition comes out clean.
///
/// **Unconditional.** The inhabitation antecedent this carried for as long as
/// there was no empty set is gone: [`separation_full`] covers the vacuous case
/// with `∅`. `empty` must be a proof `⊢ ∀z. ¬(z ∈ e)`; it is consumed and does
/// not appear in the conclusion, and it is [`separation_full`] that checks it
/// says so.
pub fn value_collection(env: &mut Env, sets: &Sets, snd_in_uu: &Thm, empty: &Thm) -> DResult<Thm> {
    let (f, a, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, ty) = (Term::var(f), Term::var(a), Term::var(y));
    let uuf = sets.union_of(sets.union_of(tf.clone()));

    let l = Formula::mem(sets.pair(ta.clone(), ty.clone()), tf.clone());
    let mem_uu = Formula::mem(ty.clone(), uuf.clone());
    let sep_cond = Formula::and(mem_uu.clone(), l.clone());

    let sep = separation_full(env, y, &l, &uuf, empty)?;

    // ⊢ ⟨a,y⟩ ∈ f → y ∈ ⋃⋃f, and hence `L ↔ (y ∈ ⋃⋃f ∧ L)`.
    let l_to_uu = inst_all(snd_in_uu, &[tf.clone(), ta.clone(), ty.clone()])?;
    let l_to_both = hyp_and(&l_to_uu, &imp_refl(l.clone()))?;
    let both_to_l = and_right(mem_uu, l.clone());

    // Swap the membership condition inside the existential. Under `P(s)`, the
    // set's own characterisation composes with the two halves above.
    let sv = env.fresh_var();
    let mem_ys = Formula::mem(ty.clone(), Term::var(sv));
    let p_s = Formula::forall(y, Formula::iff(mem_ys.clone(), sep_cond));
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(sv, p_s.clone()),
        "value_collection: Separation has an unexpected shape"
    );

    let p_inst = prim::ax_inst(p_s.clone(), ty.clone())?;
    let p_fwd = hyp_syl(&hyp_iff_mp(&p_inst)?, &a1i(&both_to_l, p_s.clone()))?;
    let p_bwd = hyp_syl(&a1i(&l_to_both, p_s.clone()), &hyp_iff_mpr(&p_inst)?)?;
    let p_q = prim::mp(
        &prim::ax_dist(y, p_s.clone(), Formula::iff(mem_ys.clone(), l.clone()))?,
        &Thm::gen(y, &hyp_and(&p_fwd, &p_bwd)?),
    )?;
    let out = prim::mp(&exists_mono(sv, &Thm::gen(sv, &p_q))?, &sep)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::exists(sv, Formula::forall(y, Formula::iff(mem_ys, l))),
        "value_collection: unexpected shape"
    );
    Ok(gen_all(&[f, a], &out))
}

/// The collection symbol `coll(f,a) = { y : ⟨a,y⟩ ∈ f }`, together with
/// `⊢ ∀f ∀a ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f)`.
///
/// **Unconditional, and the condition defined is the intended one.** A
/// definitional extension has to be *total*, and for as long as the vacuous
/// case of Separation was out of reach the only way to get totality was a
/// default disjunct: the condition actually defined read
///
/// ```text
/// y ∈ coll(f,a)  ↔  ⟨a,y⟩ ∈ f  ∨  (¬∃y. ⟨a,y⟩ ∈ f  ∧  y ∈ f)
/// ```
///
/// so that `coll(f,a)` degenerated to `f` when there was nothing to collect,
/// and the characteristic theorem had to be conditional on inhabitation to hide
/// that away. With `∅` available the empty case has a name, [`separation_full`]
/// produces the set outright, and the disjunct is gone: `coll(f,a)` *is* the
/// collection, empty or not.
pub fn collection(env: &mut Env, sets: &Sets, value_coll: &Thm) -> DResult<(FnSym, Thm)> {
    let (f, a, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, ty) = (Term::var(f), Term::var(a), Term::var(y));

    let l = Formula::mem(sets.pair(ta.clone(), ty), tf.clone());
    let existence = inst_all(value_coll, &[tf, ta])?;
    define_by_membership(env, &[f, a], &existence, y, &l)
}

/// `⊢ ∀f ∀a. ((∃y. ⟨a,y⟩ ∈ f) → ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f))` — the
/// conditional form of [`collection`]'s theorem, by plain weakening.
///
/// Retained because it is the shape the beta-reduction derivations consume:
/// they establish inhabitation anyway (the pair `⟨a, t(a)⟩` witnesses it), and
/// matching against an implication is what their existing steps expect. Nothing
/// is lost — this is strictly weaker than [`crate::funcs::Apply::coll_members`].
pub fn collection_conditional(env: &mut Env, sets: &Sets, coll: FnSym, coll_ax: &Thm) -> DResult<Thm> {
    let (f, a, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, ty) = (Term::var(f), Term::var(a), Term::var(y));

    let l = Formula::mem(sets.pair(ta.clone(), ty.clone()), tf.clone());
    let ne = Formula::exists(y, l.clone());
    let mem_yc = Formula::mem(ty, Term::apply(coll, vec![tf.clone(), ta.clone()]));

    let at_fa = inst_all(coll_ax, &[tf.clone(), ta.clone()])?;
    debug_assert_eq!(
        *at_fa.concl(),
        Formula::forall(y, Formula::iff(mem_yc, l)),
        "collection_conditional: the characteristic theorem has an unexpected shape"
    );
    Ok(gen_all(&[f, a], &a1i(&at_fa, ne)))
}
