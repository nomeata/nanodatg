//! Non-vacuity: the two constructors are distinct, and `succ` is injective.
//!
//! # Interface
//!
//! Private to [`crate::wnat`]; surfaced as [`crate::wnat::Nat`]'s
//! `zero_ne_succ` and `succ_inj` fields.
//!
//! # Why this file is not optional
//!
//! Three memberships about one set say nothing if that set could be a
//! singleton. Everything [`super::typing`] proves would still hold with `N` a
//! one-element set and `zero = succ zero`, so both statements are derived and
//! both are pinned in `tests/wnat.rs`:
//!
//! * `zero_ne_succ` comes from [`crate::sums::Sums::disjoint`] — the two
//!   **tags** differ — through the Kuratowski pair's injectivity;
//! * `succ_inj` comes from that same injectivity twice over, once for the
//!   W-type pair and once inside the one-point fibre function.
//!
//! Together they make `zero`, `succ zero`, `succ (succ zero)`, … pairwise
//! distinct, so `N` is provably infinite — which is what stops every membership
//! in [`super::typing`] from being satisfied by a one-element set.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::point_fun::PointFun;
use crate::wtype::Wtype;
use crate::{and_left, and_right, contrapos, gen_all, inst_all, syl};

use super::apparatus::succ_of;

/// `⊢ ∀n. ¬(⟨inl •,∅⟩ = ⟨inr •,{⟨•,n⟩}⟩)` — **zero is not a successor**.
///
/// The two W-type elements differ in their *tag*, and
/// [`crate::sums::Sums::disjoint`] says `inl(•) ≠ inr(•)`. Nothing about the
/// fibre components is used, which is why this holds for every `n` at once.
pub(super) fn zero_ne_succ(wt: &Wtype, nv: FreeVar) -> Option<Thm> {
    let s = &wt.sums;
    let point = s.point();
    let tn = Term::var(nv);
    let (l, r) = (s.inl(point.clone()), s.inr(point.clone()));
    let f = PointFun::of(s, point.clone(), tn.clone());
    let inj = inst_all(
        &wt.sup_inj,
        &[l.clone(), wt.empty(), r.clone(), f.clone()],
    )?;
    let (_, conj) = inj.concl().as_imp()?;
    let tags_eq = Formula::eq(l.clone(), r.clone());
    let fibs_eq = Formula::eq(wt.empty(), f.clone());
    debug_assert_eq!(
        conj,
        Formula::and(tags_eq.clone(), fibs_eq.clone()),
        "wnat: sup_inj does not conclude the expected conjunction"
    );
    let to_tags = syl(&inj, &and_left(tags_eq, fibs_eq))?;
    let disjoint = inst_all(&s.disjoint, &[point.clone(), point.clone()])?;
    let out = Thm::mp(&contrapos(&to_tags)?, &disjoint)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(wt.sup(l, wt.empty()), succ_of(wt, tn))),
        "wnat: zero_ne_succ has the wrong shape"
    );
    Some(Thm::gen(nv, &out))
}

/// `⊢ ∀m ∀n. (succ m = succ n → m = n)` — **the successor is injective**.
///
/// Two Kuratowski-pair inversions and one singleton inversion: the W-type pair
/// gives `{⟨•,m⟩} = {⟨•,n⟩}`, [`crate::singleton_inj`] gives `⟨•,m⟩ = ⟨•,n⟩`,
/// and injectivity of the pair again gives `m = n`.
pub(super) fn succ_inj(env: &mut Env, wt: &Wtype) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let point = s.point();
    let r = s.inr(point.clone());
    let (mv, nv) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(mv), Term::var(nv));
    let (fm, fn_) = (
        PointFun::of(s, point.clone(), tm.clone()),
        PointFun::of(s, point.clone(), tn.clone()),
    );

    let inj = inst_all(&wt.sup_inj, &[r.clone(), fm.clone(), r.clone(), fn_.clone()])?;
    let (_, conj) = inj.concl().as_imp()?;
    let tags_eq = Formula::eq(r.clone(), r.clone());
    let fibs_eq = Formula::eq(fm.clone(), fn_.clone());
    debug_assert_eq!(
        conj,
        Formula::and(tags_eq.clone(), fibs_eq.clone()),
        "wnat: sup_inj does not conclude the expected conjunction"
    );
    let to_fibs = syl(&inj, &and_right(tags_eq, fibs_eq))?;

    let sing_inj = crate::singleton_inj(env, ap.sets.up, &ap.mem_sing)?;
    let to_pairs = syl(
        &to_fibs,
        &inst_all(
            &sing_inj,
            &[ap.sets.pair(point.clone(), tm.clone()), ap.sets.pair(point.clone(), tn.clone())],
        )?,
    )?;
    let pair_inj = inst_all(
        &ap.pair_inj,
        &[point.clone(), tm.clone(), point.clone(), tn.clone()],
    )?;
    let out = syl(
        &syl(&to_pairs, &pair_inj)?,
        &and_right(
            Formula::eq(point.clone(), point.clone()),
            Formula::eq(tm.clone(), tn.clone()),
        ),
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::eq(succ_of(wt, tm.clone()), succ_of(wt, tn.clone())),
            Formula::eq(tm, tn)
        ),
        "wnat: succ_inj has the wrong shape"
    );
    Some(gen_all(&[mv, nv], &out))
}
