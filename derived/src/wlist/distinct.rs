//! Non-vacuity: the three constructors' distinctness, and an infinite `lt(α)`.
//!
//! # Interface
//!
//! Private to [`crate::wlist`]; surfaced as [`crate::wlist::WList`]'s
//! `nil_ne_cons`, `cons_inj`, `distinct3` and `three_in` fields.
//!
//! # Why this file is not optional
//!
//! Two memberships about one set say nothing if that set could be a singleton.
//! Everything [`super::typing`] proves would still hold with `lt(α)` a
//! one-element set and `nil = cons h t`, so both distinctness statements are
//! derived and pinned in `tests/wlist.rs`:
//!
//! * `nil_ne_cons` comes from [`crate::sums::Sums::disjoint`] — the two **tags**
//!   differ, whatever the head and tail are;
//! * `cons_inj` comes from the Kuratowski pair's injectivity three times over:
//!   once for the W-type pair, once through the singleton fibre, and once inside
//!   it. It gives **both** components back, so `cons` is injective in the head as
//!   well as the tail — which is what makes `α`'s elements visible inside the
//!   list and stops `lt(α)` collapsing to `N`.
//!
//! `distinct3` cashes them in: for any `h`, the three lists `nil`,
//! `cons h nil`, `cons h (cons h nil)` are pairwise distinct, and `three_in`
//! puts all three in `lt(α)` as soon as `α` has an element. So `lt(α)` is
//! provably infinite for inhabited `α`, and every membership in
//! [`super::typing`] is a statement about a set with many elements.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::point_fun::PointFun;
use crate::wtype::Wtype;
use crate::{
    a1i, and_intro, and_left, and_right, contrapos, gen_all, hyp_and, hyp_mp, inst_all, syl,
};

use super::apparatus::WList;

/// `⊢ ∀h ∀t. ¬(⟨inl •,∅⟩ = ⟨inr h,{⟨•,t⟩}⟩)` — **nil is not a cons**.
///
/// The two elements differ in their *tag*, and [`crate::sums::Sums::disjoint`]
/// says `inl(•) ≠ inr(h)` for **every** `h` — no hypothesis on `h`, and nothing
/// about the fibre components, which is why this holds for all `h` and `t` at
/// once and needs no assumption about `α`.
pub(super) fn nil_ne_cons(wt: &Wtype, hv: FreeVar, tv: FreeVar) -> Option<Thm> {
    let s = &wt.sums;
    let point = s.point();
    let (th, tt) = (Term::var(hv), Term::var(tv));
    let (l, r) = (s.inl(point.clone()), s.inr(th.clone()));
    let f = PointFun::of(s, point.clone(), tt.clone());
    let inj = inst_all(&wt.sup_inj, &[l.clone(), wt.empty(), r.clone(), f.clone()])?;
    let (_, conj) = inj.concl().as_imp()?;
    let tags_eq = Formula::eq(l.clone(), r.clone());
    let fibs_eq = Formula::eq(wt.empty(), f.clone());
    debug_assert_eq!(
        conj,
        Formula::and(tags_eq.clone(), fibs_eq.clone()),
        "wlist: sup_inj does not conclude the expected conjunction"
    );
    let to_tags = syl(&inj, &and_left(tags_eq, fibs_eq))?;
    let disjoint = inst_all(&s.disjoint, &[point.clone(), th.clone()])?;
    let out = Thm::mp(&contrapos(&to_tags)?, &disjoint)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(WList::nil_term(wt), WList::cons_term(wt, th, tt))),
        "wlist: nil_ne_cons has the wrong shape"
    );
    Some(gen_all(&[hv, tv], &out))
}

/// `⊢ ∀h ∀t ∀h′ ∀t′. (cons h t = cons h′ t′ → (h = h′ ∧ t = t′))` — **`cons` is
/// injective in both arguments**.
///
/// Three Kuratowski-pair inversions and one singleton inversion. The W-type pair
/// splits into `inr h = inr h′` and `{⟨•,t⟩} = {⟨•,t′⟩}`; the tag half is
/// [`crate::sums::Sums::inr_inj`], and the fibre half is
/// [`crate::singleton_inj`] followed by the pair's injectivity again.
///
/// The *head* component is what [`crate::wnat`]'s `succ_inj` had no counterpart
/// for: it is what makes distinct elements of `α` give distinct one-element
/// lists, so `lt(α)` sees `α` rather than only its cardinality being non-zero.
pub(super) fn cons_inj(env: &mut Env, wt: &Wtype) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let point = s.point();
    let (hv, tv, h2v, t2v) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (th, tt, th2, tt2) = (Term::var(hv), Term::var(tv), Term::var(h2v), Term::var(t2v));
    let (r1, r2) = (s.inr(th.clone()), s.inr(th2.clone()));
    let (f1, f2) = (
        PointFun::of(s, point.clone(), tt.clone()),
        PointFun::of(s, point.clone(), tt2.clone()),
    );

    let inj = inst_all(&wt.sup_inj, &[r1.clone(), f1.clone(), r2.clone(), f2.clone()])?;
    let (_, conj) = inj.concl().as_imp()?;
    let tags_eq = Formula::eq(r1.clone(), r2.clone());
    let fibs_eq = Formula::eq(f1.clone(), f2.clone());
    debug_assert_eq!(
        conj,
        Formula::and(tags_eq.clone(), fibs_eq.clone()),
        "wlist: sup_inj does not conclude the expected conjunction"
    );

    // the head: `inr h = inr h′ → h = h′`
    let heads = syl(
        &syl(&inj, &and_left(tags_eq.clone(), fibs_eq.clone()))?,
        &inst_all(&s.inr_inj, &[th.clone(), th2.clone()])?,
    )?;

    // the tail: `{⟨•,t⟩} = {⟨•,t′⟩} → ⟨•,t⟩ = ⟨•,t′⟩ → t = t′`
    let to_fibs = syl(&inj, &and_right(tags_eq, fibs_eq))?;
    let sing_inj = crate::singleton_inj(env, ap.sets.up, &ap.mem_sing)?;
    let to_pairs = syl(
        &to_fibs,
        &inst_all(
            &sing_inj,
            &[
                ap.sets.pair(point.clone(), tt.clone()),
                ap.sets.pair(point.clone(), tt2.clone()),
            ],
        )?,
    )?;
    let pair_inj =
        inst_all(&ap.pair_inj, &[point.clone(), tt.clone(), point.clone(), tt2.clone()])?;
    let tails = syl(
        &syl(&to_pairs, &pair_inj)?,
        &and_right(
            Formula::eq(point.clone(), point.clone()),
            Formula::eq(tt.clone(), tt2.clone()),
        ),
    )?;

    let out = hyp_and(&heads, &tails)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::eq(
                WList::cons_term(wt, th.clone(), tt.clone()),
                WList::cons_term(wt, th2.clone(), tt2.clone())
            ),
            Formula::and(Formula::eq(th, th2), Formula::eq(tt, tt2))
        ),
        "wlist: cons_inj has the wrong shape"
    );
    Some(gen_all(&[hv, tv, h2v, t2v], &out))
}

/// `⊢ ∀h. (¬(nil = c₁) ∧ (¬(nil = c₂) ∧ ¬(c₁ = c₂)))` for `c₁ = cons h nil` and
/// `c₂ = cons h c₁` — **three pairwise distinct lists**.
///
/// The first two are [`nil_ne_cons`] read off at two tails. The third is where
/// [`cons_inj`] earns its keep: `c₁ = c₂` would give `nil = c₁` by cancelling
/// the common head, contradicting the first. Nothing here needs `h ∈ α`, so the
/// three terms are distinct outright; [`three_in`] is what puts them in `lt(α)`.
pub(super) fn distinct3(
    env: &mut Env,
    wt: &Wtype,
    hv: FreeVar,
    nil_ne_cons: &Thm,
    cons_inj: &Thm,
) -> Option<Thm> {
    let th = Term::var(hv);
    let nil_t = WList::nil_term(wt);
    let c1 = WList::cons_term(wt, th.clone(), nil_t.clone());
    let c2 = WList::cons_term(wt, th.clone(), c1.clone());

    let ne1 = inst_all(nil_ne_cons, &[th.clone(), nil_t.clone()])?;
    let ne2 = inst_all(nil_ne_cons, &[th.clone(), c1.clone()])?;
    // `c₁ = c₂ → (h = h ∧ nil = c₁)`, then the right conjunct contradicts `ne1`.
    let inj = inst_all(cons_inj, &[th.clone(), nil_t.clone(), th.clone(), c1.clone()])?;
    let to_tail = syl(
        &inj,
        &and_right(
            Formula::eq(th.clone(), th.clone()),
            Formula::eq(nil_t.clone(), c1.clone()),
        ),
    )?;
    let ne3 = Thm::mp(&contrapos(&to_tail)?, &ne1)?;
    let _ = env;

    let out = and_intro(&ne1, &and_intro(&ne2, &ne3));
    debug_assert_eq!(
        *out.concl(),
        Formula::and(
            Formula::not(Formula::eq(nil_t.clone(), c1.clone())),
            Formula::and(
                Formula::not(Formula::eq(nil_t, c2)),
                Formula::not(Formula::eq(c1, c2_of(wt, &th)))
            )
        ),
        "wlist: distinct3 has the wrong shape"
    );
    Some(Thm::gen(hv, &out))
}

/// `c₂ = cons h (cons h nil)`, spelled out so the shape assertion above reads.
fn c2_of(wt: &Wtype, h: &Term) -> Term {
    WList::cons_term(wt, h.clone(), WList::cons_term(wt, h.clone(), WList::nil_term(wt)))
}

/// `⊢ ∀α ∀h. (h ∈ α → (nil ∈ lt(α) ∧ (c₁ ∈ lt(α) ∧ c₂ ∈ lt(α))))` — the three
/// distinct lists really are **elements of the type**, as soon as `α` has one.
///
/// This is what stops [`distinct3`] being three statements about terms that
/// might lie outside `lt(α)`. Together they say `lt(α)` has at least three
/// elements for inhabited `α`, and iterating gives infinitely many.
pub(super) fn three_in(env: &mut Env, wt: &Wtype, av: FreeVar, hv: FreeVar, nil: &Thm, cons: &Thm) -> Option<Thm> {
    let (ta, th) = (Term::var(av), Term::var(hv));
    let nil_t = WList::nil_term(wt);
    let c1 = WList::cons_term(wt, th.clone(), nil_t.clone());
    let h_in = Formula::mem(th.clone(), ta.clone());

    let nil_a = inst_all(nil, std::slice::from_ref(&ta))?;
    let _ = env;

    // `⊢ h ∈ α → c₁ ∈ lt(α)` and `⊢ h ∈ α → c₂ ∈ lt(α)`, by feeding the
    // previous membership (which is unconditional, or already conditional) in.
    let at = |t: &Term, mem: &Thm| -> Option<Thm> {
        let rule = inst_all(cons, &[ta.clone(), th.clone(), t.clone()])?;
        // `rule : (h ∈ α ∧ t ∈ lt(α)) → cons h t ∈ lt(α)`
        hyp_mp(
            &a1i(&rule, h_in.clone()),
            &hyp_and(&crate::imp_refl(h_in.clone()), &a1i(mem, h_in.clone()))?,
        )
    };
    let c1_in = at(&nil_t, &nil_a)?;
    let (_, c1_concl) = c1_in.concl().as_imp()?;
    let c1_mem = c1_concl.as_mem()?;
    debug_assert_eq!(c1_mem.0, c1, "wlist: three_in's first cons has the wrong subject");
    // `c₂` needs the *conditional* `c₁ ∈ lt(α)`, so the conjunction is built
    // under the same hypothesis rather than by weakening an outright theorem.
    let c2_in = {
        let rule = inst_all(cons, &[ta.clone(), th.clone(), c1.clone()])?;
        hyp_mp(
            &a1i(&rule, h_in.clone()),
            &hyp_and(&crate::imp_refl(h_in.clone()), &c1_in)?,
        )?
    };

    let out = hyp_and(&a1i(&nil_a, h_in.clone()), &hyp_and(&c1_in, &c2_in)?)?;
    Some(gen_all(&[av, hv], &out))
}
