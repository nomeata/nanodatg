//! What is in the step, and what is not.
//!
//! # Interface
//!
//! All three are private to [`crate::wnat_rec`]. `row_in_step` and
//! `zero_in_step` put the two branches' pairs into the step; `step_cases` is
//! the converse — every member of the step is one of those two — and is what
//! makes the step *single-valued* rather than merely defined.
//!
//! # Why case analysis is needed at all
//!
//! The step is a union of two Replacement images, one per constructor tag, and
//! nothing about a union says its members came from one side or the other.
//! `step_cases` recovers that, by reading the membership condition of each
//! image back and using [`crate::sums::Sums::disjoint`] to rule out the crossed
//! cases. Every value computation in [`super::values`] starts from it.

use kernel::{Env, Formula, Term, Thm};
use crate::funcs::{or_intro_left, or_intro_right};
use crate::wnat::Nat;
use crate::proj::Proj;
use crate::wrec::hyp_exists_elim;
use crate::wtype::Wtype;
use crate::{
    a1i, and_right, exists_intro_imp, hyp_and, hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all,
    singleton, syl,
};

use super::step::{StepSyms, key_zero, payload, row_packed};

/// `⊢ p ∈ prod(FW,FT(T)) → ⟨⟨inr •,p⟩, val(s,p)⟩ ∈ e(z,s,T)` — **the step
/// contains every `succ` point**.
///
/// One Replacement witness (`p` is its own) and one disjunct of the union.
#[allow(clippy::too_many_arguments)]
pub(super) fn row_in_step(
    env: &mut Env,
    wt: &Wtype,
    nat: &Nat,
    pj: &Proj,
    sy: &StepSyms,
    z: &Term,
    su: &Term,
    t: &Term,
    p: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let sets = &s.ap.sets;
    let dom = payload(s, nat, t);
    let row_t = row_packed(wt, pj, su, p);
    let e_t = sy.e_of(su, t);
    let sing = singleton(sets.up, sets.pair(key_zero(wt), z.clone()));
    let h = Formula::mem(p.clone(), dom.clone());

    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let body = Formula::and(
        Formula::mem(tq.clone(), dom.clone()),
        Formula::eq(row_t.clone(), row_packed(wt, pj, su, &tq)),
    );
    let ax = inst_all(&sy.e_ax, &[su.clone(), t.clone(), row_t.clone()])?;
    if *ax.concl()
        != Formula::iff(
            Formula::mem(row_t.clone(), e_t.clone()),
            Formula::exists(qv, body.clone()),
        )
    {
        return None
    }
    let intro = exists_intro_imp(qv, body, p.clone())?;
    let wit = hyp_and(
        &imp_refl(h.clone()),
        &a1i(&Thm::eq_refl(row_t.clone()), h.clone()),
    )?;
    let in_e = syl(&syl(&wit, &intro)?, &iff_mpr(&ax)?)?;

    let bu = inst_all(
        &crate::sums::mem_bin_union_iff(env, sets)?,
        &[e_t.clone(), sing.clone(), row_t.clone()],
    )?;
    let inj = or_intro_left(
        Formula::mem(row_t.clone(), e_t),
        Formula::mem(row_t.clone(), sing),
    );
    let out = syl(&syl(&in_e, &inj)?, &iff_mpr(&bu)?)?;
    if *out.concl() != Formula::imp(h, Formula::mem(row_t, sy.step_of(wt, z, su, t))) {
        return None
    }
    Some(out)
}

/// `⊢ ⟨k₀, z⟩ ∈ e(z,s,T)` — **the step contains the zero point**,
/// unconditionally.
pub(super) fn zero_in_step(
    env: &mut Env,
    wt: &Wtype,
    sy: &StepSyms,
    z: &Term,
    su: &Term,
    t: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let sets = &s.ap.sets;
    let pt = sets.pair(key_zero(wt), z.clone());
    let sing = singleton(sets.up, pt.clone());
    let e_t = sy.e_of(su, t);

    let in_sing = Thm::mp(
        &iff_mpr(&inst_all(&s.ap.mem_sing, &[pt.clone(), pt.clone()])?)?,
        &Thm::eq_refl(pt.clone()),
    )?;
    let bu = inst_all(
        &crate::sums::mem_bin_union_iff(env, sets)?,
        &[e_t.clone(), sing.clone(), pt.clone()],
    )?;
    let inj = or_intro_right(
        Formula::mem(pt.clone(), e_t),
        Formula::mem(pt.clone(), sing),
    );
    let out = Thm::mp(&iff_mpr(&bu)?, &Thm::mp(&inj, &in_sing)?)?;
    if *out.concl() != Formula::mem(pt, sy.step_of(wt, z, su, t)) {
        return None
    }
    Some(out)
}

/// `⊢ x ∈ e(z,s,T) → ((∃p. x = ⟨⟨inr •,p⟩, val(s,p)⟩) ∨ x = ⟨k₀,z⟩)` — **the
/// step contains nothing else**.
///
/// The union splits into its two halves; the right one is a singleton and the
/// left is a Replacement image, so **one** existential elimination unwinds it.
/// The membership `p ∈ prod(FW,FT(T))` is dropped on the way out: nothing below
/// needs it, and carrying it would widen every case analysis.
#[allow(clippy::too_many_arguments)]
pub(super) fn step_cases(
    env: &mut Env,
    wt: &Wtype,
    nat: &Nat,
    pj: &Proj,
    sy: &StepSyms,
    z: &Term,
    su: &Term,
    t: &Term,
    x: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let sets = &s.ap.sets;
    let dom = payload(s, nat, t);
    let e_t = sy.e_of(su, t);
    let pt = sets.pair(key_zero(wt), z.clone());
    let sing = singleton(sets.up, pt.clone());

    let bp = env.fresh_var();
    let tbp = Term::var(bp);
    let left_disj = Formula::exists(bp, Formula::eq(x.clone(), row_packed(wt, pj, su, &tbp)));
    let right_disj = Formula::eq(x.clone(), pt.clone());
    let goal = Formula::or(left_disj.clone(), right_disj.clone());

    // ── The right half: a singleton ─────────────────────────────────────────
    let in_sing = iff_mp(&inst_all(&s.ap.mem_sing, &[pt.clone(), x.clone()])?)?;
    let right = syl(
        &in_sing,
        &or_intro_right(left_disj.clone(), right_disj.clone()),
    )?;

    // ── The left half: the Replacement image ────────────────────────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let mem_q = Formula::mem(tq.clone(), dom.clone());
    let eq_q = Formula::eq(x.clone(), row_packed(wt, pj, su, &tq));
    let body = Formula::and(mem_q.clone(), eq_q.clone());
    let ax = inst_all(&sy.e_ax, &[su.clone(), t.clone(), x.clone()])?;
    if *ax.concl()
        != Formula::iff(
            Formula::mem(x.clone(), e_t.clone()),
            Formula::exists(qv, body.clone()),
        )
    {
        return None
    }
    let mem_x_e = Formula::mem(x.clone(), e_t.clone());
    let k_eq = syl(
        &and_right(mem_x_e.clone(), body.clone()),
        &and_right(mem_q, eq_q),
    )?;
    let k_ex = syl(
        &k_eq,
        &exists_intro_imp(
            bp,
            Formula::eq(x.clone(), row_packed(wt, pj, su, &tbp)),
            tq.clone(),
        )?,
    )?;
    let k_goal = syl(
        &k_ex,
        &or_intro_left(left_disj.clone(), right_disj.clone()),
    )?;
    let left = hyp_exists_elim(qv, &k_goal, &iff_mp(&ax)?)?;

    // ── The two halves, across the union's membership condition ─────────────
    let bu = inst_all(
        &crate::sums::mem_bin_union_iff(env, sets)?,
        &[e_t, sing, x.clone()],
    )?;
    let cases = iff_mp(&bu)?;
    let hyp = Formula::mem(x.clone(), sy.step_of(wt, z, su, t));
    let out = hyp_or_elim(&cases, &a1i(&left, hyp.clone()), &a1i(&right, hyp.clone()))?;
    if *out.concl() != Formula::imp(hyp, goal) {
        return None
    }
    Some(out)
}
