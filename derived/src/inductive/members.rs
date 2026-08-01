//! What is in the general step, and what is not.
//!
//! # Interface
//!
//! Both private to [`crate::inductive`]. [`row_in_step`] puts the `i`-th
//! branch's rows into the step — one Replacement witness and a walk up the
//! union chain. [`step_cases`] is the converse: every member of the step is a
//! row of **some** branch — the membership condition of each Replacement
//! image read back, one disjunct per constructor, with the base of the chain
//! (`∅`) contributing nothing. It is what makes the step *single-valued*
//! rather than merely defined; every value computation in [`super::values`]
//! starts from it.
//!
//! The domain membership `q ∈ Qᵢ` is dropped on the way out of
//! [`step_cases`], exactly as in [`crate::wlist_rec`]: nothing below needs
//! it, and carrying it would widen every case analysis — the recorded reason
//! the existential encoding was rejected.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{or_intro_left, or_intro_right};
use crate::{
    a1i, and_right, disj_inject, disj_of, ex_falso, exists_intro_imp, exists_mono, hyp_and,
    hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all, syl,
};

use super::step::{Rx, StepSym};

/// `⊢ q ∈ Qᵢ → rowᵢ(π₁q, π₂q) ∈ e(p⃗,s⃗,T)` — **the step contains every row of
/// the `i`-th branch**.
///
/// One Replacement witness (`q` is its own) and a walk up the union chain:
/// `i` right injections and, at level `i`, one left injection.
pub(super) fn row_in_step(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    i: usize,
    q: &Term,
) -> Option<Thm> {
    let dom = cx.domain(i)?;
    let row_t = cx.row_at(i, q)?;
    let e_t = cx.e_of(syms, i);
    let h = Formula::mem(q.clone(), dom.clone());

    // ── The Replacement witness ─────────────────────────────────────────────
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let body = Formula::and(
        Formula::mem(tb.clone(), dom.clone()),
        Formula::eq(row_t.clone(), cx.row_at(i, &tb)?),
    );
    let mut args = cx.ps.clone();
    args.push(cx.minors[i].clone());
    args.push(cx.t.clone());
    args.push(row_t.clone());
    let ax = inst_all(&syms[i].e_ax, &args)?;
    if *ax.concl()
        != Formula::iff(
            Formula::mem(row_t.clone(), e_t.clone()),
            Formula::exists(bv, body.clone()),
        )
    {
        return None
    }
    let intro = exists_intro_imp(bv, body, q.clone())?;
    let wit = hyp_and(
        &imp_refl(h.clone()),
        &a1i(&Thm::eq_refl(row_t.clone()), h.clone()),
    )?;
    let mut th = syl(&syl(&wit, &intro)?, &iff_mpr(&ax)?)?;

    // ── Climb the union chain: left at level `i`, right below it ───────────
    let bu = |j: usize, x: &Term| -> Option<Thm> {
        iff_mpr(&inst_all(
            &cx.bin,
            &[cx.e_of(syms, j), cx.chain(syms, j + 1), x.clone()],
        )?)
    };
    let left = or_intro_left(
        Formula::mem(row_t.clone(), e_t),
        Formula::mem(row_t.clone(), cx.chain(syms, i + 1)),
    );
    th = syl(&syl(&th, &left)?, &bu(i, &row_t)?)?;
    for j in (0..i).rev() {
        let right = or_intro_right(
            Formula::mem(row_t.clone(), cx.e_of(syms, j)),
            Formula::mem(row_t.clone(), cx.chain(syms, j + 1)),
        );
        th = syl(&syl(&th, &right)?, &bu(j, &row_t)?)?;
    }
    if *th.concl() != Formula::imp(h, Formula::mem(row_t, cx.step(syms))) {
        return None
    }
    Some(th)
}

/// `⊢ x ∈ e(p⃗,s⃗,T) → ⋁ᵢ ∃q. x = rowᵢ(π₁q, π₂q)` — **the step contains
/// nothing else**.
///
/// The union chain splits link by link; each link's left half is a
/// Replacement image, unwound by one existential weakening, and the base is
/// `¬(x ∈ ∅)`. The disjuncts and their bound variables are returned alongside
/// so the case analyses downstream rebuild exactly these formulas.
pub(super) fn step_cases(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    x: &Term,
) -> Option<(Thm, Vec<kernel::FreeVar>, Vec<Formula>)> {
    let n = cx.n();
    let qvs: Vec<kernel::FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
    let disjuncts: Vec<Formula> = (0..n)
        .map(|i| {
            Some(Formula::exists(
                qvs[i],
                Formula::eq(x.clone(), cx.row_at(i, &Term::var(qvs[i]))?),
            ))
        })
        .collect::<Option<_>>()?;
    let goal = disj_of(&disjuncts)?;

    // ── The base: nothing is in the trailing `∅` ────────────────────────────
    let mut claim = syl(
        &inst_all(&cx.ap().empty_ax, std::slice::from_ref(x))?,
        &ex_falso(goal.clone()),
    )?;

    for j in (0..n).rev() {
        let e_t = cx.e_of(syms, j);
        let here = Formula::mem(x.clone(), cx.chain(syms, j));

        // The left half: the Replacement image, its domain membership dropped.
        let left = {
            let tq = Term::var(qvs[j]);
            let mem_q = Formula::mem(tq.clone(), cx.domain(j)?);
            let eq_q = Formula::eq(x.clone(), cx.row_at(j, &tq)?);
            let mut args = cx.ps.clone();
            args.push(cx.minors[j].clone());
            args.push(cx.t.clone());
            args.push(x.clone());
            let ax = inst_all(&syms[j].e_ax, &args)?;
            if *ax.concl()
                != Formula::iff(
                    Formula::mem(x.clone(), e_t.clone()),
                    Formula::exists(qvs[j], Formula::and(mem_q.clone(), eq_q.clone())),
                )
            {
                return None
            }
            let weaken = exists_mono(qvs[j], &Thm::gen(qvs[j], &and_right(mem_q, eq_q)))?;
            syl(&syl(&iff_mp(&ax)?, &weaken)?, &disj_inject(&disjuncts, j)?)?
        };

        let cases = iff_mp(&inst_all(
            &cx.bin,
            &[e_t, cx.chain(syms, j + 1), x.clone()],
        )?)?;
        claim = hyp_or_elim(&cases, &a1i(&left, here.clone()), &a1i(&claim, here))?;
    }
    if *claim.concl() != Formula::imp(Formula::mem(x.clone(), cx.step(syms)), goal) {
        return None
    }
    Some((claim, qvs, disjuncts))
}
