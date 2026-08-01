//! The general step's values, and hence that it is a function — (S2).
//!
//! # Interface
//!
//! Private to [`crate::inductive`]. [`value_at`] computes what any pair in
//! the step whose key belongs to the `i`-th branch must have as its value;
//! [`step_single_valued`] assembles `n²` of those comparisons into
//! single-valuedness, which is what [`crate::wrec_total::Recursor`] needs of
//! a step.
//!
//! # Where the tags are spent
//!
//! Branch separation comes from [`crate::isum::ISumSyms::inj_distinct`]
//! **alone** — never from the summands, because two constructors with
//! identical argument types share one telescope by cache design, so their
//! summands are the same *term* and could not separate anything (failure mode
//! §7.8). Within a branch, [`crate::isum::ISumSyms::inj_inj`] and the
//! Kuratowski pair's injectivity force the key's components, and the value is
//! equal by congruence because a row is one closure applied to `q` — the
//! recorded `wlist_rec` lesson about never reassembling `q` applies verbatim,
//! at every arity.

use kernel::{Env, Formula, Term, Thm};

use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::{a1i, and_left, and_right, ex_falso, gen_all, hyp_mp, inst_all, syl};

use super::members::step_cases;
use super::rec_shared::{hyp_disj_elim, hyp_ex_branch, split_pair};
use super::step::{Rx, StepSym};

/// `⊢ ⟨⟨Injᵢ(σ), p⟩, y⟩ ∈ e → y = valᵢ(σ, π₁p, π₂p)` — **every value the step
/// takes at an `i`-branch key is the intended one**.
///
/// Stated at the **packed** payload, so its proof mentions no fibre
/// component. [`step_cases`] leaves `n` possibilities: branch `i` gives
/// another row equal to this one, and pair injectivity twice — plus
/// `Injᵢ`'s — forces `σ = π₁q` and `p = π₂q`; every branch `j ≠ i` gives
/// `Injᵢ(σ) = Injⱼ(π₁q)`, which `inj_distinct` refutes.
pub(super) fn value_at(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    i: usize,
    sigma: &Term,
    p: &Term,
    y: &Term,
) -> Option<Thm> {
    let s = cx.s();
    let ap = cx.ap();
    let key = cx.key(i, sigma, p)?;
    let val = cx.val_packed(i, sigma, p)?;
    let x = ap.sets.pair(key.clone(), y.clone());
    let hyp = Formula::mem(x.clone(), cx.step(syms));
    let goal = Formula::eq(y.clone(), val.clone());

    let (cases, qvs, _) = step_cases(env, cx, syms, &x)?;

    let mut branches = Vec::with_capacity(cx.n());
    for (j, qv) in qvs.iter().enumerate() {
        let tq = Term::var(*qv);
        let (fq, sq) = (cx.pj().fst_of(ap, tq.clone()), cx.pj().snd_of(ap, tq.clone()));
        let key2 = cx.key(j, &fq, &sq)?;
        let val2 = cx.val_packed(j, &fq, &sq)?;
        let body = Formula::eq(x.clone(), cx.row_at(j, &tq)?);
        let k_eq = and_right(hyp.clone(), body.clone());
        let (k_keys, k_val) = split_pair(ap, &k_eq, &key, y, &key2, &val2)?;
        let (k_tag, k_pay) = split_pair(
            ap,
            &k_keys,
            &cx.mach.syms.inj(i, sigma.clone())?,
            p,
            &cx.mach.syms.inj(j, fq.clone())?,
            &sq,
        )?;

        let k_goal = if j == i {
            let k_sig = syl(
                &k_tag,
                &inst_all(cx.mach.syms.inj_inj(i)?, &[sigma.clone(), fq.clone()])?,
            )?;
            let back_sig = hyp_eq_symm(env, &k_sig)?;
            let back_pay = hyp_eq_symm(env, &k_pay)?;
            let sq_c = sq.clone();
            let v1 = hyp_congr(env, &back_sig, |w| {
                cx.val_packed(i, &w, &sq_c).expect("arity ensured")
            })?;
            let v2 = hyp_congr(env, &back_pay, |w| {
                cx.val_packed(i, sigma, &w).expect("arity ensured")
            })?;
            let v12 = hyp_eq_trans(env, &v1, &v2)?;
            hyp_eq_trans(env, &k_val, &v12)?
        } else {
            let ne = cx.mach.syms.inj_distinct(env, s, i, j)?;
            let k_false = syl(&k_tag, &inst_all(&ne, &[sigma.clone(), fq.clone()])?)?;
            syl(&k_false, &ex_falso(goal.clone()))?
        };
        branches.push(hyp_ex_branch(*qv, &k_goal, &hyp, &goal)?);
    }

    let out = hyp_disj_elim(&cases, &hyp, &branches)?;
    if *out.concl() != Formula::imp(hyp, goal) {
        return None
    }
    Some(out)
}

/// `⊢ sv(e(p⃗,s⃗,T))` — **the step is single-valued**, hence a function
/// wherever it is defined. Unconditional: no `HYP` and no typing enters.
///
/// [`step_cases`] on the first of the two pairs decides which branch the
/// shared key came from, and then [`value_at`] forces *both* values.
pub(super) fn step_single_valued(env: &mut Env, cx: &Rx<'_>, syms: &[StepSym]) -> Option<Thm> {
    let ap = cx.ap();
    let sets = &ap.sets;
    let step = cx.step(syms);
    let want = crate::funspace::is_single_valued(env, sets, &step);

    let (xv, yv, y2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(xv), Term::var(yv), Term::var(y2v));
    let m1 = Formula::mem(sets.pair(tx.clone(), ty.clone()), step.clone());
    let m2 = Formula::mem(sets.pair(tx.clone(), ty2.clone()), step.clone());
    let h = Formula::and(m1.clone(), m2.clone());
    let h_1 = and_left(m1.clone(), m2.clone());
    let h_2 = and_right(m1, m2);
    let goal = Formula::eq(ty.clone(), ty2.clone());

    let p1 = sets.pair(tx.clone(), ty.clone());
    let (cases0, qvs, _) = step_cases(env, cx, syms, &p1)?;
    let cases = syl(&h_1, &cases0)?;

    let mut branches = Vec::with_capacity(cx.n());
    for (j, qv) in qvs.iter().enumerate() {
        let tq = Term::var(*qv);
        let (fq, sq) = (cx.pj().fst_of(ap, tq.clone()), cx.pj().snd_of(ap, tq.clone()));
        let key2 = cx.key(j, &fq, &sq)?;
        let val2 = cx.val_packed(j, &fq, &sq)?;
        let body = Formula::eq(p1.clone(), cx.row_at(j, &tq)?);
        let k = Formula::and(h.clone(), body.clone());
        let k_eq = and_right(h.clone(), body.clone());
        let (k_x, k_y) = split_pair(ap, &k_eq, &tx, &ty, &key2, &val2)?;

        // The second membership, its key rewritten to the branch's.
        let hole = env.fresh_var();
        let k_m2 = hyp_mp(
            &hyp_mp(
                &a1i(
                    &Thm::eq_leibniz(
                        tx.clone(),
                        key2.clone(),
                        hole,
                        Formula::mem(sets.pair(Term::var(hole), ty2.clone()), step.clone()),
                    ),
                    k.clone(),
                ),
                &k_x,
            )?,
            &syl(&and_left(h.clone(), body.clone()), &h_2)?,
        )?;
        let k_y2 = hyp_mp(
            &a1i(&value_at(env, cx, syms, j, &fq, &sq, &ty2)?, k.clone()),
            &k_m2,
        )?;
        let k_back = hyp_eq_symm(env, &k_y2)?;
        let k_goal = hyp_eq_trans(env, &k_y, &k_back)?;
        branches.push(hyp_ex_branch(*qv, &k_goal, &h, &goal)?);
    }

    let body = hyp_disj_elim(&cases, &h, &branches)?;
    let out = gen_all(&[xv, yv, y2v], &body);
    if *out.concl() != want {
        return None
    }
    Some(out)
}
