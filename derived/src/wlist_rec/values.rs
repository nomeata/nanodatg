//! The step's values, and hence that it is a function.
//!
//! # Interface
//!
//! Private to [`crate::wlist_rec`]. `value_at_packed` and `value_at_nil` compute
//! `app(e, ·)` at the two branches; `step_single_valued` assembles them into
//! single-valuedness, which is what [`crate::wrec_total::Recursor`] needs of a
//! step.
//!
//! # Where the tags are spent
//!
//! `tags_ne` — the two constructor tags of `1 + α` are different sets — is what
//! makes the two branches disjoint, and `super::shared::split_pair` is what
//! takes an equation between Kuratowski pairs apart. Between them they turn
//! [`super::members`]'s disjunction into a genuine case analysis: given a pair in
//! the step, exactly one branch can have produced it, and the value is read off
//! that branch alone.
//!
//! The `cons` branch is where this costs more than [`crate::wnat_rec`]'s: the
//! key carries a head as well as a tail, so cancelling it needs the pair
//! injectivity applied one level deeper.

use kernel::{Env, Formula, Term, Thm};
use crate::proj::Proj;
use crate::sums::Sums;
use crate::wlist::WList;
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, ex_falso, gen_all, hyp_mp, hyp_or_elim, inst_all, syl, uncurry,
};

use super::shared::split_pair;
use super::step::{StepSyms, key_nil, key_packed, row_at, value_packed};
use super::members::step_cases;

/// `⊢ ¬(inl(•) = inr(b))`, the disjointness every case split turns on.
fn tags_ne(s: &Sums, b: &Term) -> Option<Thm> {
    inst_all(&s.disjoint, &[s.point(), b.clone()])
}

/// `⊢ ⟨⟨inr h,p⟩, y⟩ ∈ e(α,z,s,T) → y = val(s,h,p)` — **every value the step
/// takes at a cons key is the intended one**.
///
/// Stated at the **packed** payload, so its proof mentions no fibre component.
/// [`step_cases`] leaves two possibilities: the cons one gives another row equal
/// to this one, and the Kuratowski pair's injectivity twice — plus `inr`'s —
/// forces `h = π₁ q` and `p = π₂ q`; the nil one gives `inr h = inl •`, which
/// [`crate::sums::Sums::disjoint`] refutes.
#[allow(clippy::too_many_arguments)]
fn value_at_packed(
    env: &mut Env,
    wt: &Wtype,
    wl: &WList,
    pj: &Proj,
    sy: &StepSyms,
    alpha: &Term,
    z: &Term,
    su: &Term,
    t: &Term,
    h: &Term,
    p: &Term,
    y: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let sets = &ap.sets;
    let key = key_packed(wt, h, p);
    let val = value_packed(ap, pj, su, h, p);
    let x = sets.pair(key.clone(), y.clone());
    let hyp = Formula::mem(x.clone(), sy.step_of(wt, alpha, z, su, t));
    let goal = Formula::eq(y.clone(), val.clone());

    let cases = step_cases(env, wt, wl, pj, sy, alpha, z, su, t, &x)?;
    let (_, disj) = cases.concl().as_imp()?;
    let (_, right_disj) = disj.as_imp()?;

    // ── The cons case ───────────────────────────────────────────────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let (fq, sq) = (pj.fst_of(ap, tq.clone()), pj.snd_of(ap, tq.clone()));
    let key2 = key_packed(wt, &fq, &sq);
    let val2 = value_packed(ap, pj, su, &fq, &sq);
    let k_eq = and_right(hyp.clone(), Formula::eq(x.clone(), row_at(wt, pj, su, &tq)));
    let (k_keys, k_val) = split_pair(ap, &k_eq, &key, y, &key2, &val2)?;
    let (k_tag, k_pay) = split_pair(ap, &k_keys, &s.inr(h.clone()), p, &s.inr(fq.clone()), &sq)?;
    let k_head = syl(&k_tag, &inst_all(&s.inr_inj, &[h.clone(), fq.clone()])?)?;
    let k_back_h = hyp_eq_symm(env, &k_head)?;
    let k_back_p = hyp_eq_symm(env, &k_pay)?;
    let sq_c = sq.clone();
    let k_v1 = hyp_congr(env, &k_back_h, |w| value_packed(ap, pj, su, &w, &sq_c))?;
    let k_v2 = hyp_congr(env, &k_back_p, |w| value_packed(ap, pj, su, h, &w))?;
    let k_v = hyp_eq_trans(env, &k_v1, &k_v2)?;
    let k_goal = hyp_eq_trans(env, &k_val, &k_v)?;
    let k_all = crate::exists_elim_imp(
        qv,
        &Thm::gen(qv, &crate::com12(&uncurry(&k_goal)?)?),
        &Formula::imp(hyp.clone(), goal.clone()),
    )?;

    // ── The nil case, refuted ───────────────────────────────────────────────
    let n_eq = and_right(hyp.clone(), right_disj.clone());
    let (n_keys, _) = split_pair(ap, &n_eq, &key, y, &key_nil(wt), z)?;
    let (n_tag, _) = split_pair(
        ap,
        &n_keys,
        &s.inr(h.clone()),
        p,
        &s.inl(s.point()),
        &sets.pair(wt.empty(), wt.empty()),
    )?;
    let n_flip = hyp_eq_symm(env, &n_tag)?;
    let n_false = syl(&n_flip, &tags_ne(s, h)?)?;
    let right = uncurry(&syl(&n_false, &ex_falso(goal.clone()))?)?;

    let out = hyp_or_elim(&cases, &crate::com12(&k_all)?, &right)?;
    if *out.concl() != Formula::imp(hyp, goal) {
        return None
    }
    Some(out)
}

/// `⊢ ⟨k₀, y⟩ ∈ e(α,z,s,T) → y = z` — **the value at the nil key is the nil
/// minor premise**.
///
/// [`value_at_packed`] with the two cases exchanged: here the cons case is the
/// refuted one, `inl • = inr(π₁ q)` again.
#[allow(clippy::too_many_arguments)]
fn value_at_nil(
    env: &mut Env,
    wt: &Wtype,
    wl: &WList,
    pj: &Proj,
    sy: &StepSyms,
    alpha: &Term,
    z: &Term,
    su: &Term,
    t: &Term,
    y: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let sets = &ap.sets;
    let k0 = key_nil(wt);
    let x = sets.pair(k0.clone(), y.clone());
    let hyp = Formula::mem(x.clone(), sy.step_of(wt, alpha, z, su, t));
    let goal = Formula::eq(y.clone(), z.clone());

    let cases = step_cases(env, wt, wl, pj, sy, alpha, z, su, t, &x)?;
    let (_, disj) = cases.concl().as_imp()?;
    let (_, right_disj) = disj.as_imp()?;

    // ── The cons case, refuted ──────────────────────────────────────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let (fq, sq) = (pj.fst_of(ap, tq.clone()), pj.snd_of(ap, tq.clone()));
    let key2 = key_packed(wt, &fq, &sq);
    let val2 = value_packed(ap, pj, su, &fq, &sq);
    let k_eq = and_right(hyp.clone(), Formula::eq(x.clone(), row_at(wt, pj, su, &tq)));
    let (k_keys, _) = split_pair(ap, &k_eq, &k0, y, &key2, &val2)?;
    let (k_tag, _) = split_pair(
        ap,
        &k_keys,
        &s.inl(s.point()),
        &sets.pair(wt.empty(), wt.empty()),
        &s.inr(fq.clone()),
        &sq,
    )?;
    let k_false = syl(&k_tag, &tags_ne(s, &fq)?)?;
    let k_goal = syl(&k_false, &ex_falso(goal.clone()))?;
    let left = crate::exists_elim_imp(
        qv,
        &Thm::gen(qv, &crate::com12(&uncurry(&k_goal)?)?),
        &Formula::imp(hyp.clone(), goal.clone()),
    )?;

    // ── The nil case ────────────────────────────────────────────────────────
    let n_eq = and_right(hyp.clone(), right_disj.clone());
    let (_, n_val) = split_pair(ap, &n_eq, &k0, y, &k0, z)?;
    let right = uncurry(&n_val)?;

    let out = hyp_or_elim(&cases, &crate::com12(&left)?, &right)?;
    if *out.concl() != Formula::imp(hyp, goal) {
        return None
    }
    Some(out)
}

/// `⊢ sv(e(α,z,s,T))` — **the step is single-valued**, hence a function wherever
/// it is defined.
///
/// [`step_cases`] on the first of the two pairs decides which key `x` is, and
/// then [`value_at_packed`] or [`value_at_nil`] forces *both* values.
#[allow(clippy::too_many_arguments)]
pub(super) fn step_single_valued(
    env: &mut Env,
    wt: &Wtype,
    wl: &WList,
    pj: &Proj,
    sy: &StepSyms,
    alpha: &Term,
    z: &Term,
    su: &Term,
    t: &Term,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let sets = &ap.sets;
    let step = sy.step_of(wt, alpha, z, su, t);
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
    let cases = syl(&h_1, &step_cases(env, wt, wl, pj, sy, alpha, z, su, t, &p1)?)?;
    let (_, disj) = cases.concl().as_imp()?;
    let (_, right_disj) = disj.as_imp()?;

    // ── `x` is a cons key ───────────────────────────────────────────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let (fq, sq) = (pj.fst_of(ap, tq.clone()), pj.snd_of(ap, tq.clone()));
    let key2 = key_packed(wt, &fq, &sq);
    let val2 = value_packed(ap, pj, su, &fq, &sq);
    let k = Formula::and(h.clone(), Formula::eq(p1.clone(), row_at(wt, pj, su, &tq)));
    let k_eq = and_right(h.clone(), Formula::eq(p1.clone(), row_at(wt, pj, su, &tq)));
    let (k_x, k_y) = split_pair(ap, &k_eq, &tx, &ty, &key2, &val2)?;
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
        &syl(
            &and_left(h.clone(), Formula::eq(p1.clone(), row_at(wt, pj, su, &tq))),
            &h_2,
        )?,
    )?;
    let k_y2 = hyp_mp(
        &a1i(
            &value_at_packed(env, wt, wl, pj, sy, alpha, z, su, t, &fq, &sq, &ty2)?,
            k.clone(),
        ),
        &k_m2,
    )?;
    let k_back = hyp_eq_symm(env, &k_y2)?;
    let k_goal = hyp_eq_trans(env, &k_y, &k_back)?;
    let left = crate::exists_elim_imp(
        qv,
        &Thm::gen(qv, &crate::com12(&uncurry(&k_goal)?)?),
        &Formula::imp(h.clone(), goal.clone()),
    )?;

    // ── `x` is the nil key ──────────────────────────────────────────────────
    let k0 = key_nil(wt);
    let n = Formula::and(h.clone(), right_disj.clone());
    let n_eq = and_right(h.clone(), right_disj.clone());
    let (n_x, n_y) = split_pair(ap, &n_eq, &tx, &ty, &k0, z)?;
    let hole2 = env.fresh_var();
    let n_m2 = hyp_mp(
        &hyp_mp(
            &a1i(
                &Thm::eq_leibniz(
                    tx.clone(),
                    k0.clone(),
                    hole2,
                    Formula::mem(sets.pair(Term::var(hole2), ty2.clone()), step.clone()),
                ),
                n.clone(),
            ),
            &n_x,
        )?,
        &syl(&and_left(h.clone(), right_disj.clone()), &h_2)?,
    )?;
    let n_y2 = hyp_mp(
        &a1i(&value_at_nil(env, wt, wl, pj, sy, alpha, z, su, t, &ty2)?, n.clone()),
        &n_m2,
    )?;
    let n_back = hyp_eq_symm(env, &n_y2)?;
    let n_goal = hyp_eq_trans(env, &n_y, &n_back)?;
    let right = uncurry(&n_goal)?;

    let body = hyp_or_elim(&cases, &crate::com12(&left)?, &right)?;
    let out = gen_all(&[xv, yv, y2v], &body);
    if *out.concl() != want {
        return None
    }
    Some(out)
}
