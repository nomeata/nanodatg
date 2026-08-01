//! **Stage arithmetic**: what one more `succ` buys, and how a stage sits inside
//! the tower.
//!
//! # Interface
//!
//! Writing `Vₚ` for `app(iter(S), p)` and `T` for `tower(S)`:
//!
//! ```text
//! ⊢ ∀p. (p ∈ ω → ∀z. (z ∈ Vₚ → z ∈ T))                             [mem_tower]
//! ⊢ ∀p. (p ∈ ω → ∀z. (z ⊆ Vₚ → z ∈ V₍succ p₎))                     [sub_in_stage]
//! ⊢ ∀p. (p ∈ ω → ∀x ∀y. ((x ∈ Vₚ ∧ y ∈ Vₚ)
//!                            → ⟨x,y⟩ ∈ V₍succ succ p₎))            [pair_in_stage]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # What they are for
//!
//! These are the three moves the `sup` closure of the tower is assembled from.
//! Given `a ∈ A` and `f : B(a) → T` with `B(a)` finite,
//! [`super::bounded`] produces one stage `Vₚ` holding every value of `f`, and
//! then: each pair `⟨b, f(b)⟩` of the graph is in `V₍succ succ p₎`
//! ([`pair_in_stage`]), so `f` itself — a subset of that stage — is in
//! `V₍succ³ p₎` ([`sub_in_stage`]), so `⟨a,f⟩` is in `V₍succ⁵ p₎`
//! ([`pair_in_stage`] again), so `⟨a,f⟩ ∈ T` ([`mem_tower`]). Every step is one
//! of these three, and the only arithmetic involved is applying `succ`.

use kernel::{Env, Formula, Term, Thm};

use crate::funspace::pow_pow::upair_subset;
use crate::recursion::Rec;
use crate::separation::hyp_syl;
use crate::{
    a1i, and_intro_imp, eq_symm_imp, exists_intro_imp, hyp_and, hyp_mp, iff_mpr,
    imp_mono_r, inst_all, opair, singleton, syl,
};

use super::stages::Stages;

/// `⊢ ∀p. (p ∈ ω → ∀z. (z ∈ Vₚ → z ∈ T))` — every stage is inside the tower.
pub fn mem_tower(env: &mut Env, r: &Rec, st: &Stages) -> Option<Thm> {
    let (pv, zv, nv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tz, tn) = (Term::var(pv), Term::var(zv), Term::var(nv));
    let om = r.omega();

    let p_om = Formula::mem(tp.clone(), om.clone());
    let z_vp = Formula::mem(tz.clone(), st.v(r, tp.clone()));
    let body = Formula::and(
        Formula::mem(tn.clone(), om),
        Formula::mem(tz.clone(), st.v(r, tn)),
    );
    let members_at = inst_all(&st.tower.members, std::slice::from_ref(&tz))?;
    let to_tower = syl(&exists_intro_imp(nv, body, tp.clone())?, &iff_mpr(&members_at)?)?;

    let pack = and_intro_imp(p_om.clone(), z_vp.clone());
    let inner = syl(&pack, &imp_mono_r(&to_tower, z_vp.clone())?)?;
    let out = Thm::mp(
        &Thm::ax_dist(
            zv,
            p_om.clone(),
            Formula::imp(z_vp, Formula::mem(tz, st.tower_set())),
        )?,
        &Thm::gen(zv, &inner),
    )?;
    Some(Thm::gen(pv, &out))
}

/// `⊢ ∀p. (p ∈ ω → ∀z. (z ⊆ Vₚ → z ∈ V₍succ p₎))` — one `succ` absorbs every
/// subset of a stage.
pub fn sub_in_stage(env: &mut Env, r: &Rec, st: &Stages) -> Option<Thm> {
    let (pv, zv) = (env.fresh_var(), env.fresh_var());
    let (tp, tz) = (Term::var(pv), Term::var(zv));
    let p_om = Formula::mem(tp.clone(), r.omega());

    let move_up = next_stage(env, r, st, &tp, &tz, &p_om)?;
    let sub_at = inst_all(&st.step.sub, &[st.v(r, tp.clone()), tz.clone()])?;
    let inner = hyp_syl(&a1i(&sub_at, p_om.clone()), &move_up)?;

    let vsp = st.v(r, r.succ_of(tp.clone()));
    let goal = Formula::imp(
        kernel::thm::subset(env, tz.clone(), st.v(r, tp.clone())),
        Formula::mem(tz.clone(), vsp),
    );
    let out = Thm::mp(&Thm::ax_dist(zv, p_om, goal)?, &Thm::gen(zv, &inner))?;
    Some(Thm::gen(pv, &out))
}

/// `⊢ H → (z ∈ G(Vₚ) → z ∈ V₍succ p₎)` for `H := p ∈ ω` — the rewrite along the
/// step equation, which both lemmas above run.
fn next_stage(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    p: &Term,
    z: &Term,
    h: &Formula,
) -> Option<Thm> {
    let vp = st.v(r, p.clone());
    let vsp = st.v(r, r.succ_of(p.clone()));
    let gvp = st.step.of(vp);
    let h_eq = inst_all(&st.rec.step, std::slice::from_ref(p))?;
    debug_assert_eq!(*h_eq.concl(), Formula::imp(h.clone(), Formula::eq(vsp.clone(), gvp.clone())));
    let sym = syl(&h_eq, &eq_symm_imp(env, vsp.clone(), gvp.clone()))?;
    let wv = env.fresh_var();
    let leib =
        Thm::eq_leibniz(gvp, vsp, wv, Formula::mem(z.clone(), Term::var(wv)));
    syl(&sym, &leib)
}

/// `⊢ ∀p. (p ∈ ω → ∀x ∀y. ((x ∈ Vₚ ∧ y ∈ Vₚ) → ⟨x,y⟩ ∈ V₍succ succ p₎))` —
/// **two** `succ`s absorb an ordered pair of members of a stage.
///
/// `{x,y}` and `{x}` are subsets of `Vₚ`, hence members of `V₍succ p₎`; the
/// Kuratowski pair `{{x},{x,y}}` is then a subset of `V₍succ p₎`, hence a member
/// of `V₍succ succ p₎`. Three applications of
/// [`crate::funspace::pow_pow::upair_subset`] and two of [`sub_in_stage`].
pub fn pair_in_stage(env: &mut Env, r: &Rec, st: &Stages, sub_in: &Thm) -> Option<Thm> {
    let (pv, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tx, ty) = (Term::var(pv), Term::var(xv), Term::var(yv));
    let up = r.ap.sets.up;
    let om = r.omega();

    let vp = st.v(r, tp.clone());
    let sp = r.succ_of(tp.clone());
    let vsp = st.v(r, sp.clone());
    let ssp = r.succ_of(sp.clone());
    let vssp = st.v(r, ssp);

    let p_om = Formula::mem(tp.clone(), om.clone());
    let x_vp = Formula::mem(tx.clone(), vp.clone());
    let y_vp = Formula::mem(ty.clone(), vp.clone());
    // `H := p ∈ ω ∧ (x ∈ Vₚ ∧ y ∈ Vₚ)`.
    let both = Formula::and(x_vp.clone(), y_vp.clone());
    let h = Formula::and(p_om.clone(), both.clone());
    let h_p = crate::and_left(p_om.clone(), both.clone());
    let h_xy = crate::and_right(p_om.clone(), both.clone());
    let h_x = syl(&h_xy, &crate::and_left(x_vp.clone(), y_vp.clone()))?;
    let h_y = syl(&h_xy, &crate::and_right(x_vp, y_vp))?;

    let up_sub = upair_subset(env, &r.ap.sets)?;
    let sub_at_p = hyp_mp(
        &a1i(&inst_all(sub_in, std::slice::from_ref(&tp))?, h.clone()),
        &h_p,
    )?;
    let succ_closed_at = inst_all(&r.core().succ_closed, std::slice::from_ref(&tp))?;
    let h_sp = hyp_mp(&a1i(&succ_closed_at, h.clone()), &h_p)?;
    let sub_at_sp = hyp_mp(
        &a1i(&inst_all(sub_in, std::slice::from_ref(&sp))?, h.clone()),
        &h_sp,
    )?;

    // `{x,y} ∈ V₍succ p₎` and `{x} ∈ V₍succ p₎`.
    let pair_up = |a: &Term, b: &Term| Term::apply(up, vec![a.clone(), b.clone()]);
    let (_, all_z_p) = sub_at_p.concl().as_imp()?;
    let (_, all_z_sp) = sub_at_sp.concl().as_imp()?;

    let xy = pair_up(&tx, &ty);
    let us_xy = inst_all(&up_sub, &[tx.clone(), ty.clone(), vp.clone()])?;
    let xy_sub = hyp_mp(&a1i(&us_xy, h.clone()), &hyp_and(&h_x, &h_y)?)?;
    let xy_in = hyp_mp(
        &syl(&sub_at_p, &Thm::ax_inst(all_z_p.clone(), xy.clone())?)?,
        &xy_sub,
    )?;

    let sx = singleton(up, tx.clone());
    let us_x = inst_all(&up_sub, &[tx.clone(), tx.clone(), vp.clone()])?;
    let x_sub = hyp_mp(&a1i(&us_x, h.clone()), &hyp_and(&h_x, &h_x)?)?;
    let x_in =
        hyp_mp(&syl(&sub_at_p, &Thm::ax_inst(all_z_p, sx.clone())?)?, &x_sub)?;

    // `⟨x,y⟩ = {{x},{x,y}} ⊆ V₍succ p₎`, hence a member of `V₍succ succ p₎`.
    let pair = opair(up, tx.clone(), ty.clone());
    let us_p = inst_all(&up_sub, &[sx, xy, vsp])?;
    let pair_sub = hyp_mp(&a1i(&us_p, h.clone()), &hyp_and(&x_in, &xy_in)?)?;
    let out = hyp_mp(
        &syl(&sub_at_sp, &Thm::ax_inst(all_z_sp, pair.clone())?)?,
        &pair_sub,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(pair, vssp.clone())),
        "pair_in_stage: unexpected shape"
    );

    let curried = super::step::curry(&out)?;
    let body_y = Formula::imp(
        both,
        Formula::mem(opair(up, tx.clone(), ty.clone()), vssp),
    );
    let all_y = Thm::mp(
        &Thm::ax_dist(yv, p_om.clone(), body_y.clone())?,
        &Thm::gen(yv, &curried),
    )?;
    let all_x = Thm::mp(
        &Thm::ax_dist(xv, p_om, Formula::forall(yv, body_y))?,
        &Thm::gen(xv, &all_y),
    )?;
    Some(Thm::gen(pv, &all_x))
}
