//! The one-point attempt.
//!
//! # Interface
//!
//! [`singleton_attempt`] returns a [`UnitAttempt`] holding
//!
//! ```text
//! ⊢ g ∈ Att({c}, ∅, U(c), T, e)                              [UnitAttempt::att]
//! ⊢ app(g, ⟨c,∅⟩) = V                                      [UnitAttempt::value]
//! ```
//!
//! where `V := app(e, ⟨c,⟨∅,∅⟩⟩)` ([`unit_value`]), `T := {V}`
//! ([`unit_target`]) and `g := {⟨⟨c,∅⟩, V⟩}` ([`unit_graph`]). Callers need
//! none of the derivation below.
//!
//! # What has to be checked, and why each is cheap
//!
//! All three clauses of the attempt condition, for a graph with one pair:
//!
//! * **a subset of `prod(W,T)`** — `⟨c,∅⟩ ∈ W` from
//!   [`super::instance`], and `V ∈ T` because `T` is `{V}`;
//! * **single-valued** — a one-pair graph is, by injectivity of the Kuratowski
//!   pair;
//! * **the recursion condition** — the only point of the domain is `⟨c,∅⟩`, its
//!   fibre is empty so there are no subterms to be in the domain, and the value
//!   equation is `app(g,⟨c,∅⟩) = app(e, ⟨c,⟨∅, comp(g,∅,∅)⟩⟩)`, which
//!   [`super::comp_empty_domain`] turns into the definition of `V`.
//!
//! This is the whole reason the instance was chosen: every obligation degenerates
//! rather than being discharged by an argument.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::funspace::is_single_valued;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans, hyp_exists_elim, indom, rec_cond};
use crate::wtype::Wtype;
use crate::{
    a1i, and_intro, and_left, and_right, com12, eq_symm_imp, ex_falso, hyp_and, iff_mp, iff_mpr,
    imp_refl, inst_all, singleton, syl,
};

use super::shared::{congr, eq_trans};
use super::composite::comp_empty_domain;

/// The term `V = app(e, ⟨c, ⟨∅,∅⟩⟩)` — the value the step forces at `⟨c,∅⟩`.
///
/// Closed in `wrec`: the third component is the composite over the empty fibre,
/// which [`comp_empty_domain`] equates with `∅`.
pub fn unit_value(ap: &Apply, c: &Term, e: &Term) -> Term {
    let z = Term::apply(ap.empty, vec![]);
    ap.apply(
        e.clone(),
        ap.sets.pair(c.clone(), ap.sets.pair(z.clone(), z)),
    )
}

/// The term `T = {V}` — the smallest target the one-point attempt can have.
pub fn unit_target(ap: &Apply, c: &Term, e: &Term) -> Term {
    singleton(ap.sets.up, unit_value(ap, c, e))
}

/// The term `g = {⟨⟨c,∅⟩, V⟩}` — the one-point attempt itself.
pub fn unit_graph(ap: &Apply, c: &Term, e: &Term) -> Term {
    let z = Term::apply(ap.empty, vec![]);
    singleton(
        ap.sets.up,
        ap.sets.pair(ap.sets.pair(c.clone(), z), unit_value(ap, c, e)),
    )
}

/// What [`singleton_attempt`] derives about `g = {⟨⟨c,∅⟩, V⟩}`.
pub struct UnitAttempt {
    /// `⊢ g ∈ Att({c}, ∅, U(c), {V}, e)`.
    pub att: Thm,
    /// `⊢ sv(g)`.
    pub sv: Thm,
    /// `⊢ ⟨⟨c,∅⟩, V⟩ ∈ g`.
    pub mem: Thm,
    /// `⊢ app(g, ⟨c,∅⟩) = V` — the attempt's value, computed.
    pub value: Thm,
}

/// **The one-point graph is an attempt.**
///
/// `sup` is `⊢ ⟨c,∅⟩ ∈ W({c},∅,u)` and `u` the bound it is stated over — in
/// practice `UnitWtype`'s two fields at `u := U(c)`, but nothing below needs
/// `u` to be a universe.
///
/// The three clauses of [`crate::wrec::attempt_cond`]:
///
/// * `g ⊆ prod(W,{V})` — one point, `⟨c,∅⟩ ∈ W` by `sup` and `V ∈ {V}` by
///   reflexivity;
/// * `sv(g)` — two pairs of a singleton are the same pair, so
///   [`crate::pairs::opair_inj`] equates their second components with `V`;
/// * `rec_cond(∅, e, g)` — the subterm clause is vacuous, because
///   `B(a) = app(∅,a) = ∅`; and the equation holds because `indom(g,⟨a,f⟩)`
///   forces `a = c` and `f = ∅`, while [`comp_empty_domain`] collapses the
///   composite, leaving `V = V`.
#[allow(clippy::too_many_arguments)]
pub fn singleton_attempt(
    env: &mut Env,
    wt: &Wtype,
    comp: FnSym,
    comp_ax: &Thm,
    att_ax: &Thm,
    sup: &Thm,
    c: &Term,
    u: &Term,
    e: &Term,
) -> Option<UnitAttempt> {
    let s = &wt.sums;
    let ap = &s.ap;
    let up = ap.sets.up;

    let z = wt.empty();
    let sing_c = singleton(up, c.clone());
    let w0 = wt.sup(c.clone(), z.clone()); // ⟨c,∅⟩
    let v = unit_value(ap, c, e);
    let t_t = unit_target(ap, c, e);
    let p = ap.sets.pair(w0.clone(), v.clone()); // ⟨⟨c,∅⟩, V⟩
    let g = unit_graph(ap, c, e);
    let w_t = wt.of(sing_c.clone(), z.clone(), u.clone());
    let prod_t = s.prod.of(w_t.clone(), t_t.clone());

    // ── `⟨⟨c,∅⟩,V⟩ ∈ g` and `V ∈ {V}` ───────────────────────────────────────
    let p_in_g = Thm::mp(
        &iff_mpr(&inst_all(&ap.mem_sing, &[p.clone(), p.clone()])?)?,
        &Thm::eq_refl(p.clone()),
    )?;
    let v_in_t = Thm::mp(
        &iff_mpr(&inst_all(&ap.mem_sing, &[v.clone(), v.clone()])?)?,
        &Thm::eq_refl(v.clone()),
    )?;

    // ── `g ∈ 𝒫(prod(W,{V}))` ────────────────────────────────────────────────
    let p_in_prod = Thm::mp(
        &iff_mpr(&inst_all(
            &s.pair_in_prod,
            &[w_t.clone(), t_t.clone(), w0.clone(), v.clone()],
        )?)?,
        &and_intro(sup, &v_in_t),
    )?;
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let hole = env.fresh_var();
    let step = syl(
        &syl(
            &iff_mp(&inst_all(&ap.mem_sing, &[p.clone(), tz.clone()])?)?,
            &eq_symm_imp(env, tz.clone(), p.clone()),
        )?,
        &Thm::eq_leibniz(
            p.clone(),
            tz.clone(),
            hole,
            Formula::mem(Term::var(hole), prod_t.clone()),
        ),
    )?;
    let sub = Thm::gen(zv, &Thm::mp(&com12(&step)?, &p_in_prod)?);
    debug_assert_eq!(
        *sub.concl(),
        kernel::thm::subset(env, g.clone(), prod_t.clone()),
        "singleton_attempt: the inclusion has the wrong shape"
    );
    let in_pow = Thm::mp(
        &iff_mpr(&inst_all(&s.pow_ax, &[prod_t, g.clone()])?)?,
        &sub,
    )?;

    // ── `sv(g)` ─────────────────────────────────────────────────────────────
    let (xv, yv, y2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(xv), Term::var(yv), Term::var(y2v));
    let sv = {
        let second = |y: &Term| -> Option<Thm> {
            let pair = ap.sets.pair(tx.clone(), y.clone());
            let inj = inst_all(&ap.pair_inj, &[tx.clone(), y.clone(), w0.clone(), v.clone()])?;
            syl(
                &syl(
                    &iff_mp(&inst_all(&ap.mem_sing, &[p.clone(), pair])?)?,
                    &inj,
                )?,
                &and_right(
                    Formula::eq(tx.clone(), w0.clone()),
                    Formula::eq(y.clone(), v.clone()),
                ),
            )
        };
        let get_y = second(&ty)?;
        let get_y2 = second(&ty2)?;
        let m1 = Formula::mem(ap.sets.pair(tx.clone(), ty.clone()), g.clone());
        let m2 = Formula::mem(ap.sets.pair(tx.clone(), ty2.clone()), g.clone());
        let h_y = syl(&and_left(m1.clone(), m2.clone()), &get_y)?;
        let h_y2 = syl(&and_right(m1, m2), &get_y2)?;
        let h_v_y2 = hyp_eq_symm(env, &h_y2)?;
        let body = hyp_eq_trans(env, &h_y, &h_v_y2)?;
        Thm::gen(xv, &Thm::gen(yv, &Thm::gen(y2v, &body)))
    };
    debug_assert_eq!(
        *sv.concl(),
        is_single_valued(env, &ap.sets, &g),
        "singleton_attempt: sv(g) has the wrong shape"
    );

    // ── `app(g, ⟨c,∅⟩) = V` ─────────────────────────────────────────────────
    let g_value = Thm::mp(
        &inst_all(&wt.app_pair, &[g.clone(), w0.clone(), v.clone()])?,
        &and_intro(&sv, &p_in_g),
    )?;

    // ── `rec_cond(∅, e, g)` ─────────────────────────────────────────────────
    let comp_empty = comp_empty_domain(env, ap, comp, comp_ax)?;
    let (pa, pf, y0) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, ty0) = (Term::var(pa), Term::var(pf), Term::var(y0));
    let wa = ap.sets.pair(tpa.clone(), tpf.clone()); // ⟨a,f⟩
    let fibre = wt.fibre(z.clone(), tpa.clone()); // app(∅,a)
    let phi = Formula::mem(ap.sets.pair(wa.clone(), ty0.clone()), g.clone());
    let h = Formula::exists(y0, phi.clone());
    debug_assert_eq!(h, indom(env, ap, &g, &wa), "singleton_attempt: indom drifted");

    let app_empty_a = inst_all(&wt.app_empty, std::slice::from_ref(&tpa))?;

    // The subterm clause is vacuous: `b ∈ app(∅,a)` is refutable.
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let sub_goal = indom(env, ap, &g, &ap.apply(tpf.clone(), tb.clone()));
    let hole_b = env.fresh_var();
    let to_empty = Thm::mp(
        &Thm::eq_leibniz(
            fibre.clone(),
            z.clone(),
            hole_b,
            Formula::mem(tb.clone(), Term::var(hole_b)),
        ),
        &app_empty_a,
    )?;
    let refuted = syl(&to_empty, &inst_all(&ap.empty_ax, std::slice::from_ref(&tb))?)?;
    let subterms = Thm::gen(bv, &syl(&refuted, &ex_falso(sub_goal))?);

    // The equation, under `K := indom(g,⟨a,f⟩) ∧ ⟨⟨a,f⟩,y⟩ ∈ g`.
    let k = Formula::and(h.clone(), phi.clone());
    let k_phi = and_right(h.clone(), phi.clone());
    let k_pair_eq = syl(
        &k_phi,
        &iff_mp(&inst_all(
            &ap.mem_sing,
            &[p.clone(), ap.sets.pair(wa.clone(), ty0.clone())],
        )?)?,
    )?;
    let k_conj = syl(
        &k_pair_eq,
        &inst_all(&ap.pair_inj, &[wa.clone(), ty0.clone(), w0.clone(), v.clone()])?,
    )?;
    let k_w = syl(
        &k_conj,
        &and_left(
            Formula::eq(wa.clone(), w0.clone()),
            Formula::eq(ty0.clone(), v.clone()),
        ),
    )?;
    let k_af = syl(
        &k_w,
        &inst_all(&ap.pair_inj, &[tpa.clone(), tpf.clone(), c.clone(), z.clone()])?,
    )?;
    let eq_a = Formula::eq(tpa.clone(), c.clone());
    let eq_f = Formula::eq(tpf.clone(), z.clone());
    let k_a = syl(&k_af, &and_left(eq_a.clone(), eq_f.clone()))?;
    let k_f = syl(&k_af, &and_right(eq_a, eq_f))?;

    // Left: `app(g,⟨a,f⟩) = app(g,⟨c,∅⟩) = V`.
    let k_at_w0 = hyp_congr(env, &k_w, |t| ap.apply(g.clone(), t))?;
    let k_lhs = hyp_eq_trans(env, &k_at_w0, &a1i(&g_value, k.clone()))?;

    // Right: the composite collapses, then `f` and `a` are rewritten.
    let fibre_coll = congr(env, &app_empty_a, |t| comp_of(comp, g.clone(), tpf.clone(), t))?;
    let coll = eq_trans(env, &fibre_coll, &inst_all(&comp_empty, &[g.clone(), tpf.clone()])?)?;
    let r1 = congr(env, &coll, |t| {
        ap.apply(
            e.clone(),
            ap.sets.pair(tpa.clone(), ap.sets.pair(tpf.clone(), t)),
        )
    })?;
    let r2 = hyp_congr(env, &k_f, |t| {
        ap.apply(
            e.clone(),
            ap.sets.pair(tpa.clone(), ap.sets.pair(t, z.clone())),
        )
    })?;
    let r3 = hyp_congr(env, &k_a, |t| {
        ap.apply(
            e.clone(),
            ap.sets.pair(t, ap.sets.pair(z.clone(), z.clone())),
        )
    })?;
    let k_r12 = hyp_eq_trans(env, &a1i(&r1, k.clone()), &r2)?;
    let k_rhs = hyp_eq_trans(env, &k_r12, &r3)?;

    let k_rhs_symm = hyp_eq_symm(env, &k_rhs)?;
    let k_eqn = hyp_eq_trans(env, &k_lhs, &k_rhs_symm)?;
    let h_eqn = hyp_exists_elim(y0, &k_eqn, &imp_refl(h.clone()))?;

    let body = hyp_and(&a1i(&subterms, h), &h_eqn)?;
    let rc = Thm::gen(pa, &Thm::gen(pf, &body));
    debug_assert_eq!(
        *rc.concl(),
        rec_cond(env, ap, comp, &z, e, &g),
        "singleton_attempt: rec_cond(g) has the wrong shape"
    );

    // ── The three clauses, assembled ────────────────────────────────────────
    let att = Thm::mp(
        &iff_mpr(&inst_all(att_ax, &[sing_c, z, u.clone(), t_t, e.clone(), g])?)?,
        &and_intro(&in_pow, &and_intro(&sv, &rc)),
    )?;

    Some(UnitAttempt { att, sv, mem: p_in_g, value: g_value })
}
