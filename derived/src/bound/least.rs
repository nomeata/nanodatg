//! **Step 5** — the transfer to `U(c)`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(c)))
//!                 → closed(A,B,U(c)))                     [least_universe_closed]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why this is not [`super::closure`] at `u := U(c)`
//!
//! Because `is_universe(U(c))` is **not available**: its inaccessibility clause
//! is open, see [`crate::universe::inaccessibility_reduction`]. So the closure
//! property has to be transferred rather than instantiated, and the transfer is
//! the one [`crate::universe::least_universe_pairing`] makes — a property that
//! holds in *every* universe holds in `U(c)`, because `U(c) ⊆ u` for every
//! universe `u ∋ c`.
//!
//! The one wrinkle is that the hypothesis moves the wrong way:
//! `f ∈ fs(B(a), U(c))` has to become `f ∈ fs(B(a), u)` before
//! [`super::closure`] applies, which is [`crate::wtype::fs_mono`] —
//! monotonicity of the function space in its codomain — over the inclusion
//! `least_universe_subset` derives here.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::sums::Sums;
use crate::universe::is_universe;
use crate::wtype::closed;
use crate::{
    a1i, and_left, and_right, com12, gen_all, hyp_and, hyp_mp, iff_mpr, inst_all, opair, syl,
    uncurry,
};

use super::shared::hyp_inst_mp;
use super::closure::fibres_in;

/// `⊢ A_univ → U(c) ⊆ u`, where `A_univ := is_universe(u) ∧ c ∈ u`.
///
/// The intersection of all universes containing `c` is contained in each of
/// them — [`crate::universe::least_universe_transfer`] generalised over the
/// element.
///
/// `pub` for [`crate::cumul::DeclUniverse::over_at_general`], whose step (f)
/// needs `W(A,B,U({A,T})) ⊆ Uₙ` and gets it from `W ⊆ U({A,T})` (W1) composed
/// with this at `c := {A,T}`, `u := Uₙ`. That is the one place in the path
/// route where a *new* set-theoretic fact is spent rather than an assembled
/// one.
pub fn least_universe_subset(env: &mut Env, lu_ax: &Thm, c: &Term, w: &Term, u: &Term) -> Option<Thm> {
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let transfer = crate::universe::least_universe_transfer(env, lu_ax, c, &tz, u)?;
    let flipped = com12(&transfer)?;
    let (a_univ, body) = flipped.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(zv, a_univ.clone(), body)?, &Thm::gen(zv, &flipped))?;
    if *out.concl() != Formula::imp(a_univ, kernel::thm::subset(env, w.clone(), u.clone())) {
        return None
    }
    Some(out)
}

/// `⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(c))) → closed(A,B,U(c)))`
/// — **the bound hypothesis discharged at the canonical universe**, with no
/// hypothesis about `U(c)` at all.
///
/// Fix any universe `u ∋ c`. Then `A ∈ u` and every `B(a) ∈ u` by
/// [`crate::universe::least_universe_transfer`], and `U(c) ⊆ u`, so a function
/// `f ∈ fs(B(a), U(c))` is a function `f ∈ fs(B(a), u)` by
/// [`crate::wtype::fs_mono`]. [`crate::bound::universe_closed`] then puts `⟨a,f⟩` in `u` —
/// for *every* such `u`, which is membership in `U(c)`.
///
/// `fs_mono` must be [`crate::wtype::fs_mono`]'s output and `general`
/// [`crate::bound::universe_closed`]'s; both are rebuilt and compared.
pub fn least_universe_closed(
    env: &mut Env,
    s: &Sums,
    lu: FnSym,
    lu_ax: &Thm,
    fs_mono: &Thm,
    general: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 {
        return None
    }
    let up = s.ap.sets.up;
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let (pav, pfv) = (env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pav), Term::var(pfv));

    // `H := A ∈ U(c) ∧ ∀a ∈ A. B(a) ∈ U(c)`.
    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let fam_w = Formula::forall(
        pav,
        Formula::imp(
            Formula::mem(tpa.clone(), ta.clone()),
            Formula::mem(s.ap.apply(tb.clone(), tpa.clone()), w.clone()),
        ),
    );
    if fam_w != fibres_in(env, s, &ta, &tb, &w) {
        return None
    }
    let h = Formula::and(a_in_w.clone(), fam_w.clone());
    let h_a = and_left(a_in_w.clone(), fam_w.clone());
    let h_fam = and_right(a_in_w, fam_w);

    // `G := (H ∧ a ∈ A) ∧ f ∈ fs(B(a), U(c))`, the `u`-free working context.
    let fibre = s.ap.apply(tb.clone(), tpa.clone());
    let mem_aa = Formula::mem(tpa.clone(), ta.clone());
    let mem_f_w = Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), w.clone()));
    let pair_t = opair(up, tpa.clone(), tpf.clone());
    let front = Formula::and(h.clone(), mem_aa.clone());
    let g = Formula::and(front.clone(), mem_f_w.clone());
    let g_front = and_left(front.clone(), mem_f_w.clone());
    let g_h = syl(&g_front, &and_left(h.clone(), mem_aa.clone()))?;
    let g_aa = syl(&g_front, &and_right(h.clone(), mem_aa.clone()))?;
    let g_f = and_right(front.clone(), mem_f_w.clone());

    // A universe `u` containing `c`, held fixed until the very end.
    let uv = env.fresh_var();
    let tu = Term::var(uv);
    let univ_u = is_universe(env, &tu);
    let c_in_u = Formula::mem(tc.clone(), tu.clone());
    let a_univ = Formula::and(univ_u.clone(), c_in_u.clone());

    let k = Formula::and(g.clone(), a_univ.clone());
    let k_g = and_left(g.clone(), a_univ.clone());
    let k_au = and_right(g.clone(), a_univ.clone());
    let k_univ = syl(&k_au, &and_left(univ_u, c_in_u))?;
    let k_h = syl(&k_g, &g_h)?;
    let k_aa = syl(&k_g, &g_aa)?;
    let k_f = syl(&k_g, &g_f)?;

    // ── `A ∈ u`, and every fibre in `u` ─────────────────────────────────────
    let tr_a = crate::universe::least_universe_transfer(env, lu_ax, &tc, &ta, &tu)?;
    let k_a_u = hyp_mp(&hyp_mp(&a1i(&tr_a, k.clone()), &syl(&k_h, &h_a)?)?, &k_au)?;

    // A *second* fresh variable for the family clause: `a` is free in `G`, so
    // the one `G` speaks about cannot be generalised back out.
    let qav = env.fresh_var();
    let tqa = Term::var(qav);
    let mem_qa = Formula::mem(tqa.clone(), ta.clone());
    let fibre_q = s.ap.apply(tb.clone(), tqa.clone());
    let p_k = and_left(k.clone(), mem_qa.clone());
    let p_aa = and_right(k.clone(), mem_qa.clone());
    let p_bw = hyp_inst_mp(&syl(&syl(&p_k, &k_h)?, &h_fam)?, &tqa, &p_aa)?;
    let tr_b = crate::universe::least_universe_transfer(env, lu_ax, &tc, &fibre_q, &tu)?;
    let p_bu = hyp_mp(&syl(&p_bw, &tr_b)?, &syl(&p_k, &k_au)?)?;
    let fam_u = Formula::forall(
        qav,
        Formula::imp(mem_qa.clone(), Formula::mem(fibre_q.clone(), tu.clone())),
    );
    let p_curried = uncurry(&p_bu)?;
    let k_fam = Thm::mp(
        &Thm::ax_dist(qav, k.clone(), p_curried.concl().as_imp()?.1.clone())?,
        &Thm::gen(qav, &p_curried),
    )?;
    if *k_fam.concl() != Formula::imp(k.clone(), fam_u.clone()) {
        return None
    }

    // ── `closed(A,B,u)` from step 4 ─────────────────────────────────────────
    let gen_at = inst_all(general, &[tu.clone(), ta.clone(), tb.clone()])?;
    if *gen_at.concl()
        != Formula::imp(
            Formula::and(
                is_universe(env, &tu),
                Formula::and(Formula::mem(ta.clone(), tu.clone()), fam_u),
            ),
            closed(env, s, &ta, &tb, &tu),
        )
    {
        return None
    }
    let k_closed =
        hyp_mp(&a1i(&gen_at, k.clone()), &hyp_and(&k_univ, &hyp_and(&k_a_u, &k_fam)?)?)?;

    // ── The function, re-aimed at `u` along `U(c) ⊆ u` ──────────────────────
    let k_sub = syl(&k_au, &least_universe_subset(env, lu_ax, &tc, &w, &tu)?)?;
    let mono_at = inst_all(fs_mono, &[fibre.clone(), w.clone(), tu.clone(), tpf.clone()])?;
    let mem_f_u = Formula::mem(tpf.clone(), s.fs.of(fibre.clone(), tu.clone()));
    if *mono_at.concl()
        != Formula::imp(
            Formula::and(mem_f_w.clone(), kernel::thm::subset(env, w.clone(), tu.clone())),
            mem_f_u,
        )
    {
        return None
    }
    let k_f_u = syl(&hyp_and(&k_f, &k_sub)?, &mono_at)?;

    // `closed` applied at `a` and `f`.
    let k_at_a = hyp_inst_mp(&k_closed, &tpa, &k_aa)?;
    let k_goal = hyp_inst_mp(&k_at_a, &tpf, &k_f_u)?;
    if *k_goal.concl() != Formula::imp(k, Formula::mem(pair_t.clone(), tu.clone())) {
        return None
    }

    // ── Generalise over `u`: membership in every universe is membership in `U(c)` ──
    let g_all = Thm::mp(
        &Thm::ax_dist(uv, g.clone(), Formula::imp(a_univ, Formula::mem(pair_t.clone(), tu)))?,
        &Thm::gen(uv, &uncurry(&k_goal)?),
    )?;
    if *g_all.concl()
        != Formula::imp(g.clone(), crate::universe::in_all_universes(env, &tc, &pair_t))
    {
        return None
    }
    let g_goal = syl(
        &g_all,
        &iff_mpr(&crate::universe::least_universe_mem(lu_ax, &tc, &pair_t)?)?,
    )?;

    // ── Reassemble into `closed`'s own shape ────────────────────────────────
    let x_f = Formula::imp(mem_f_w, Formula::mem(pair_t, w.clone()));
    let front_all = Thm::mp(
        &Thm::ax_dist(pfv, front.clone(), x_f.clone())?,
        &Thm::gen(pfv, &uncurry(&g_goal)?),
    )?;
    let inner = Formula::imp(mem_aa, Formula::forall(pfv, x_f));
    let out = Thm::mp(
        &Thm::ax_dist(pav, h.clone(), inner)?,
        &Thm::gen(pav, &uncurry(&front_all)?),
    )?;

    if *out.concl() != Formula::imp(h, closed(env, s, &ta, &tb, &w)) {
        return None
    }
    Some(gen_all(&[cv, av, bv], &out))
}
