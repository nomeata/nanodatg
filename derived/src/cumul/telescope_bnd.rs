//! **`⊢ bnd(Σ y:β₀(p⃗). 1)`** — a **one-level** telescope is no bigger than its
//! domain.
//!
//! # Interface
//!
//! ```text
//! bnd_telescope1(env, ic, mach, tel, ps, dom_bnd) -> Option<Thm>
//!
//! ⊢ bnd(T(p⃗))        given  ⊢ bnd(β₀(p⃗))  and  tel.ys.len() == 1
//! ```
//!
//! `T(p⃗)` is [`Telescope::ty_of`], the packed type §5.2 gives a one-binder
//! telescope; at a **fibre** telescope `γᵢⱼ = [c]` that is exactly the summand
//! [`fibre_summands`](crate::inductive::carrier::fibre_summands) computes, so
//! this is the last step of the chain
//! [`super::DeclUniverse::over_at_general`]'s `FibreFacts::bnd` sits on:
//!
//! ```text
//! bnd(⟦γ⟧)                    super::bnd_carrier, at the interpretation's own declaration
//! bnd(Σ z:⟦γ⟧. 1)             here
//! bnd(Sum_m(A⃗))               super::bnd_isum
//! ```
//!
//! # Why the inversion is free here and was not at the W-type
//!
//! [`Telescope::eta`] is `⊢ ∀p⃗ ∀q. (q ∈ T(p⃗) → ⟨comp₀ q, •⟩ = q)` — a
//! **term-level** inversion, with no existential to eliminate, because the
//! projections name the components. So the pullback's witness at `q` is
//! `π₁q` and there is no `discharge` step at all; this is the shortest of the
//! four instances of the pattern, and [`super::bnd_tagged_copy`]'s header
//! describes the pattern itself.
//!
//! # Depth ≥ 2 is a different argument, and this file does not attempt it
//!
//! `Σ y₀:β₀. Σ y₁:β₁(y₀). 1` has a fibre that **varies with `y₀`**. The
//! pullback here works because the second component of every element is the
//! *same* term `•`; at depth 2 it is an element of `β₁(y₀)`, so a family on the
//! nest restricts to one family per `y₀` and the stages have to be merged over
//! `β₀`-many indices. That is a Replacement-indexed union and
//! [`super::Stages::directed`] merges two, not a set-indexed family. The guard
//! `tel.ys.len() == 1` is therefore a statement about the argument and not a
//! convenience.
//!
//! Nothing in the tutorial corpus needs depth ≥ 2 today: `zoneb`'s spec walk
//! declines a `γ` of depth `≥ 2` before a telescope is ever built. That is a
//! reason the gap has no witness, **not** a reason it is not a gap.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`] body `co(g,x) = app(g,⟨x,•⟩)` and its
//! [`crate::funcs::lambda_n`] graph — one Replacement instance. `dom_bnd` is
//! checked at `β₀(p⃗)` for the conclusion it must have and for an empty
//! hypothesis set, and every rule read off `tel` is compared against the
//! formula this file rebuilds.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{beta_conditional_n, lambda_n};
use crate::funspace::discharge;
use crate::inductive::Machine;
use crate::recursion::hyp::hyp_eq_trans;
use crate::sigma::Telescope;
use crate::{
    a1i, and_left, and_right, define_abbrev, eq_symm_imp, exists_intro_imp, hyp_and, hyp_mp,
    inst_all, syl,
};

use super::apparatus::IndChain;
use super::bounded::bnd;
use super::finite::Bnd;
use super::step::curry;

/// **`⊢ bnd(T(p⃗))`** at a one-binder telescope, given `⊢ bnd(β₀(p⃗))`.
///
/// `ps` must be the outer parameters as terms, one per [`Telescope::outer`].
/// `None` when the telescope has any depth but `1`, when `mach` is not `ic`'s
/// apparatus, or when `dom_bnd` is not `⊢ bnd(β₀(p⃗))`.
pub fn bnd_telescope1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    tel: &Telescope,
    ps: &[Term],
    dom_bnd: &Thm,
) -> Option<Thm> {
    if !ic.is_over(mach) || tel.ys.len() != 1 || tel.outer.len() != ps.len() {
        return None
    }
    let (r, st) = (&ic.chain.r, &ic.chain.st);
    let s = mach.wt.sums.clone();
    let sets = s.ap.sets.clone();
    let point = s.point();
    if r.zero() != s.zero() {
        return None
    }

    let dom = Term::apply(*tel.betas.first()?, ps.to_vec());
    let kset = tel.ty_of(ps.to_vec());
    if !dom_bnd.hyps().is_empty() || *dom_bnd.concl() != bnd(env, r, st, &dom) {
        return None
    }

    // ── the pullback graph `G = λx ∈ β₀(p⃗). app(g, ⟨x,•⟩)` ─────────────────
    let (g0, x0) = (env.fresh_var(), env.fresh_var());
    let co_body = r.apply(Term::var(g0), sets.pair(Term::var(x0), point.clone()));
    let (co, co_ax) = define_abbrev(env, &[g0, x0], &co_body)?;
    let (lam, lam_ax) = lambda_n(env, &r.ap, co)?;
    let beta = beta_conditional_n(env, &r.ap, co, lam, &lam_ax)?;

    let d = Bnd::new(env, r, st);
    let (pv2, wv) = (env.fresh_var(), env.fresh_var());
    let tp = Term::var(pv2);
    let tb = Term::var(d.bv);
    let tg = Term::var(d.gv);
    let tower = st.tower_set();
    let comp_b = Telescope::comp_of(&s.ap, &mach.proj, 0, tb.clone());

    let gterm = Term::apply(lam, vec![tg.clone(), dom.clone()]);
    let sub = |f: Formula| f.subst(d.gv, &gterm);

    let beta_at = |env: &mut Env, x: &Term| -> Option<Thm> {
        let e1 = inst_all(&beta, &[tg.clone(), dom.clone(), x.clone()])?;
        let e2 = a1i(
            &inst_all(&co_ax, &[tg.clone(), x.clone()])?,
            Formula::mem(x.clone(), dom.clone()),
        );
        hyp_eq_trans(env, &e1, &e2)
    };
    let beta_b = beta_at(env, &tb)?;
    let beta_c = beta_at(env, &comp_b)?;

    // ── the three rules, at these parameters ────────────────────────────────
    let pair_b = sets.pair(tb.clone(), point.clone());
    let pair_c = sets.pair(comp_b.clone(), point.clone());
    let intro_at = {
        let mut args = ps.to_vec();
        args.push(tb.clone());
        inst_all(&tel.intro, &args)?
    };
    if *intro_at.concl()
        != Formula::imp(
            Formula::mem(tb.clone(), dom.clone()),
            Formula::mem(pair_b.clone(), kset.clone()),
        )
    {
        return None
    }
    let (proj_at, eta_at) = {
        let mut args = ps.to_vec();
        args.push(tb.clone());
        (inst_all(tel.proj_mem.first()?, &args)?, inst_all(&tel.eta, &args)?)
    };
    if *proj_at.concl()
        != Formula::imp(
            Formula::mem(tb.clone(), kset.clone()),
            Formula::mem(comp_b.clone(), dom.clone()),
        )
        || *eta_at.concl()
            != Formula::imp(
                Formula::mem(tb.clone(), kset.clone()),
                Formula::eq(pair_c.clone(), tb.clone()),
            )
    {
        return None
    }

    let h = d.hyp(&kset); // `∀b. (b ∈ T(p⃗) → app(g,b) ∈ T)`

    // ── the pullback inherits the hypothesis ────────────────────────────────
    let jb = Formula::and(h.clone(), Formula::mem(tb.clone(), dom.clone()));
    let jb_h = and_left(h.clone(), Formula::mem(tb.clone(), dom.clone()));
    let jb_b = and_right(h.clone(), Formula::mem(tb.clone(), dom.clone()));

    let jb_gt = hyp_mp(
        &syl(&jb_h, &Thm::ax_inst(h.clone(), pair_b.clone())?)?,
        &syl(&jb_b, &intro_at)?,
    )?;
    let jb_eq = syl(
        &jb_b,
        &syl(
            &beta_b,
            &eq_symm_imp(
                env,
                r.apply(gterm.clone(), tb.clone()),
                r.apply(tg.clone(), pair_b.clone()),
            ),
        )?,
    )?;
    let jb_goal = hyp_mp(
        &syl(
            &jb_eq,
            &Thm::eq_leibniz(
                r.apply(tg.clone(), pair_b.clone()),
                r.apply(gterm.clone(), tb.clone()),
                wv,
                Formula::mem(Term::var(wv), tower.clone()),
            ),
        )?,
        &jb_gt,
    )?;
    if *jb_goal.concl()
        != Formula::imp(jb, Formula::mem(r.apply(gterm.clone(), tb.clone()), tower.clone()))
    {
        return None
    }
    let hyp_g = sub(d.hyp(&dom));
    let h_hyp_g = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            h.clone(),
            Formula::imp(
                Formula::mem(tb.clone(), dom.clone()),
                Formula::mem(r.apply(gterm.clone(), tb.clone()), tower.clone()),
            ),
        )?,
        &Thm::gen(d.bv, &curry(&jb_goal)?),
    )?;
    if *h_hyp_g.concl() != Formula::imp(h.clone(), hyp_g.clone()) {
        return None
    }

    // ── the stage the pullback gets is the stage `g` gets ────────────────────
    let h_ex = syl(&h_hyp_g, &inst_all(dom_bnd, std::slice::from_ref(&gterm))?)?;
    let e1 = sub(d.body(&dom, &tp));
    if *h_ex.concl() != Formula::imp(h.clone(), Formula::exists(pv2, e1.clone())) {
        return None
    }

    let j1 = Formula::and(h.clone(), e1.clone());
    let j1_e1 = and_right(h.clone(), e1.clone());
    let p_om = Formula::mem(tp.clone(), r.omega());
    let cov = sub(d.all_in(&dom, &d.v(tp.clone())));
    let j1_p = syl(&j1_e1, &and_left(p_om.clone(), cov.clone()))?;
    let j1_cov = syl(&j1_e1, &and_right(p_om, cov.clone()))?;

    // ── `η` names the witness, so there is no existential to eliminate ──────
    let stage = d.v(tp.clone());
    let b_in = Formula::mem(tb.clone(), kset.clone());
    let j2 = Formula::and(j1.clone(), b_in.clone());
    let j2_j1 = and_left(j1.clone(), b_in.clone());
    let j2_b = and_right(j1.clone(), b_in.clone());

    let j2_comp = syl(&j2_b, &proj_at)?;
    let j2_cov_c = hyp_mp(
        &syl(&syl(&j2_j1, &j1_cov)?, &Thm::ax_inst(cov.clone(), comp_b.clone())?)?,
        &j2_comp,
    )?;
    let j2_beta = syl(&j2_comp, &beta_c)?;
    let j2_at_pair = hyp_mp(
        &syl(
            &j2_beta,
            &Thm::eq_leibniz(
                r.apply(gterm.clone(), comp_b.clone()),
                r.apply(tg.clone(), pair_c.clone()),
                wv,
                Formula::mem(Term::var(wv), stage.clone()),
            ),
        )?,
        &j2_cov_c,
    )?;
    let j2_goal = hyp_mp(
        &syl(
            &syl(&j2_b, &eta_at)?,
            &Thm::eq_leibniz(
                pair_c.clone(),
                tb.clone(),
                wv,
                Formula::mem(r.apply(tg.clone(), Term::var(wv)), stage.clone()),
            ),
        )?,
        &j2_at_pair,
    )?;
    if *j2_goal.concl()
        != Formula::imp(j2, Formula::mem(r.apply(tg.clone(), tb.clone()), stage.clone()))
    {
        return None
    }

    let j1_cov_k = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j1.clone(),
            Formula::imp(b_in, Formula::mem(r.apply(tg.clone(), tb.clone()), stage)),
        )?,
        &Thm::gen(d.bv, &curry(&j2_goal)?),
    )?;
    if *j1_cov_k.concl() != Formula::imp(j1.clone(), d.all_in(&kset, &d.v(tp.clone()))) {
        return None
    }

    let j1_goal = syl(
        &hyp_and(&j1_p, &j1_cov_k)?,
        &exists_intro_imp(d.pv, d.body(&kset, &Term::var(d.pv)), tp.clone())?,
    )?;
    let h_goal = discharge(pv2, &h_ex, &j1_goal)?;
    let out = Thm::gen(d.gv, &h_goal);

    let expected = bnd(env, r, st, &kset);
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}
