//! **`⊢ bnd(D) → bnd(K)`** — the one derivation behind every `bnd` result in
//! this directory that moves a bound along a **term-former**.
//!
//! # Interface
//!
//! ```text
//! bnd_via_pullback(env, r, st, params, dom, big, mk, intro, inversion) -> Option<Thm>
//!
//! ⊢ bnd(D) → bnd(K)
//!     given   mk         a term-former `x ↦ mk(x)`, as a Rust closure
//!             intro      ⊢ ∀y. (y ∈ D → mk(y) ∈ K)
//!             inversion  ⊢ ∀b. (b ∈ K → ∃y. (y ∈ D ∧ b = mk(y)))
//! ```
//!
//! `params` are the free variables `mk` mentions besides its argument; they
//! become parameters of the abbreviation below, so a caller may quantify over
//! them afterwards. Everything else `mk` mentions must be closed.
//!
//! # The argument
//!
//! A family `g` on `K` is **pulled back** to a family on `D` by `x ↦ g(mk(x))`,
//! which is one [`crate::funcs::lambda_n`] graph over one
//! [`crate::define_abbrev`] body. `bnd(D)` hands that pullback a single stage
//! `Vₚ`, and `inversion` says every member of `K` **is** some `mk(y)` with
//! `y ∈ D`, so the same `Vₚ` bounds `g` itself. **One stage, no merge** — the
//! pullback and the original take the same values, so
//! [`super::Stages::directed`] is not needed and the conclusion is not a union.
//!
//! # Why a term-former and not a function
//!
//! [`mod@super::finite`]'s header declines transport along a **surjection**, and
//! correctly: `bnd(D)` speaks of `app(g,·)`, so moving it along an `h ∈ fs(D,K)`
//! needs the composite `g ∘ h` **as a set**, i.e. a Replacement instance per
//! call. A *term*-former composes for free — `λx. app(g, mk(x))` is one graph
//! and [`crate::funcs::beta_conditional_n`] computes it on the domain. That
//! asymmetry is the whole reason the three instances below are cheap.
//!
//! # The three instances, and what each brings
//!
//! | caller | `mk(x)` | `params` | `inversion` |
//! |---|---|---|---|
//! | [`super::bnd_tagged_copy`] | `⟨t,x⟩` | `t` | [`crate::sums::tagged_copy_members`], forwards |
//! | [`super::bnd_carrier`] | `⟨x,∅⟩` | — | [`crate::wtype::w_inversion`] with the fibre shown empty |
//! | [`super::bnd_telescope1`] | `⟨x,•⟩` | — | [`Telescope::eta`](crate::sigma::Telescope) at the witness `π₁ b` |
//!
//! The `params` column is why `mk` is a closure over caller terms rather than a
//! pair of symbols: the tagged copy is proved `∀t`, and `t` therefore has to be
//! a parameter of the abbreviation *and* an argument of the graph, while the
//! other two have no such variable.
//!
//! # Why `⊢ bnd(D) → bnd(K)` and not `⊢ bnd(K)` from a `⊢ bnd(D)`
//!
//! Two of the three callers hold a proved `⊢ bnd(D)` and would rather hand it
//! over; the third proves `∀t ∀a. (bnd(a) → bnd({t}×a))` and **cannot**, since
//! its `a` is a variable it generalises afterwards. The implication form serves
//! both — `Thm::mp` recovers the first, `Thm::gen` the second — and the
//! derivation is the same either way, because `bnd(D)` is used exactly once, at
//! the pullback.
//!
//! # Depth is where this stops
//!
//! The argument needs the *whole* of `K` to be `mk`'s image over `D`. At a
//! telescope of depth `≥ 2` the second component varies with the first, so a
//! family on `K` restricts to one family per `y₀` and the stages have to be
//! merged over `β₀`-many indices — a Replacement-indexed union, which
//! [`super::Stages::directed`] does not do. See
//! [`mod@super::telescope_bnd`]'s header.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`] body `co(g,p⃗,x) = app(g,mk(x))` and its
//! [`crate::funcs::lambda_n`] graph — one Replacement instance per call — and
//! nothing else. Both caller-supplied theorems are checked against the formula
//! this file rebuilds **and** for an empty hypothesis set, and the result is
//! checked against `bnd(D) → bnd(K)` before it is returned.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funcs::{beta_conditional_n, lambda_n};
use crate::funspace::discharge;
use crate::recursion::hyp::{hyp_eq_symm, hyp_eq_trans};
use crate::recursion::Rec;
use crate::{
    a1i, and_left, and_right, define_abbrev, eq_symm_imp, exists_intro_imp, hyp_and, hyp_mp,
    inst_all, syl,
};

use super::finite::Bnd;
use super::stages::Stages;
use super::step::curry;

/// The formula `intro` must conclude: `∀y. (y ∈ dom → mk(y) ∈ big)`.
pub(super) fn intro_shape(
    env: &mut Env,
    dom: &Term,
    big: &Term,
    mk: &dyn Fn(&Term) -> Term,
) -> Formula {
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    Formula::forall(
        yv,
        Formula::imp(Formula::mem(ty.clone(), dom.clone()), Formula::mem(mk(&ty), big.clone())),
    )
}

/// The formula `inversion` must conclude:
/// `∀b. (b ∈ big → ∃y. (y ∈ dom ∧ b = mk(y)))`.
pub(super) fn inversion_shape(
    env: &mut Env,
    dom: &Term,
    big: &Term,
    mk: &dyn Fn(&Term) -> Term,
) -> Formula {
    let (bv, yv) = (env.fresh_var(), env.fresh_var());
    let (tb, ty) = (Term::var(bv), Term::var(yv));
    Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tb.clone(), big.clone()),
            Formula::exists(
                yv,
                Formula::and(
                    Formula::mem(ty.clone(), dom.clone()),
                    Formula::eq(tb.clone(), mk(&ty)),
                ),
            ),
        ),
    )
}

/// **`⊢ bnd(dom) → bnd(big)`** — see the module header.
///
/// `None` when either input has the wrong conclusion or a non-empty hypothesis
/// set, when the abbreviation cannot be minted (`params` must cover every free
/// variable of `mk(x)` other than `x` itself), or when any intermediate step
/// fails its own pin.
#[allow(clippy::too_many_arguments)]
pub(super) fn bnd_via_pullback(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    params: &[FreeVar],
    dom: &Term,
    big: &Term,
    mk: &dyn Fn(&Term) -> Term,
    intro: &Thm,
    inversion: &Thm,
) -> Option<Thm> {
    // ── the two inputs, against what this file rebuilds ─────────────────────
    if !intro.hyps().is_empty() || *intro.concl() != intro_shape(env, dom, big, mk) {
        return None
    }
    if !inversion.hyps().is_empty() || *inversion.concl() != inversion_shape(env, dom, big, mk) {
        return None
    }

    // ── the pullback's graph: `co(g,p⃗,x) = app(g,mk(x))`, and `λx. co(g,p⃗,x)` ─
    let (g0, x0) = (env.fresh_var(), env.fresh_var());
    let co_body = r.apply(Term::var(g0), mk(&Term::var(x0)));
    let mut abbrev = Vec::with_capacity(params.len() + 2);
    abbrev.push(g0);
    abbrev.extend_from_slice(params);
    abbrev.push(x0);
    let (co, co_ax) = define_abbrev(env, &abbrev, &co_body)?;
    let (lam, lam_ax) = lambda_n(env, &r.ap, co)?;
    let beta = beta_conditional_n(env, &r.ap, co, lam, &lam_ax)?;

    let d = Bnd::new(env, r, st);
    let (pv2, yv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, ty) = (Term::var(pv2), Term::var(yv));
    let tb = Term::var(d.bv);
    let tg = Term::var(d.gv);
    let tower = st.tower_set();

    let pts: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    let gterm = {
        let mut args = Vec::with_capacity(params.len() + 2);
        args.push(tg.clone());
        args.extend(pts.iter().cloned());
        args.push(dom.clone());
        Term::apply(lam, args)
    };
    let sub = |f: Formula| f.subst(d.gv, &gterm);

    // `⊢ x ∈ D → app(G,x) = app(g,mk(x))` — **the β step**, at the two points
    // this derivation reduces the pullback at: the bound variable of the
    // hypothesis, and the witness the inversion hands back.
    let beta_at = |env: &mut Env, x: &Term| -> Option<Thm> {
        let mut a1 = Vec::with_capacity(params.len() + 3);
        a1.push(tg.clone());
        a1.extend(pts.iter().cloned());
        a1.push(dom.clone());
        a1.push(x.clone());
        let e1 = inst_all(&beta, &a1)?;
        let mut a2 = Vec::with_capacity(params.len() + 2);
        a2.push(tg.clone());
        a2.extend(pts.iter().cloned());
        a2.push(x.clone());
        let e2 = a1i(&inst_all(&co_ax, &a2)?, Formula::mem(x.clone(), dom.clone()));
        hyp_eq_trans(env, &e1, &e2)
    };
    let beta_b = beta_at(env, &tb)?;
    let beta_y = beta_at(env, &ty)?;

    let intro_b = inst_all(intro, std::slice::from_ref(&tb))?;
    let inv_b = inst_all(inversion, std::slice::from_ref(&tb))?;

    let k = d.all(env, dom); // `bnd(D)`
    let h = d.hyp(big); // `∀b. (b ∈ K → app(g,b) ∈ T)`
    let j0 = Formula::and(k.clone(), h.clone());
    let j0_k = and_left(k.clone(), h.clone());
    let j0_h = and_right(k.clone(), h.clone());

    // ── the pullback inherits the hypothesis ────────────────────────────────
    //
    // `J0 ∧ b ∈ D ⊢ app(G,b) ∈ T`, from `mk(b) ∈ K` and one β step.
    let mk_b = mk(&tb);
    let jb = Formula::and(j0.clone(), Formula::mem(tb.clone(), dom.clone()));
    let jb_j0 = and_left(j0.clone(), Formula::mem(tb.clone(), dom.clone()));
    let jb_b = and_right(j0.clone(), Formula::mem(tb.clone(), dom.clone()));

    let jb_gt = hyp_mp(
        &syl(&syl(&jb_j0, &j0_h)?, &Thm::ax_inst(h.clone(), mk_b.clone())?)?,
        &syl(&jb_b, &intro_b)?,
    )?;
    // `app(g,mk(b)) = app(G,b)` — the β step, run backwards.
    let jb_eq = syl(
        &jb_b,
        &syl(
            &beta_b,
            &eq_symm_imp(
                env,
                r.apply(gterm.clone(), tb.clone()),
                r.apply(tg.clone(), mk_b.clone()),
            ),
        )?,
    )?;
    let jb_goal = hyp_mp(
        &syl(
            &jb_eq,
            &Thm::eq_leibniz(
                r.apply(tg.clone(), mk_b.clone()),
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
    let hyp_g = sub(d.hyp(dom));
    let j0_hyp_g = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j0.clone(),
            Formula::imp(
                Formula::mem(tb.clone(), dom.clone()),
                Formula::mem(r.apply(gterm.clone(), tb.clone()), tower.clone()),
            ),
        )?,
        &Thm::gen(d.bv, &curry(&jb_goal)?),
    )?;
    if *j0_hyp_g.concl() != Formula::imp(j0.clone(), hyp_g.clone()) {
        return None
    }

    // ── the stage the pullback gets is the stage `g` gets ────────────────────
    let j0_ex = hyp_mp(&syl(&j0_k, &Thm::ax_inst(k.clone(), gterm.clone())?)?, &j0_hyp_g)?;
    let e1 = sub(d.body(dom, &tp));
    if *j0_ex.concl() != Formula::imp(j0.clone(), Formula::exists(pv2, e1.clone())) {
        return None
    }

    let j1 = Formula::and(j0.clone(), e1.clone());
    let j1_e1 = and_right(j0.clone(), e1.clone());
    let p_om = Formula::mem(tp.clone(), r.omega());
    let cov = sub(d.all_in(dom, &d.v(tp.clone())));
    let j1_p = syl(&j1_e1, &and_left(p_om.clone(), cov.clone()))?;
    let j1_cov = syl(&j1_e1, &and_right(p_om, cov.clone()))?;

    // ── every member of `K` is an `mk(y)`, so the same stage covers it ───────
    let b_in = Formula::mem(tb.clone(), big.clone());
    let j2 = Formula::and(j1.clone(), b_in.clone());
    let j2_j1 = and_left(j1.clone(), b_in.clone());
    let j2_b = and_right(j1.clone(), b_in.clone());
    let mk_y = mk(&ty);
    let w = Formula::and(
        Formula::mem(ty.clone(), dom.clone()),
        Formula::eq(tb.clone(), mk_y.clone()),
    );
    let j2_ex = syl(&j2_b, &inv_b)?;
    if *j2_ex.concl() != Formula::imp(j2.clone(), Formula::exists(yv, w.clone())) {
        return None
    }

    let j3 = Formula::and(j2.clone(), w.clone());
    let j3_j2 = and_left(j2.clone(), w.clone());
    let j3_w = and_right(j2.clone(), w.clone());
    let j3_y = syl(
        &j3_w,
        &and_left(
            Formula::mem(ty.clone(), dom.clone()),
            Formula::eq(tb.clone(), mk_y.clone()),
        ),
    )?;
    let j3_eq = syl(
        &j3_w,
        &and_right(
            Formula::mem(ty.clone(), dom.clone()),
            Formula::eq(tb.clone(), mk_y.clone()),
        ),
    )?;

    let stage = d.v(tp.clone());
    // `app(G,y) ∈ Vₚ`, then the β step forwards, then `b = mk(y)` backwards.
    let j3_cov_y = hyp_mp(
        &syl(
            &syl(&j3_j2, &syl(&j2_j1, &j1_cov)?)?,
            &Thm::ax_inst(cov.clone(), ty.clone())?,
        )?,
        &j3_y,
    )?;
    let j3_beta = syl(&j3_y, &beta_y)?;
    let j3_at_mk = hyp_mp(
        &syl(
            &j3_beta,
            &Thm::eq_leibniz(
                r.apply(gterm.clone(), ty.clone()),
                r.apply(tg.clone(), mk_y.clone()),
                wv,
                Formula::mem(Term::var(wv), stage.clone()),
            ),
        )?,
        &j3_cov_y,
    )?;
    let j3_goal = hyp_mp(
        &syl(
            &hyp_eq_symm(env, &j3_eq)?,
            &Thm::eq_leibniz(
                mk_y.clone(),
                tb.clone(),
                wv,
                Formula::mem(r.apply(tg.clone(), Term::var(wv)), stage.clone()),
            ),
        )?,
        &j3_at_mk,
    )?;
    if *j3_goal.concl()
        != Formula::imp(j3, Formula::mem(r.apply(tg.clone(), tb.clone()), stage.clone()))
    {
        return None
    }
    let j2_goal = discharge(yv, &j2_ex, &j3_goal)?;
    let j1_cov_big = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j1.clone(),
            Formula::imp(b_in, Formula::mem(r.apply(tg.clone(), tb.clone()), stage)),
        )?,
        &Thm::gen(d.bv, &curry(&j2_goal)?),
    )?;
    if *j1_cov_big.concl() != Formula::imp(j1.clone(), d.all_in(big, &d.v(tp.clone()))) {
        return None
    }

    let j1_goal = syl(
        &hyp_and(&j1_p, &j1_cov_big)?,
        &exists_intro_imp(d.pv, d.body(big, &Term::var(d.pv)), tp.clone())?,
    )?;
    let j0_goal = discharge(pv2, &j0_ex, &j1_goal)?;

    let out = Thm::mp(
        &Thm::ax_dist(d.gv, k.clone(), Formula::imp(h.clone(), d.ex(big)))?,
        &Thm::gen(d.gv, &curry(&j0_goal)?),
    )?;

    let expected = Formula::imp(k, d.all(env, big));
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}
