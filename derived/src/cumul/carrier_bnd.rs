//! **`⊢ bnd(ind(p⃗))`** — a declaration with **no recursive arguments** has a
//! bounded carrier.
//!
//! # Interface
//!
//! ```text
//! bnd_carrier(env, ic, mach, ind, inversion, tags_bnd) -> Option<Thm>
//!
//! ⊢ bnd(ind(p⃗))        given  ⊢ bnd(A)  and  every constructor's `recs = 0`
//! ```
//!
//! `A` is [`Inductive::tags`], and `⊢ bnd(A)` is
//! [`super::bnd_isum`] over the constructors' tag summands — so the hypothesis
//! reads *"every constructor's field set is bounded"*, one layer down. At a
//! declaration all of whose constructors are **nullary** every summand is `1`
//! and that input is [`super::bnd_unit`] folded, with nothing else to supply.
//!
//! `inversion` must be [`crate::wtype::w_inversion`] over `mach`'s `Wtype`; it
//! is passed rather than rebuilt because **it mints a symbol per call**, which
//! is the same reason [`crate::bound::w_inversion_at`] takes it.
//!
//! # What this is for
//!
//! [`super::DeclUniverse::over_at_general`] needs `⊢ bnd(Aᵢⱼ)` at each fibre
//! summand `Aᵢⱼ = Σ(z::γᵢⱼ)`, and `γᵢⱼ`'s binder types are the interpretations
//! of **Lean types** — for `RTree.node : (Bool → RTree) → RTree`, `⟦Bool⟧`,
//! which is a carrier of exactly this shape. This is the bottom of that chain.
//! It is **not** the whole of it: see "What is still missing" below.
//!
//! # Why this is not an induction
//!
//! The obvious route is [`crate::wtype::w_rect`] at
//! `φ(z) := ⋁ᵢ ∃y⃗. z = cᵢ(y⃗)`, and it is not needed. With no recursive
//! arguments every fibre is empty, so
//! [`crate::wtype::w_inversion`] — which is *already* `w_rect` at "z is a sup",
//! derived once and stated generally — plus
//! [`crate::wtype::empty_funspace`] (`f ∈ fs(∅,T) → f = ∅`) says outright that
//! every element of `W` is `⟨a,∅⟩` with `a ∈ A`. There is no induction
//! hypothesis to use and no per-declaration `φ` to write, which matters
//! because a hand-built disjunction of constructor equations is a
//! **declaration-specific** formula and this file has none.
//!
//! # The construction
//!
//! The same shape as [`super::bnd_tagged_copy`], with `W` in place of the
//! tagged copy: a family `g` on `W` is pulled back to a family on `A` by
//! `x ↦ app(g, ⟨x,∅⟩)`, one [`crate::funcs::lambda_n`] graph, and the stage
//! that bounds the pullback bounds `g`. **One stage, no merge.** The two
//! membership directions are
//!
//! ```text
//! a ∈ A  →  ⟨a,∅⟩ ∈ W                     Wtype::sup_mem, at `f := ∅`
//! w ∈ W  →  ∃a ∈ A. w = ⟨a,∅⟩              w_inversion, then empty_funspace
//! ```
//!
//! and the fibres are shown empty by [`super::decl::fin_elim`] at
//! `φ(x) := x = ∅`: a non-recursive constructor's fibre value is `Sum_0()`,
//! whose defining equation is `Sum_0() = ∅`, and the codomain `T` is the finite
//! union of those values.
//!
//! # This is not the whole chain, and the next link is a different term
//!
//! `over_at_general` consumes `bnd(Σ(z::γ))` — the **fibre telescope's type** —
//! and this file produces `bnd(⟦γ⟧)`. Those are different terms:
//! `Σ z:⟦Bool⟧. 1` is a one-level [`crate::sigma::DSum`] over `⟦Bool⟧`, not
//! `⟦Bool⟧`. [`super::bnd_telescope1`] is the bridge, and it is a fourth
//! instance of the same pullback pattern. At telescope depth `≥ 2` the pattern
//! does **not** extend — see that file's header — so this chain closes a
//! one-binder `γ` and no more.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`] body `co(g,x) = app(g,⟨x,∅⟩)` and its
//! [`crate::funcs::lambda_n`] graph — one Replacement instance — and nothing
//! else. `inversion`, `tags_bnd` and [`Inductive::closed`] are all checked at
//! the terms used here, for the conclusion they must have **and** for an empty
//! hypothesis set.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{beta_conditional_n, lambda_n};
use crate::funspace::discharge;
use crate::inductive::{Inductive, Machine};
use crate::recursion::hyp::{hyp_eq_symm, hyp_eq_trans};
use crate::{
    a1i, and_left, and_right, define_abbrev, eq_symm_imp, exists_intro_imp, hyp_and, hyp_mp,
    inst_all, opair, syl,
};

use super::apparatus::IndChain;
use super::bounded::bnd;
use super::decl::fin_elim;
use super::finite::Bnd;
use super::step::curry;

/// **`⊢ bnd(ind(p⃗))`** at a declaration none of whose constructors takes a
/// recursive argument.
///
/// `tags_bnd` must be `⊢ bnd(A)` at [`Inductive::tags`], unconditional and with
/// an empty hypothesis set. `inversion` must be
/// [`crate::wtype::w_inversion`] over `mach`'s `Wtype`.
///
/// `None` when any constructor has `recs > 0`, when `mach` is not `ind`'s
/// apparatus and `ic`'s signature, or when either input has the wrong shape —
/// all of which is checked rather than assumed.
pub fn bnd_carrier(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    inversion: &Thm,
    tags_bnd: &Thm,
) -> Option<Thm> {
    if !ic.is_over(mach) || !ind.is_over(mach) || !tags_bnd.hyps().is_empty() {
        return None
    }
    if ind.spec.ctors.iter().any(|c| c.recs != 0) {
        return None
    }
    let (r, st) = (&ic.chain.r, &ic.chain.st);
    let s = mach.wt.sums.clone();
    let sets = s.ap.sets.clone();
    let up = sets.up;
    let zero = s.zero();
    if r.zero() != zero || *tags_bnd.concl() != bnd(env, r, st, &ind.tags) {
        return None
    }

    let tags = ind.tags.clone();
    let fam = ind.fibre.fam.clone();
    let wty = ind.wty.clone();

    // ── every fibre is empty ────────────────────────────────────────────────
    //
    // A constructor with no recursive arguments has the fibre value `Sum_0()`,
    // and `sum_ax(0)` is `⊢ Sum_0() = ∅`. `T` is the finite union of the
    // values, so `fin_elim` at `φ(x) := x = ∅` sends every member of `T` to
    // `∅`, and `values_in_target` puts `app(B,a)` there for every `a ∈ A`.
    let values = ind.fibre.values.clone();
    let nil = mach.syms.sum(&[])?;
    let sum0 = inst_all(mach.syms.sum_ax(0)?, &[])?;
    if *sum0.concl() != Formula::eq(nil.clone(), zero.clone()) {
        return None
    }
    let hole = env.fresh_var();
    let phi = Formula::eq(Term::var(hole), zero.clone());
    let cases: Vec<Thm> = values
        .iter()
        .map(|v| if *v == nil { Some(sum0.clone()) } else { None })
        .collect::<Option<_>>()?;
    let bu_elim = super::step::mem_bin_union_elim(env, &sets)?;
    let to_zero = fin_elim(env, &s, &bu_elim, &values, hole, &phi, &cases)?;

    let av = env.fresh_var();
    let ta = Term::var(av);
    let fibre_a = r.apply(fam.clone(), ta.clone());
    let zero_fibre = syl(
        &inst_all(&ind.fibre.values_in_target, std::slice::from_ref(&ta))?,
        &inst_all(&to_zero, std::slice::from_ref(&fibre_a))?,
    )?;
    if *zero_fibre.concl()
        != Formula::imp(
            Formula::mem(ta.clone(), tags.clone()),
            Formula::eq(fibre_a.clone(), zero.clone()),
        )
    {
        return None
    }

    // ── the two membership directions, at this declaration's `W` ────────────
    let closed_args = [tags.clone(), fam.clone(), ind.bound.clone()];
    let sup_at = Thm::mp(&inst_all(&mach.wt.sup_mem, &closed_args)?, &ind.closed)?;
    let inv_at = Thm::mp(&inst_all(inversion, &closed_args)?, &ind.closed)?;

    let empty_prod = crate::wtype::empty_product(env, &s)?;
    let empty_fs = crate::wtype::empty_funspace(env, &s, &empty_prod)?;

    // `a ∈ A → ∅ ∈ fs(app(B,a), W)`, from `∅ ∈ fs(∅,W)` across the fibre
    // equation — the one place the emptiness is spent on the way in.
    let e_in_fs = {
        let base = inst_all(&mach.wt.empty_fun, std::slice::from_ref(&wty))?;
        let w2 = env.fresh_var();
        let carry = Thm::eq_leibniz(
            zero.clone(),
            fibre_a.clone(),
            w2,
            Formula::mem(zero.clone(), s.fs.of(Term::var(w2), wty.clone())),
        );
        hyp_mp(&syl(&hyp_eq_symm(env, &zero_fibre)?, &carry)?, &a1i(&base, Formula::mem(ta.clone(), tags.clone())))?
    };

    // ── the pullback graph `G = λx ∈ A. app(g, ⟨x,∅⟩)` ──────────────────────
    let (g0, x0) = (env.fresh_var(), env.fresh_var());
    let co_body = r.apply(Term::var(g0), opair(up, Term::var(x0), zero.clone()));
    let (co, co_ax) = define_abbrev(env, &[g0, x0], &co_body)?;
    let (lam, lam_ax) = lambda_n(env, &r.ap, co)?;
    let beta = beta_conditional_n(env, &r.ap, co, lam, &lam_ax)?;

    let d = Bnd::new(env, r, st);
    let (pv2, av2, fv, wv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, ta2, tf) = (Term::var(pv2), Term::var(av2), Term::var(fv));
    let tb = Term::var(d.bv);
    let tg = Term::var(d.gv);
    let tower = st.tower_set();

    let gterm = Term::apply(lam, vec![tg.clone(), tags.clone()]);
    let sub = |f: Formula| f.subst(d.gv, &gterm);

    let beta_at = |env: &mut Env, x: &Term| -> Option<Thm> {
        let e1 = inst_all(&beta, &[tg.clone(), tags.clone(), x.clone()])?;
        let e2 = a1i(
            &inst_all(&co_ax, &[tg.clone(), x.clone()])?,
            Formula::mem(x.clone(), tags.clone()),
        );
        hyp_eq_trans(env, &e1, &e2)
    };
    let beta_b = beta_at(env, &tb)?;
    let beta_a = beta_at(env, &ta2)?;

    let h = d.hyp(&wty); // `∀b. (b ∈ W → app(g,b) ∈ T)`

    // ── the pullback inherits the hypothesis ────────────────────────────────
    let sup_b = opair(up, tb.clone(), zero.clone());
    let jb = Formula::and(h.clone(), Formula::mem(tb.clone(), tags.clone()));
    let jb_h = and_left(h.clone(), Formula::mem(tb.clone(), tags.clone()));
    let jb_b = and_right(h.clone(), Formula::mem(tb.clone(), tags.clone()));

    // `b ∈ A → ⟨b,∅⟩ ∈ W`, at `f := ∅`.
    let into_w = {
        let at_b = Thm::ax_inst(sup_at.concl().clone(), tb.clone())?;
        let step = Thm::mp(&at_b, &sup_at)?;
        // `⊢ b ∈ A → ∀f. (f ∈ fs(app(B,b), W) → ⟨b,f⟩ ∈ W)`
        let (_, all_f) = step.concl().as_imp()?;
        let at_e = syl(&step, &Thm::ax_inst(all_f, zero.clone())?)?;
        let e_here = {
            let mut t = e_in_fs.clone();
            t = Thm::gen(av, &t);
            inst_all(&t, std::slice::from_ref(&tb))?
        };
        hyp_mp(&at_e, &e_here)?
    };
    if *into_w.concl()
        != Formula::imp(
            Formula::mem(tb.clone(), tags.clone()),
            Formula::mem(sup_b.clone(), wty.clone()),
        )
    {
        return None
    }

    let jb_gt = hyp_mp(
        &syl(&jb_h, &Thm::ax_inst(h.clone(), sup_b.clone())?)?,
        &syl(&jb_b, &into_w)?,
    )?;

    let jb_eq = syl(
        &jb_b,
        &syl(
            &beta_b,
            &eq_symm_imp(
                env,
                r.apply(gterm.clone(), tb.clone()),
                r.apply(tg.clone(), sup_b.clone()),
            ),
        )?,
    )?;
    let jb_goal = hyp_mp(
        &syl(
            &jb_eq,
            &Thm::eq_leibniz(
                r.apply(tg.clone(), sup_b.clone()),
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
    let hyp_g = sub(d.hyp(&tags));
    let h_hyp_g = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            h.clone(),
            Formula::imp(
                Formula::mem(tb.clone(), tags.clone()),
                Formula::mem(r.apply(gterm.clone(), tb.clone()), tower.clone()),
            ),
        )?,
        &Thm::gen(d.bv, &curry(&jb_goal)?),
    )?;
    if *h_hyp_g.concl() != Formula::imp(h.clone(), hyp_g.clone()) {
        return None
    }

    // ── the stage the pullback gets is the stage `g` gets ────────────────────
    let h_ex = syl(&h_hyp_g, &inst_all(tags_bnd, std::slice::from_ref(&gterm))?)?;
    let e1 = sub(d.body(&tags, &tp));
    if *h_ex.concl() != Formula::imp(h.clone(), Formula::exists(pv2, e1.clone())) {
        return None
    }

    let j1 = Formula::and(h.clone(), e1.clone());
    let j1_e1 = and_right(h.clone(), e1.clone());
    let p_om = Formula::mem(tp.clone(), r.omega());
    let cov = sub(d.all_in(&tags, &d.v(tp.clone())));
    let j1_p = syl(&j1_e1, &and_left(p_om.clone(), cov.clone()))?;
    let j1_cov = syl(&j1_e1, &and_right(p_om, cov.clone()))?;

    // ── every element of `W` is `⟨a,∅⟩`, so the same stage covers it ────────
    let b_in = Formula::mem(tb.clone(), wty.clone());
    let j2 = Formula::and(j1.clone(), b_in.clone());
    let j2_j1 = and_left(j1.clone(), b_in.clone());
    let j2_b = and_right(j1.clone(), b_in.clone());
    let j2_ex = syl(&j2_b, &Thm::mp(&Thm::ax_inst(inv_at.concl().clone(), tb.clone())?, &inv_at)?)?;
    let (_, inner_a) = j2_ex.concl().as_imp()?;
    // `∃a. (a ∈ A ∧ ∃f. (f ∈ fs(app(B,a),W) ∧ b = ⟨a,f⟩))` — rebuilt and pinned.
    let fibre_a2 = r.apply(fam.clone(), ta2.clone());
    let inner_f = Formula::exists(
        fv,
        Formula::and(
            Formula::mem(tf.clone(), s.fs.of(fibre_a2.clone(), wty.clone())),
            Formula::eq(tb.clone(), opair(up, ta2.clone(), tf.clone())),
        ),
    );
    let w_a = Formula::and(Formula::mem(ta2.clone(), tags.clone()), inner_f.clone());
    if inner_a != Formula::exists(av2, w_a.clone()) {
        return None
    }

    let j3 = Formula::and(j2.clone(), w_a.clone());
    let j3_j2 = and_left(j2.clone(), w_a.clone());
    let j3_w = and_right(j2.clone(), w_a.clone());
    let j3_a = syl(&j3_w, &and_left(Formula::mem(ta2.clone(), tags.clone()), inner_f.clone()))?;
    let j3_exf = syl(&j3_w, &and_right(Formula::mem(ta2.clone(), tags.clone()), inner_f.clone()))?;

    let w_f = Formula::and(
        Formula::mem(tf.clone(), s.fs.of(fibre_a2.clone(), wty.clone())),
        Formula::eq(tb.clone(), opair(up, ta2.clone(), tf.clone())),
    );
    let j4 = Formula::and(j3.clone(), w_f.clone());
    let j4_j3 = and_left(j3.clone(), w_f.clone());
    let j4_w = and_right(j3.clone(), w_f.clone());
    let j4_f = syl(
        &j4_w,
        &and_left(
            Formula::mem(tf.clone(), s.fs.of(fibre_a2.clone(), wty.clone())),
            Formula::eq(tb.clone(), opair(up, ta2.clone(), tf.clone())),
        ),
    )?;
    let j4_eq = syl(
        &j4_w,
        &and_right(
            Formula::mem(tf.clone(), s.fs.of(fibre_a2.clone(), wty.clone())),
            Formula::eq(tb.clone(), opair(up, ta2.clone(), tf.clone())),
        ),
    )?;

    // `f = ∅`, through the empty fibre.
    let j4_a = syl(&j4_j3, &j3_a)?;
    let j4_fibre = syl(&j4_a, &{
        let t = Thm::gen(av, &zero_fibre);
        inst_all(&t, std::slice::from_ref(&ta2))?
    })?;
    let w3 = env.fresh_var();
    let j4_f_empty_dom = hyp_mp(
        &syl(
            &j4_fibre,
            &Thm::eq_leibniz(
                fibre_a2.clone(),
                zero.clone(),
                w3,
                Formula::mem(tf.clone(), s.fs.of(Term::var(w3), wty.clone())),
            ),
        )?,
        &j4_f,
    )?;
    let j4_f_zero = hyp_mp(
        &a1i(&inst_all(&empty_fs, &[wty.clone(), tf.clone()])?, j4.clone()),
        &j4_f_empty_dom,
    )?;
    // `b = ⟨a,f⟩` with `f = ∅` gives `b = ⟨a,∅⟩`.
    let sup_a = opair(up, ta2.clone(), zero.clone());
    let w4 = env.fresh_var();
    let j4_b_eq = hyp_mp(
        &syl(
            &j4_f_zero,
            &Thm::eq_leibniz(
                tf.clone(),
                zero.clone(),
                w4,
                Formula::eq(tb.clone(), opair(up, ta2.clone(), Term::var(w4))),
            ),
        )?,
        &j4_eq,
    )?;

    // `app(G,a) ∈ Vₚ`, the β step, then `b = ⟨a,∅⟩` backwards.
    let stage = d.v(tp.clone());
    let j4_cov_a = hyp_mp(
        &syl(
            &syl(&j4_j3, &syl(&j3_j2, &syl(&j2_j1, &j1_cov)?)?)?,
            &Thm::ax_inst(cov.clone(), ta2.clone())?,
        )?,
        &j4_a,
    )?;
    let j4_beta = syl(&j4_a, &beta_a)?;
    let j4_at_sup = hyp_mp(
        &syl(
            &j4_beta,
            &Thm::eq_leibniz(
                r.apply(gterm.clone(), ta2.clone()),
                r.apply(tg.clone(), sup_a.clone()),
                wv,
                Formula::mem(Term::var(wv), stage.clone()),
            ),
        )?,
        &j4_cov_a,
    )?;
    let j4_goal = hyp_mp(
        &syl(
            &hyp_eq_symm(env, &j4_b_eq)?,
            &Thm::eq_leibniz(
                sup_a.clone(),
                tb.clone(),
                wv,
                Formula::mem(r.apply(tg.clone(), Term::var(wv)), stage.clone()),
            ),
        )?,
        &j4_at_sup,
    )?;
    if *j4_goal.concl()
        != Formula::imp(j4, Formula::mem(r.apply(tg.clone(), tb.clone()), stage.clone()))
    {
        return None
    }

    let j3_goal = discharge(fv, &j3_exf, &j4_goal)?;
    let j2_goal = discharge(av2, &j2_ex, &j3_goal)?;
    let j1_cov_w = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j1.clone(),
            Formula::imp(b_in, Formula::mem(r.apply(tg.clone(), tb.clone()), stage)),
        )?,
        &Thm::gen(d.bv, &curry(&j2_goal)?),
    )?;
    if *j1_cov_w.concl() != Formula::imp(j1.clone(), d.all_in(&wty, &d.v(tp.clone()))) {
        return None
    }

    let j1_goal = syl(
        &hyp_and(&j1_p, &j1_cov_w)?,
        &exists_intro_imp(d.pv, d.body(&wty, &Term::var(d.pv)), tp.clone())?,
    )?;
    let h_goal = discharge(pv2, &h_ex, &j1_goal)?;
    let on_wty = Thm::gen(d.gv, &h_goal);
    if !on_wty.hyps().is_empty() || *on_wty.concl() != bnd(env, r, st, &wty) {
        return None
    }

    // ── and onto the abbreviation `ind(p⃗)` ──────────────────────────────────
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let to_ty = crate::eq_symm(env, &inst_all(&ind.ty_ax, &ps)?)?;
    if *to_ty.concl() != Formula::eq(wty.clone(), ind.carrier.clone()) {
        return None
    }
    let hole2 = env.fresh_var();
    let out = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(wty, ind.carrier.clone(), hole2, bnd(env, r, st, &Term::var(hole2))),
            &to_ty,
        )?,
        &on_wty,
    )?;
    let expected = bnd(env, r, st, &ind.carrier);
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}

/// **`⊢ bnd(A)`** at a declaration all of whose constructors are **nullary** —
/// the input [`bnd_carrier`] wants, with nothing left for a caller to supply.
///
/// A nullary constructor's tag summand is `1`, which its telescope's `base_ax`
/// says on the nose ([`super::nullary_summand_at`] reads the same equation for
/// the universe side), so every summand's `bnd` is [`super::bnd_unit`] carried
/// across one equation and [`super::bnd_isum`] folds them.
///
/// `None` when any constructor takes an argument or a recursive argument — a
/// constructor with **fields** has `Aᵢ = Σy⃗:β⃗. 1` and its `bnd` is not this
/// file's; see the module header for what that bridge is and is not.
pub fn bnd_nullary_tags(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
) -> Option<Thm> {
    if !ic.is_over(mach) || !ind.is_over(mach) {
        return None
    }
    if ind.spec.ctors.iter().any(|c| !c.args.is_empty() || c.recs != 0) {
        return None
    }
    let (r, st) = (&ic.chain.r, &ic.chain.st);
    let s = mach.wt.sums.clone();
    let unit_bnd = super::sum_bnd::bnd_unit(env, r, st, &s)?;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();

    let mut bnds = Vec::with_capacity(ind.summands.len());
    for i in 0..ind.summands.len() {
        let base_at = inst_all(&ind.telescopes[i].base_ax, &ps)?;
        let summand = ind.summands[i].clone();
        if *base_at.concl() != Formula::eq(summand.clone(), s.unit()) {
            return None
        }
        let hole = env.fresh_var();
        let at = Thm::mp(
            &Thm::mp(
                &Thm::eq_leibniz(
                    s.unit(),
                    summand.clone(),
                    hole,
                    bnd(env, r, st, &Term::var(hole)),
                ),
                &crate::eq_symm(env, &base_at)?,
            )?,
            &unit_bnd,
        )?;
        bnds.push(at);
    }
    let out = super::sum_bnd::bnd_isum(
        env,
        r,
        st,
        &s,
        &mach.syms,
        &ic.bnd_sum,
        &ind.summands,
        &bnds,
    )?;
    (out.hyps().is_empty() && *out.concl() == bnd(env, r, st, &ind.tags)).then_some(out)
}
