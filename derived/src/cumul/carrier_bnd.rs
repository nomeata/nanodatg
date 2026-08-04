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
//! [`super::pullback::bnd_via_pullback`] at `mk(x) = ⟨x,∅⟩`, with `W` as the
//! big set and `A` as the small one. What this file owes it is the two
//! membership directions:
//!
//! ```text
//! a ∈ A  →  ⟨a,∅⟩ ∈ W                     Wtype::sup_mem, at `f := ∅`
//! w ∈ W  →  ∃a. (a ∈ A ∧ w = ⟨a,∅⟩)       w_inversion, then empty_funspace
//! ```
//!
//! and the fibres are shown empty by [`super::decl::fin_elim`] at
//! `φ(x) := x = ∅`: a non-recursive constructor's fibre value is `Sum_0()`,
//! whose defining equation is `Sum_0() = ∅`, and the codomain `T` is the finite
//! union of those values.
//!
//! **The emptiness is spent entirely on the second line.** `w_inversion` hands
//! back a *two*-level existential, `∃a ∃f`, and the shared derivation consumes
//! one level; flattening `∃f` away — the fibre is `∅`, so
//! [`crate::wtype::empty_funspace`] names the witness `∅` — is the whole of
//! what distinguishes this instance from the other two, and it is the whole of
//! why `recs = 0` is a hypothesis rather than a convenience.
//!
//! # This is not the whole chain, and the next link is a different term
//!
//! `over_at_general` consumes `bnd(Σ(z::γ))` — the **fibre telescope's type** —
//! and this file produces `bnd(⟦γ⟧)`. Those are different terms:
//! `Σ z:⟦Bool⟧. 1` is a one-level [`crate::sigma::DSum`] over `⟦Bool⟧`, not
//! `⟦Bool⟧`. [`super::bnd_telescope1`] is the bridge, and it is the third
//! instance of the same pullback. At telescope depth `≥ 2` the pattern does
//! **not** extend — see that file's header — so this chain closes a one-binder
//! `γ` and no more.
//!
//! # Nothing here is an axiom
//!
//! One [`crate::define_abbrev`] body `co(g,x) = app(g,⟨x,∅⟩)` and its
//! [`crate::funcs::lambda_n`] graph — one Replacement instance, minted by
//! [`mod@super::pullback`] and by nothing here — and nothing else.
//! `inversion`, `tags_bnd` and [`Inductive::closed`] are all checked at the
//! terms used here, for the conclusion they must have **and** for an empty
//! hypothesis set.

use kernel::{Env, Formula, Term, Thm};

use crate::funspace::discharge;
use crate::inductive::{Inductive, Machine};
use crate::recursion::hyp::hyp_eq_symm;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, hyp_and, hyp_mp, inst_all, opair, syl,
};

use super::apparatus::IndChain;
use super::bounded::bnd;
use super::decl::fin_elim;
use super::pullback::bnd_via_pullback;

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

    let zero_fibre_all = Thm::gen(av, &zero_fibre);
    let e_in_fs_all = Thm::gen(av, &e_in_fs);
    let mk = |x: &Term| opair(up, x.clone(), zero.clone());

    let (zv, av2, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tz, ta2, tf) = (Term::var(zv), Term::var(av2), Term::var(fv));

    // ── `⊢ ∀z. (z ∈ A → ⟨z,∅⟩ ∈ W)` — `sup_mem` at `f := ∅` ─────────────────
    let intro = {
        let at_z = Thm::mp(&Thm::ax_inst(sup_at.concl().clone(), tz.clone())?, &sup_at)?;
        // `⊢ z ∈ A → ∀f. (f ∈ fs(app(B,z), W) → ⟨z,f⟩ ∈ W)`
        let (_, all_f) = at_z.concl().as_imp()?;
        let at_e = syl(&at_z, &Thm::ax_inst(all_f, zero.clone())?)?;
        let step = hyp_mp(&at_e, &inst_all(&e_in_fs_all, std::slice::from_ref(&tz))?)?;
        if *step.concl()
            != Formula::imp(
                Formula::mem(tz.clone(), tags.clone()),
                Formula::mem(mk(&tz), wty.clone()),
            )
        {
            return None
        }
        Thm::gen(zv, &step)
    };

    // ── `⊢ ∀z. (z ∈ W → ∃a. (a ∈ A ∧ z = ⟨a,∅⟩))` ───────────────────────────
    //
    // `w_inversion` gives a **two**-level existential — `∃a ∃f` — and the whole
    // of this declaration's emptiness is spent flattening it to the one level
    // the pullback consumes: the fibre is `∅`, so `empty_funspace` makes the
    // inner witness `∅` and the outer one is the tag.
    let flat = {
        let inv_z = Thm::mp(&Thm::ax_inst(inv_at.concl().clone(), tz.clone())?, &inv_at)?;
        let (_, inner_a) = inv_z.concl().as_imp()?;
        let fibre_a2 = r.apply(fam.clone(), ta2.clone());
        let fs_a2 = s.fs.of(fibre_a2.clone(), wty.clone());
        let f_mem = Formula::mem(tf.clone(), fs_a2.clone());
        let f_eq = Formula::eq(tz.clone(), opair(up, ta2.clone(), tf.clone()));
        let w_f = Formula::and(f_mem.clone(), f_eq.clone());
        let inner_f = Formula::exists(fv, w_f.clone());
        let a_mem = Formula::mem(ta2.clone(), tags.clone());
        let w_a = Formula::and(a_mem.clone(), inner_f.clone());
        // `∃a. (a ∈ A ∧ ∃f. (f ∈ fs(app(B,a),W) ∧ z = ⟨a,f⟩))` — rebuilt, pinned.
        if inner_a != Formula::exists(av2, w_a.clone()) {
            return None
        }

        let z_in = Formula::mem(tz.clone(), wty.clone());
        let j2 = Formula::and(z_in.clone(), w_a.clone());
        let j2_w = and_right(z_in.clone(), w_a.clone());
        let j2_a = syl(&j2_w, &and_left(a_mem.clone(), inner_f.clone()))?;
        let j2_exf = syl(&j2_w, &and_right(a_mem, inner_f))?;

        let j3 = Formula::and(j2.clone(), w_f.clone());
        let j3_j2 = and_left(j2.clone(), w_f.clone());
        let j3_w = and_right(j2, w_f);
        let j3_f = syl(&j3_w, &and_left(f_mem.clone(), f_eq.clone()))?;
        let j3_eq = syl(&j3_w, &and_right(f_mem, f_eq))?;
        let j3_a = syl(&j3_j2, &j2_a)?;

        // `f = ∅`, through the empty fibre.
        let j3_fibre = syl(&j3_a, &inst_all(&zero_fibre_all, std::slice::from_ref(&ta2))?)?;
        let w3 = env.fresh_var();
        let j3_empty_dom = hyp_mp(
            &syl(
                &j3_fibre,
                &Thm::eq_leibniz(
                    fibre_a2.clone(),
                    zero.clone(),
                    w3,
                    Formula::mem(tf.clone(), s.fs.of(Term::var(w3), wty.clone())),
                ),
            )?,
            &j3_f,
        )?;
        let j3_f_zero = hyp_mp(
            &a1i(&inst_all(&empty_fs, &[wty.clone(), tf.clone()])?, j3.clone()),
            &j3_empty_dom,
        )?;
        // `z = ⟨a,f⟩` with `f = ∅` gives `z = ⟨a,∅⟩`.
        let w4 = env.fresh_var();
        let j3_z_eq = hyp_mp(
            &syl(
                &j3_f_zero,
                &Thm::eq_leibniz(
                    tf.clone(),
                    zero.clone(),
                    w4,
                    Formula::eq(tz.clone(), opair(up, ta2.clone(), Term::var(w4))),
                ),
            )?,
            &j3_eq,
        )?;

        let goal = Formula::and(
            Formula::mem(ta2.clone(), tags.clone()),
            Formula::eq(tz.clone(), mk(&ta2)),
        );
        let j3_goal = syl(
            &hyp_and(&j3_a, &j3_z_eq)?,
            &exists_intro_imp(av2, goal, ta2.clone())?,
        )?;
        let j2_goal = discharge(fv, &j2_exf, &j3_goal)?;
        Thm::gen(zv, &discharge(av2, &inv_z, &j2_goal)?)
    };

    let core = bnd_via_pullback(env, r, st, &[], &tags, &wty, &mk, &intro, &flat)?;
    let on_wty = Thm::mp(&core, tags_bnd)?;
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
