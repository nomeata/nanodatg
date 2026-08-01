//! **`⊢ [H →] Aᵢ ∈ U₁` for a constructor with one non-recursive argument** —
//! the `Σ`-telescope of `cons : α → List α → List α`, and of every other
//! single-argument constructor, inside the first universe.
//!
//! # Interface
//!
//! Writing `Aᵢ = Σy : β₀(p⃗). 1` for the `i`-th tag summand,
//! `img(p⃗) = {C₁(p⃗,x) : x ∈ β₀(p⃗)}` for the Replacement image
//! [`crate::sigma::dsum`](fn@crate::sigma::dsum) builds it over, and `U₁` for `U(ω)`:
//!
//! ```text
//! ⊢ img(p⃗) ⊆ {1}                                       [unary_image_is_a_point]
//! ⊢ [H →] Σy : β₀(p⃗). 1 ∈ U₁     given ⊢ [H →] β₀(p⃗) ∈ U₁   [unary_summand_in_u1]
//! ```
//!
//! `H` is the optional antecedent [`super::tags`] and [`super::decl`] carry —
//! for `List α` it is `α ∈ U₁`, and it is genuinely needed: a `List` over a
//! parameter that is not itself small is no member of `U₁`.
//!
//! # Why one argument and not `k`, stated precisely
//!
//! [`crate::sigma::dsum`](fn@crate::sigma::dsum) defines `Σ(p⃗)` by Separation inside
//! `β₀(p⃗) × ⋃img(p⃗)`, so
//!
//! ```text
//! Σ(p⃗) ∈ U₁   ⇐   β₀(p⃗) ∈ U₁   and   img(p⃗) ∈ U₁
//! ```
//!
//! by `U₁`'s product and union closures and `C₂`. That reduction is **general
//! at every `k`** and is what [`unary_summand_in_u1`] performs. What is *not*
//! general is the second input. `img(p⃗)` is a Replacement image, and a
//! universe's closure under Replacement — derivable from `ax_tarski`'s
//! inaccessibility clause `C₄` — is **not derived anywhere in this crate**.
//!
//! At `k = 1` it is not needed, and the reason is structural rather than
//! lucky: the fibre of the outermost `Σ` is the telescope's innermost level,
//! [`crate::sigma::Telescope`]'s `base_ax` says that level is the constant `1`,
//! so `img(p⃗)` is a set every member of which is `1` — a subset of `{1}`, and
//! `C₂` finishes without a Replacement instance
//! ([`unary_image_is_a_point`]). At `k ≥ 2` the fibre is another `Σ` that
//! genuinely varies with `y₀`, the image is genuinely a Replacement image, and
//! the missing lemma is the whole of what is missing. This file therefore
//! **extends** to `k ≥ 2` by supplying `img(p⃗) ∈ U₁` — the reduction above does
//! not change — rather than being replaced by a different argument.
//!
//! # Nothing here is an axiom
//!
//! No symbol is introduced: [`crate::sigma::dsum`](fn@crate::sigma::dsum)'s `img` and `Σ` already
//! exist and this file only reads their characteristic theorems. The
//! caller-supplied argument membership is checked for its conclusion **and**
//! for an empty hypothesis set.

use kernel::{Env, Formula, Term, Thm};

use crate::inductive::Inductive;
use crate::sigma::DSum;
use crate::{
    and_right, exists_elim_imp, iff_mp, iff_mpr, inst_all, singleton, syl,
};

use super::apparatus::IndChain;
use super::opt::Ctx;

/// The `i`-th constructor's outermost `Σ`, with the checks that it is the one
/// this file's argument applies to: exactly one non-recursive argument, so the
/// telescope is one `Σ` over the constant innermost level.
fn unary_sum<'a>(ic: &IndChain, ind: &'a Inductive, i: usize) -> Option<&'a DSum> {
    if !ind.is_over(&ic.mach) || i >= ind.summands.len() || ind.spec.ctors[i].args.len() != 1 {
        return None
    }
    let tel = &ind.telescopes[i];
    let d = tel.sums.first()?;
    // `Σ` is the outermost level and its fibre is the innermost one — i.e. the
    // level `base_ax` is about. Both are true by `Telescope::new`'s
    // construction and neither is assumed here.
    (tel.levels.len() == 2
        && tel.levels[0] == d.sigma
        && tel.levels[1] == d.fib
        && tel.betas[0] == d.dom)
        .then_some(d)
}

/// **`⊢ img(p⃗) ⊆ {1}`** — a one-argument constructor's fibre image is a point.
///
/// `img(p⃗)` is `{C₁(p⃗,x) : x ∈ β₀(p⃗)}` and
/// [`crate::sigma::Telescope`]'s `base_ax` is `⊢ ∀p⃗ ∀y. C₁(p⃗,y) = 1`, so every
/// member of the image *is* `1`. One `∃`-elimination and one Leibniz step; no
/// Replacement instance, which is the whole point (see the module header).
pub fn unary_image_is_a_point(
    env: &mut Env,
    ic: &IndChain,
    ind: &Inductive,
    i: usize,
) -> Option<Thm> {
    let d = unary_sum(ic, ind, i)?;
    let s = &ic.mach.wt.sums;
    let up = s.ap.sets.up;
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let dom_at = Term::apply(d.dom, ps.clone());
    let img_at = Term::apply(d.img, ps.clone());

    let (wv, xv) = (env.fresh_var(), env.fresh_var());
    let (tw, tx) = (Term::var(wv), Term::var(xv));
    let at = |f: kernel::FnSym, t: &Term| {
        let mut a = ps.clone();
        a.push(t.clone());
        Term::apply(f, a)
    };
    let fib_x = at(d.fib, &tx);

    let img_at_w = inst_all(&d.img_ax, &{
        let mut a = ps.clone();
        a.push(tw.clone());
        a
    })?;
    let base_x = inst_all(&ind.telescopes[i].base_ax, &{
        let mut a = ps.clone();
        a.push(tx.clone());
        a
    })?;
    if *base_x.concl() != Formula::eq(fib_x.clone(), s.unit()) {
        return None
    }

    // `w = C₁(p⃗,x) → w = 1 → w ∈ {1}`, under the `∃x` and its `x ∈ β₀(p⃗)`.
    let hole = env.fresh_var();
    let to_one = Thm::mp(
        &Thm::eq_leibniz(
            fib_x.clone(),
            s.unit(),
            hole,
            Formula::eq(tw.clone(), Term::var(hole)),
        ),
        &base_x,
    )?;
    let into_sing = iff_mpr(&inst_all(&s.ap.mem_sing, &[s.unit(), tw.clone()])?)?;
    let in_sing = Formula::mem(tw.clone(), singleton(up, s.unit()));
    let case = syl(
        &and_right(
            Formula::mem(tx.clone(), dom_at.clone()),
            Formula::eq(tw.clone(), fib_x),
        ),
        &syl(&to_one, &into_sing)?,
    )?;
    let from_ex = exists_elim_imp(xv, &Thm::gen(xv, &case), &in_sing)?;
    let out = Thm::gen(wv, &syl(&iff_mp(&img_at_w)?, &from_ex)?);

    (out.hyps().is_empty()
        && *out.concl() == kernel::thm::subset(env, img_at, singleton(up, s.unit())))
    .then_some(out)
}

/// **`⊢ [H →] Aᵢ ∈ U₁`** for a constructor with exactly one non-recursive
/// argument, given `⊢ [H →] β₀(p⃗) ∈ U₁`.
///
/// `arg_in_u1` must conclude the argument type's membership **at the symbol
/// application `β₀(p⃗)`**, not at whatever that symbol abbreviates — for
/// `List`'s `β₀(p) = p` the caller moves `α ∈ U₁` along the defining equation
/// first. Its conclusion and its empty hypothesis set are both checked.
///
/// `None` when `i` is out of range, when the constructor does not take exactly
/// one argument, or when `ind` was not built over `ic`'s
/// [`crate::inductive::Machine`].
pub fn unary_summand_in_u1(
    env: &mut Env,
    ic: &IndChain,
    ind: &Inductive,
    i: usize,
    hyp: Option<&Formula>,
    arg_in_u1: &Thm,
) -> Option<Thm> {
    let d = unary_sum(ic, ind, i)?;
    let ctx = Ctx(hyp.cloned());
    let s = &ic.mach.wt.sums;
    let ap = &s.ap;
    let up = ap.sets.up;
    let u1 = &ic.chain.u1;
    let proj = &ic.mach.proj;

    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let dom_at = Term::apply(d.dom, ps.clone());
    let img_at = Term::apply(d.img, ps.clone());
    let uimg = ap.sets.union_of(img_at.clone());
    let prod_at = s.prod.of(dom_at.clone(), uimg.clone());
    let sigma_at = Term::apply(d.sigma, ps.clone());

    if !arg_in_u1.hyps().is_empty()
        || *arg_in_u1.concl() != ctx.wrap(Formula::mem(dom_at.clone(), u1.set.clone()))
        || sigma_at != ind.summands[i]
    {
        return None
    }

    // ── `img(p⃗) ∈ U₁`, because it is a subset of `{1}` ──────────────────────
    let img_sub = unary_image_is_a_point(env, ic, ind, i)?;
    let one_in = Thm::mp(
        &inst_all(&u1.pairing, &[s.zero(), s.zero()])?,
        &crate::and_intro(&u1.empty_mem, &u1.empty_mem),
    )?;
    if *one_in.concl() != Formula::mem(s.unit(), u1.set.clone()) {
        return None
    }
    let sing_in = Thm::mp(
        &inst_all(&u1.pairing, &[s.unit(), s.unit()])?,
        &crate::and_intro(&one_in, &one_in),
    )?;
    let img_in = Thm::mp(
        &inst_all(
            &Thm::mp(
                &inst_all(&u1.sub, std::slice::from_ref(&singleton(up, s.unit())))?,
                &sing_in,
            )?,
            std::slice::from_ref(&img_at),
        )?,
        &img_sub,
    )?;
    let uimg_in = Thm::mp(&inst_all(&u1.union, std::slice::from_ref(&img_at))?, &img_in)?;

    // ── `β₀(p⃗) × ⋃img(p⃗) ∈ U₁`, the only step that carries `H` ─────────────
    let prod_in = ctx.mp(
        &ctx.lift(&inst_all(&u1.product, &[dom_at.clone(), uimg])?),
        &ctx.and(arg_in_u1, &ctx.lift(&uimg_in))?,
    )?;

    // ── `Σ(p⃗) ⊆ β₀(p⃗) × ⋃img(p⃗)`, read off the Separation ──────────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let sig_at = inst_all(&d.sigma_ax, &{
        let mut a = ps.clone();
        a.push(tq.clone());
        a
    })?;
    let psi = Formula::mem(proj.snd_of(ap, tq.clone()), {
        let mut a = ps.clone();
        a.push(proj.fst_of(ap, tq.clone()));
        Term::apply(d.fib, a)
    });
    let in_prod = Formula::mem(tq.clone(), prod_at.clone());
    let fwd = iff_mp(&sig_at)?;
    if *fwd.concl()
        != Formula::imp(
            Formula::mem(tq.clone(), sigma_at.clone()),
            Formula::and(in_prod.clone(), psi.clone()),
        )
    {
        return None
    }
    let sigma_sub = Thm::gen(qv, &syl(&fwd, &crate::and_left(in_prod, psi))?);
    if *sigma_sub.concl() != kernel::thm::subset(env, sigma_at.clone(), prod_at.clone()) {
        return None
    }

    // ── and `C₂` at the product ─────────────────────────────────────────────
    let out = ctx.mp(
        &ctx.inst(
            &ctx.mp(&ctx.lift(&inst_all(&u1.sub, std::slice::from_ref(&prod_at))?), &prod_in)?,
            sigma_at.clone(),
        )?,
        &ctx.lift(&sigma_sub),
    )?;
    (out.hyps().is_empty() && *out.concl() == ctx.wrap(Formula::mem(sigma_at, u1.set.clone())))
        .then_some(out)
}
