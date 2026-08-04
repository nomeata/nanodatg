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
//! [`mod@super::pullback`] carries the derivation; this file supplies the
//! former `x ↦ ⟨x,•⟩` and its two directions. [`Telescope::eta`] is
//! `⊢ ∀p⃗ ∀q. (q ∈ T(p⃗) → ⟨comp₀ q, •⟩ = q)` — a **term-level** inversion,
//! because the projections *name* the components. So the existential the shared
//! derivation eliminates is introduced here at the named witness `π₁q` rather
//! than searched for, and this is the shortest of the three instances.
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
//! [`crate::funcs::lambda_n`] graph — one Replacement instance, minted by
//! [`mod@super::pullback`] and by nothing here. `dom_bnd` is checked at `β₀(p⃗)`
//! for the conclusion it must have and for an empty hypothesis set, and every
//! rule read off `tel` is compared against the formula this file rebuilds.

use kernel::{Env, Formula, Term, Thm};

use crate::inductive::Machine;
use crate::sigma::Telescope;
use crate::{eq_symm_imp, exists_intro_imp, hyp_and, inst_all, syl};

use super::apparatus::IndChain;
use super::bounded::bnd;
use super::pullback::bnd_via_pullback;

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
    let mk = |x: &Term| sets.pair(x.clone(), point.clone());

    // ── the three rules, at these parameters ────────────────────────────────
    let (zv, yv) = (env.fresh_var(), env.fresh_var());
    let (tz, ty) = (Term::var(zv), Term::var(yv));
    let comp_z = Telescope::comp_of(&s.ap, &mach.proj, 0, tz.clone());
    let at_z = |th: &Thm| -> Option<Thm> {
        let mut args = ps.to_vec();
        args.push(tz.clone());
        inst_all(th, &args)
    };
    let intro_at = at_z(&tel.intro)?;
    let proj_at = at_z(tel.proj_mem.first()?)?;
    let eta_at = at_z(&tel.eta)?;
    if *intro_at.concl()
        != Formula::imp(
            Formula::mem(tz.clone(), dom.clone()),
            Formula::mem(mk(&tz), kset.clone()),
        )
        || *proj_at.concl()
            != Formula::imp(
                Formula::mem(tz.clone(), kset.clone()),
                Formula::mem(comp_z.clone(), dom.clone()),
            )
        || *eta_at.concl()
            != Formula::imp(
                Formula::mem(tz.clone(), kset.clone()),
                Formula::eq(mk(&comp_z), tz.clone()),
            )
    {
        return None
    }

    // ── `η` names the witness, so the inversion needs no search ─────────────
    //
    // `⊢ ∀z. (z ∈ T(p⃗) → ∃y. (y ∈ β₀(p⃗) ∧ z = ⟨y,•⟩))`, at `y := comp₀ z`:
    // the projection puts the witness in the domain and `η` says the pair
    // rebuilds `z`.
    let inversion = {
        let body = Formula::and(
            Formula::mem(ty.clone(), dom.clone()),
            Formula::eq(tz.clone(), mk(&ty)),
        );
        let back = syl(&eta_at, &eq_symm_imp(env, mk(&comp_z), tz.clone()))?;
        Thm::gen(
            zv,
            &syl(
                &hyp_and(&proj_at, &back)?,
                &exists_intro_imp(yv, body, comp_z.clone())?,
            )?,
        )
    };

    let core = bnd_via_pullback(
        env,
        r,
        st,
        &[],
        &dom,
        &kset,
        &mk,
        &Thm::gen(zv, &intro_at),
        &inversion,
    )?;
    let out = Thm::mp(&core, dom_bnd)?;

    let expected = bnd(env, r, st, &kset);
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}
