//! **A constructor's term and its typing rule** — §5.2's `sup` at the tag the
//! `spec` judgment gave it.
//!
//! # The term
//!
//! A W-type element is a pair of a tag and a function out of the tag's fibre.
//! For the `i`-th constructor of a declaration, with non-recursive arguments
//! `y⃗` and recursive arguments `r⃗`, §5.2 fixes both halves:
//!
//! ```text
//! ctor_i(y⃗, r⃗) := ⟨ inj_i⟨y₀,⟨y₁, … ⟨y_{k-1}, •⟩⟩⟩ ,  f(r⃗) ⟩
//! ```
//!
//! — the tag is the `i`-th injection ([`crate::isum`]) of the arguments packed
//! into the constructor's telescope ([`crate::sigma::Telescope::tuple_of`]), and
//! the function is [`crate::recarg`]'s dispatcher out of `finord(m)`. Note that
//! **the term mentions no parameter**: `p⃗` occurs in the constructor's *type*,
//! never in its value, which is why [`Ctor::inj`] and
//! [`Inductive::distinct`](super::Inductive::distinct) are parameter-free.
//!
//! # The typing rule, and where each hypothesis comes from
//!
//! Six steps, all of them instances of something already derived:
//!
//! | step | from |
//! |---|---|
//! | `⟨y⃗⟩ ∈ Aᵢ` | [`Telescope::intro`](crate::sigma::Telescope::intro) |
//! | `inj_i⟨y⃗⟩ ∈ A` | [`crate::isum::inj_mem_at`] |
//! | `app(B, inj_i⟨y⃗⟩) = finord(mᵢ)` | [`Fibre::fibre`](crate::fibre::Fibre::fibre) |
//! | `f(r⃗) ∈ fs(finord(mᵢ), W)` | [`RecArg::in_funspace`](crate::recarg::RecArg::in_funspace) |
//! | `f(r⃗) ∈ fs(app(B, inj_i⟨y⃗⟩), W)` | Leibniz along the previous two |
//! | `⟨inj_i⟨y⃗⟩, f(r⃗)⟩ ∈ W` | `sup`, with the bound discharged |
//!
//! and one transport of `W(A,B,U({A,T}))` to the abbreviation `ind(p⃗)`.
//!
//! The hypotheses are exactly the `k + m` typings Lean's own constructor states
//! — `yⱼ ∈ βⱼ(p⃗, y₀…y_{j-1})` and `rⱼ ∈ ind(p⃗)` — and **nothing else**. In
//! particular no hypothesis about a parameter's own type appears, confirming at
//! general arity what `derived/src/wlist.rs` found for `List`: the bound
//! obligation never asks what `α` is. When `k = m = 0` there is no hypothesis at
//! all and the rule is a closed theorem; see [`super::shared`].
//!
//! # Interface
//!
//! [`ctor_typing`] is private to [`super`]; its result is [`Ctor`], surfaced as
//! [`Inductive::ctors`](super::Inductive::ctors).

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::recarg::RecArg;
use crate::sigma::Telescope;
use crate::{conj_of, gen_all, inst_all};

use super::carrier::{ctor_atoms, Frame};
use super::distinct::ctor_injective;
use super::machine::Machine;
use crate::ctx::Ctx;

/// One constructor of a translated declaration.
pub struct Ctor {
    /// Its position in the declaration.
    pub index: usize,
    /// The `k` non-recursive argument variables `y₀ … y_{k-1}`.
    pub args: Vec<FreeVar>,
    /// The `m` recursive argument variables `r₀ … r_{m-1}`.
    pub recs: Vec<FreeVar>,
    /// `inj_i⟨y₀, … ⟨y_{k-1}, •⟩⟩`, the tag.
    pub tag: Term,
    /// `f(r⃗)`, the function out of the fibre.
    pub fun: Term,
    /// `ctor_i(y⃗, r⃗)`, at [`Ctor::args`] and [`Ctor::recs`].
    pub term: Term,
    /// The right-nested conjunction of the `k + m` hypotheses, or `None` for a
    /// nullary constructor.
    pub hyp: Option<Formula>,
    /// `⊢ ∀p⃗ ∀y⃗ ∀r⃗. (H → ctor_i(y⃗,r⃗) ∈ ind(p⃗))`, and without the `H →` when
    /// the constructor is nullary.
    pub mem: Thm,
    /// `⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. (ctor_i(y⃗,r⃗) = ctor_i(y⃗′,r⃗′) → E)`, where `E` is the
    /// **flat right-nested chain** of all `k + m` equations in declaration
    /// order, `y₀ = y₀′ ∧ (… ∧ (r₀ = r₀′ ∧ (… ∧ r_{m-1} = r_{m-1}′)))` — not
    /// grouped into an arguments half and a recursive-arguments half.
    /// `None` for a nullary constructor, where there is nothing to state.
    pub inj: Option<Thm>,
}

/// Derive the `i`-th constructor's term, typing rule and injectivity.
pub(super) fn ctor_typing(
    env: &mut Env,
    mach: &Machine,
    frame: &Frame<'_>,
    i: usize,
) -> Option<Ctor> {
    let s = &mach.wt.sums;
    let tel = &frame.telescopes[i];
    let ra = &frame.recargs[i];
    let (k, m) = (tel.betas.len(), ra.m);

    let args: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let recs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = args.iter().map(|v| Term::var(*v)).collect();
    let rs: Vec<Term> = recs.iter().map(|v| Term::var(*v)).collect();

    let tuple = Telescope::tuple_of(s, &ys);
    let tag = mach.syms.inj(i, tuple.clone())?;
    let fun = RecArg::of(s, &mach.cases, &rs);
    let term = mach.wt.sup(tag.clone(), fun.clone());

    // The hypotheses, stated at `W(…)`; transported to `ind(p⃗)` at the end.
    let atoms = ctor_atoms(tel, frame.ps, &ys, &rs, frame.wty);
    let ctx = Ctx(conj_of(&atoms));

    // ── 1. the arguments pack into the constructor's tag summand ────────────
    let tuple_mem = if k == 0 {
        ctx.lift(&inst_all(&tel.intro, frame.ps)?)
    } else {
        let mut a = frame.ps.to_vec();
        a.extend(ys.iter().cloned());
        ctx.syl(&ctx.sub(&atoms, 0, k)?, &inst_all(&tel.intro, &a)?)?
    };

    // ── 2. the tag is in the tag set ────────────────────────────────────────
    let tag_mem = {
        let mut a = frame.summands.to_vec();
        a.push(tuple.clone());
        ctx.syl(&tuple_mem, &inst_all(mach.syms.inj_mem(frame.summands.len(), i)?, &a)?)?
    };

    // ── 3. the fibre at that tag is `finord(mᵢ)` ────────────────────────────
    let fib = ctx.syl(&tuple_mem, &inst_all(&frame.fibre.fibre[i], std::slice::from_ref(&tuple))?)?;

    // ── 4. the recursive-argument function is typed on that fibre ───────────
    let f_fs = if m == 0 {
        ctx.lift(&inst_all(&ra.in_funspace, std::slice::from_ref(frame.wty))?)
    } else {
        let mut a = vec![frame.wty.clone()];
        a.extend(rs.iter().cloned());
        ctx.syl(&ctx.sub(&atoms, k, k + m)?, &inst_all(&ra.in_funspace, &a)?)?
    };

    // ── 5. rewrite its domain backwards along the fibre equation ────────────
    let f_typed = {
        let back = ctx.eq_symm(env, &fib)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            mach.syms.finord(s, m)?,
            mach.wt.fibre(frame.fibre.fam.clone(), tag.clone()),
            hole,
            Formula::mem(fun.clone(), s.fs.of(Term::var(hole), frame.wty.clone())),
        );
        ctx.mp(&ctx.syl(&back, &leib)?, &f_fs)?
    };

    // ── 6. `sup` ────────────────────────────────────────────────────────────
    let raw = {
        let at_tag = ctx.syl(&tag_mem, &inst_all(frame.sup, std::slice::from_ref(&tag))?)?;
        ctx.mp(&ctx.inst(&at_tag, fun.clone())?, &f_typed)?
    };

    // ── the transport `W(A,B,U({A,T})) ↦ ind(p⃗)`, in hypothesis and goal ───
    let hole = env.fresh_var();
    let th = Term::var(hole);
    let phi = {
        let open = ctor_atoms(tel, frame.ps, &ys, &rs, &th);
        let concl = Formula::mem(term.clone(), th.clone());
        match conj_of(&open) {
            Some(h) => Formula::imp(h, concl),
            None => concl,
        }
    };
    debug_assert_eq!(
        phi.clone().subst(hole, frame.wty),
        *raw.concl(),
        "inductive::ctor: the transport context does not reproduce the statement"
    );
    let carried = Thm::mp(
        &Thm::mp(&Thm::eq_leibniz(frame.wty.clone(), frame.carrier.clone(), hole, phi), frame.to_ty)?,
        &raw,
    )?;

    let mut quant = frame.params.to_vec();
    quant.extend(args.iter().copied());
    quant.extend(recs.iter().copied());
    let mem = gen_all(&quant, &carried);

    let hyp = conj_of(&ctor_atoms(tel, frame.ps, &ys, &rs, frame.carrier));
    let inj = ctor_injective(env, mach, frame, i)?;

    Some(Ctor { index: i, args, recs, tag, fun, term, hyp, mem, inj })
}
