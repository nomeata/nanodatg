//! **`⊢ A ∈ U₁` for a declaration's tag set** — the one obligation of
//! [`super::decl`] that a declaration's *arguments* can make arbitrarily hard,
//! and hence the one that stays with the caller.
//!
//! # Interface
//!
//! Writing `A = Sum_n(A₀ … A_{n-1})` for [`Inductive::tags`], `Aᵢ` for
//! [`Inductive::summands`]`[i]` (the `i`-th constructor's `Σ`-telescope, at the
//! declaration's parameters) and `U₁` for `U(ω)`:
//!
//! ```text
//! ⊢ Aᵢ ∈ U₁                    for a constructor with no arguments  [nullary_summand_in_u1]
//! ⊢ [H →] A ∈ U₁               from the n summand memberships       [tags_in_u1]
//! ```
//!
//! `H` is an optional antecedent carried through the fold, for a
//! **parameterised** declaration whose summands are only small under an
//! assumption about the parameters (`α ∈ U₁` for `List α`). With no antecedent
//! the output is unconditional.
//!
//! # Why `A ∈ U₁` is a genuine antecedent and not a gap
//!
//! It is **necessary**: `Fin⁺` makes the seed `S` a superset of `A`, `S ∈ U₁`
//! is what [`super::WMem::w_in_universe_bnd`] spends, and `C₂` turns
//! `A ⊆ S ∈ U₁` back into `A ∈ U₁`. So no choice of seed removes it — a
//! declaration whose tag set is not small has no W-type in `U₁`, and `List α`
//! for a `α ∉ U₁` is exactly that declaration. What this file supplies is the
//! part that is *always* dischargeable (a constructor with no non-recursive
//! arguments contributes `1`) and the fold that assembles the rest.
//!
//! Note what does **not** appear: the recursive-argument counts. `A` collects
//! only the non-recursive arguments, so `N`, `Tree` and every enumeration have
//! the same tag set they would have with the recursion removed, and
//! [`nullary_summand_in_u1`] covers all of them.
//!
//! # Where the general case stops, precisely
//!
//! A constructor with `k ≥ 1` arguments contributes
//! `Aᵢ = Σy₀:β₀. … Σy_{k-1}:β_{k-1}. 1`, and
//! [`crate::sigma::dsum`](fn@crate::sigma::dsum) builds each `Σ` as a Separation subset of
//! `dom(p⃗) × ⋃img(p⃗)` with `img(p⃗) = {fib(p⃗,x) : x ∈ dom(p⃗)}` a **Replacement
//! image**. `Σ ∈ U₁` therefore reduces to `dom ∈ U₁` and `img ∈ U₁`, and the
//! second is closure of a universe under Replacement — derivable from `ax_tarski`'s
//! inaccessibility clause `C₄`, but *not derived anywhere in this crate*. That
//! is the honest boundary: this file does not have it, does not assume it, and
//! [`tags_in_u1`] takes the summand membership as an input rather than pretend
//! otherwise.
//!
//! # Nothing here is an axiom
//!
//! The fold is `n` uses of the sum's **defining equation**
//! [`Sums::sum_def`](crate::sums::Sums::sum_def) — `A + B` abbreviates
//! `({∅} × A) ∪ ({1} × B)` — over `U₁`'s pairing, product and binary-union
//! closures, exactly the route [`super::NatMem`] takes for `1 + 1`. No
//! Replacement instance and no case analysis. Every caller-supplied theorem is
//! checked for the conclusion it must have **and** for an empty hypothesis set,
//! since a `Γ ⊢` would ride through `mp` into a statement advertised without
//! one.

use kernel::{Env, Formula, Term, Thm};

use crate::isum::isum_of;
use crate::sums::Sums;
use crate::tower::Level;
use crate::inductive::{Inductive, Machine};
use crate::{and_intro, eq_symm, inst_all, singleton};

use super::apparatus::IndChain;
use super::opt::Ctx;

/// `⊢ 1 ∈ U₁` and `⊢ {1} ∈ U₁`, the two tag singletons the sum's defining
/// equation is built out of.
fn tag_singletons(u1: &Level, s: &Sums) -> Option<(Thm, Thm)> {
    let up = s.ap.sets.up;
    let (zero, one) = (s.zero(), s.unit());
    let one_in = Thm::mp(
        &inst_all(&u1.pairing, &[zero.clone(), zero])?,
        &and_intro(&u1.empty_mem, &u1.empty_mem),
    )?;
    if *one_in.concl() != Formula::mem(one.clone(), u1.set.clone()) {
        return None
    }
    let sing_in = Thm::mp(
        &inst_all(&u1.pairing, &[one.clone(), one.clone()])?,
        &and_intro(&one_in, &one_in),
    )?;
    if *sing_in.concl() != Formula::mem(singleton(up, one), u1.set.clone()) {
        return None
    }
    Some((one_in, sing_in))
}

/// **`⊢ Aᵢ ∈ U₁`** for a constructor with no non-recursive arguments.
///
/// Such a constructor's telescope is the bare innermost level, and
/// [`crate::sigma::Telescope`]'s `base_ax` says it is `1` — which is
/// `{∅}`, so `U₁`'s pairing closure at `∅` supplies the membership and one
/// Leibniz step moves it onto the level symbol. The symbol matters: `A₀` is
/// `C₀(p⃗)`, an application, and **not** syntactically `1`, so without the
/// unfolding the statement would be about the wrong term.
///
/// `None` when `i` is out of range, when the `i`-th constructor takes an
/// argument, or when `mach` is not `ind`'s apparatus and `ic`'s signature.
pub fn nullary_summand_in_u1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
) -> Option<Thm> {
    if !ic.is_over(mach)
        || !ind.is_over(mach)
        || i >= ind.summands.len()
        || !ind.spec.ctors[i].args.is_empty()
    {
        return None
    }
    let s = &mach.wt.sums;
    let u1 = &ic.chain.u1;
    let (one_in, _) = tag_singletons(u1, s)?;

    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let base_at = inst_all(&ind.telescopes[i].base_ax, &ps)?;
    let summand = ind.summands[i].clone();
    if *base_at.concl() != Formula::eq(summand.clone(), s.unit()) {
        return None
    }
    let hole = env.fresh_var();
    let out = Thm::mp(
        &Thm::mp(
            &Thm::eq_leibniz(
                s.unit(),
                summand.clone(),
                hole,
                Formula::mem(Term::var(hole), u1.set.clone()),
            ),
            &eq_symm(env, &base_at)?,
        )?,
        &one_in,
    )?;
    (out.hyps().is_empty() && *out.concl() == Formula::mem(summand, u1.set.clone()))
        .then_some(out)
}

/// [`nullary_summand_in_u1`] at every constructor — the whole input
/// [`tags_in_u1`] needs, for a declaration none of whose constructors takes a
/// non-recursive argument.
///
/// That is every enumeration, `N`, and `Tree`: recursive arguments do not enter
/// the tag set. `None` as soon as one constructor does take an argument.
pub fn nullary_summands_in_u1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
) -> Option<Vec<Thm>> {
    (0..ind.summands.len()).map(|i| nullary_summand_in_u1(env, ic, mach, ind, i)).collect()
}

/// **`⊢ [H →] Sum_n(A₀ … A_{n-1}) ∈ U₁`** from the `n` summand memberships.
///
/// `summands[i]` must be `⊢ Aᵢ ∈ U₁` when `hyp` is `None` and `⊢ H → Aᵢ ∈ U₁`
/// when it is `Some(H)`, at [`Inductive::summands`]`[i]` and at this chain's
/// `U₁` — all of which is checked, along with each resting on nothing. At
/// `n = 0` (Lean's `Empty`) the fold is the base alone and the answer is
/// `⊢ Sum_0() ∈ U₁`, which is `∅ ∈ U₁` behind one unfolding.
pub fn tags_in_u1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    hyp: Option<&Formula>,
    summands: &[Thm],
) -> Option<Thm> {
    if !ic.is_over(mach) || !ind.is_over(mach) || summands.len() != ind.summands.len() {
        return None
    }
    let ctx = Ctx(hyp.cloned());
    let s = &mach.wt.sums;
    let u1 = &ic.chain.u1;
    let up = s.ap.sets.up;
    let n = summands.len();

    for (i, t) in summands.iter().enumerate() {
        if !t.hyps().is_empty()
            || *t.concl() != ctx.wrap(Formula::mem(ind.summands[i].clone(), u1.set.clone()))
        {
            return None
        }
    }
    let (one_in, sing_in) = tag_singletons(u1, s)?;

    // ── the fold up the nest `A₀ + (A₁ + (… + 0))` ──────────────────────────
    let mut acc = ctx.lift(&u1.empty_mem);
    if *acc.concl() != ctx.wrap(Formula::mem(s.zero(), u1.set.clone())) {
        return None
    }
    for i in (0..n).rev() {
        let a = ind.summands[i].clone();
        let b = isum_of(s, &ind.summands[i + 1..]);
        // `a + b` **is** `({∅} × a) ∪ ({1} × b)`; the defining equation is the
        // short way and the membership condition is not needed.
        let def_at = inst_all(&s.sum_def, &[a.clone(), b.clone()])?;
        let p_left = s.prod.of(s.unit(), a.clone());
        let p_right = s.prod.of(singleton(up, s.unit()), b.clone());
        let body = crate::funspace::bin_union(&s.ap.sets, p_left.clone(), p_right.clone());
        if *def_at.concl() != Formula::eq(s.sum_of(a.clone(), b.clone()), body.clone()) {
            return None
        }
        let left_in = ctx.mp(
            &ctx.lift(&inst_all(&u1.product, &[s.unit(), a.clone()])?),
            &ctx.and(&ctx.lift(&one_in), &summands[i])?,
        )?;
        let right_in = ctx.mp(
            &ctx.lift(&inst_all(&u1.product, &[singleton(up, s.unit()), b.clone()])?),
            &ctx.and(&ctx.lift(&sing_in), &acc)?,
        )?;
        let body_in = ctx.mp(
            &ctx.lift(&inst_all(&u1.bin_union, &[p_left, p_right])?),
            &ctx.and(&left_in, &right_in)?,
        )?;
        let hole = env.fresh_var();
        let back = Thm::mp(
            &Thm::eq_leibniz(
                body,
                s.sum_of(a.clone(), b.clone()),
                hole,
                Formula::mem(Term::var(hole), u1.set.clone()),
            ),
            &eq_symm(env, &def_at)?,
        )?;
        acc = ctx.mp(&ctx.lift(&back), &body_in)?;
    }

    // ── and onto the symbol `Sum_n`, which the nest is not ──────────────────
    let sum_ax = inst_all(mach.syms.sum_ax(n)?, &ind.summands)?;
    let nest = isum_of(s, &ind.summands);
    if *sum_ax.concl() != Formula::eq(ind.tags.clone(), nest.clone()) {
        return None
    }
    let hole = env.fresh_var();
    let onto = Thm::mp(
        &Thm::eq_leibniz(nest, ind.tags.clone(), hole, Formula::mem(Term::var(hole), u1.set.clone())),
        &eq_symm(env, &sum_ax)?,
    )?;
    let out = ctx.mp(&ctx.lift(&onto), &acc)?;
    (out.hyps().is_empty()
        && *out.concl() == ctx.wrap(Formula::mem(ind.tags.clone(), u1.set.clone())))
    .then_some(out)
}
