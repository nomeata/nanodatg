//! **`⊢ A ∈ Uₙ` for a declaration's tag set** — the one obligation of
//! [`super::decl`] that a declaration's *arguments* can make arbitrarily hard,
//! and hence the one that stays with the caller.
//!
//! # Interface
//!
//! Writing `A = Sum_n(A₀ … A_{n-1})` for [`Inductive::tags`], `Aᵢ` for
//! [`Inductive::summands`]`[i]` (the `i`-th constructor's `Σ`-telescope, at the
//! declaration's parameters) and `Uₙ` for the [`Rung`] the caller hands in:
//!
//! ```text
//! ⊢ Aᵢ ∈ Uₙ                    for a constructor with no arguments  [nullary_summand_at]
//! ⊢ [H →] A ∈ Uₙ               from the n summand memberships       [tags_at]
//! ```
//!
//! [`nullary_summand_in_u1`], [`nullary_summands_in_u1`] and [`tags_in_u1`] are
//! the `n = 1` instances, one line each, so an existing caller changes nothing
//! and pays nothing.
//!
//! `H` is an optional antecedent carried through the fold, for a
//! **parameterised** declaration whose summands are only small under an
//! assumption about the parameters (`α ∈ U₁` for `List α`). With no antecedent
//! the output is unconditional.
//!
//! # Why `A ∈ Uₙ` is a genuine antecedent and not a gap
//!
//! It is **necessary**: `Fin⁺` makes the seed `S` a superset of `A`, `S ∈ Uₙ`
//! is what [`super::WMem::w_in_universe_bnd`] spends, and `C₂` turns
//! `A ⊆ S ∈ Uₙ` back into `A ∈ Uₙ`. So no choice of seed removes it — a
//! declaration whose tag set is not small has no W-type in `Uₙ`, and `List α`
//! for an `α ∉ U₁` is exactly that declaration at `n = 1`. What this file
//! supplies is the part that is *always* dischargeable (a constructor with no
//! non-recursive arguments contributes `1`) and the fold that assembles the
//! rest.
//!
//! Note what does **not** appear: the recursive-argument counts. `A` collects
//! only the non-recursive arguments, so `N`, `Tree` and every enumeration have
//! the same tag set they would have with the recursion removed, and
//! [`nullary_summand_at`] covers all of them.
//!
//! # Which rung to fold at
//!
//! The fold spends `Uₙ`'s `pairing`, `product` and `bin_union` and its
//! `⊢ ∅ ∈ Uₙ`, all of which every rung has, so folding at rung `n` costs what
//! folding at rung 1 costs. The rung is a *caller-side parameter*, and the rule
//! for choosing it is [`super::sigma_n`]'s: run the summand/tag pipeline
//! **exactly once**, at
//! `n₀ := max(1, max over the fields of the rung that field's type lives in)`,
//! and [`crate::tower::Cumul::raise`] the finished `A ∈ U_{n₀}` to whatever
//! rung the declaration is placed at — `raise` is one `inst_all` and one `mp`
//! and mints nothing, whereas a second run of [`super::sigma_n`] mints a fresh
//! image symbol and a fresh Replacement axiom instance per outer telescope
//! level. A summand membership available *below* `n₀` is raised individually
//! before the fold, which is again one `mp`. For a declaration all of whose
//! fields are small, `n₀ = 1` and this is the old behaviour on the nose.
//!
//! # Where the general case stops, precisely
//!
//! A constructor with `k ≥ 1` arguments contributes
//! `Aᵢ = Σy₀:β₀. … Σy_{k-1}:β_{k-1}. 1`, and
//! [`crate::sigma::dsum`](fn@crate::sigma::dsum) builds each `Σ` as a Separation subset of
//! `dom(p⃗) × ⋃img(p⃗)` with `img(p⃗) = {fib(p⃗,x) : x ∈ dom(p⃗)}` a **Replacement
//! image**. `Σ ∈ Uₙ` therefore reduces to `dom ∈ Uₙ` and `img ∈ Uₙ`, and the
//! second is closure of a universe under Replacement. This header used to say
//! that closure is "*not derived anywhere in this crate*". That is **void**:
//! [`crate::universe::least_universe_replacement_n`] derives it from
//! `ax_tarski`'s inaccessibility clause `C₄`, and
//! [`super::sigma_n::summand_at`] composes it with the reduction above by
//! induction on telescope depth. What stays with the caller is not the closure
//! but the *argument types'* smallness: `βⱼ(p⃗,y⃗) ∈ Uₙ` is a fact about the
//! declaration, not about the universe, and [`tags_at`] therefore takes the
//! summand membership as an input.
//!
//! # Nothing here is an axiom
//!
//! The fold is `n` uses of the sum's **defining equation**
//! [`Sums::sum_def`](crate::sums::Sums::sum_def) — `A + B` abbreviates
//! `({∅} × A) ∪ ({1} × B)` — over `Uₙ`'s pairing, product and binary-union
//! closures, exactly the route [`super::bool_tags_in_u1`] takes for `1 + 1`. No
//! Replacement instance and no case analysis. Every caller-supplied theorem is
//! checked for the conclusion it must have **and** for an empty hypothesis set,
//! since a `Γ ⊢` would ride through `mp` into a statement advertised without
//! one; and the [`Rung`] handed in is checked to be a rung of *this* chain's
//! tower.

use kernel::{Env, Formula, Term, Thm};

use crate::isum::isum_of;
use crate::sums::Sums;
use crate::tower::Rung;
use crate::inductive::{Inductive, Machine};
use crate::{all_unconditional, and_intro, eq_symm, establishes, inst_all, singleton};

use super::apparatus::IndChain;
use super::opt::Ctx;

/// The handed-in [`Rung`] really is a rung of **this chain's own** tower, and
/// every field this file spends is a `⊢` with nothing on the left.
///
/// The check [`super::decl::DeclUniverse::over_at`] makes, on *statements*
/// rather than on symbols, over the fields this file reads and no others: `Uₙ`
/// is this chain's `U(·)` applied to the rung's **own seed** — a `Rung` from a
/// second [`crate::tower::Tower`] in the same `Env` fails here, because its
/// `set` is the *other* `U(·)` of something, and so does a `Rung` whose `set`
/// and `seed` have drifted apart; `⊢ ∅ ∈ Uₙ` is about *this* [`Sums`]' `∅`,
/// which is also the base of the fold; and the three closure schemas the fold
/// spends — `pairing`, `product`, `bin_union` — rest on nothing.
fn rung_ok(ic: &IndChain, s: &Sums, rung: &Rung) -> bool {
    Term::apply(ic.chain.lu(), vec![rung.seed.clone()]) == rung.set
        && establishes(&rung.empty_mem, &Formula::mem(s.zero(), rung.set.clone()))
        && all_unconditional(&[&rung.pairing, &rung.product, &rung.bin_union])
}

/// `⊢ 1 ∈ Uₙ` and `⊢ {1} ∈ Uₙ`, the two tag singletons the sum's defining
/// equation is built out of.
fn tag_singletons(rung: &Rung, s: &Sums) -> Option<(Thm, Thm)> {
    let up = s.ap.sets.up;
    let (zero, one) = (s.zero(), s.unit());
    let one_in = Thm::mp(
        &inst_all(&rung.pairing, &[zero.clone(), zero])?,
        &and_intro(&rung.empty_mem, &rung.empty_mem),
    )?;
    if *one_in.concl() != Formula::mem(one.clone(), rung.set.clone()) {
        return None
    }
    let sing_in = Thm::mp(
        &inst_all(&rung.pairing, &[one.clone(), one.clone()])?,
        &and_intro(&one_in, &one_in),
    )?;
    if *sing_in.concl() != Formula::mem(singleton(up, one), rung.set.clone()) {
        return None
    }
    Some((one_in, sing_in))
}

/// **`⊢ Aᵢ ∈ U₁`** for a constructor with no non-recursive arguments.
///
/// [`nullary_summand_at`] at `ic.chain.u1`, and nothing else.
pub fn nullary_summand_in_u1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
) -> Option<Thm> {
    nullary_summand_at(env, ic, mach, ind, i, &ic.chain.u1)
}

/// **`⊢ Aᵢ ∈ Uₙ`** for a constructor with no non-recursive arguments, at
/// **any** rung.
///
/// Such a constructor's telescope is the bare innermost **telescope level** —
/// a [`crate::sigma::Telescope`] stage, not a tower rung and not a Lean
/// universe level — and [`crate::sigma::Telescope`]'s `base_ax` says it is `1`,
/// which is `{∅}`; so `Uₙ`'s pairing closure at `∅` supplies the membership and
/// one Leibniz step moves it onto that stage's symbol. The symbol matters: `A₀`
/// is `C₀(p⃗)`, an application, and **not** syntactically `1`, so without the
/// unfolding the statement would be about the wrong term.
///
/// `None` when `i` is out of range, when the `i`-th constructor takes an
/// argument, when `mach` is not `ind`'s apparatus and `ic`'s signature, or when
/// `rung` is not a rung of this chain's own tower ([`rung_ok`]).
pub fn nullary_summand_at(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    rung: &Rung,
) -> Option<Thm> {
    if !ic.is_over(mach)
        || !ind.is_over(mach)
        || i >= ind.summands.len()
        || !ind.spec.ctors[i].args.is_empty()
    {
        return None
    }
    let s = &mach.wt.sums;
    if !rung_ok(ic, s, rung) {
        return None
    }
    let (one_in, _) = tag_singletons(rung, s)?;

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
                Formula::mem(Term::var(hole), rung.set.clone()),
            ),
            &eq_symm(env, &base_at)?,
        )?,
        &one_in,
    )?;
    (out.hyps().is_empty() && *out.concl() == Formula::mem(summand, rung.set.clone()))
        .then_some(out)
}

/// [`nullary_summand_in_u1`] at every constructor — [`nullary_summands_at`] at
/// `ic.chain.u1`, and nothing else.
pub fn nullary_summands_in_u1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
) -> Option<Vec<Thm>> {
    nullary_summands_at(env, ic, mach, ind, &ic.chain.u1)
}

/// [`nullary_summand_at`] at every constructor — the whole input [`tags_at`]
/// needs, for a declaration none of whose constructors takes a non-recursive
/// argument.
///
/// That is every enumeration, `N`, and `Tree`: recursive arguments do not enter
/// the tag set. `None` as soon as one constructor does take an argument.
pub fn nullary_summands_at(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    rung: &Rung,
) -> Option<Vec<Thm>> {
    (0..ind.summands.len()).map(|i| nullary_summand_at(env, ic, mach, ind, i, rung)).collect()
}

/// **`⊢ [H →] Sum_n(A₀ … A_{n-1}) ∈ U₁`** from the `n` summand memberships —
/// [`tags_at`] at `ic.chain.u1`, and nothing else.
pub fn tags_in_u1(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    hyp: Option<&Formula>,
    summands: &[Thm],
) -> Option<Thm> {
    tags_at(env, ic, mach, ind, hyp, &ic.chain.u1, summands)
}

/// **`⊢ [H →] Sum_n(A₀ … A_{n-1}) ∈ Uₙ`** from the `n` summand memberships, at
/// **any** rung.
///
/// `summands[i]` must be `⊢ Aᵢ ∈ Uₙ` when `hyp` is `None` and `⊢ H → Aᵢ ∈ Uₙ`
/// when it is `Some(H)`, at [`Inductive::summands`]`[i]` and at `rung`'s set —
/// all of which is checked, along with each resting on nothing. At `n = 0`
/// (Lean's `Empty`) the fold is the base alone and the answer is
/// `⊢ Sum_0() ∈ Uₙ`, which is `∅ ∈ Uₙ` behind one unfolding.
///
/// All `n` summands must be at **one** rung; a summand available lower is
/// raised by [`crate::tower::Cumul::raise`] first, which is one `mp`. See the
/// module header for which rung to pick.
#[allow(clippy::too_many_arguments)]
pub fn tags_at(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    hyp: Option<&Formula>,
    rung: &Rung,
    summands: &[Thm],
) -> Option<Thm> {
    if !ic.is_over(mach) || !ind.is_over(mach) || summands.len() != ind.summands.len() {
        return None
    }
    let ctx = Ctx(hyp.cloned());
    let s = &mach.wt.sums;
    if !rung_ok(ic, s, rung) {
        return None
    }
    let up = s.ap.sets.up;
    let n = summands.len();

    for (i, t) in summands.iter().enumerate() {
        if !t.hyps().is_empty()
            || *t.concl() != ctx.wrap(Formula::mem(ind.summands[i].clone(), rung.set.clone()))
        {
            return None
        }
    }
    let (one_in, sing_in) = tag_singletons(rung, s)?;

    // ── the fold up the nest `A₀ + (A₁ + (… + 0))` ──────────────────────────
    let mut acc = ctx.lift(&rung.empty_mem);
    if *acc.concl() != ctx.wrap(Formula::mem(s.zero(), rung.set.clone())) {
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
            &ctx.lift(&inst_all(&rung.product, &[s.unit(), a.clone()])?),
            &ctx.and(&ctx.lift(&one_in), &summands[i])?,
        )?;
        let right_in = ctx.mp(
            &ctx.lift(&inst_all(&rung.product, &[singleton(up, s.unit()), b.clone()])?),
            &ctx.and(&ctx.lift(&sing_in), &acc)?,
        )?;
        let body_in = ctx.mp(
            &ctx.lift(&inst_all(&rung.bin_union, &[p_left, p_right])?),
            &ctx.and(&left_in, &right_in)?,
        )?;
        let hole = env.fresh_var();
        let back = Thm::mp(
            &Thm::eq_leibniz(
                body,
                s.sum_of(a.clone(), b.clone()),
                hole,
                Formula::mem(Term::var(hole), rung.set.clone()),
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
        &Thm::eq_leibniz(nest, ind.tags.clone(), hole, Formula::mem(Term::var(hole), rung.set.clone())),
        &eq_symm(env, &sum_ax)?,
    )?;
    let out = ctx.mp(&ctx.lift(&onto), &acc)?;
    (out.hyps().is_empty()
        && *out.concl() == ctx.wrap(Formula::mem(ind.tags.clone(), rung.set.clone())))
    .then_some(out)
}
