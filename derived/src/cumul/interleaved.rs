//! **The interleaved-to-prenex bridge** — from the `∀y. (H → …)` shape a
//! consumer that opens and closes one binder at a time produces, to the
//! `∀y⃗. (Dⱼ → …)` shape [`super::sigma_n::arg_obligations`] states.
//!
//! # Interface
//!
//! Fix a declaration, a constructor index `ci`, and keep
//! [`super::sigma_n`]'s notation: `k` non-recursive arguments,
//! `Hⱼ := yⱼ ∈ βⱼ(p⃗, y₀ … y_{j-1})`, `D₀ := H` (the caller's optional
//! antecedent, or nothing) and `Dⱼ₊₁ := Dⱼ ∧ Hⱼ`. Then the two shapes of the
//! `j`-th obligation are
//!
//! ```text
//! interleaved   ⊢ [H →] ∀y₀. (H₀ → ∀y₁. (H₁ → … ∀y_{j-1}. (H_{j-1} → φ) … ))
//! prenex        ⊢ ∀y₀ … ∀y_{j-1}. (Dⱼ → φ)                 [arg_obligations()[j]]
//! ```
//!
//! and this file turns the first into the second:
//!
//! ```text
//! summand_obligation(env, given, hyp, j)  -> Option<Thm>    one obligation
//! summand_obligations(env, ic, mach, ind, ci, hyp, given) -> Option<Vec<Thm>>
//! summand_obligations_at(env, ic, mach, ind, ci, hyp, rung, given)
//! ```
//!
//! [`summand_obligations`] is the one a consumer wants: hand it the `k`
//! interleaved theorems in constructor order and it returns the `k` theorems
//! [`super::sigma_n::summand_in_u1`] accepts, each **pinned against
//! [`super::sigma_n::arg_obligations`]'s own formula** before it is handed
//! back. Nothing about the target shape has to be known at the call site.
//!
//! # The rung
//!
//! `φ` is `βⱼ(p⃗,y⃗) ∈ Uₙ`, so the obligation this bridge pins against is a
//! statement at a rung, and [`summand_obligations_at`] takes the rung the same
//! way [`super::sigma_n::arg_obligations_at`], [`super::sigma_n::summand_at`]
//! and [`super::tags::tags_at`] do — the last argument before the theorem list.
//! [`summand_obligations`] is `summand_obligations_at` at `ic.chain.u1`, so an
//! existing caller pays nothing.
//!
//! **The conversion itself does not mention the rung at all**, and neither does
//! [`summand_obligation`]: peeling `∀`s and re-associating implications is the
//! same bookkeeping whatever `φ` is. All the rung does is select which family
//! of formulas the result is checked against — which is precisely why leaving
//! it hardwired here would have been invisible until a caller needed a
//! declaration above `Type 0`, and why the fix is one argument threaded through
//! one call.
//!
//! [`summand_obligation`] is the same step at one `j`, stated with no reference
//! to a declaration at all: it is pure implication-and-quantifier bookkeeping
//! over an arbitrary `φ` and arbitrary guards, and is exposed because the
//! bundle version needs the whole telescope to be readable and a caller
//! sometimes has only one leg.
//!
//! # What the consumer still owes: the domain terms
//!
//! The bridge instantiates the given theorem's own binders at variables it
//! mints, so the *names* a consumer bound its scopes with never matter. The
//! **domain terms** do: `arg_obligations`' guard at level `i` is
//! `yᵢ ∈ βᵢ(p⃗, y₀ … y_{i-1})` at the telescope's own `FnSym`, so a scope opened
//! at anything but
//!
//! ```text
//! Term::apply(ind.telescopes[ci].betas[i], params ++ [w₀ … w_{i-1}])
//! ```
//!
//! (`wⱼ` the consumer's own scope variables, `params` the declaration's
//! parameters as terms) produces a theorem this file will convert faithfully
//! and [`summand_obligations`] will then refuse, because it is an obligation
//! about a different family. That refusal is the point: the alternative is a
//! `summand_in_u1` that silently reads a guard it was not given.
//!
//! # Why this is `derived/`'s job and not the consumer's
//!
//! The consumer that raised this — `mini` — confines `Thm::assume` and
//! `Thm::implies_intr` to one module by invariant, so anything needing them
//! would have to live there. **Nothing here needs them.** Both directions of
//! the conversion are built from rules that only rearrange an implication and
//! a quantifier:
//!
//! * [`kernel::Thm::ax_inst`] as an *implication* (`⊢ (∀v.ψ) → ψ[t/v]`),
//!   composed with [`crate::syl`] — this is what pushes an antecedent through a
//!   `∀`, and it is this module's `Ctx::inst`;
//! * [`crate::and_left`] / [`crate::and_right`] as implications, with
//!   [`crate::hyp_mp`] — this is [`crate::conjoin`], `⊢ A → (B → C)` to
//!   `⊢ (A ∧ B) → C`;
//! * [`kernel::Thm::gen`], on variables minted here and therefore free in no
//!   hypothesis.
//!
//! So the shape mismatch is a library-side convention, and it is fixed on the
//! library side. The alternative considered and rejected was to have
//! `arg_obligations` *also* offer the interleaved shape and `summand_in_u1`
//! accept either: that doubles the surface of the file whose whole job is to be
//! the single source of truth for these `k` formulas, and it would leave two
//! shapes in circulation for the same obligation. One shape, one bridge.
//!
//! # The true converse of [`crate::uncurry`]
//!
//! [`crate::conjoin`] is `⊢ A → (B → C)` to `⊢ (A ∧ B) → C`. It did not exist:
//! [`crate::uncurry`] and [`super::step::curry`] are, despite their names, the
//! **same** rule in the **same** direction (`⊢ (A ∧ B) → C` to
//! `⊢ A → (B → C)`), so neither is an inverse of the other. It was private here
//! while this bridge was its only consumer, with a note that a second consumer
//! should lift it into [`crate`]'s propositional toolkit rather than copy it.
//! [`crate::inductive::family::trunc_rec`] is that second consumer — the
//! existential elimination that turns `‖ind(p⃗)‖`'s inhabitant into a member of
//! `W` needs exactly this shape — so it has been lifted, and this file calls it
//! there.
//!
//! # Nothing here is an axiom
//!
//! No symbol is introduced and no set-theoretic lemma is used — the file never
//! mentions `∈` except through the formulas it is handed. Every input is
//! checked to be a `⊢` with nothing on the left, and [`summand_obligations`]
//! checks every output against [`super::sigma_n::arg_obligations`] with
//! [`crate::establishes`] before returning it.

use kernel::{Env, Formula, Term, Thm};

use crate::inductive::{Inductive, Machine};
use crate::tower::Rung;
use crate::{conjoin, establishes, gen_all};

use super::apparatus::IndChain;
use super::opt::Ctx;
use super::sigma_n::arg_obligations_at;

/// **The bundle**, at `U₁`. [`summand_obligations_at`] at `ic.chain.u1`, and
/// nothing else.
pub fn summand_obligations(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    ci: usize,
    hyp: Option<&Formula>,
    given: &[Thm],
) -> Option<Vec<Thm>> {
    summand_obligations_at(env, ic, mach, ind, ci, hyp, &ic.chain.u1, given)
}

/// **The bundle.** The `k` theorems [`super::sigma_n::summand_at`] accepts, from
/// the `k` theorems a binder-discharging consumer produces, at **any** rung.
///
/// `given[j]` must be the interleaved obligation at depth `j` — see the module
/// header for the two shapes — and unconditional. Each converted theorem is
/// compared with [`super::sigma_n::arg_obligations_at`]'s `j`-th formula by
/// [`crate::establishes`], so the result is accepted by `summand_at` at the
/// same rung or this returns `None`; there is no third outcome in which a
/// wrongly-shaped obligation reaches the induction.
///
/// `rung` must be a rung of the same tower the chain was built over;
/// [`arg_obligations_at`] makes that check and this returns `None` with it. The
/// conversion is rung-free (see the header), so the *only* thing `rung` changes
/// is which formulas the results are pinned against — hand in a rung and get
/// obligations that `summand_at` accepts at that rung and at no other.
///
/// `None` in exactly [`arg_obligations_at`]' cases, plus a `given` of the wrong
/// length or with an entry of the wrong shape.
#[allow(clippy::too_many_arguments)]
pub fn summand_obligations_at(
    env: &mut Env,
    ic: &IndChain,
    mach: &Machine,
    ind: &Inductive,
    ci: usize,
    hyp: Option<&Formula>,
    rung: &Rung,
    given: &[Thm],
) -> Option<Vec<Thm>> {
    let want = arg_obligations_at(env, ic, mach, ind, ci, hyp, rung)?;
    if given.len() != want.len() {
        return None
    }
    let mut out = Vec::with_capacity(want.len());
    for (j, g) in given.iter().enumerate() {
        let t = summand_obligation(env, g, hyp, j)?;
        if !establishes(&t, &want[j]) {
            return None
        }
        out.push(t);
    }
    Some(out)
}

/// **One obligation**, stated with no reference to a declaration:
///
/// ```text
/// from  ⊢ [H →] ∀y₀. (G₀ → ∀y₁. (G₁ → … ∀y_{d-1}. (G_{d-1} → φ) … ))
/// infer ⊢ ∀y₀ … ∀y_{d-1}. ((…((H ∧ G₀) ∧ G₁) … ∧ G_{d-1}) → φ)
/// ```
///
/// `hyp` is `H`, or `None` when there is no outer antecedent — in which case
/// the conjunction starts at `G₀` and `d = 0` is the identity. `depth` is `d`;
/// it is taken rather than discovered because `φ` may itself be a `∀`, and
/// guessing where the guard chain stops is exactly the mistake the caller's
/// `j` already rules out.
///
/// The guards `Gᵢ` are read off the given theorem as it is peeled, never
/// rebuilt, so this cannot substitute a guard the input did not carry. It is
/// the caller's business — [`summand_obligations`] does it — to check that the
/// guards are the ones the obligation is *about*.
///
/// `None` if `given` rests on a hypothesis, or if it does not have `depth`
/// alternating `∀`/`→` layers under the optional `H`.
pub fn summand_obligation(
    env: &mut Env,
    given: &Thm,
    hyp: Option<&Formula>,
    depth: usize,
) -> Option<Thm> {
    if !given.hyps().is_empty() {
        return None
    }
    // `H` must be the antecedent the given theorem actually carries. Without
    // this the loop would accumulate the `Dᵢ` the *caller named* while
    // `conjoin` accumulated the one the *theorem had*, and the two would part
    // company at the first step — a true theorem, correctly labelled by its own
    // conclusion, but not the formula this function's header promises.
    if let Some(h) = hyp {
        if given.concl().as_imp()?.0 != *h {
            return None
        }
    }
    let mut vs = Vec::with_capacity(depth);
    let mut cur = given.clone();
    // `d` is `Dᵢ`: the antecedent already accumulated, left-nested.
    let mut d: Option<Formula> = hyp.cloned();

    for _ in 0..depth {
        let v = env.fresh_var();
        // `⊢ [Dᵢ →] (Gᵢ → rest)`, the `∀yᵢ` opened at a variable of our own.
        cur = Ctx(d.clone()).inst(&cur, Term::var(v))?;
        let guard = match &d {
            Some(_) => cur.concl().as_imp()?.1.as_imp()?.0,
            None => cur.concl().as_imp()?.0,
        };
        // `⊢ Dᵢ₊₁ → rest`. With no `Dᵢ` the theorem already has that shape.
        cur = match &d {
            Some(_) => conjoin(&cur)?,
            None => cur,
        };
        d = Some(match d {
            Some(prev) => Formula::and(prev, guard),
            None => guard,
        });
        vs.push(v);
    }

    // Every `vᵢ` was minted above, so it is free in no hypothesis of `cur` —
    // there are none — and in nothing but the formula being generalised.
    Some(gen_all(&vs, &cur))
}

