//! **`bnd` is closed under the binary sum**, and hence under the iterated one
//! the general inductive translation puts on a constructor's tag.
//!
//! # Interface
//!
//! Writing `bnd` for [`super::bounded::bnd`], `{t} × a` for the tagged copy the
//! sum is built out of, and `Sum_m(A⃗)` for
//! [`ISumSyms::sum`](crate::isum::ISumSyms::sum):
//!
//! ```text
//! ⊢ ∀t ∀a. (bnd(a) → bnd({t} × a))                            [bnd_tagged_copy]
//! ⊢ ∀a ∀b. ((bnd(a) ∧ bnd(b)) → bnd(a + b))                   [bnd_sum]
//! ⊢ bnd(Sum_m(A⃗))    from  ⊢ bnd(A₀) … ⊢ bnd(A_{m-1})          [bnd_isum]
//! ```
//!
//! all at a free seed `S`, so each is really `∀S`. [`bnd_isums`] is the last at
//! a whole declaration's constructors, deriving the first two **once** rather
//! than per constructor — the split [`super::bnd_finords`] makes over
//! [`mod@super::finite`]'s three lemmas, and for the same reason: the first two
//! do not depend on `m`, and one of them **mints two symbols**.
//!
//! # What this is for
//!
//! [`crate::cumul::DeclUniverse`] asks `bnd(vᵢ)` of every fibre value.
//! §5.2's recursive-argument rule (`thesis.txt:1800`) makes that value
//! `Sum_{mᵢ}(Σ(z::γ₀) … Σ(z::γ_{mᵢ-1}))`
//! ([`fibre_values`](crate::inductive::carrier::fibre_values)); when every `γⱼ`
//! is empty every summand is `1` and the value is *literally* `finord(mᵢ)`,
//! which [`mod@super::finord`] already handles. One non-empty `γⱼ` — a
//! **function-typed recursive argument**, `RTree.node : (Bool → RTree) → RTree`
//! — and the summand is a telescope's type instead, which no arity can name.
//!
//! This file is the general statement: `bnd` of an iterated sum, given `bnd` of
//! each summand. `bnd(finord(m))` is the instance where each of those is
//! [`super::finite::bnd_singleton`] at `∅`, because `1` **is** `{∅}`.
//!
//! # The route, and the two things it is *not*
//!
//! `A + B` is not an abstract coproduct here: it is **definitionally**
//! `({∅} × A) ∪ ({1} × B)` (`crate::sums`'s `sum_body`, one
//! [`crate::define_abbrev`]). So the merge — the one genuinely hard step, and
//! the only place [`super::Stages::directed`] is needed — is
//! [`super::finite::bnd_bin_union`], **which is already built**, and what is
//! left is one lemma about a single tagged copy, which needs no merge at all:
//! one `p` serves, because `{t} × a` has exactly `a`'s worth of points.
//!
//! Two routes were considered and are not taken.
//!
//! * **`bnd(a) → bnd(inl"a)`, the image.** `inl"a` is the same set as
//!   `{∅} × a`, but naming it as an image costs a fresh symbol and a fresh
//!   Replacement instance per declaration, and then `A + B = inl"A ∪ inr"B`
//!   has to be proved. Going through the *product* costs neither: the term is
//!   already the one `sum_def` unfolds to, and
//!   [`crate::sums::tagged_copy_members`] already inverts membership in it in
//!   both directions.
//! * **Transport along a surjection.** Declined, and the reason is now
//!   [`mod@super::pullback`]'s header rather than this one: `⟨t,·⟩` is a *term
//!   former*, which composes with `app(g,·)` for free, and a set function does
//!   not. `bnd_tagged_copy` is the first of that file's three instances.
//!
//! # The one hypothesis a caller cannot fake
//!
//! `bnd(Aⱼ)` is required **unconditional**, and that is not a convenience. A
//! summand mentioning a declaration's parameter — the genuinely infinitary
//! `α → T α`, whose summand is `⟦α⟧` — has no `bnd` to give under
//! `α ∈ U₁` either: [`mod@super::bounded`]'s header records that `bnd(k)` is
//! *refutable* at an infinite `k`, and `α := ⟦Nat⟧` is such an instance. So a
//! summand whose universe membership needs the declaration's antecedent `H` is
//! exactly a summand whose `bnd` is unavailable at any `H`, and the two
//! per-summand obligations stand or fall together. Requiring `⊢` with nothing
//! on the left, and no antecedent in the conclusion, loses nothing that is
//! true.
//!
//! # Nothing here is an axiom
//!
//! [`bnd_tagged_copy`] introduces two symbols — a
//! [`crate::define_abbrev`] body `co(g,t,x) = app(g,⟨t,x⟩)` and its
//! [`crate::funcs::lambda_n`] graph, one Replacement instance — and nothing
//! else does. Both are minted inside [`mod@super::pullback`], which is the only
//! place in this directory that mints them. Every caller-supplied theorem is
//! checked for the conclusion it must have **and** for an empty hypothesis set.

use kernel::{Env, Formula, Term, Thm};

use crate::isum::{isum_of, ISumSyms};
use crate::recursion::Rec;
use crate::sums::{tagged_copy_members, Sums};
use crate::{
    a1i, and_left, and_right, eq_symm, exists_intro_imp, hyp_and, hyp_mp, iff_mp, iff_mpr,
    imp_refl, inst_all, singleton, syl,
};

use super::bounded::bnd;
use super::pullback::bnd_via_pullback;
use super::stages::Stages;

/// **`⊢ ∀t ∀a. (bnd(a) → bnd({t} × a))`** — a tagged copy is no bigger than
/// what it copies.
///
/// [`super::pullback::bnd_via_pullback`] at `mk(x) = ⟨t,x⟩`, with `t` as the
/// former's one parameter, and both directions of
/// [`crate::sums::tagged_copy_members`] as its two inputs: `{t} × a`'s members
/// are exactly the `⟨t,y⟩` with `y ∈ a`, so the introduction is the `mpr`
/// direction at the witness `y := b` and the inversion is the `mp` direction on
/// the nose. **One stage, no merge** — the pullback and the original have the
/// same values.
///
/// `t` and `a` are generalised *after* the pullback, which is why the shared
/// derivation concludes an implication: `a` is a variable here and a proved
/// `⊢ bnd(a)` does not exist.
///
/// `r` must share its `Apply` with `s`; the guard is that `r.zero()` and
/// `s.zero()` are the same term, since every set former below is taken from one
/// of the two.
pub fn bnd_tagged_copy(env: &mut Env, r: &Rec, st: &Stages, s: &Sums) -> Option<Thm> {
    if r.zero() != s.zero() {
        return None
    }
    let sets = s.ap.sets.clone();
    let up = sets.up;

    let (tv, av) = (env.fresh_var(), env.fresh_var());
    let (tt, ta) = (Term::var(tv), Term::var(av));
    let tc = s.prod.of(singleton(up, tt.clone()), ta.clone());
    let mk = |x: &Term| sets.pair(tt.clone(), x.clone());

    let tagged = tagged_copy_members(env, &sets, &s.ap.mem_sing, &s.prod)?;

    // `⊢ ∀z. (z ∈ a → ⟨t,z⟩ ∈ {t}×a)`, witnessing the existential at `y := z`.
    let (zv, yv) = (env.fresh_var(), env.fresh_var());
    let (tz, ty) = (Term::var(zv), Term::var(yv));
    let intro = {
        let mem_z = Formula::mem(tz.clone(), ta.clone());
        let body = Formula::and(
            Formula::mem(ty.clone(), ta.clone()),
            Formula::eq(mk(&tz), mk(&ty)),
        );
        let witness =
            hyp_and(&imp_refl(mem_z.clone()), &a1i(&Thm::eq_refl(mk(&tz)), mem_z.clone()))?;
        Thm::gen(
            zv,
            &syl(
                &syl(&witness, &exists_intro_imp(yv, body, tz.clone())?)?,
                &iff_mpr(&inst_all(&tagged, &[tt.clone(), ta.clone(), mk(&tz)])?)?,
            )?,
        )
    };

    // `⊢ ∀z. (z ∈ {t}×a → ∃y. (y ∈ a ∧ z = ⟨t,y⟩))` — the same iff, forwards.
    let inversion = Thm::gen(
        zv,
        &iff_mp(&inst_all(&tagged, &[tt.clone(), ta.clone(), tz.clone()])?)?,
    );

    let core = bnd_via_pullback(env, r, st, &[tv], &ta, &tc, &mk, &intro, &inversion)?;
    let out = Thm::gen(tv, &Thm::gen(av, &core));

    let expected = Formula::forall(
        tv,
        Formula::forall(
            av,
            Formula::imp(bnd(env, r, st, &ta), bnd(env, r, st, &tc)),
        ),
    );
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}

/// **`⊢ ∀a ∀b. ((bnd(a) ∧ bnd(b)) → bnd(a + b))`** — `bnd` survives the binary
/// sum.
///
/// Three steps, of which only the first is new: [`bnd_tagged_copy`] at each of
/// the sum's two halves, [`super::finite::bnd_bin_union`] to merge the stages,
/// and `sum_def` — the sum's *defining equation*, `A + B = ({∅}×A) ∪ ({1}×B)` —
/// carried by Leibniz. There is no coproduct reasoning anywhere: the union is
/// the term, not a description of it.
pub fn bnd_sum(env: &mut Env, r: &Rec, st: &Stages, s: &Sums) -> Option<Thm> {
    let copy = bnd_tagged_copy(env, r, st, s)?;
    let union = super::finite::bnd_bin_union(env, r, st)?;
    bnd_sum_over(env, r, st, s, &copy, &union)
}

/// [`bnd_sum`] over lemmas the caller already has.
fn bnd_sum_over(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    s: &Sums,
    copy: &Thm,
    union: &Thm,
) -> Option<Thm> {
    let sets = s.ap.sets.clone();
    let (av, bv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));

    let bnd_a = bnd(env, r, st, &ta);
    let bnd_b = bnd(env, r, st, &tb);
    let k = Formula::and(bnd_a.clone(), bnd_b.clone());

    let cl = s.prod.of(singleton(sets.up, s.zero()), ta.clone());
    let cr = s.prod.of(singleton(sets.up, s.unit()), tb.clone());
    let un = crate::funspace::bin_union(&sets, cl.clone(), cr.clone());

    let k_left = syl(
        &and_left(bnd_a.clone(), bnd_b.clone()),
        &inst_all(copy, &[s.zero(), ta.clone()])?,
    )?;
    let k_right = syl(
        &and_right(bnd_a.clone(), bnd_b.clone()),
        &inst_all(copy, &[s.unit(), tb.clone()])?,
    )?;
    let k_un = hyp_mp(
        &a1i(&inst_all(union, &[cl.clone(), cr.clone()])?, k.clone()),
        &hyp_and(&k_left, &k_right)?,
    )?;
    if *k_un.concl() != Formula::imp(k.clone(), bnd(env, r, st, &un)) {
        return None
    }

    // `a + b = ({∅}×a) ∪ ({1}×b)`, run backwards onto the symbol.
    let sum_here = s.sum_of(ta.clone(), tb.clone());
    let def_at = inst_all(&s.sum_def, &[ta.clone(), tb.clone()])?;
    if *def_at.concl() != Formula::eq(sum_here.clone(), un.clone()) {
        return None
    }
    let onto = Thm::mp(
        &Thm::eq_leibniz(un, sum_here.clone(), wv, bnd(env, r, st, &Term::var(wv))),
        &eq_symm(env, &def_at)?,
    )?;
    let out = Thm::gen(av, &Thm::gen(bv, &syl(&k_un, &onto)?));

    let expected = Formula::forall(
        av,
        Formula::forall(bv, Formula::imp(k, bnd(env, r, st, &sum_here))),
    );
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}

/// **`⊢ bnd(Sum_m(A⃗))`** — the fibre value of a constructor whose recursive
/// arguments have arbitrary domains.
///
/// `bnds[j]` must be `⊢ bnd(Aⱼ)` at `summands[j]`, unconditional and with an
/// empty hypothesis set; both are checked. See the module header for why the
/// unconditionality is not a restriction on anything true.
///
/// `sum2` must be [`bnd_sum`] — a caller with several constructors derives it
/// once and passes it here, which is what [`bnd_isums`] does.
///
/// `syms` must have been [`ISumSyms::ensure`]d to arity `m` over `s`. The fold
/// proves membership of the *nest* `A₀ + (… + 0)` and the last step moves it
/// onto the **symbol** `Sum_m(A⃗)` through
/// [`sum_ax`](ISumSyms::sum_ax) — which matters most at `m = 0`, where the nest
/// is the term `∅` and `Sum_0()` is a symbol that is not syntactically `∅`.
#[allow(clippy::too_many_arguments)]
pub fn bnd_isum(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    s: &Sums,
    syms: &ISumSyms,
    sum2: &Thm,
    summands: &[Term],
    bnds: &[Thm],
) -> Option<Thm> {
    if !syms.is_over(s) || r.zero() != s.zero() || summands.len() != bnds.len() {
        return None
    }
    let m = summands.len();
    for j in 0..m {
        if !bnds[j].hyps().is_empty() || *bnds[j].concl() != bnd(env, r, st, &summands[j]) {
            return None
        }
    }

    let mut acc = super::finite::bnd_empty(env, r, st)?;
    for j in (0..m).rev() {
        let tail = isum_of(s, &summands[j + 1..]);
        let at = inst_all(sum2, &[summands[j].clone(), tail.clone()])?;
        acc = Thm::mp(&at, &crate::and_intro(&bnds[j], &acc))?;
    }
    let nest = isum_of(s, summands);
    if *acc.concl() != bnd(env, r, st, &nest) {
        return None
    }

    // ── the nest becomes the symbol `Sum_m(A⃗)` ──────────────────────────────
    let sigma = syms.sum(summands)?;
    let ax = inst_all(syms.sum_ax(m)?, summands)?;
    if *ax.concl() != Formula::eq(sigma.clone(), nest.clone()) {
        return None
    }
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(nest, sigma.clone(), hole, bnd(env, r, st, &Term::var(hole)));
    let out = Thm::mp(&Thm::mp(&leib, &eq_symm(env, &ax)?)?, &acc)?;

    let expected = bnd(env, r, st, &sigma);
    (out.hyps().is_empty() && *out.concl() == expected).then_some(out)
}

/// [`bnd_isum`] at every constructor of a declaration, over **one** `bnd_sum`.
///
/// `summands[i]` and `bnds[i]` are the `i`-th constructor's fibre summands and
/// their `bnd`s — the shape
/// [`fibre_summands`](crate::inductive::carrier::fibre_summands) hands back.
///
/// `sum2` is passed rather than derived because [`bnd_tagged_copy`] **mints two
/// symbols and one Replacement instance**: deriving it per constructor would
/// not merely repeat work, it would leave `n − 1` redundant symbols in the
/// signature. [`crate::cumul::IndChain`] holds one for the whole client, which
/// is the same discipline [`crate::isum::SumClosure`] already has.
#[allow(clippy::too_many_arguments)]
pub fn bnd_isums(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    s: &Sums,
    syms: &ISumSyms,
    sum2: &Thm,
    summands: &[Vec<Term>],
    bnds: &[Vec<Thm>],
) -> Option<Vec<Thm>> {
    if summands.len() != bnds.len() {
        return None
    }
    (0..summands.len())
        .map(|i| bnd_isum(env, r, st, s, syms, sum2, &summands[i], &bnds[i]))
        .collect()
}

/// `⊢ bnd(1)` — the unit summand a *plain* recursive argument contributes.
///
/// [`super::finite::bnd_singleton`] at `∅`, because `1` **is** `{∅}`. This is
/// the whole of what makes [`bnd_isum`] subsume [`super::bnd_finord`]: at `m`
/// copies of this the conclusion is `bnd(Sum_m(1,…,1))`, which is
/// `bnd(finord(m))` at the same term.
pub fn bnd_unit(env: &mut Env, r: &Rec, st: &Stages, s: &Sums) -> Option<Thm> {
    if r.zero() != s.zero() {
        return None
    }
    let sing = super::finite::bnd_singleton(env, r, st)?;
    let out = inst_all(&sing, std::slice::from_ref(&s.zero()))?;
    (out.hyps().is_empty() && *out.concl() == bnd(env, r, st, &s.unit())).then_some(out)
}
