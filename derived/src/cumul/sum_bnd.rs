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
//! * **Transport along a surjection.** [`mod@super::finite`]'s header declines
//!   it, and correctly: `bnd(k)` speaks of `app(g,b)`, so moving it along
//!   `h ∈ fs(k,X)` needs the composite `g ∘ h` **as a set**. At `inl`
//!   specifically there is no composite to form, because the map is a *term
//!   former* rather than a set function: `λx. app(g, ⟨t,x⟩)` is one
//!   [`crate::funcs::lambda_n`] graph over a [`crate::define_abbrev`] body, and
//!   [`crate::funcs::beta_conditional_n`] computes it on the domain. That
//!   asymmetry — a symbol composes for free, a set does not — is the whole
//!   reason this case is cheap and the general one is not.
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
//! else does. Every caller-supplied theorem is checked for the conclusion it
//! must have **and** for an empty hypothesis set.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::{beta_conditional_n, lambda_n};
use crate::funspace::discharge;
use crate::isum::{isum_of, ISumSyms};
use crate::recursion::hyp::hyp_eq_trans;
use crate::recursion::Rec;
use crate::sums::{tagged_copy_members, Sums};
use crate::{
    a1i, and_left, and_right, define_abbrev, eq_symm, eq_symm_imp, exists_intro_imp, hyp_and,
    hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, singleton, syl,
};

use super::bounded::bnd;
use super::finite::Bnd;
use super::stages::Stages;
use super::step::curry;

/// **`⊢ ∀t ∀a. (bnd(a) → bnd({t} × a))`** — a tagged copy is no bigger than
/// what it copies.
///
/// The family `g` on `{t} × a` is pulled back to a family on `a` by
/// `x ↦ app(g, ⟨t,x⟩)`, which is one lambda graph; the stage that bounds the
/// pullback bounds `g`, because [`crate::sums::tagged_copy_members`] says every
/// member of `{t} × a` **is** some `⟨t,y⟩` with `y ∈ a`. **One stage, no
/// merge** — the pullback and the original have the same values.
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

    // ── the pullback's graph: `co(g,t,x) = app(g,⟨t,x⟩)`, and `λx. co(g,t,x)` ─
    let (g0, t0, x0) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let co_body = r.apply(Term::var(g0), sets.pair(Term::var(t0), Term::var(x0)));
    let (co, co_ax) = define_abbrev(env, &[g0, t0, x0], &co_body)?;
    let (lam, lam_ax) = lambda_n(env, &r.ap, co)?;
    let beta = beta_conditional_n(env, &r.ap, co, lam, &lam_ax)?;

    let d = Bnd::new(env, r, st);
    let (tv, av, pv2, yv, wv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tt, ta, tp, ty) = (Term::var(tv), Term::var(av), Term::var(pv2), Term::var(yv));
    let tb = Term::var(d.bv);
    let tg = Term::var(d.gv);
    let tower = st.tower_set();

    // `{t} × a`, and the pullback `G = λx ∈ a. app(g,⟨t,x⟩)`.
    let tc = s.prod.of(singleton(up, tt.clone()), ta.clone());
    let gterm = Term::apply(lam, vec![tg.clone(), tt.clone(), ta.clone()]);
    let sub = |f: Formula| f.subst(d.gv, &gterm);

    let tagged = tagged_copy_members(env, &sets, &s.ap.mem_sing, &s.prod)?;

    // `⊢ x ∈ a → app(G,x) = app(g,⟨t,x⟩)` — **the β step**, at the two points
    // this derivation reduces the pullback at: the bound variable of the
    // hypothesis, and the witness the tagged copy's membership hands back.
    let beta_at = |env: &mut Env, x: &Term| -> Option<Thm> {
        let e1 = inst_all(&beta, &[tg.clone(), tt.clone(), ta.clone(), x.clone()])?;
        let e2 = a1i(
            &inst_all(&co_ax, &[tg.clone(), tt.clone(), x.clone()])?,
            Formula::mem(x.clone(), ta.clone()),
        );
        hyp_eq_trans(env, &e1, &e2)
    };
    let beta_b = beta_at(env, &tb)?;
    let beta_y = beta_at(env, &ty)?;

    let k = d.all(env, &ta); // `bnd(a)`
    let h = d.hyp(&tc); // `∀b. (b ∈ {t}×a → app(g,b) ∈ T)`
    let j0 = Formula::and(k.clone(), h.clone());
    let j0_k = and_left(k.clone(), h.clone());
    let j0_h = and_right(k.clone(), h.clone());

    // ── the pullback inherits the hypothesis ────────────────────────────────
    //
    // `J0 ∧ b ∈ a ⊢ app(G,b) ∈ T`, from `⟨t,b⟩ ∈ {t}×a` and one β step.
    let pair_b = sets.pair(tt.clone(), tb.clone());
    let jb = Formula::and(j0.clone(), Formula::mem(tb.clone(), ta.clone()));
    let jb_j0 = and_left(j0.clone(), Formula::mem(tb.clone(), ta.clone()));
    let jb_b = and_right(j0.clone(), Formula::mem(tb.clone(), ta.clone()));

    // `b ∈ a → ⟨t,b⟩ ∈ {t}×a`, witnessing the existential at `y := b`.
    let into_tc = {
        let mem_b = Formula::mem(tb.clone(), ta.clone());
        let body = Formula::and(
            Formula::mem(ty.clone(), ta.clone()),
            Formula::eq(pair_b.clone(), sets.pair(tt.clone(), ty.clone())),
        );
        let witness = hyp_and(
            &imp_refl(mem_b.clone()),
            &a1i(&Thm::eq_refl(pair_b.clone()), mem_b.clone()),
        )?;
        syl(
            &syl(&witness, &exists_intro_imp(yv, body, tb.clone())?)?,
            &iff_mpr(&inst_all(&tagged, &[tt.clone(), ta.clone(), pair_b.clone()])?)?,
        )?
    };

    let jb_pair_in = syl(&jb_b, &into_tc)?;
    let jb_gt = hyp_mp(
        &syl(&syl(&jb_j0, &j0_h)?, &Thm::ax_inst(h.clone(), pair_b.clone())?)?,
        &jb_pair_in,
    )?;
    // `app(g,⟨t,b⟩) = app(G,b)` — the β step, run backwards.
    let jb_eq = syl(
        &jb_b,
        &syl(
            &beta_b,
            &eq_symm_imp(env, r.apply(gterm.clone(), tb.clone()), r.apply(tg.clone(), pair_b.clone())),
        )?,
    )?;
    let jb_goal = hyp_mp(
        &syl(
            &jb_eq,
            &Thm::eq_leibniz(
                r.apply(tg.clone(), pair_b.clone()),
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
    let hyp_g = sub(d.hyp(&ta));
    let j0_hyp_g = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j0.clone(),
            Formula::imp(
                Formula::mem(tb.clone(), ta.clone()),
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
    let e1 = sub(d.body(&ta, &tp));
    if *j0_ex.concl() != Formula::imp(j0.clone(), Formula::exists(pv2, e1.clone())) {
        return None
    }

    let j1 = Formula::and(j0.clone(), e1.clone());
    let j1_e1 = and_right(j0.clone(), e1.clone());
    let p_om = Formula::mem(tp.clone(), r.omega());
    let cov = sub(d.all_in(&ta, &d.v(tp.clone())));
    let j1_p = syl(&j1_e1, &and_left(p_om.clone(), cov.clone()))?;
    let j1_cov = syl(&j1_e1, &and_right(p_om, cov.clone()))?;

    // ── every member of `{t}×a` is a `⟨t,y⟩`, so the same stage covers it ────
    let b_in = Formula::mem(tb.clone(), tc.clone());
    let j2 = Formula::and(j1.clone(), b_in.clone());
    let j2_j1 = and_left(j1.clone(), b_in.clone());
    let j2_b = and_right(j1.clone(), b_in.clone());
    let pair_y = sets.pair(tt.clone(), ty.clone());
    let w = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::eq(tb.clone(), pair_y.clone()),
    );
    let j2_ex = syl(
        &j2_b,
        &iff_mp(&inst_all(&tagged, &[tt.clone(), ta.clone(), tb.clone()])?)?,
    )?;
    if *j2_ex.concl() != Formula::imp(j2.clone(), Formula::exists(yv, w.clone())) {
        return None
    }

    let j3 = Formula::and(j2.clone(), w.clone());
    let j3_j2 = and_left(j2.clone(), w.clone());
    let j3_w = and_right(j2.clone(), w.clone());
    let j3_y = syl(&j3_w, &and_left(Formula::mem(ty.clone(), ta.clone()), Formula::eq(tb.clone(), pair_y.clone())))?;
    let j3_eq = syl(&j3_w, &and_right(Formula::mem(ty.clone(), ta.clone()), Formula::eq(tb.clone(), pair_y.clone())))?;

    let stage = d.v(tp.clone());
    // `app(G,y) ∈ Vₚ`, then the β step forwards, then `b = ⟨t,y⟩` backwards.
    let j3_cov_y = hyp_mp(
        &syl(
            &syl(&j3_j2, &syl(&j2_j1, &j1_cov)?)?,
            &Thm::ax_inst(cov.clone(), ty.clone())?,
        )?,
        &j3_y,
    )?;
    let j3_beta = syl(&j3_y, &beta_y)?;
    let j3_at_pair = hyp_mp(
        &syl(
            &j3_beta,
            &Thm::eq_leibniz(
                r.apply(gterm.clone(), ty.clone()),
                r.apply(tg.clone(), pair_y.clone()),
                wv,
                Formula::mem(Term::var(wv), stage.clone()),
            ),
        )?,
        &j3_cov_y,
    )?;
    let j3_goal = hyp_mp(
        &syl(
            &crate::recursion::hyp::hyp_eq_symm(env, &j3_eq)?,
            &Thm::eq_leibniz(
                pair_y.clone(),
                tb.clone(),
                wv,
                Formula::mem(r.apply(tg.clone(), Term::var(wv)), stage.clone()),
            ),
        )?,
        &j3_at_pair,
    )?;
    if *j3_goal.concl()
        != Formula::imp(j3, Formula::mem(r.apply(tg.clone(), tb.clone()), stage.clone()))
    {
        return None
    }
    let j2_goal = discharge(yv, &j2_ex, &j3_goal)?;
    let j1_cov_tc = Thm::mp(
        &Thm::ax_dist(
            d.bv,
            j1.clone(),
            Formula::imp(b_in, Formula::mem(r.apply(tg.clone(), tb.clone()), stage)),
        )?,
        &Thm::gen(d.bv, &curry(&j2_goal)?),
    )?;
    if *j1_cov_tc.concl() != Formula::imp(j1.clone(), d.all_in(&tc, &d.v(tp.clone()))) {
        return None
    }

    let j1_goal = syl(
        &hyp_and(&j1_p, &j1_cov_tc)?,
        &exists_intro_imp(d.pv, d.body(&tc, &Term::var(d.pv)), tp.clone())?,
    )?;
    let j0_goal = discharge(pv2, &j0_ex, &j1_goal)?;

    let out = Thm::gen(
        tv,
        &Thm::gen(
            av,
            &Thm::mp(
                &Thm::ax_dist(d.gv, k.clone(), Formula::imp(h.clone(), d.ex(&tc)))?,
                &Thm::gen(d.gv, &curry(&j0_goal)?),
            )?,
        ),
    );

    let expected =
        Formula::forall(tv, Formula::forall(av, Formula::imp(k, d.all(env, &tc))));
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

/// [`bnd_sum`] over lemmas the caller already has — see [`bnd_isums`] for why
/// the split exists.
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

/// [`bnd_isum`] at every constructor of a declaration, deriving
/// [`bnd_tagged_copy`] and [`super::finite::bnd_bin_union`] **once**.
///
/// `summands[i]` and `bnds[i]` are the `i`-th constructor's fibre summands and
/// their `bnd`s — the shape
/// [`fibre_summands`](crate::inductive::carrier::fibre_summands) hands back.
/// Re-deriving the two closure lemmas per constructor is the only thing that
/// would make this quadratic in the declaration, and [`bnd_tagged_copy`] mints
/// symbols, so it would also leave `n − 1` redundant ones in the signature.
pub fn bnd_isums(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    s: &Sums,
    syms: &ISumSyms,
    summands: &[Vec<Term>],
    bnds: &[Vec<Thm>],
) -> Option<Vec<Thm>> {
    if summands.len() != bnds.len() {
        return None
    }
    let copy = bnd_tagged_copy(env, r, st, s)?;
    let union = super::finite::bnd_bin_union(env, r, st)?;
    let sum2 = bnd_sum_over(env, r, st, s, &copy, &union)?;
    (0..summands.len())
        .map(|i| bnd_isum(env, r, st, s, syms, &sum2, &summands[i], &bnds[i]))
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
