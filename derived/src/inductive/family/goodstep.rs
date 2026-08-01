//! **The `good` recursion's packed step**, and the finding the design predicted:
//! its `step_typed` is **unconditional**.
//!
//! # What is shared, and what is not
//!
//! `INDEXED-DESIGN.md` §3.4 says the `good` recursion is "the existing general
//! W-recursor at one new target", and that is meant literally. The step is the
//! *same* construction as [`crate::inductive::step`] — one Replacement per
//! constructor over `Qᵢ = prod(Aᵢ, prod(FWᵢ, FTᵢ))`, unioned right-nested — with
//! [`Vals::Good`] in the value slot instead of [`Vals::Minor`]:
//!
//! ```text
//! rowᵢ(σ, p) := ⟨⟨Injᵢ(σ), p⟩, Gᵢ(p⃗, σ, π₂p)⟩         — π₁p, the row of
//!                                                       recursive subterms,
//!                                                       is dead
//! e_G(p⃗)     := E₀ ∪ (E₁ ∪ (… ∪ ∅))
//! ```
//!
//! Everything that does not look inside the value is therefore *shared code,
//! not shared shape*: [`crate::inductive::members`] (what is in the step and
//! what is not), [`crate::inductive::values`] (single-valuedness, (S2)) and
//! [`crate::inductive::computes`] ((S1)) are called here unchanged. Only
//! `step_typed` is written afresh, and it is written afresh because it is
//! *smaller*, not because it is different.
//!
//! # (S3) came out unconditional — the design's claim, checked
//!
//! The value recursor's (S3) is the general recursor's one standing hypothesis:
//! `HYP → step_typed`, where `HYP` bundles `n` pointwise minor-typing
//! statements, because `sᵢ` is an arbitrary set and nothing says its
//! applications land in `T`. Here the value is `Gᵢ(p⃗,σ,r)`, which is a
//! Separation out of `Idx(p⃗)` **by its defining axiom**, hence a member of
//! `𝒫(Idx(p⃗))` for every `σ` and every `r` whatsoever
//! ([`GoodValues::in_target`]). So:
//!
//! ```text
//! ⊢ step_typed(A, B, U({A,T′}), 𝒫(Idx(p⃗)), e_G(p⃗))         no antecedent
//! ```
//!
//! and with [`Inductive::closed`](crate::inductive::Inductive::closed) — which
//! the carrier discharges unconditionally at every arity — the `good`
//! recursion's totality and ι carry **no hypothesis at all**. That is the
//! whole of why the indexed carrier is cheap: the branch of the argument that
//! costs the value recursor a `HYP` it cannot discharge without a `T`-policy
//! costs `good` two lines.
//!
//! The price, and it is not zero: `𝒫(Idx(p⃗))` is the *only* target at which
//! this holds, so unlike [`crate::inductive::GenRecursor`] the `good`
//! recursion is not generic in its target and [`Rx::t`] is a term rather than a
//! variable here. Nothing downstream wants it generic.
//!
//! # Interface
//!
//! ```text
//! e_G(p⃗)                                                    [GoodStep::step]
//! ⊢ (σ ∈ Aᵢ ∧ (f ∈ FWᵢ ∧ r ∈ FTᵢ)) →
//!       app(e_G, ⟨Injᵢ(σ),⟨f,r⟩⟩) = Gᵢ(p⃗,σ,r)     (S1)      [GoodStep::computes]
//! ⊢ sv(e_G(p⃗))                                   (S2)      [GoodStep::sv]
//! ⊢ step_typed(A, B, U({A,T′}), 𝒫(Idx(p⃗)), e_G)  (S3)      [GoodStep::step_typed]
//! ```
//!
//! all at the declaration's own parameter variables — `∀`-closed over them by
//! the caller, not here, because [`super::good`] needs them free to compose.

use kernel::{Env, Formula, Term, Thm};

use crate::inductive::carrier::Inductive;
use crate::inductive::computes::step_app;
use crate::inductive::machine::Machine;
use crate::inductive::rec_shared::{
    carry_back, gen_under, hyp_disj_elim, hyp_ex_branch, under,
};
use crate::inductive::step::{Rx, StepSym, Vals};
use crate::inductive::values::step_single_valued;
use crate::wrec::{hyp_congr, hyp_eq_trans};
use crate::{a1i, and_left, and_right, disj_of, gen_all, hyp_and, hyp_mp, inst_all, syl, uncurry};

use super::gval::GoodValues;
use super::index::IndexSpace;
use super::spec::IndexedDeclSpec;

/// The `good` recursion's step and its three schemas.
pub struct GoodStep {
    /// One Replacement symbol per constructor, of arity `np` — no minor and no
    /// target parameter, because `good` has neither.
    pub steps: Vec<StepSym>,
    /// `e_G(p⃗)`, at the declaration's parameters.
    pub step: Term,
    /// (S1) per constructor, generalised over `(σ, f, r)` but **not** over the
    /// parameters.
    pub computes: Vec<Thm>,
    /// (S2), `⊢ sv(e_G(p⃗))`.
    pub sv: Thm,
    /// (S3), `⊢ step_typed(A, B, U({A,T′}), 𝒫(Idx(p⃗)), e_G(p⃗))` —
    /// **unconditional**.
    pub step_typed: Thm,
}

/// The term-forming context the `good` recursion works in: the same [`Rx`] the
/// value recursor uses, with [`Vals::Good`] in the value slot, no minors, and
/// the concrete target `𝒫(Idx(p⃗))`.
///
/// Rebuilt rather than stored, by [`GoodStep::build`] and by
/// [`super::good::Good::build`], because it is a pure term-forming context: the
/// only theorem in it is the union chain's walk, and two calls produce
/// syntactically identical terms.
pub(super) fn good_rx<'a>(
    env: &mut Env,
    mach: &'a Machine,
    ind: &'a Inductive,
    gv: &GoodValues,
    ix: &IndexSpace,
) -> Option<Rx<'a>> {
    Some(Rx {
        mach,
        ind,
        ps: ind.params.iter().map(|v| Term::var(*v)).collect(),
        minors: Vec::new(),
        t: ix.target.clone(),
        bin: crate::sums::mem_bin_union_iff(env, &mach.wt.sums.ap.sets)?,
        vals: Vals::Good(gv.syms.clone()),
    })
}

impl GoodStep {
    /// Build the step and derive (S1), (S2) and (S3).
    pub fn build(
        env: &mut Env,
        mach: &Machine,
        ind: &Inductive,
        spec: &IndexedDeclSpec,
        ix: &IndexSpace,
        gv: &GoodValues,
    ) -> Option<GoodStep> {
        let n = spec.len();
        if n == 0 || gv.syms.len() != n {
            return None
        }
        let cx = good_rx(env, mach, ind, gv, ix)?;
        let steps: Vec<StepSym> =
            (0..n).map(|i| StepSym::new(env, &cx, i, &[])).collect::<Option<_>>()?;

        let sv = step_single_valued(env, &cx, &steps)?;
        let mut computes = Vec::with_capacity(n);
        for i in 0..n {
            let (sig_v, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
            let at = step_app(
                env,
                &cx,
                &steps,
                &sv,
                i,
                &Term::var(sig_v),
                &Term::var(fv),
                &Term::var(rv),
            )?;
            computes.push(gen_all(&[sig_v, fv, rv], &at));
        }
        let step_typed = good_step_typed(env, &cx, &steps, &computes, gv, ix)?;
        let step = cx.step(&steps);
        // The Replacement symbols are the only thing `cx` owns; drop it so the
        // borrow of `mach`/`ind` ends here.
        drop(cx);
        Some(GoodStep { steps, step, computes, sv, step_typed })
    }
}

/// **The branch computation** — `p → app(e_G, ⟨a,⟨f,r⟩⟩) = Gᵢ(p⃗,σ,r)`, given
/// that `a` is the `i`-th injection of `σ` and that `f`/`r` are typed at the
/// fibre over `a`.
///
/// Both consumers of the step's computation rule are this shape: `step_typed`
/// runs it at an arbitrary `a ∈ A` split by `no_junk`, and
/// [`super::vacuous`] runs it at the `⟨a,f⟩` decomposition of an arbitrary
/// element of `W`. Written once, with the ambient hypothesis a parameter, so
/// the two cannot drift.
#[allow(clippy::too_many_arguments)]
pub(super) fn branch_value(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    computes: &[Thm],
    i: usize,
    p: &Formula,
    facts: BranchFacts<'_>,
    a: &Term,
    f: &Term,
    r: &Term,
    sigma: &Term,
) -> Option<Thm> {
    let s = cx.s();
    let ap = cx.ap();
    let fam = cx.ind.fibre.fam.clone();
    let w = cx.w();
    let t = cx.t.clone();
    let finord = cx.finord(i)?;
    let fibre_t = ap.apply(fam.clone(), a.clone());
    let step = cx.step(syms);

    // The fibre at this tag computes to `finord(mᵢ)`.
    let k_acong = hyp_congr(env, facts.eq_tag, |q| ap.apply(fam.clone(), q))?;
    let fib_at = inst_all(&cx.ind.fibre.fibre[i], std::slice::from_ref(sigma))?;
    let k_fib = hyp_eq_trans(env, &k_acong, &syl(facts.in_summand, &fib_at)?)?;

    // `f` and `r` retyped to that domain, then widened into the Replacement's
    // ranges — `fs(d,c) ⊆ 𝒫(prod(d,c))`, no typing side condition.
    let retype = |env: &mut Env, prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
        let cod_c = cod.clone();
        let cong = hyp_congr(env, &k_fib, move |q| s.fs.of(q, cod_c.clone()))?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            s.fs.of(fibre_t.clone(), cod.clone()),
            s.fs.of(finord.clone(), cod.clone()),
            hole,
            Formula::mem(g.clone(), Term::var(hole)),
        );
        hyp_mp(&hyp_mp(&a1i(&leib, p.clone()), &cong)?, prem)
    };
    let widen = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
        let inc = inst_all(&s.fs.fs_sub, &[finord.clone(), cod.clone()])?;
        let at = Thm::mp(&Thm::ax_inst(inc.concl().clone(), g.clone())?, &inc)?;
        syl(prem, &at)
    };
    let k_f = retype(env, facts.f_typed, &w, f)?;
    let k_r = retype(env, facts.r_typed, &t, r)?;
    let k_fw = widen(&k_f, &w, f)?;
    let k_ft = widen(&k_r, &t, r)?;

    // Rewrite the key's tag, then (S1).
    let triple = |x: &Term| {
        ap.apply(step.clone(), ap.sets.pair(x.clone(), ap.sets.pair(f.clone(), r.clone())))
    };
    let k_tag = hyp_congr(env, facts.eq_tag, |q| triple(&q))?;
    let k_app = hyp_mp(
        &a1i(
            &inst_all(&computes[i], &[sigma.clone(), f.clone(), r.clone()])?,
            p.clone(),
        ),
        &hyp_and(facts.in_summand, &hyp_and(&k_fw, &k_ft)?)?,
    )?;
    hyp_eq_trans(env, &k_tag, &k_app)
}

/// The four facts [`branch_value`] needs, each in `p → …` form.
#[derive(Clone, Copy)]
pub(super) struct BranchFacts<'a> {
    /// `p → σ ∈ Aᵢ`.
    pub(super) in_summand: &'a Thm,
    /// `p → a = Injᵢ(σ)`.
    pub(super) eq_tag: &'a Thm,
    /// `p → f ∈ fs(app(B,a), W)`.
    pub(super) f_typed: &'a Thm,
    /// `p → r ∈ fs(app(B,a), 𝒫(Idx(p⃗)))`.
    pub(super) r_typed: &'a Thm,
}

/// (S3), **unconditional**: `⊢ step_typed(A, B, U({A,T′}), 𝒫(Idx(p⃗)), e_G)`.
fn good_step_typed(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    computes: &[Thm],
    gv: &GoodValues,
    ix: &IndexSpace,
) -> Option<Thm> {
    let s = cx.s();
    let ap = cx.ap();
    let wt = &cx.mach.wt;
    let n = cx.n();
    let tags = cx.ind.tags.clone();
    let fam = cx.ind.fibre.fam.clone();
    let u = cx.ind.bound.clone();
    let w = cx.w();
    let t = cx.t.clone();
    let step = cx.step(syms);

    let (av, fv, rv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tr) = (Term::var(av), Term::var(fv), Term::var(rv));
    let fibre_t = ap.apply(fam.clone(), ta.clone());

    let ma = Formula::mem(ta.clone(), tags.clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre_t.clone(), w.clone()));
    let mr = Formula::mem(tr.clone(), s.fs.of(fibre_t, t.clone()));
    let front = Formula::and(ma.clone(), mf.clone());
    let p = Formula::and(front.clone(), mr.clone());

    let p_front = and_left(front.clone(), mr.clone());
    let p_mr = and_right(front.clone(), mr.clone());
    let p_ma = syl(&p_front, &and_left(ma.clone(), mf.clone()))?;
    let p_mf = syl(&p_front, &and_right(ma.clone(), mf))?;

    let goal = Formula::mem(
        ap.apply(step, ap.sets.pair(ta.clone(), ap.sets.pair(tf.clone(), tr.clone()))),
        t.clone(),
    );

    // ── no_junk splits the tag ──────────────────────────────────────────────
    let nj = cx.mach.syms.no_junk(env, s, n)?;
    let mut nj_args: Vec<Term> = cx.ind.summands.clone();
    nj_args.push(ta.clone());
    let nj_at = inst_all(&nj, &nj_args)?;
    let sigvs: Vec<kernel::FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
    let bodies: Vec<Formula> = (0..n)
        .map(|i| {
            let tsig = Term::var(sigvs[i]);
            Some(Formula::and(
                Formula::mem(tsig.clone(), cx.summand(i)),
                Formula::eq(ta.clone(), cx.mach.syms.inj(i, tsig)?),
            ))
        })
        .collect::<Option<_>>()?;
    let disjuncts: Vec<Formula> =
        (0..n).map(|i| Formula::exists(sigvs[i], bodies[i].clone())).collect();
    if *nj_at.concl() != Formula::imp(ma, disj_of(&disjuncts)?) {
        return None
    }
    let cases = syl(&p_ma, &nj_at)?;

    // ── the `n` branches, each closing on an unconditional membership ───────
    let ps: Vec<Term> = cx.ps.clone();
    let mut branches = Vec::with_capacity(n);
    for i in 0..n {
        let tsig = Term::var(sigvs[i]);
        let k = Formula::and(p.clone(), bodies[i].clone());
        let k_p = and_left(p.clone(), bodies[i].clone());
        let k_body = and_right(p.clone(), bodies[i].clone());
        let mem_sig = Formula::mem(tsig.clone(), cx.summand(i));
        let eq_a = Formula::eq(ta.clone(), cx.mach.syms.inj(i, tsig.clone())?);
        let k_sig = syl(&k_body, &and_left(mem_sig.clone(), eq_a.clone()))?;
        let k_a = syl(&k_body, &and_right(mem_sig, eq_a))?;
        let k_mf = syl(&k_p, &p_mf)?;
        let k_mr = syl(&k_p, &p_mr)?;

        let k_val = branch_value(
            env,
            cx,
            syms,
            computes,
            i,
            &k,
            BranchFacts {
                in_summand: &k_sig,
                eq_tag: &k_a,
                f_typed: &k_mf,
                r_typed: &k_mr,
            },
            &ta,
            &tf,
            &tr,
            &tsig,
        )?;

        // **The whole of (S3):** the value is a Separation subset of `Idx(p⃗)`.
        let mut ga = ps.clone();
        ga.push(tsig.clone());
        ga.push(tr.clone());
        let k_in_t = under(&inst_all(&gv.in_target[i], &ga)?, &k);
        if *k_in_t.concl()
            != Formula::imp(
                k.clone(),
                Formula::mem(gv.of(i, &ps, &tsig, &tr)?, ix.target.clone()),
            )
        {
            return None
        }

        let k_goal = carry_back(env, &k_val, &k_in_t, &t)?;
        branches.push(hyp_ex_branch(sigvs[i], &k_goal, &p, &goal)?);
    }

    let body = hyp_disj_elim(&cases, &p, &branches)?;

    // ── regeneralise into `step_typed`'s own shape, with no antecedent ──────
    let over_r = gen_under(rv, &front, &uncurry(&body)?)?;
    let out = Thm::gen(av, &gen_under(fv, &Formula::mem(ta, tags.clone()), &uncurry(&over_r)?)?);
    if *out.concl() != crate::wrec_total::step_typed(env, s, wt, &tags, &fam, &u, &t, &cx.step(syms))
    {
        return None
    }
    Some(out)
}
