//! The general ι rules — (S4), one per constructor: **the deliverable**.
//!
//! ```text
//! ⊢ ∀p⃗ ∀s⃗ ∀T ∀y⃗ ∀t⃗. ((HYP ∧ Hᵢ^ctor) →
//!     app(grec(p⃗,s⃗,T), ctorᵢ(y⃗,t⃗))
//!       = sᵢ ⟪y⃗, t⃗ in declared order⟫ app(grec, t₀) … app(grec, t_{m−1}))
//! ```
//!
//! with every recursive call live, every field live, at every arity, and the
//! hypotheses exactly `HYP` plus the constructor's own argument typings —
//! `Hᵢ^ctor` is [`super::carrier::ctor_atoms`], the same conjunction the
//! carrier's constructor rule carries, with the recursive arguments typed at
//! the Lean-facing `ind(p⃗)`.
//!
//! # The argument, in the design's numbering (§4.2 steps 3–5)
//!
//! Fire [`crate::wrec_total`]'s unguarded ι at `a := Injᵢ(tuple y⃗)`,
//! `f := recfun(t⃗)` under `closed ∧ step_typed` (the carrier's `closed`, and
//! (S3) under `HYP`); rewrite the composite's domain along the fibre
//! equation; compute the step there by (S1), whose one non-trivial
//! membership — `comp(grec, recfun, finord(mᵢ)) ∈ FTᵢ` — comes from
//! `composite_typed` with its value premise discharged by two applications of
//! the function-space application rule; then read the components back:
//! `compⱼ(tuple y⃗) = yⱼ` by literal projections, `app(recfun, Injⱼ(•)) = tⱼ`
//! by [`crate::recarg::RecArg::app`], and
//! `app(comp, Injⱼ(•)) = app(grec, tⱼ)` by `composite_app` chained with the
//! same. Nothing needs a new proof idea; every step is an instance of a lemma
//! that exists, looped.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::recarg::RecArg;
use crate::sigma::Telescope;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wrec_total::Recursor;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, conj_sub, eq_trans, hyp_and, hyp_mp, imp_refl,
    inst_all, syl, uncurry,
};

use super::carrier::ctor_atoms;
use super::rec_shared::{carry_under, congr_ctx, gen_under, hyp_conj, hyp_inst, rewrite_under, under};
use super::step::{applied_minor, Rx, StepSym};

/// **The value-agnostic half of the ι argument** — everything up to and
/// including "the step computes at this key", plus the component equations
/// both halves of the ι rule need.
///
/// The split is where the two recursions over one skeleton part company: every
/// step listed in this file's header runs identically whether the step's value
/// slot holds a minor premise or a `good` set ([`super::step::Vals`]), because
/// none of them looks inside `valᵢ`. What *is* value-specific is only the last
/// move — rewriting the value's own arguments — and the two recursions write
/// their own. [`super::family::good`] consumes this struct directly: for it
/// `valᵢ(tuple, recfun, cmp)` is already `Gᵢ(p⃗, tuple, cmp)` and there is
/// nothing left to rewrite.
pub(crate) struct IotaCore {
    /// The ambient hypothesis `P` — `HYP ∧ Hᵢ^ctor`, or `HYP` alone when the
    /// constructor is nullary.
    pub(crate) p: Formula,
    /// `⊢ P → app(grec, ctorᵢ(y⃗,t⃗)) = valᵢ(tuple(y⃗), recfun(t⃗), cmp)`.
    pub(crate) chain: Thm,
    /// `grec(p⃗,s⃗,T)` — the recursor term the equation is about.
    pub(crate) grec: Term,
    /// `ctorᵢ(y⃗, t⃗)`.
    pub(crate) ctor: Term,
    /// `⟨y₀, ⟨…, ⟨y_{k−1}, •⟩…⟩⟩`, the tag payload.
    pub(crate) tuple: Term,
    /// `f(t⃗)`, the recursive-argument dispatcher.
    pub(crate) recfun: Term,
    /// `comp(grec, recfun, finord(mᵢ))` — the ih row.
    pub(crate) cmp: Term,
    /// `⊢ compⱼ(tuple) = yⱼ` — unconditional, `k` of them.
    pub(crate) comp_eqs: Vec<Thm>,
    /// `⊢ app(recfun, Injⱼ(•)) = tⱼ` — unconditional, `m` of them.
    pub(crate) sub_eqs: Vec<Thm>,
    /// `⊢ app(cmp, Injⱼ(•)) = app(grec, tⱼ)` — unconditional, `m` of them.
    /// **This is the ih-row spelling**: one application, not two.
    pub(crate) ih_eqs: Vec<Thm>,
}

/// The `i`-th ι rule at the working variables, `y⃗`/`t⃗` fresh from the caller.
///
/// `st` is (S3) at the working variables; `computes[i]` is (S1) generalised
/// over its `(σ, f, r)`; `iota`/`funspace` are the shared W-recursor
/// theorems; `comp_app`/`comp_typed` the composite's computation and typing
/// rules, derived once by the caller.
///
/// **`iota` and `funspace` are not checked here, and must not be.** Both are
/// `mp`-ed against below, so a hypothesis on either rides into the returned
/// theorem, which the (S4) header states as a `⊢`. Checking them per
/// constructor would be `n` copies of the same test in the inner loop; instead
/// the two *public* doors — [`super::recursor::GenRecursor::build`] and
/// [`super::family::good::Good::build`] — pin both statements and require both
/// to be unconditional before the first symbol is minted. If a third caller
/// ever appears, it owes the same two lines.
#[allow(clippy::too_many_arguments)]
pub(super) fn iota_at(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    rc: &Recursor,
    computes: &[Thm],
    st: &Thm,
    hyp: &Formula,
    iota: &Thm,
    funspace: &Thm,
    comp_app: &Thm,
    comp_typed: &Thm,
    i: usize,
    yvs: &[FreeVar],
    tvs: &[FreeVar],
) -> Option<Thm> {
    let core = iota_core(
        env, cx, syms, rc, computes, st, hyp, iota, funspace, comp_app, comp_typed, i, yvs, tvs,
    )?;
    iota_tail(env, cx, &core, i, yvs, tvs)
}

/// [`IotaCore`] — the shared prefix. See that struct for what the split is
/// and why it is where it is, and [`iota_at`] for why `iota` and `funspace`
/// are the caller's to check rather than this function's.
#[allow(clippy::too_many_arguments)]
pub(crate) fn iota_core(
    env: &mut Env,
    cx: &Rx<'_>,
    syms: &[StepSym],
    rc: &Recursor,
    computes: &[Thm],
    st: &Thm,
    hyp: &Formula,
    iota: &Thm,
    funspace: &Thm,
    comp_app: &Thm,
    comp_typed: &Thm,
    i: usize,
    yvs: &[FreeVar],
    tvs: &[FreeVar],
) -> Option<IotaCore> {
    let s = cx.s();
    let ap = cx.ap();
    let wt = &cx.mach.wt;
    let tel = cx.tel(i).clone();
    let ra = &cx.ind.recargs[i];
    let (kk, m) = (cx.k(i), cx.m(i));
    debug_assert_eq!(yvs.len(), kk);
    debug_assert_eq!(tvs.len(), m);

    let tags = cx.ind.tags.clone();
    let fam = cx.ind.fibre.fam.clone();
    let u = cx.ind.bound.clone();
    let w = cx.w();
    let t = cx.t.clone();
    let step = cx.step(syms);
    let grec = rc.of(&tags, &fam, &u, &t, &step);
    let fibre = cx.fibre(i)?;

    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let tuple = Telescope::tuple_of(s, &ys);
    let tag = cx.mach.syms.inj(i, tuple.clone())?;
    let recfun = RecArg::of(s, &cx.mach.cases, &ts);
    let ctor = wt.sup(tag.clone(), recfun.clone());
    debug_assert_eq!(
        Some(ctor.clone()),
        cx.ind.ctor_term(cx.mach, i, &ys, &ts),
        "iota: the constructor term drifted from the carrier's"
    );

    // ── the ambient hypothesis `P := HYP ∧ Hᵢ^ctor` ─────────────────────────
    let atoms = ctor_atoms(&tel, &cx.ps, &ys, &ts, &cx.ind.carrier);
    let (p, p_hyp, p_ctor) = match conj_of(&atoms) {
        Some(h) => (
            Formula::and(hyp.clone(), h.clone()),
            and_left(hyp.clone(), h.clone()),
            Some(and_right(hyp.clone(), h)),
        ),
        None => (hyp.clone(), imp_refl(hyp.clone()), None),
    };

    // ── `tuple ∈ Aᵢ` and `Injᵢ(tuple) ∈ A` ──────────────────────────────────
    let p_tuple = if kk == 0 {
        under(&inst_all(&tel.intro, &cx.ps)?, &p)
    } else {
        let mut a = cx.ps.clone();
        a.extend(ys.iter().cloned());
        syl(
            &syl(p_ctor.as_ref()?, &conj_sub(&atoms, 0, kk)?)?,
            &inst_all(&tel.intro, &a)?,
        )?
    };
    let p_tag = {
        let mut a = cx.ind.summands.clone();
        a.push(tuple.clone());
        syl(&p_tuple, &inst_all(cx.mach.syms.inj_mem(cx.n(), i)?, &a)?)?
    };

    // ── the recursive arguments, moved from `ind(p⃗)` to the raw `W` ────────
    let ty_at = inst_all(&cx.ind.ty_ax, &cx.ps)?; // ⊢ ind(p⃗) = W
    let mut p_ts_w = Vec::with_capacity(m);
    for (j, tj) in ts.iter().enumerate() {
        let at = syl(p_ctor.as_ref()?, &conj_proj(&atoms, kk + j)?)?;
        let tj = tj.clone();
        p_ts_w.push(carry_under(env, &ty_at, move |x| Formula::mem(tj.clone(), x), &at)?);
    }

    // ── `recfun ∈ fs(finord(mᵢ), W)`, then at the fibre `B(tag)` ────────────
    let p_rf = if m == 0 {
        under(&inst_all(&ra.in_funspace, std::slice::from_ref(&w))?, &p)
    } else {
        let mut a = vec![w.clone()];
        a.extend(ts.iter().cloned());
        hyp_mp(&a1i(&inst_all(&ra.in_funspace, &a)?, p.clone()), &hyp_conj(&p_ts_w)?)?
    };
    let p_fib = syl(
        &p_tuple,
        &inst_all(&cx.ind.fibre.fibre[i], std::slice::from_ref(&tuple))?,
    )?;
    let p_rf_fib = {
        let back = hyp_eq_symm(env, &p_fib)?;
        let (rf, ww) = (recfun.clone(), w.clone());
        rewrite_under(
            env,
            &back,
            move |q| Formula::mem(rf.clone(), s.fs.of(q, ww.clone())),
            &p_rf,
        )?
    };

    // ── fire the W-recursor's unguarded ι ───────────────────────────────────
    let args = [tags.clone(), fam.clone(), u.clone(), t.clone(), step.clone()];
    let both = hyp_and(&under(&cx.ind.closed, &p), &syl(&p_hyp, st)?)?;
    let dis = syl(&both, &inst_all(iota, &args)?)?;
    let fs_thm = syl(&both, &inst_all(funspace, &args)?)?;
    let fired = hyp_mp(
        &hyp_inst(&dis, &[tag.clone(), recfun.clone()])?,
        &hyp_and(&p_tag, &p_rf_fib)?,
    )?;

    // ── the composite's domain computes to `finord(mᵢ)` ─────────────────────
    let cmp = comp_of(rc.comp, grec.clone(), recfun.clone(), fibre.clone());
    let cong = {
        let (st_c, tg, rf, gr) = (step.clone(), tag.clone(), recfun.clone(), grec.clone());
        hyp_congr(env, &p_fib, move |q| {
            ap.apply(
                st_c.clone(),
                ap.sets.pair(
                    tg.clone(),
                    ap.sets.pair(rf.clone(), comp_of(rc.comp, gr.clone(), rf.clone(), q)),
                ),
            )
        })?
    };
    let at_fin = hyp_eq_trans(env, &fired, &cong)?;

    // ── `cmp ∈ fs(finord(mᵢ), T)` by `composite_typed` ──────────────────────
    let p_val = {
        let bv = env.fresh_var();
        let tb = Term::var(bv);
        let mem_b = Formula::mem(tb.clone(), fibre.clone());
        let kf = Formula::and(p.clone(), mem_b.clone());
        let k_p = and_left(p.clone(), mem_b.clone());
        let k_b = and_right(p.clone(), mem_b);
        let k_rfb = hyp_mp(
            &a1i(
                &inst_all(&wt.app_mem, &[fibre.clone(), w.clone(), recfun.clone(), tb.clone()])?,
                kf.clone(),
            ),
            &hyp_and(&syl(&k_p, &p_rf)?, &k_b)?,
        )?;
        let k_gr = hyp_mp(
            &a1i(
                &inst_all(
                    &wt.app_mem,
                    &[w.clone(), t.clone(), grec.clone(), ap.apply(recfun.clone(), tb)],
                )?,
                kf.clone(),
            ),
            &hyp_and(&syl(&k_p, &fs_thm)?, &k_rfb)?,
        )?;
        gen_under(bv, &p, &uncurry(&k_gr)?)?
    };
    let p_cmp = hyp_mp(
        &a1i(
            &inst_all(comp_typed, &[grec.clone(), recfun.clone(), fibre.clone(), t.clone()])?,
            p.clone(),
        ),
        &p_val,
    )?;

    // ── both payload halves land in the Replacement's ranges ────────────────
    let sub = |prem: &Thm, cod: &Term, g: &Term| -> Option<Thm> {
        let inc = inst_all(&s.fs.fs_sub, &[fibre.clone(), cod.clone()])?;
        let at = Thm::mp(&Thm::ax_inst(inc.concl().clone(), g.clone())?, &inc)?;
        syl(prem, &at)
    };
    let p_fw = sub(&p_rf, &w, &recfun)?;
    let p_ft = sub(&p_cmp, &t, &cmp)?;

    // ── the step computes at this key — (S1) ────────────────────────────────
    let p_step = hyp_mp(
        &a1i(
            &inst_all(&computes[i], &[tuple.clone(), recfun.clone(), cmp.clone()])?,
            p.clone(),
        ),
        &hyp_and(&p_tuple, &hyp_and(&p_fw, &p_ft)?)?,
    )?;
    let chain = hyp_eq_trans(env, &at_fin, &p_step)?;

    // ── read the components back, unconditionally ───────────────────────────
    // `compⱼ(tuple) = yⱼ` — literal projections down the tuple spine.
    let mut comp_eqs = Vec::with_capacity(kk);
    let mut cur = Thm::eq_refl(tuple.clone());
    for j in 0..kk {
        let rest = Telescope::tuple_of(s, &ys[j + 1..]);
        let fst_lift = congr_ctx(env, &cur, |x| cx.pj().fst_of(ap, x))?;
        let fst_at = inst_all(&cx.pj().fst, &[ys[j].clone(), rest.clone()])?;
        comp_eqs.push(eq_trans(env, &fst_lift, &fst_at)?);
        let snd_lift = congr_ctx(env, &cur, |x| cx.pj().snd_of(ap, x))?;
        let snd_at = inst_all(&cx.pj().snd, &[ys[j].clone(), rest])?;
        cur = eq_trans(env, &snd_lift, &snd_at)?;
    }
    // `app(recfun, Injⱼ(•)) = tⱼ`, and `app(cmp, Injⱼ(•)) = app(grec, tⱼ)`.
    let mut sub_eqs = Vec::with_capacity(m);
    let mut ih_eqs = Vec::with_capacity(m);
    for j in 0..m {
        let se = inst_all(&ra.app[j], &ts)?;
        let ca = Thm::mp(
            &inst_all(comp_app, &[grec.clone(), recfun.clone(), fibre.clone(), cx.inj_pt(j)?])?,
            &cx.inj_pt_mem(i, j)?,
        )?;
        let lift = congr_ctx(env, &se, |x| ap.apply(grec.clone(), x))?;
        ih_eqs.push(eq_trans(env, &ca, &lift)?);
        sub_eqs.push(se);
    }

    Some(IotaCore {
        p,
        chain,
        grec,
        ctor,
        tuple,
        recfun,
        cmp,
        comp_eqs,
        sub_eqs,
        ih_eqs,
    })
}

/// The value-recursor half: rewrite `valᵢ`'s arguments from the key's
/// components to the constructor's own, one application position at a time.
fn iota_tail(
    env: &mut Env,
    cx: &Rx<'_>,
    core: &IotaCore,
    i: usize,
    yvs: &[FreeVar],
    tvs: &[FreeVar],
) -> Option<Thm> {
    let ap = cx.ap();
    let m = cx.m(i);
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
    let (p, chain) = (core.p.clone(), core.chain.clone());
    let (grec, cmp, tuple, recfun) =
        (core.grec.clone(), core.cmp.clone(), core.tuple.clone(), core.recfun.clone());
    let (comp_eqs, sub_eqs, ih_eqs) = (&core.comp_eqs, &core.sub_eqs, &core.ih_eqs);

    // ── rewrite the value's arguments, one position at a time ───────────────
    let comps = cx.comps(i, &tuple);
    let f_apps = cx.fibre_apps(i, &recfun)?;
    let ih_olds = cx.fibre_apps(i, &cmp)?;
    let ih_news: Vec<Term> = ts.iter().map(|tj| ap.apply(grec.clone(), tj.clone())).collect();

    // Application-order lists of (old, new, equation).
    let mut olds: Vec<Term> = Vec::new();
    let mut news: Vec<Term> = Vec::new();
    let mut eqs: Vec<Thm> = Vec::new();
    let (mut pi, mut ri) = (0, 0);
    for sl in cx.order(i) {
        match sl {
            super::spec::Slot::Plain => {
                olds.push(comps[pi].clone());
                news.push(ys[pi].clone());
                eqs.push(comp_eqs[pi].clone());
                pi += 1;
            }
            super::spec::Slot::Rec => {
                olds.push(f_apps[ri].clone());
                news.push(ts[ri].clone());
                eqs.push(sub_eqs[ri].clone());
                ri += 1;
            }
        }
    }
    for j in 0..m {
        olds.push(ih_olds[j].clone());
        news.push(ih_news[j].clone());
        eqs.push(ih_eqs[j].clone());
    }

    let out = if olds.is_empty() {
        chain.clone()
    } else {
        let mut acc: Option<Thm> = None;
        for pos in 0..olds.len() {
            let ctx_step = {
                let (news_c, olds_c) = (news.clone(), olds.clone());
                let su = cx.minors[i].clone();
                congr_ctx(env, &eqs[pos], move |x| {
                    let mut args = news_c[..pos].to_vec();
                    args.push(x);
                    args.extend(olds_c[pos + 1..].iter().cloned());
                    args.iter().fold(su.clone(), |acc, y| ap.apply(acc, y.clone()))
                })?
            };
            acc = Some(match acc {
                None => ctx_step,
                Some(a) => eq_trans(env, &a, &ctx_step)?,
            });
        }
        hyp_eq_trans(env, &chain, &a1i(&acc?, p.clone()))?
    };

    let rhs = applied_minor(ap, cx.order(i), &cx.minors[i], &ys, &ts, &ih_news);
    if *out.concl() != Formula::imp(p, Formula::eq(ap.apply(grec, core.ctor.clone()), rhs)) {
        return None
    }
    Some(out)
}
