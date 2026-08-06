//! The general ι rules — (S4), one per constructor: **the deliverable**.
//!
//! ```text
//! ⊢ ∀p⃗ ∀s⃗ ∀T ∀y⃗ ∀t⃗. ((HYP ∧ Hᵢ^ctor) →
//!     app(grec(p⃗,s⃗,T), ctorᵢ(y⃗,t⃗))
//!       = sᵢ ⟪y⃗, t⃗ in declared order⟫ ih₀ … ih_{m−1})
//! ```
//!
//! with every recursive call live, every field live, at every arity, and the
//! hypotheses exactly `HYP` plus the constructor's own argument typings —
//! `Hᵢ^ctor` is [`super::carrier::ctor_atoms_at`], the same conjunction the
//! carrier's constructor rule carries, with the recursive arguments typed at
//! the Lean-facing `ind(p⃗)`.
//!
//! # The two slot shapes
//!
//! At a **plain** recursive argument `ihⱼ` is `app(grec, tⱼ)` and `Hᵢ^ctor`'s
//! `j`-th atom is `tⱼ ∈ ind(p⃗)` — the whole of the file until `#37`. At a
//! **function-typed** one the field is a function `tⱼ ∈ fs(Aⱼ, ind(p⃗))` and
//! `app(grec, tⱼ)` is not even well typed: `ihⱼ` is the **composite**
//! `comp(grec, tⱼ, Aⱼ)`, the recursor applied along the field, on the field's
//! own domain.
//!
//! One consequence with no counterpart in the plain case. A constructor with
//! *any* non-empty `γⱼ` takes [`RecArg::general`] as a whole, so the carrier
//! states every one of its branches as a function — including a `γⱼ = ∅` slot,
//! whose `Aⱼ` is `1`. At such a **mixed** constructor the plain slot's value is
//! `app(tⱼ, •)` and its ih is `app(grec, app(tⱼ, •))`. Every rule that keys off
//! the constructor rather than the slot agrees with the right answer everywhere
//! except here.
//!
//! # The argument, in the design's numbering (§4.2 steps 3–5)
//!
//! Fire [`crate::wrec_total`]'s unguarded ι at `a := Injᵢ(tuple y⃗)`,
//! `f := recfun(t⃗)` under `closed ∧ step_typed` (the carrier's `closed`, and
//! (S3) under `HYP`); rewrite the composite's domain along the fibre
//! equation; compute the step there by (S1), whose one non-trivial
//! membership — `comp(grec, recfun, Sum_{mᵢ}(A⃗)) ∈ FTᵢ` — comes from
//! `composite_typed` with its value premise discharged by two applications of
//! the function-space application rule; then read the components back:
//! `compⱼ(tuple y⃗) = yⱼ` by literal projections, and per recursive slot either
//! `app(recfun, Injⱼ(•)) = tⱼ` by [`crate::recarg::RecArg::app`] with
//! `app(comp, Injⱼ(•)) = app(grec, tⱼ)` by `composite_app` chained with the
//! same, or — at a function-typed slot — the two *function* identifications
//! `recfun|ⱼ = tⱼ` and `cmp|ⱼ = comp(grec, tⱼ, Aⱼ)`, each one
//! [`crate::ext::funspace_ext`] over [`crate::isum::Branch`]'s computation rule
//! chained with [`RecArg::general`]'s. Nothing needs a new proof idea; every
//! step is an instance of a lemma that exists, looped.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::ext::funspace_ext;
#[allow(unused_imports)] // doc links
use crate::recarg::RecArg;
use crate::sigma::Telescope;
use crate::wrec::{comp_of, hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wrec_total::Recursor;
use crate::{
    a1i, and_left, and_right, conj_of, conj_proj, conj_sub, eq_trans, hyp_and, hyp_mp, imp_refl,
    inst_all, syl, uncurry,
};

use super::carrier::{ctor_atoms_at, rec_sets};
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
    /// **The ih row, at the constructor's own grain** — what
    /// [`super::family::good`] transports so that the good-set matrix's `j`-th
    /// conjunct can be rewritten from the composite onto the child's own
    /// good-set. See [`IhRow`]: one application, not two, at both spellings.
    ///
    /// [`IotaCore::ih_at`] is the *value recursor's* form of the same fact and
    /// is not a substitute — it identifies whole functions
    /// (`cmp|ⱼ = comp(grec, tⱼ, Aⱼ)`), which is what a minor premise's ih slot
    /// receives, whereas the matrix needs the value at one point of the fibre.
    /// There is no unconditional `sub_eqs` beside this because nothing consumes
    /// one.
    pub(crate) ih_row: IhRow,
    /// What the ι rule's right-hand side puts in the `m` **recursive** slots:
    /// `tⱼ` at a plain slot, `tⱼ` again at a function-typed one — where `tⱼ` is
    /// itself the field's function — and `app(tⱼ, •)` at a plain slot of a
    /// constructor that takes [`RecArg::general`] as a whole, whose every branch
    /// is a function and whose plain branch is one out of `1`.
    pub(crate) subs: Vec<Term>,
    /// What it puts in the `m` **induction-hypothesis** slots: `app(grec, tⱼ)`
    /// at a plain slot and `comp(grec, tⱼ, Aⱼ)` — the recursor composed with the
    /// field, on the field's own domain — at a function-typed one.
    pub(crate) ih_news: Vec<Term>,
    /// `⊢ P → (the key's `j`-th recursive slot) = subs[j]`, `m` of them, at
    /// **every** constructor: [`RecArg::app`] lifted under `P` at a plain slot,
    /// and a [`crate::ext::funspace_ext`] over [`crate::isum::Branch`]'s
    /// computation rule at a function-typed one.
    pub(crate) sub_at: Vec<Thm>,
    /// `⊢ P → (the key's `j`-th ih slot) = ih_news[j]`, likewise.
    pub(crate) ih_at: Vec<Thm>,
}

/// **The `j`-th recursive child's good-set, read off the ih row** — one entry
/// per recursive argument, in one of two spellings chosen by the constructor.
///
/// The two are the two shapes of [`crate::recarg::RecArg`]'s computation rule,
/// and the split is per **constructor** rather than per slot because
/// `RecArg::general` is: at a mixed constructor every branch is a function,
/// including the one whose `Aⱼ` is `1`, so the point form is not available
/// there even though Lean's field is a plain recursive occurrence.
pub enum IhRow {
    /// A constructor whose recursive arguments are plain:
    /// `⊢ app(cmp, Injⱼ(•)) = app(grec, tⱼ)` — **unconditional**.
    Point(Vec<Thm>),
    /// A constructor taking [`RecArg::general`]:
    /// `⊢ P → ∀z. (z ∈ Aⱼ → app(cmp, Injⱼ(z)) = app(grec, app(tⱼ, z)))`.
    ///
    /// Conditional, and not by omission: computing `app(f(g⃗), Injⱼ z)` at all
    /// needs `gⱼ` to be a function, which is the ambient's own content
    /// ([`crate::recarg`]'s header says why that antecedent cannot be dropped).
    Fibre(Vec<Thm>),
}

impl IhRow {
    /// The `m` theorems, whichever spelling they are in.
    pub fn thms(&self) -> &[Thm] {
        match self {
            IhRow::Point(v) | IhRow::Fibre(v) => v,
        }
    }
}

/// One slot's pointwise facts at a general constructor, derived once and read
/// by both the ih row and the function-typed slot's two identifications.
struct FibreAt {
    /// The `z` every formula below is stated at.
    zv: FreeVar,
    tz: Term,
    /// `P ∧ z ∈ Aⱼ`.
    kz: Formula,
    /// `⊢ (P ∧ z ∈ Aⱼ) → z ∈ Aⱼ`.
    kz_z: Thm,
    /// `⊢ (P ∧ z ∈ Aⱼ) → app(recfun, Injⱼ z) = app(tⱼ, z)`.
    rf_at_z: Thm,
    /// `⊢ (P ∧ z ∈ Aⱼ) → app(cmp, Injⱼ z) = app(grec, app(tⱼ, z))`.
    pw_ih: Thm,
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
    iota_tail(env, cx, &core, i, yvs)
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
    // **Not `RecArg::of`.** The dispatcher is chosen per constructor, and the
    // degenerate builder at a function-typed constructor's arguments is a
    // perfectly well-formed term over `fin(g⃗)` that this declaration has no
    // theorem about — the defect `4ba0904` fixed in the other direction. One
    // funnel, [`Inductive::recfun_of`], so `ctor_term` and this cannot drift.
    let recfun = cx.ind.recfun_of(cx.mach, i, &ts)?;
    let ctor = wt.sup(tag.clone(), recfun.clone());
    debug_assert_eq!(
        Some(ctor.clone()),
        cx.ind.ctor_term(cx.mach, i, &ys, &ts),
        "iota: the constructor term drifted from the carrier's"
    );

    // ── the ambient hypothesis `P := HYP ∧ Hᵢ^ctor` ─────────────────────────
    //
    // The recursive arguments' stated sets are the *carrier's* choice and are
    // per **constructor**: `rⱼ ∈ ind(p⃗)` when the dispatcher is the degenerate
    // one, and `gⱼ ∈ fs(Aⱼ, ind(p⃗))` for every branch when it is the general
    // one — which is `RecArg::general`'s own hypothesis at `S := ind(p⃗)`, so
    // `ra.in_funspace` consumes the conjunction unchanged below.
    let atoms = ctor_atoms_at(&tel, &cx.ps, &ys, &ts, &rec_sets(s, ra, &cx.ind.carrier));
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
        // The context is the stated set with a hole in the carrier position —
        // `tⱼ ∈ ·` or `tⱼ ∈ fs(Aⱼ, ·)`, matching `rec_sets` above.
        let aj = ra.hyp.as_ref().and(ra.summands.get(j)).cloned();
        p_ts_w.push(carry_under(
            env,
            &ty_at,
            move |x| {
                let set = match &aj {
                    None => x,
                    Some(a) => s.fs.of(a.clone(), x),
                };
                Formula::mem(tj.clone(), set)
            },
            &at,
        )?);
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
    // ── the `m` recursive slots, one at a time ──────────────────────────────
    //
    // A **plain** slot reads a value back: `app(recfun, Injⱼ(•)) = tⱼ` and
    // `app(cmp, Injⱼ(•)) = app(grec, tⱼ)`, both unconditional when the whole
    // constructor is plain. A **function-typed** slot cannot — the minor premise
    // there takes the field's own function, and `recfun` is a dispatcher — so it
    // identifies two whole *functions* on `Aⱼ` instead:
    //
    // ```text
    //   recfun|ⱼ = tⱼ                    cmp|ⱼ = comp(grec, tⱼ, Aⱼ)
    // ```
    //
    // each by `funspace_ext` over `Branch`'s computation rule chained with
    // `RecArg::general`'s. The right-hand sides are what the ι rule's own
    // right-hand side then carries: the ih slot becomes a **composite** and not
    // an application.
    let doms = cx.ind.rec_slot_domains(i);
    let general = ra.hyp.is_some();
    // `⊢ P → H`, `RecArg::general`'s antecedent at `S := W`. Every general
    // computation rule below is `mp`-ed against it.
    let h_all = if general && m > 0 { Some(hyp_conj(&p_ts_w)?) } else { None };
    // Derived only where a slot needs it, which is never on the plain path.
    let fs_ext = if doms.iter().any(|d| d.is_some()) {
        Some(funspace_ext(env, ap, &s.prod, &s.fs, &wt.app_pair)?)
    } else {
        None
    };

    // **The two vectors are the funnel's, not this loop's.** What a minor
    // premise is handed at each slot is [`Inductive::minor_subs`] and
    // [`Inductive::minor_ihs`]; the loop below proves the key's `j`-th slot
    // *equal* to them and never chooses them, so [`super::dep`] rebuilding the
    // dependent ι rule from the same funnel cannot disagree with this one.
    let subs = cx.ind.minor_subs(cx.mach, i, &ts)?;
    let ih_news = cx.ind.minor_ihs(cx.mach, rc.comp, &grec, i, &ts)?;
    let mut sub_at: Vec<Thm> = Vec::with_capacity(m);
    let mut ih_at: Vec<Thm> = Vec::with_capacity(m);
    let mut ih_point: Vec<Thm> = Vec::with_capacity(m);
    let mut ih_fibre: Vec<Thm> = Vec::with_capacity(m);

    for j in 0..m {
        // The composite's computation at the `j`-th point of the fibre —
        // `⊢ app(cmp, Injⱼ(•)) = app(grec, app(recfun, Injⱼ(•)))`. Both plain
        // shapes start here.
        let plain_ca = || -> Option<Thm> {
            Thm::mp(
                &inst_all(
                    comp_app,
                    &[grec.clone(), recfun.clone(), fibre.clone(), cx.inj_pt(j)?],
                )?,
                &cx.inj_pt_mem(i, j)?,
            )
        };

        // ── the ih row at a general constructor, once per slot ──────────────
        //
        // `⊢ P → ∀z. (z ∈ Aⱼ → app(cmp, Injⱼ z) = app(grec, app(tⱼ, z)))`, and
        // it exists at **every** slot of such a constructor — the degenerate
        // one included, because `RecArg::general` dispatches over every summand
        // alike and its computation rule is the one available there too. The
        // function-typed arm below chains the same pointwise fact between
        // `Branch`'s two computation rules, so it is derived here and not
        // twice.
        let fib = if general {
            let aj = ra.summands.get(j)?.clone();
            let zv = env.fresh_var();
            let tz = Term::var(zv);
            let mem_z = Formula::mem(tz.clone(), aj.clone());
            let kz = Formula::and(p.clone(), mem_z.clone());
            let kz_p = and_left(p.clone(), mem_z.clone());
            let kz_z = and_right(p.clone(), mem_z);

            // `app(recfun, Injⱼ z) = app(tⱼ, z)` — the general computation
            // rule, its two antecedents discharged.
            let rf_at_z = {
                let mut a = vec![w.clone()];
                a.extend(ts.iter().cloned());
                a.push(tz.clone());
                hyp_mp(
                    &hyp_mp(
                        &a1i(&inst_all(&ra.app[j], &a)?, kz.clone()),
                        &syl(&kz_p, h_all.as_ref()?)?,
                    )?,
                    &kz_z,
                )?
            };
            let inj_z_mem = {
                let mut a = ra.summands.clone();
                a.push(tz.clone());
                syl(&kz_z, &inst_all(cx.mach.syms.inj_mem(ra.summands.len(), j)?, &a)?)?
            };
            let ca_z = hyp_mp(
                &a1i(
                    &inst_all(
                        comp_app,
                        &[
                            grec.clone(),
                            recfun.clone(),
                            fibre.clone(),
                            cx.mach.syms.inj(j, tz.clone())?,
                        ],
                    )?,
                    kz.clone(),
                ),
                &inj_z_mem,
            )?;
            let lift_z = hyp_congr(env, &rf_at_z, |x| ap.apply(grec.clone(), x))?;
            let pw_ih = hyp_eq_trans(env, &ca_z, &lift_z)?;
            ih_fibre.push(gen_under(zv, &p, &uncurry(&pw_ih)?)?);
            Some(FibreAt { zv, tz, kz, kz_z, rf_at_z, pw_ih })
        } else {
            None
        };

        match doms.get(j).and_then(|d| d.as_ref()) {
            // ── a plain slot of a plain constructor: unconditional ──────────
            None if !general => {
                let se = inst_all(&ra.app[j], &ts)?;
                let lift = congr_ctx(env, &se, |x| ap.apply(grec.clone(), x))?;
                let ie = eq_trans(env, &plain_ca()?, &lift)?;
                sub_at.push(under(&se, &p));
                ih_at.push(under(&ie, &p));
                ih_point.push(ie);
            }
            // ── a plain slot of a **mixed** constructor ─────────────────────
            //
            // `Aⱼ` is `1` and the branch is still a *function* out of it — that
            // is the carrier's per-constructor choice — so the value the minor
            // premise receives is `app(tⱼ, •)` and not `tⱼ`. The two `1`s are
            // not interchangeable, and this is where that bites.
            None => {
                let point = s.point();
                if ra.summands.get(j)? != &s.unit() {
                    return None
                }
                let mut a = vec![w.clone()];
                a.extend(ts.iter().cloned());
                a.push(point.clone());
                let raw = inst_all(&ra.app[j], &a)?;
                let se = hyp_mp(
                    &hyp_mp(&a1i(&raw, p.clone()), h_all.as_ref()?)?,
                    &under(&s.unit_mem, &p),
                )?;
                let lift = hyp_congr(env, &se, |x| ap.apply(grec.clone(), x))?;
                let ie = hyp_eq_trans(env, &under(&plain_ca()?, &p), &lift)?;
                sub_at.push(se);
                ih_at.push(ie);
            }
            // ── a function-typed slot: two function identifications ─────────
            Some(aj) => {
                let br = cx.branches.get(&j)?.clone();
                let restr_rf = br.of(recfun.clone(), aj.clone());
                let restr_cmp = br.of(cmp.clone(), aj.clone());
                let comp_j = comp_of(rc.comp, grec.clone(), ts[j].clone(), aj.clone());
                let bfs =
                    cx.mach.syms.branch_in_funspace(env, s, &wt.app_mem, ra.summands.len(), j)?;
                let at_bfs = |cod: &Term, g: &Term| -> Option<Thm> {
                    let mut a = ra.summands.clone();
                    a.push(cod.clone());
                    a.push(g.clone());
                    inst_all(&bfs, &a)
                };
                let p_restr_rf = syl(&p_rf, &at_bfs(&w, &recfun)?)?;
                let p_restr_cmp = syl(&p_cmp, &at_bfs(&t, &cmp)?)?;

                // `comp(grec, tⱼ, Aⱼ) ∈ fs(Aⱼ, T)`, by the composite's typing
                // rule at the field's own domain: two applications of the
                // function-space application rule, exactly as `p_cmp` above.
                let p_comp_j = {
                    let bv = env.fresh_var();
                    let tb = Term::var(bv);
                    let mem_b = Formula::mem(tb.clone(), aj.clone());
                    let kb = Formula::and(p.clone(), mem_b.clone());
                    let k_p = and_left(p.clone(), mem_b.clone());
                    let k_b = and_right(p.clone(), mem_b);
                    let k_tb = hyp_mp(
                        &a1i(
                            &inst_all(
                                &wt.app_mem,
                                &[aj.clone(), w.clone(), ts[j].clone(), tb.clone()],
                            )?,
                            kb.clone(),
                        ),
                        &hyp_and(&syl(&k_p, &p_ts_w[j])?, &k_b)?,
                    )?;
                    let k_gr = hyp_mp(
                        &a1i(
                            &inst_all(
                                &wt.app_mem,
                                &[
                                    w.clone(),
                                    t.clone(),
                                    grec.clone(),
                                    ap.apply(ts[j].clone(), tb),
                                ],
                            )?,
                            kb.clone(),
                        ),
                        &hyp_and(&syl(&k_p, &fs_thm)?, &k_tb)?,
                    )?;
                    let vals = gen_under(bv, &p, &uncurry(&k_gr)?)?;
                    hyp_mp(
                        &a1i(
                            &inst_all(
                                comp_typed,
                                &[grec.clone(), ts[j].clone(), aj.clone(), t.clone()],
                            )?,
                            p.clone(),
                        ),
                        &vals,
                    )?
                };

                // The two pointwise agreements, over the `z ∈ Aⱼ` the ih row
                // was already taken at — so `cmp|ⱼ`'s chain runs *through* the
                // ih row's own equation and the two cannot say different
                // things about `app(cmp, Injⱼ z)`.
                let FibreAt { zv, tz, kz, kz_z, rf_at_z, pw_ih } = fib.as_ref()?;
                let (zv, kz) = (*zv, kz.clone());

                let pw_rf = hyp_eq_trans(
                    env,
                    &syl(kz_z, &inst_all(&br.app, &[recfun.clone(), aj.clone(), tz.clone()])?)?,
                    rf_at_z,
                )?;
                let se = hyp_mp(
                    &a1i(
                        &inst_all(
                            fs_ext.as_ref()?,
                            &[aj.clone(), w.clone(), restr_rf.clone(), ts[j].clone()],
                        )?,
                        p.clone(),
                    ),
                    &hyp_and(
                        &p_restr_rf,
                        &hyp_and(&p_ts_w[j], &gen_under(zv, &p, &uncurry(&pw_rf)?)?)?,
                    )?,
                )?;

                // `app(cmp|ⱼ, z) = app(cmp, Injⱼ z) = app(grec, app(tⱼ, z))
                //   = app(comp(grec,tⱼ,Aⱼ), z)`, the middle step being the ih
                // row's.
                let c1 = syl(kz_z, &inst_all(&br.app, &[cmp.clone(), aj.clone(), tz.clone()])?)?;
                let c4 = hyp_eq_symm(
                    env,
                    &hyp_mp(
                        &a1i(
                            &inst_all(
                                comp_app,
                                &[grec.clone(), ts[j].clone(), aj.clone(), tz.clone()],
                            )?,
                            kz.clone(),
                        ),
                        kz_z,
                    )?,
                )?;
                let pw_cmp = {
                    let a = hyp_eq_trans(env, &c1, pw_ih)?;
                    hyp_eq_trans(env, &a, &c4)?
                };
                let ie = hyp_mp(
                    &a1i(
                        &inst_all(
                            fs_ext.as_ref()?,
                            &[aj.clone(), t.clone(), restr_cmp.clone(), comp_j.clone()],
                        )?,
                        p.clone(),
                    ),
                    &hyp_and(
                        &p_restr_cmp,
                        &hyp_and(&p_comp_j, &gen_under(zv, &p, &uncurry(&pw_cmp)?)?)?,
                    )?,
                )?;

                sub_at.push(se);
                ih_at.push(ie);
            }
        }
    }

    // Exactly one spelling, and it is the constructor's. The length check is
    // what says every slot contributed: a `general` constructor that skipped a
    // slot would otherwise hand back a short row and a consumer indexing it
    // would read another slot's equation.
    let ih_row = if general {
        if ih_fibre.len() != m {
            return None
        }
        IhRow::Fibre(ih_fibre)
    } else {
        if ih_point.len() != m {
            return None
        }
        IhRow::Point(ih_point)
    };

    Some(IotaCore {
        p,
        chain,
        grec,
        ctor,
        tuple,
        recfun,
        cmp,
        comp_eqs,
        ih_row,
        subs,
        ih_news,
        sub_at,
        ih_at,
    })
}

/// The value-recursor half: rewrite `valᵢ`'s arguments from the key's
/// components to the constructor's own, one application position at a time.
///
/// **Every rewriting step runs under the ambient `P`.** At a plain constructor
/// the component equations are unconditional and this is one `a1i` more than it
/// needs to be; at a function-typed one the two identifications
/// `recfun|ⱼ = tⱼ` and `cmp|ⱼ = comp(grec, tⱼ, Aⱼ)` are conditional on the
/// branches being functions, which is [`RecArg::general`]'s own antecedent and
/// not removable. One walk rather than two, and the concluding shape check is
/// what says the plain case did not move.
fn iota_tail(
    env: &mut Env,
    cx: &Rx<'_>,
    core: &IotaCore,
    i: usize,
    yvs: &[FreeVar],
) -> Option<Thm> {
    let ap = cx.ap();
    let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
    let (p, chain) = (core.p.clone(), core.chain.clone());
    let (grec, cmp, tuple, recfun) =
        (core.grec.clone(), core.cmp.clone(), core.tuple.clone(), core.recfun.clone());
    let comp_eqs = &core.comp_eqs;

    // ── rewrite the value's arguments, one position at a time ───────────────
    let comps = cx.comps(i, &tuple);
    let f_apps = cx.fibre_apps(i, &recfun)?;
    let ih_olds = cx.fibre_apps(i, &cmp)?;

    // Application-order lists of (old, new, equation), every equation `P → …`.
    let mut olds: Vec<Term> = Vec::new();
    let mut news: Vec<Term> = Vec::new();
    let mut eqs: Vec<Thm> = Vec::new();
    let (mut pi, mut ri) = (0, 0);
    for sl in cx.order(i) {
        match sl {
            super::spec::Slot::Plain => {
                olds.push(comps[pi].clone());
                news.push(ys[pi].clone());
                eqs.push(under(&comp_eqs[pi], &p));
                pi += 1;
            }
            super::spec::Slot::Rec => {
                olds.push(f_apps[ri].clone());
                news.push(core.subs.get(ri)?.clone());
                eqs.push(core.sub_at.get(ri)?.clone());
                ri += 1;
            }
        }
    }
    // One induction hypothesis per recursive slot. The bound is `ih_olds`' own
    // length rather than a second read of `cx.m(i)`: [`Rx::fibre_apps`] builds
    // exactly `m` entries, so the two cannot drift, and `ih_news`/`ih_at` are
    // still reached through `get` so a short `IotaCore` is a `None` here.
    for (j, old) in ih_olds.iter().enumerate() {
        olds.push(old.clone());
        news.push(core.ih_news.get(j)?.clone());
        eqs.push(core.ih_at.get(j)?.clone());
    }

    let out = if olds.is_empty() {
        chain.clone()
    } else {
        let mut acc: Option<Thm> = None;
        for pos in 0..olds.len() {
            let ctx_step = {
                let (news_c, olds_c) = (news.clone(), olds.clone());
                let su = cx.minors[i].clone();
                hyp_congr(env, &eqs[pos], move |x| {
                    let mut args = news_c[..pos].to_vec();
                    args.push(x);
                    args.extend(olds_c[pos + 1..].iter().cloned());
                    args.iter().fold(su.clone(), |acc, y| ap.apply(acc, y.clone()))
                })?
            };
            acc = Some(match acc {
                None => ctx_step,
                Some(a) => hyp_eq_trans(env, &a, &ctx_step)?,
            });
        }
        hyp_eq_trans(env, &chain, &acc?)?
    };

    let rhs =
        applied_minor(ap, cx.order(i), &cx.minors[i], &ys, &core.subs, &core.ih_news);
    if *out.concl() != Formula::imp(p, Formula::eq(ap.apply(grec, core.ctor.clone()), rhs)) {
        return None
    }
    Some(out)
}
