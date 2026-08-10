//! **The ι rule of a class-(T) eliminator, at a use site** — the certificate
//! `whnf`'s recursor arm needs when the major premise is a constructor
//! application and the eliminator is the *derived* one.
//!
//! # Interface
//!
//! ```text
//! iota_dep::fire(checker, T.rec, σ, …) -> Result<(Thm, Term), Gap>
//! ```
//!
//! One **composed** equation
//!
//! ```text
//! Γ ⊢ app(…app(⟦T.rec⟧, ⟦p⃗⟧)…, ⟦major⟧) = ⟦rhs⟧
//! ```
//!
//! together with `⟦rhs⟧`, or a named absence. Called from
//! [`crate::kernel::Checker::whnf_conv`]'s constructor-match branch and nowhere
//! else.
//!
//! # What was actually missing, and what was not
//!
//! Not the theorem. [`derived::inductive::DepRecursor::iota`] has been in
//! `IndApparatus::deprecs` under the very key the gap names since the
//! eliminator's *typing* was derived:
//!
//! ```text
//! ⊢ PRE → ∀y⃗ ∀t⃗. ( Hᵢ → app(drec, ctorᵢ(y⃗,t⃗)) = Sᵢ⟪y⃗,t⃗⟫ app(drec,t⃗) )
//! ```
//!
//! `PRE = COD(C,T) ∧ DEP(C,S⃗)` is a fact about **the use site's own minors**,
//! which are arbitrary terms and not the eliminator nest's binders.
//! `rec_dep::dep_bottom` derived it at the bottom of that nest, spent it on the
//! typing and dropped it, along with the abbreviation naming `app(drec,⟦t⟧)` —
//! `MINI-HANDOFF.md` §2's sixth instance. So the two things this module needed
//! were a `PRE` at other terms ([`crate::rec_dep::pre_at`]) and the
//! abbreviation kept ([`crate::interp::DepElim`]); neither is a derivation and
//! `derived/` owes this row nothing.
//!
//! # The composite, and why it is one leg rather than four
//!
//! | step | from | to | how |
//! |---|---|---|---|
//! | 1 | `app(…⟦T.rec⟧…, ⟦major⟧)` | `app(drec, ⟦major⟧)` | `beta_spine` down the stored nest, then [`DepElim::ax`](crate::interp::DepElim::ax) |
//! | 2 | `⟦major⟧` | `ctorᵢ(⟦y⃗⟧,⟦t⃗⟧)` | `beta_spine` down `⟦T.ctorᵢ⟧`'s nest, then `Translated::ctor_abbrev`, under one `app` congruence |
//! | 3 | `app(drec, ctorᵢ(…))` | `Sᵢ⟪⟦y⃗⟧,⟦t⃗⟧⟫ app(drec,⟦t⃗⟧)` | `dr.iota[i]`, generalised and instantiated at the caller's terms, `mp` with `PRE`, `mp` with `Hᵢ` |
//! | 4 | that | `⟦rhs⟧` | the Lean rhs spells each recursive result `T.rec p⃗ C S⃗ tⱼ`, so step 1 again at `tⱼ`, reversed, under `m` congruences |
//!
//! **`MINI-HANDOFF.md` §8 said this ends in a chain of one `step!` per level,
//! and it does not.** That is true of [`Checker::nest_iota`], whose legs are
//! *per argument* and are lifted by `whnf`'s own macro. Here the right
//! instrument is [`Interp::beta_spine`], which does the `congr` lifting
//! internally and hands back a single equation about the whole spine — so the
//! caller removes the consumed arguments from `stack_tms` first and emits
//! **one** `step!`. Composing per-argument legs by hand is the `ConvCompose`
//! trap; using a function that never produces them avoids it by construction.
//!
//! # What is checked
//!
//! The endpoint is compared against `⟦rhs⟧` **inferred**, exactly as
//! [`Checker::nest_iota`] does and for the same reason: `whnf`'s contract is
//! that `cur_tm` is the interpretation of `cur`, so a composite that landed
//! somewhere else would hand the next step a certificate about a different
//! term. Step 4 exists only because at `mᵢ > 0` the two differ *by* the
//! recursive calls, and the whole of it is the equation step 1 already proves,
//! run at `tⱼ` and turned around.
//!
//! # What declines
//!
//! * **an indexed family** — `IndexedDepRecursor::iota` is the same table one
//!   row along (`SCOPING.md` §8, construction 3) and `IndexedDepRecursor` is
//!   not `DepRecursor`;
//! * **a `Prop`-valued motive** — `⟦T.rec.{0,σ}⟧` is `•` and there is no `drec`
//!   at all, so the equation is between two proofs and wants irrelevance, not a
//!   computation rule. Unreachable in practice: `split_app` already answers
//!   `None` on a proof spine, so `whnf` arrives with no interpretation to
//!   transport;
//! * **a major whose parameters are not the eliminator's own, syntactically.**
//!   Well-typedness makes them convertible; making them *equal* is a conversion
//!   nothing here holds, and the transport would be about a different carrier.
//!
//! Every decline is reported by the caller as `Gap::Iota`, unchanged, so
//! `077`'s row keeps its name while it waits for construction 3.

use kernel::{Formula, Term, Thm};

use derived::inductive::step::applied_minor;
use derived::inductive::Slot;

use crate::env::ConstantInfo;
use crate::ev::{Cause, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::interp::{Interp, PiShape};
use crate::kernel::Checker;
use crate::rec_dep::{self, At, Site};
use crate::scope::Scopes;

const INDEXED: &str = "iota: an indexed family — IndexedDepRecursor, not DepRecursor";
const PROP: &str = "iota: a Prop-valued motive has no drec";
const SHAPE: &str = "iota: the recursor's arity or its declaration disagree";
const CARRIER: &str = "iota: the declaration has no class-(T) carrier";
const MAJOR: &str = "iota: the major premise is not this constructor at the eliminator's own \
                     parameters";
const NEST: &str = "iota: the beta chain down the stored eliminator";
const ABBREV: &str = "iota: the eliminator's nest bottom has no stored abbreviation";
const CTOR: &str = "iota: the major does not reach Inductive::ctor_term";
const ATOM: &str = "iota: a field typing does not move onto the set derived states it at";
const RULE: &str = "iota: DepRecursor::iota does not instantiate here";
const RHS: &str = "iota: the composite did not land on the Lean right-hand side";

/// The ι certificate at one use site: `Γ ⊢ ⟦T.rec p⃗ C S⃗ major⟧ = ⟦rhs⟧`.
///
/// `args`/`arg_tms` are the `np + 1 + n + 1` arguments up to and including the
/// major premise, with their interpretations; `ctor_args` is the major's own
/// spine (parameters then fields, in declared order) and `rhs` the Lean
/// right-hand side `whnf` is about to move to.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fire(
    c: &mut Checker<'_, '_>,
    rec: &Name,
    rec_inst: &[u32],
    rec_ty: &E,
    np: usize,
    n: usize,
    head_tm: &Term,
    args: &[E],
    arg_tms: &[Term],
    ctor: &Name,
    ctor_args: &[E],
    rhs: &E,
) -> Result<(Thm, Term), Gap> {
    let depth = np + 1 + n + 1;
    let bad = |w: &'static str| Gap::Recursor(*rec, w, Cause::Threading);
    if args.len() != depth || arg_tms.len() != depth {
        return Err(bad(SHAPE))
    }

    // ── which declaration, which constructor, which clause ──────────────────
    let ind_name = c.environment().owner(rec).cloned().ok_or_else(|| bad(SHAPE))?;
    let Some(ConstantInfo::Inductive { ctors, num_params, num_indices, .. }) =
        c.environment().get(&ind_name)
    else {
        return Err(bad(SHAPE))
    };
    if *num_indices != 0 {
        return Err(bad(INDEXED))
    }
    if *num_params as usize != np {
        return Err(bad(SHAPE))
    }
    let ctors = ctors.clone();
    let i = ctors.iter().position(|x| x == ctor).ok_or_else(|| bad(SHAPE))?;
    // The recursor's level list is the declaration's with the motive's
    // prepended, which is `rec_dep::motive_level`'s premise too.
    let ind_inst = rec_inst.get(1..).ok_or_else(|| bad(SHAPE))?.to_vec();
    let u1 = rec_dep::motive_level(rec_ty, np, 0).ok_or_else(|| bad(SHAPE))?;
    if u1 == 0 {
        return Err(bad(PROP))
    }
    let codomain = crate::zoneb::peel(rec_ty, depth).ok_or_else(|| bad(SHAPE))?;

    let tr = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.decls.get(&(ind_name, crate::ground::ground_levels(&ind_inst))).cloned().ok_or_else(|| bad(CARRIER))?
    };
    if tr.ind.spec.ctors.len() != n || tr.ind.params.len() != np {
        return Err(bad(SHAPE))
    }
    let spec = tr.ind.spec.ctors[i].clone();
    let (k, m) = (spec.args.len(), spec.recs);
    if ctor_args.len() != np + k + m || ctor_args[..np] != args[..np] {
        return Err(bad(MAJOR))
    }

    let site = Site {
        ind: ind_name,
        inst: ind_inst.clone(),
        rec: *rec,
        rec_inst: rec_inst.to_vec(),
        ctors: ctors.clone(),
        np,
        n,
        depth,
        codomain,
        u1,
        tr,
    };

    // ── the Lean side: interpretations and the memberships beta consumes ────
    //
    // `⟦rhs⟧` first, because everything after this point holds `Interp`
    // mutably and inference is the checker's.
    let want = c.infer_type(rhs).map_err(|_| Gap::Classifier)?;
    let want = want.tm.clone().ok_or_else(|| want.ev.reason(Gap::NoEndpoint))?;
    let mems = c.nest_arg_mems(head_tm, rec_ty, args, arg_tms)?;

    // **The right-hand side's own arguments, one at a time** — and only when a
    // slot is function-typed, because that is the one shape in which
    // `⟦rhs⟧`'s arguments are not the terms `derived`'s ι rule names. At a
    // plain slot the ih is the eliminator applied to the field and step 4's
    // beta chain closes it; at a function-typed one it is a **λ**, and closing
    // it needs that λ's own graph — see [`ih_leg`]. Inferred here for
    // [`want`]'s reason: everything past this point holds `Interp` mutably.
    let general = spec.rec_doms.iter().any(|g| !g.is_empty());
    let rhs_arg_tms: Vec<Option<Term>> = if general {
        let (_, rargs) = crate::expr::get_app(rhs);
        rargs
            .iter()
            .map(|a| c.infer_type(a).ok().and_then(|t| t.tm.clone()))
            .collect()
    } else {
        Vec::new()
    };

    let major_tm = arg_tms[depth - 1].clone();
    let ctor_former = c.stored_term(ctor, &ind_inst).ok_or_else(|| bad(CTOR))?;
    let ctor_tms = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let (head, ts) = peel_app(ip, &major_tm, np + k + m).ok_or_else(|| bad(MAJOR))?;
        if head != ctor_former {
            return Err(bad(MAJOR))
        }
        ts
    };
    let ctor_ty = {
        let cinfo = c.environment().get(ctor).ok_or_else(|| bad(CTOR))?;
        ground::subst_ground(cinfo.ty(), cinfo.lparams(), &ind_inst)
    };
    let c_mems = c.nest_arg_mems(&ctor_former, &ctor_ty, ctor_args, &ctor_tms)?;

    let former = c.stored_term(&ind_name, &ind_inst).ok_or_else(|| bad(CARRIER))?;
    let mut ctor_formers = Vec::with_capacity(n);
    for name in &ctors {
        ctor_formers.push(c.stored_term(name, &ind_inst).ok_or_else(|| bad(CARRIER))?);
    }

    let elim = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.dep_elims
            .get(&(*rec, crate::ground::ground_levels(rec_inst)))
            .cloned()
            .ok_or_else(|| bad(ABBREV))?
    };

    // The conversions the walk below cannot mint, from the frame this
    // reduction's own arguments are spelled in — `rec_dep::CtorBridge`. Taken
    // before `Interp` is borrowed, for `want`'s reason: both legs are `whnf`.
    let bridges = rec_dep::ctor_bridges(c, &site, &args[..np], &arg_tms[..np])?;

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let at = At {
        goal: ip.app(arg_tms[np].clone(), major_tm.clone()),
        xs: arg_tms.to_vec(),
        mems,
        vars: Vec::new(),
        former,
        ctor_formers,
        prop: false,
        bridges,
    };
    let bridge = at.bridges.get(i).ok_or_else(|| bad(CTOR))?;
    if bridge.rec_eq.len() != m {
        return Err(bad(CTOR))
    }
    let cx = rec_dep::cx_of(ip, &site, &at)?;
    let rec_dep::Pre { dep, pre, sub } = rec_dep::pre_at(ip, &site, &at, &cx)?;
    let dr = &dep.dr;
    let ap = ip.prelude.tower.sums.ap.clone();
    let ap_sym = ap.app;

    // ── step 1: down the eliminator's nest and off mini's own name ──────────
    let (bottom, beta_eq) =
        ip.beta_spine(head_tm, arg_tms, &at.mems).ok_or_else(|| bad(NEST))?;
    if bottom != ip.mk(elim.sym, arg_tms.to_vec()) {
        return Err(bad(NEST))
    }
    let unfold = derived::inst_all(&elim.ax, arg_tms).ok_or_else(|| bad(ABBREV))?;
    let step1 = eq_trans(ip, &beta_eq, &unfold).ok_or_else(|| bad(ABBREV))?;
    let drec_at = derived::subst_term(&dr.rec, &sub);
    if *step1.concl() != Formula::eq(spine(&ap, head_tm, arg_tms), ap.apply(drec_at.clone(), major_tm.clone()))
    {
        return Err(bad(NEST))
    }

    // ── step 2: the major, down `⟦T.ctorᵢ⟧`'s nest and onto `ctor_term` ─────
    let (_, ctor_beta) =
        ip.beta_spine(&ctor_former, &ctor_tms, &c_mems).ok_or_else(|| bad(CTOR))?;
    // `Translated::ctor_abbrev` is stated over `p⃗ ++ f⃗`, which is `ctor_tms`
    // — the same list `beta_spine` just walked `⟦T.ctorᵢ⟧`'s nest at.
    let cax = derived::inst_all(&site.tr.ctor_abbrev[i], &ctor_tms).ok_or_else(|| bad(CTOR))?;
    let ceq = eq_trans(ip, &ctor_beta, &cax).ok_or_else(|| bad(CTOR))?;
    let (ceq_lhs, ctor_term) = ceq.concl().as_eq().ok_or_else(|| bad(CTOR))?;
    if ceq_lhs != major_tm {
        return Err(bad(CTOR))
    }
    let cong = derived::congr(&mut ip.env_mut(), ap_sym, &[Thm::eq_refl(drec_at.clone()), ceq.clone()])
        .ok_or_else(|| bad(CTOR))?;
    let step2 = eq_trans(ip, &step1, &cong).ok_or_else(|| bad(CTOR))?;

    // ── the field typings `Hᵢ`, moved onto the sets `derived` states them at ─
    //
    // The same two equations `minor_at` uses, in the same direction reversed:
    // a plain field's `⟦βⱼ⟧` along `Translated::field_abbrev`, a recursive
    // field's `⟦T p⃗⟧` along the carrier equation. Both were *kept* when the
    // declaration was translated, which is why nothing is re-minted here.
    // **The crossing at each recursive slot, or `None` at a plain one.** A use
    // site is the mirror of a minor premise: `rec_dep::minor_at` opens the
    // slot's scope at `derived`'s `fs(Aⱼ,W)` and hands the interpretation the
    // pushed function, while `whnf` arrives holding Lean's own `⟦f⟧` and has to
    // produce the *pulled* one the ι rule quantifies — which is the very term
    // `zoneb::rec_slot_terms` put inside `⟦T.ctorᵢ f⟧`.
    let cross = rec_dep::crossings(ip, &site, &cx, i).ok_or_else(|| bad(ATOM))?;

    let (mut ys, mut ts) = (Vec::with_capacity(k), Vec::with_capacity(m));
    let (mut y_mems, mut t_mems, mut t_raw) = (Vec::new(), Vec::new(), Vec::new());
    // Lean's own recursive fields, and — at a function-typed slot — the
    // `fs(β₀(p⃗), W)` typing the round trip's hypothesis is stated at.
    let (mut lean_ts, mut lean_mems, mut fs_mems) = (Vec::new(), Vec::new(), Vec::new());
    for (j, sl) in spec.order.iter().enumerate() {
        let tm = ctor_tms[np + j].clone();
        let mem = c_mems[np + j].clone();
        match sl {
            Slot::Plain => {
                let mut a = cx.ps.clone();
                a.extend(ys.iter().cloned());
                let fa = site
                    .tr
                    .field_abbrev
                    .get(i)
                    .and_then(|f| f.get(ys.len()))
                    .and_then(|t| derived::inst_all(t, &a))
                    .ok_or_else(|| bad(ATOM))?;
                let back = derived::eq_symm(&mut ip.env_mut(), &fa).ok_or_else(|| bad(ATOM))?;
                y_mems.push(ip.retarget_set(&mem, &back).ok_or_else(|| bad(ATOM))?);
                ys.push(tm);
            }
            Slot::Rec => {
                match cross.get(ts.len()).and_then(|c| c.as_ref()) {
                    None => {
                        // **A plain recursive field's Lean type need not
                        // *spell* the spine.** `052_reduceCtorParam`'s is
                        // `constType (T α) (T α)`, so `mem` arrives at `⟦that⟧`
                        // and `Cx::w_eq` starts at `⟦T α⟧`: the reduction goes
                        // first, and where there is none the carrier equation
                        // is the whole step, as it was.
                        let onto = match bridge.rec_eq.get(ts.len()).and_then(|e| e.as_ref())
                        {
                            None => cx.w_eq.clone(),
                            Some(eq) => rec_dep::eq_trans_pub(ip, eq, &cx.w_eq)
                                .ok_or_else(|| bad(ATOM))?,
                        };
                        t_mems.push(ip.retarget_set(&mem, &onto).ok_or_else(|| bad(ATOM))?);
                        fs_mems.push(None);
                        ts.push(tm.clone());
                    }
                    Some(cr) => {
                        let cod_eq = bridge.rec_eq.get(ts.len()).and_then(|e| e.as_ref());
                        let (pulled, in_fs) =
                            rec_dep::pull_from_pi(ip, &cx, cr, &tm, &mem, cod_eq)
                                .ok_or_else(|| bad(ATOM))?;
                        t_mems.push(pulled);
                        fs_mems.push(Some(in_fs));
                        ts.push(cr.pull_of(&tm, &cx.ps));
                    }
                }
                t_raw.push(mem.clone());
                lean_ts.push(tm);
                lean_mems.push(mem);
            }
        }
    }
    let hyp = y_mems
        .iter()
        .chain(t_mems.iter())
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc));

    // ── step 3: the ι rule itself, at the caller's own terms ────────────────
    let (quant, iargs) = rec_dep::quant_at(&cx, dr);
    let rule = rec_dep::gen_all_checked(&quant, dr.iota.get(i).ok_or_else(|| bad(RULE))?)
        .and_then(|t| derived::inst_all(&t, &iargs))
        .ok_or_else(|| bad(RULE))?;
    let over = Thm::mp(&rule, &pre).ok_or_else(|| bad(RULE))?;
    let mut prefix = ys.clone();
    prefix.extend(ts.iter().cloned());
    let at_fields = derived::inst_all(&over, &prefix).ok_or_else(|| bad(RULE))?;
    let iota = match &hyp {
        None => at_fields,
        Some(h) => Thm::mp(&at_fields, h).ok_or_else(|| bad(RULE))?,
    };
    // **What the minor receives is `Inductive::minor_ihs` and then
    // `Inductive::minor_args`** — the composite at a function-typed slot, and
    // both families pushed onto `β₀ⱼ(p⃗)` there, which is the grain `⟦Sᵢ⟧` is a
    // function on. Rebuilt through `derived`'s own funnels rather than spelled
    // here, so that a use site and the eliminator's own clause cannot disagree
    // about what the ι rule concludes.
    let vs = {
        let (mut kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let kenv = &mut *kenv;
        let comp = app.wrec(kenv).ok_or_else(|| bad(RULE))?.rc.comp;
        cx.ind
            .minor_ihs(&app.mach.borrow(), comp, &drec_at, i, &ts)
            .ok_or_else(|| bad(RULE))?
    };
    let (a_ts, a_vs) = {
        let (mut kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let kenv = &mut *kenv;
        let a_ts =
            cx.ind.minor_args(kenv, &app.mach.borrow(), i, &ts).ok_or_else(|| bad(RULE))?;
        let a_vs =
            cx.ind.minor_args(kenv, &app.mach.borrow(), i, &vs).ok_or_else(|| bad(RULE))?;
        (a_ts, a_vs)
    };
    let landed = applied_minor(&ap, &spec.order, &cx.s_tms[i], &ys, &a_ts, &a_vs);
    if *iota.concl() != Formula::eq(ap.apply(drec_at.clone(), ctor_term), landed.clone()) {
        return Err(bad(RULE))
    }
    let step3 = eq_trans(ip, &step2, &iota).ok_or_else(|| bad(RULE))?;
    if landed == want {
        return Ok((step3, want))
    }

    // ── step 4: put every argument back in the Lean spelling ────────────────
    //
    // `⟦rhs⟧` is `Sᵢ` applied to Lean's own fields and to `mᵢ` recursive
    // results, and `landed` is `Sᵢ` applied to `derived`'s. The two agree at a
    // plain field and differ in **two** places at a recursive slot:
    //
    // | position | `⟦rhs⟧` | `landed` | the leg |
    // |---|---|---|---|
    // | plain recursive field | `⟦tⱼ⟧` | `⟦tⱼ⟧` | reflexivity |
    // | plain ih | `⟦T.rec p⃗ C S⃗ tⱼ⟧` | `app(drec,⟦tⱼ⟧)` | step 1 at `tⱼ` |
    // | function-typed field | `⟦f⟧` | `push(pull(⟦f⟧,T(p⃗)),β₀(p⃗))` | `sigma::pull_push_roundtrip` |
    // | function-typed ih | `⟦λ z:γ. T.rec p⃗ C S⃗ (f z)⟧` | `push(comp(drec,pull(⟦f⟧,T(p⃗)),Aⱼ),β₀(p⃗))` | [`ih_leg`] |
    //
    // So the spine is rebuilt argument by argument from `⟦Sᵢ⟧` itself rather
    // than from a common prefix: with a function-typed slot present there is no
    // common prefix, because the *field* positions differ too.
    let nrec = spec.order.len();
    let mut acc = Thm::eq_refl(cx.s_tms[i].clone());
    let mut ri = 0usize;
    for (j, sl) in spec.order.iter().enumerate() {
        let leg = match sl {
            Slot::Plain => Thm::eq_refl(ctor_tms[np + j].clone()),
            Slot::Rec => {
                let r = ri;
                ri += 1;
                match cross.get(r).and_then(|c| c.as_ref()) {
                    None => Thm::eq_refl(lean_ts[r].clone()),
                    Some(cr) => {
                        let rule = derived::inst_all(
                            &cr.pull_roundtrip,
                            &[cx.w_term.clone(), lean_ts[r].clone()],
                        )
                        .ok_or_else(|| bad(RHS))?;
                        let fs = fs_mems[r].as_ref().ok_or_else(|| bad(RHS))?;
                        let trip = Thm::mp(&rule, fs).ok_or_else(|| bad(RHS))?;
                        derived::eq_symm(&mut ip.env_mut(), &trip).ok_or_else(|| bad(RHS))?
                    }
                }
            }
        };
        acc = derived::congr(&mut ip.env_mut(), ap_sym, &[acc, leg]).ok_or_else(|| bad(RHS))?;
    }
    for j in 0..m {
        let leg = match cross.get(j).and_then(|c| c.as_ref()) {
            None => {
                let mut jargs = arg_tms[..depth - 1].to_vec();
                jargs.push(ts[j].clone());
                let mut jmems = at.mems[..depth - 1].to_vec();
                jmems.push(t_raw[j].clone());
                let (_, jbeta) =
                    ip.beta_spine(head_tm, &jargs, &jmems).ok_or_else(|| bad(NEST))?;
                let jax = derived::inst_all(&elim.ax, &jargs).ok_or_else(|| bad(ABBREV))?;
                eq_trans(ip, &jbeta, &jax).ok_or_else(|| bad(NEST))?
            }
            Some(cr) => {
                let lam_tm = rhs_arg_tms
                    .get(nrec + j)
                    .and_then(|t| t.clone())
                    .ok_or_else(|| bad(RHS))?;
                ih_leg(
                    ip,
                    &cx,
                    cr,
                    &elim,
                    head_tm,
                    &arg_tms[..depth - 1],
                    &at.mems[..depth - 1],
                    &lean_ts[j],
                    &lean_mems[j],
                    &ts[j],
                    &vs[j],
                    &drec_at,
                    &lam_tm,
                )
                .ok_or_else(|| bad(RHS))?
            }
        };
        acc = derived::congr(&mut ip.env_mut(), ap_sym, &[acc, leg]).ok_or_else(|| bad(RHS))?;
    }
    let back = derived::eq_symm(&mut ip.env_mut(), &acc).ok_or_else(|| bad(RHS))?;
    let out = eq_trans(ip, &step3, &back).ok_or_else(|| bad(RHS))?;
    if out.concl().as_eq().map(|(_, r)| r) != Some(want.clone()) {
        return Err(bad(RHS))
    }
    Ok((out, want))
}

/// `Γ ⊢ ⟦λ z:γ. T.rec p⃗ C S⃗ (f z)⟧ = push(comp(drec, pull(⟦f⟧,T(p⃗)), Aⱼ), β₀(p⃗))`
/// — **the induction hypothesis a function-typed slot's ι rule delivers, and the
/// λ Lean's own right-hand side spells it as.**
///
/// The two are functions on `⟦γ⟧` that agree at every point, so the equation is
/// an extensionality — and the cheap one:
/// [`derived::ext::lam_ext_n`] takes two *graph symbols* and a pointwise family
/// and asks for **no typing at all**, where `funspace_ext` would want both
/// sides in one `fs(A,S)` and so a codomain neither side names. Both sides are
/// graphs: the left is the λ clause's own [`LamSite`](crate::interp::LamSite),
/// recovered from its term by [`Interp::as_lam`], and the right is
/// `derived::sigma::Push`, which *is* a `lambda_n` graph over the body
/// `Q(v,z) = app(v, ⟨z,•⟩)`.
///
/// Pointwise, under `z ∈ ⟦γ⟧`, both sides reduce to `app(drec, app(⟦f⟧,z))`:
///
/// ```text
/// t(h⃗,z) = ⟦T.rec p⃗ C S⃗ (f z)⟧          the λ body's own defining axiom
///         = app(drec, app(⟦f⟧,z))         step 1's β chain, at app(⟦f⟧,z)
/// Q(X,z) = app(X, ⟨z,•⟩)                  Push::body_ax
///        = app(drec, app(pull(⟦f⟧,T),⟨z,•⟩))   wrec_typing::composite_app
///        = app(drec, app(⟦f⟧,z))          sigma::reindex_at_tuple
/// ```
///
/// The domain equation is `⟦γ⟧ = β₀(p⃗)`, which is the abbreviation the
/// boundary walk kept — the same one every other leg of this crossing travels
/// on.
#[allow(clippy::too_many_arguments)]
fn ih_leg(
    ip: &mut Interp,
    cx: &rec_dep::Cx,
    cr: &rec_dep::Crossing,
    elim: &crate::interp::DepElim,
    head_tm: &Term,
    prefix: &[Term],
    prefix_mems: &[Thm],
    lean_f: &Term,
    f_mem: &Thm,
    pulled: &Term,
    composite: &Term,
    drec: &Term,
    lam_tm: &Term,
) -> Option<Thm> {
    let s = ip.prelude.tower.sums.clone();
    let ap = s.ap.clone();
    let (lam_site, lam_dom) = ip.as_lam(lam_tm)?;
    if lam_dom != cr.gamma {
        return None
    }
    let PiShape::Dep { site: fsite, dom: gamma } =
        ip.as_pi(&f_mem.concl().as_mem()?.1)?
    else {
        return None
    };
    if gamma != cr.gamma {
        return None
    }
    let comp_app = {
        let (mut kenv, app, _) = ip.ind_parts()?;
        let kenv = &mut *kenv;
        let w = app.wrec(kenv)?;
        derived::wrec_typing::composite_app(kenv, &s.ap, w.rc.comp, &w.rc.comp_ax)?
    };

    let mut sc = Scopes::new();
    let tok = sc.open(&mut ip.env_mut(), cr.gamma.clone());
    let (zt, zm) = {
        let sc = sc.get(0)?;
        (sc.term(), sc.assumption().clone())
    };
    let back = derived::eq_symm(&mut ip.env_mut(), &cr.gamma_ax)?;
    let z_in_beta = ip.retarget_set(&zm, &back)?;

    // ── the λ's own body, down to `app(drec, app(⟦f⟧,z))` ───────────────────
    let fz = ip.app(lean_f.clone(), zt.clone());
    let fz_mem = ip.dprod_app(&fsite, &gamma, lean_f, &zt, f_mem, &zm)?;
    let l1 = ip.symbol_at(lam_site.t, &lam_site.t_ax, &lam_site.holes, &zt)?;
    let mut jargs = prefix.to_vec();
    jargs.push(fz.clone());
    let mut jmems = prefix_mems.to_vec();
    jmems.push(fz_mem);
    let (_, jbeta) = ip.beta_spine(head_tm, &jargs, &jmems)?;
    let jax = derived::inst_all(&elim.ax, &jargs)?;
    let l2 = rec_dep::eq_trans_pub(ip, &jbeta, &jax)?;
    let l12 = rec_dep::eq_trans_pub(ip, &l1, &l2)?;

    // ── and the push's body, down to the same term ──────────────────────────
    let tup = derived::sigma::Telescope::tuple_of(&s, std::slice::from_ref(&zt));
    let mut ia = cx.ps.clone();
    ia.push(zt.clone());
    let tup_mem = Thm::mp(&derived::inst_all(&cr.tel.intro, &ia)?, &z_in_beta)?;
    let e_a = Thm::mp(
        &derived::inst_all(
            &comp_app,
            &[drec.clone(), pulled.clone(), cr.a.clone(), tup.clone()],
        )?,
        &tup_mem,
    )?;
    let att = Thm::mp(
        &derived::inst_all(&cr.at_tuple, &[lean_f.clone(), zt.clone()])?,
        &z_in_beta,
    )?;
    let e_b = derived::congr_arg(
        &mut ip.env_mut(),
        ap.app,
        &[drec.clone(), ap.apply(pulled.clone(), tup.clone())],
        1,
        &att,
    )?;
    let e_ab = rec_dep::eq_trans_pub(ip, &e_a, &e_b)?;
    let bx = derived::inst_all(&cr.px.body_ax, &[composite.clone(), zt.clone()])?;
    let q_eq = rec_dep::eq_trans_pub(ip, &bx, &e_ab)?;
    let l3 = derived::eq_symm(&mut ip.env_mut(), &q_eq)?;

    let body = rec_dep::eq_trans_pub(ip, &l12, &l3)?;
    let family = sc.close(tok).discharge(&body).ok()?;

    // ── the two graphs agree ────────────────────────────────────────────────
    let rule = derived::ext::lam_ext_n(
        &mut ip.env_mut(),
        &ap,
        lam_site.t,
        lam_site.lam,
        &lam_site.lam_ax,
        cr.px.body,
        cr.px.graph,
        &cr.px.graph_ax,
    )?;
    let mut args = lam_site.holes.clone();
    args.push(composite.clone());
    args.push(cr.gamma.clone());
    args.push(cr.beta0.clone());
    let inst = derived::inst_all(&rule, &args)?;
    let out = Thm::mp(&Thm::mp(&inst, &back)?, &family)?;
    let want = Formula::eq(lam_tm.clone(), cr.pushed(composite));
    (*out.concl() == want).then_some(out)
}

/// `app(…app(f, a₀)…, a_{n-1})`, the applicative spine an interpretation gives
/// a Lean application — used only to check step 1 against what `whnf`'s
/// accumulator is about.
fn spine(ap: &derived::funcs::Apply, f: &Term, args: &[Term]) -> Term {
    args.iter().fold(f.clone(), |acc, a| ap.apply(acc, a.clone()))
}

/// Take `n` applications off a spine: the head and the arguments, outermost
/// last. `None` at anything the interpretation did not build as an `app`.
fn peel_app(ip: &Interp, t: &Term, n: usize) -> Option<(Term, Vec<Term>)> {
    let ap = ip.prelude.ap.app;
    let mut cur = t.clone();
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let (f, args) = ip.parts_of(&cur)?;
        if f != ap || args.len() != 2 {
            return None
        }
        out.push(args[1].clone());
        cur = args[0].clone();
    }
    out.reverse();
    Some((cur, out))
}

fn eq_trans(ip: &mut Interp, a: &Thm, b: &Thm) -> Option<Thm> {
    derived::eq_trans(&mut ip.env_mut(), a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, app_n, bvar, forall, konst, lam, sort, Level};
    use crate::interp::Interp;
    use crate::kernel::add;
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }
    fn no() -> Rc<[Level]> { Vec::<Level>::new().into() }
    fn ty0() -> E { sort(Level::zero().succ()) }

    /// ```text
    /// inductive B : Type 0        | b : B
    /// inductive L (α : Type 0)    | nil : L α | cons : α → L α → L α
    /// ```
    ///
    /// `L`'s two constructors are the two halves of this construction — `nil`
    /// has `kᵢ = mᵢ = 0` and `cons` has `kᵢ = mᵢ = 1` with the mask
    /// `[Plain, Rec]` — and both recursors are **generated** by
    /// [`crate::kernel::add`], exactly as they are on the corpus. `B` is here
    /// only to give `α` something closed to be.
    fn env() -> Environment {
        let mut env = Environment::empty();
        let b = nm("B");
        add(
            &mut env,
            &Declaration::Inductive {
                name: b,
                lparams: vec![],
                num_params: 0,
                ty: ty0(),
                ctors: vec![(Name::str(&b, "b"), konst(b, no()))],
            },
        )
        .expect("B is accepted");
        let l = nm("L");
        let spine = |d: u32| app(konst(l, no()), bvar(d));
        add(
            &mut env,
            &Declaration::Inductive {
                name: l,
                lparams: vec![],
                num_params: 1,
                ty: forall(ty0(), ty0()),
                ctors: vec![
                    (Name::str(&l, "nil"), forall(ty0(), spine(0))),
                    (
                        Name::str(&l, "cons"),
                        forall(ty0(), forall(bvar(0), forall(spine(1), spine(2)))),
                    ),
                ],
            },
        )
        .expect("L is accepted");
        env
    }

    /// `L.rec.{1} B (fun _ => B) B.b (fun a l ih => ih) major`, with the two
    /// minors at the shapes the two constructors need.
    fn elim(major: E) -> E {
        let (b, l) = (nm("B"), nm("L"));
        let bty = konst(b, no());
        let lb = app(konst(l, no()), bty);
        app_n(konst(Name::str(&l, "rec"), vec![Level::zero().succ()].into()), &[
            bty,
            // the motive, constant: `fun _ : L B => B`
            lam(lb, bty),
            // `nil`'s minor
            konst(Name::str(&b, "b"), no()),
            // `cons`'s minor, which **uses the induction hypothesis** — so the
            // Lean right-hand side names the eliminator again and step 4 has
            // something to do.
            lam(bty, lam(lb, lam(bty, bvar(0)))),
            major,
        ])
    }

    fn nil() -> E { app(konst(Name::str(&nm("L"), "nil"), no()), konst(nm("B"), no())) }

    /// **The ι rule fires with a certificate, at both `mᵢ = 0` and `mᵢ = 1`.**
    ///
    /// Two cells of one build, because they are two different pieces of
    /// `iota_dep::fire` and the corpus needed four declarations to cover them:
    /// `nil` exercises the vanishing antecedent (`Hᵢ` is empty, so the ι rule
    /// is applied without a `mp`), and `cons` exercises the field typings, the
    /// declared field order `[Plain, Rec]`, and step 4 — the recursive result
    /// that `⟦rhs⟧` spells `L.rec B C S⃗ l` and the composite reaches as
    /// `app(drec, ⟦l⟧)`.
    ///
    /// Non-vacuity, three ways: the reduct must be the right *expression*, so a
    /// certificate about another redex fails; the two endpoints must differ, so
    /// nothing passes on reflexivity; and the conclusion is checked to be
    /// exactly `⟦T.rec …⟧ = ⟦rhs⟧`, so a composite that landed on
    /// `app(drec, ctorᵢ)` — which is where three of the four steps stop — is a
    /// failure and not a pass.
    ///
    /// `np = 0` and `np = 2` are the corpus's (`Bool`/`N`, `Prod`); this file
    /// is `np = 1` and does not depend on the corpus being present.
    #[test]
    fn the_iota_rule_fires_at_a_use_site_with_and_without_recursive_fields() {
        let env = env();
        for (what, major) in
            [("nil", nil()), ("cons", app_n(
                konst(Name::str(&nm("L"), "cons"), no()),
                &[konst(nm("B"), no()), konst(Name::str(&nm("B"), "b"), no()), nil()],
            ))]
        {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            let e = elim(major);
            let t = c.infer_type(&e).unwrap_or_else(|x| panic!("{what}: infer ⟦e⟧: {x}"));
            let tm = t.tm.clone().unwrap_or_else(|| panic!("{what}: ⟦e⟧ is absent: {:?}", t.ev));
            let (reduct, conv) = c
                .whnf_conv(&e, Some(tm.clone()), &Gap::NoEndpoint)
                .unwrap_or_else(|x| panic!("{what}: whnf: {x}"));
            let want = c
                .infer_type(&reduct)
                .unwrap_or_else(|x| panic!("{what}: infer ⟦rhs⟧: {x}"))
                .tm
                .unwrap_or_else(|| panic!("{what}: ⟦rhs⟧ is absent"));
            let thm = conv
                .ev
                .thm()
                .unwrap_or_else(|| panic!("{what}: the ι step has no certificate: {:?}", conv.ev))
                .clone();
            assert_ne!(tm, want, "{what}: the two endpoints must not already be one term");
            assert_eq!(
                *thm.concl(),
                Formula::eq(tm, want),
                "{what}: the certificate is about the wrong endpoints"
            );
            assert!(thm.hyps().is_empty(), "{what}: no binder is open, so Γ must be empty");
        }
    }

    /// **The reduct is the ι right-hand side and not something else.** Split
    /// from the certificate assertion on purpose: `whnf` chooses the reduct
    /// without consulting the evidence, so a wiring that certified the wrong
    /// equation and a wiring that reduced wrongly are different failures and
    /// this one is about acceptance.
    #[test]
    fn the_reduct_is_the_minor_applied_in_declared_field_order() {
        let env = env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let cons = app_n(
            konst(Name::str(&nm("L"), "cons"), no()),
            &[konst(nm("B"), no()), konst(Name::str(&nm("B"), "b"), no()), nil()],
        );
        let reduct = c.whnf(&elim(cons)).expect("whnf");
        // `(fun a l ih => ih) B.b (L.nil B) (L.rec … (L.nil B))`, then β, then ι
        // again at `nil` — so the whole thing is `B.b`. The middle argument is
        // `L.nil B` and the last is the recursive call, so a transport that put
        // the recursive result where the plain field goes would not land here.
        assert_eq!(reduct, konst(Name::str(&nm("B"), "b"), no()));
    }
}
