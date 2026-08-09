//! **The ι rule of an indexed class-(T) eliminator, at a use site** — the
//! certificate `whnf`'s recursor arm needs when the family has indices.
//!
//! # Interface
//!
//! ```text
//! iota_ix_dep::fire(checker, T.rec, σ, …) -> Result<(Thm, Term), Gap>
//! ```
//!
//! One **composed** equation
//!
//! ```text
//! Γ ⊢ app(…app(⟦T.rec⟧, ⟦p⃗⟧)…, ⟦d⃗⟧, ⟦major⟧) = ⟦rhs⟧
//! ```
//!
//! together with `⟦rhs⟧`, or a named absence. Called from
//! [`crate::kernel::Checker::whnf_conv`]'s constructor-match branch, on a
//! recursor whose declaration has `ni > 0`; [`crate::iota_dep`] is the same
//! table one row back and is what the non-indexed families take.
//!
//! # What this is made of, and none of it is a theorem
//!
//! [`IndexedDepRecursor::iota`](derived::inductive::family::IndexedDepRecursor)
//! has been in the store since the eliminator's typing was derived:
//!
//! ```text
//! ⊢ ∀p⃗ ∀m ∀S⃗ ∀T. ( PRE → ∀y⃗ ∀t⃗. ( Hᵢ → app(irec, ctorᵢ(y⃗,t⃗))
//!                                       = Sᵢ⟪y⃗,t⃗⟫ app(irec,t⃗) ) )
//! ```
//!
//! and `crate::rec_ix_dep` already keeps the abbreviation naming `app(irec,⟦t⟧)`
//! ([`crate::interp::DepElim`]). What was missing was `PRE` **at the use site's
//! own minors**, which is [`crate::rec_ix_dep::premise_at`], and that could not
//! be written until [`crate::minor_ix::transport_at`] made the minor's
//! Lean-syntax frame a parameter: an indexed minor's transport reads a recursive
//! field's index expressions out of the minor's *type*, and until then the type
//! had to be the eliminator nest's own binder.
//!
//! # The composite
//!
//! | step | from | to | how |
//! |---|---|---|---|
//! | 1 | `app(…⟦T.rec⟧…, ⟦major⟧)` | `app(irec, ⟦major⟧)` | `beta_spine` down the stored nest, then [`DepElim::ax`](crate::interp::DepElim::ax) |
//! | 2 | `⟦major⟧` | `ctorᵢ(⟦y⃗⟧,⟦t⃗⟧)` | `beta_spine` down `⟦T.ctorᵢ⟧`'s nest, then `IndexedTranslation::ctor_abbrev`, under one `app` congruence |
//! | 3 | `app(irec, ctorᵢ(…))` | `Sᵢ⟪⟦y⃗⟧,⟦t⃗⟧⟫ app(irec,⟦t⃗⟧)` | `dr.iota[i]` at `(⟦p⃗⟧,⟦C⟧,⟦S⃗⟧,T)`, `mp` with `PRE`, `mp` with `Hᵢ` |
//! | 4 | that | `⟦rhs⟧` | the Lean rhs spells each recursive result `T.rec p⃗ C S⃗ d⃗ᵢⱼ tⱼ`, so step 1 again **at the child's own index vector**, reversed, under `m` congruences |
//!
//! # Three differences from [`crate::iota_dep`], all in the statement
//!
//! * **`Hᵢ` is in *declared* field order** while the `∀y⃗ ∀t⃗` prefix is
//!   plains-then-recs. Both are exported —
//!   [`iota_atoms`](derived::inductive::family::IndexedDepRecursor::iota_atoms)
//!   and [`iota_vars`](derived::inductive::family::IndexedDepRecursor::iota_vars)
//!   — precisely because they differ, so the association is *read* here and
//!   never reconstructed from a mask.
//! * **a recursive atom is `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))`** and not `tⱼ ∈ W`: one
//!   carrier equation per child, at the child's own indices, where the
//!   non-indexed sibling had one `w_eq` for all of them. The two moves are β
//!   down the type former's nest and one congruence over the index
//!   abbreviations — [`crate::ctor_ix::index_congr`], the same pair the
//!   constructor's own bottom makes.
//! * **step 4's reverse chain carries index arguments.** `⟦rhs⟧` spells the
//!   `j`-th recursive result at `d⃗ᵢⱼ`, so the β chain is over
//!   `np + 1 + n + ni + 1` arguments with the `ni` slots differing per child,
//!   and the index memberships it consumes are the *inferred*
//!   `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧` — which exist nowhere but at the constructor's own Lean
//!   binder type.
//!
//! # What declines
//!
//! * **a non-indexed declaration** — [`crate::iota_dep`]'s row;
//! * **a `Prop`-valued motive** — `⟦T.rec.{0,σ}⟧` is `•`, so `split_app`
//!   answers `None` and `whnf` never arrives with an interpretation to
//!   transport;
//! * **a major whose parameters are not the eliminator's own, syntactically** —
//!   the same decline [`crate::iota_dep`] makes and for the same reason.
//!
//! Every decline is reported by the caller as `Gap::Iota`, unchanged.

use kernel::{Formula, Term, Thm};

use derived::inductive::step::applied_minor;
use derived::inductive::Slot;

use crate::env::ConstantInfo;
use crate::ev::{Cause, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::interp::Interp;
use crate::kernel::Checker;
use crate::minor_ix::{At, Fam, Site, Source};
use crate::rec_dep::{self, subst_f};

const NOT_INDEXED: &str = "iota: a non-indexed declaration — DepRecursor, not IndexedDepRecursor";
const PROP: &str = "iota: a Prop-valued motive has no irec";
const SHAPE: &str = "iota: the recursor's arity or its declaration disagree";
const CARRIER: &str = "iota: the declaration has no indexed carrier";
const MAJOR: &str = "iota: the major premise is not this constructor at the eliminator's own \
                     parameters";
const NEST: &str = "iota: the beta chain down the stored eliminator";
const ABBREV: &str = "iota: the eliminator's nest bottom has no stored abbreviation";
const CTOR: &str = "iota: the major does not reach the constructor's own term";
const ATOM: &str = "iota: a field typing does not move onto the set derived states it at";
const MOTIVE_TY: &str = "iota: the motive's own type does not place";
const RULE: &str = "iota: IndexedDepRecursor::iota does not instantiate here";
const RHS: &str = "iota: the composite did not land on the Lean right-hand side";
const MINOR: &str = "iota: a minor premise does not transport at the use site";

/// The ι certificate at one use site: `Γ ⊢ ⟦T.rec p⃗ C S⃗ d⃗ major⟧ = ⟦rhs⟧`.
///
/// `args`/`arg_tms` are the `np + 1 + n + ni + 1` arguments up to and including
/// the major premise, with their interpretations; `ctor_args` is the major's own
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
    ni: usize,
    head_tm: &Term,
    args: &[E],
    arg_tms: &[Term],
    ctor: &Name,
    ctor_args: &[E],
    rhs: &E,
) -> Result<(Thm, Term), Gap> {
    let depth = np + 1 + n + ni + 1;
    let bad = |w: &'static str| Gap::Recursor(*rec, w, Cause::Threading);
    if args.len() != depth || arg_tms.len() != depth || ni == 0 {
        return Err(bad(if ni == 0 { NOT_INDEXED } else { SHAPE }))
    }

    // ── which declaration, which constructor, which clause ──────────────────
    let ind_name = c.environment().owner(rec).cloned().ok_or_else(|| bad(SHAPE))?;
    let Some(ConstantInfo::Inductive { ctors, num_params, num_indices, .. }) =
        c.environment().get(&ind_name)
    else {
        return Err(bad(SHAPE))
    };
    if *num_indices as usize != ni || *num_params as usize != np {
        return Err(bad(SHAPE))
    }
    let ctors = ctors.clone();
    let i = ctors.iter().position(|x| x == ctor).ok_or_else(|| bad(SHAPE))?;
    // The recursor's level list is the declaration's with the motive's
    // prepended, which is `rec_dep::motive_level`'s premise too.
    let ind_inst = rec_inst.get(1..).ok_or_else(|| bad(SHAPE))?.to_vec();
    let u1 = rec_dep::motive_level(rec_ty, np, ni).ok_or_else(|| bad(SHAPE))?;
    if u1 == 0 {
        return Err(bad(PROP))
    }
    let codomain = crate::zoneb::peel(rec_ty, depth).ok_or_else(|| bad(SHAPE))?;

    let tr = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.indexed
            .get(&(ind_name, ind_inst.clone()))
            .cloned()
            .ok_or_else(|| bad(CARRIER))?
    };
    if tr.ii.spec.len() != n
        || tr.ii.spec.params() != np
        || tr.ii.spec.num_indices() != ni
        || tr.base.params.len() != np
        || ctors.len() != n
    {
        return Err(bad(SHAPE))
    }
    let spec = tr.ii.spec.base.ctors.get(i).ok_or_else(|| bad(SHAPE))?.clone();
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
        ni,
        depth,
        codomain,
        fam: Fam::ClassT(tr.clone()),
        minor_gap: MINOR,
    };

    // ── the Lean side: interpretations, the memberships beta consumes, and the
    //    binder types the minors' frames are read out of ─────────────────────
    //
    // `⟦rhs⟧` first, because everything after the premise holds `Interp`
    // mutably and inference is the checker's.
    let want = c.infer_type(rhs).map_err(|_| Gap::Classifier)?;
    let want = want.tm.clone().ok_or_else(|| want.ev.reason(Gap::NoEndpoint))?;
    let mems = c.nest_arg_mems(head_tm, rec_ty, args, arg_tms)?;
    let doms = binder_types(rec_ty, args).ok_or_else(|| bad(SHAPE))?;

    // **The motive's own type**, which is where the rung `T` is read off — the
    // same choice `rec_ix_dep`'s header argues for, and it has to be the same
    // one or `PRE` is about a different `T` than the stored term is.
    let m_ty = c.infer_type(&doms[np]).map_err(|_| Gap::Classifier)?;
    let lvl = rec_dep::sort_of(&m_ty.ty).ok_or_else(|| bad(MOTIVE_TY))?;
    let m_ty_mem = m_ty.ev.thm().cloned().ok_or_else(|| m_ty.ev.reason(Gap::NoEndpoint))?;

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
    let c_doms = binder_types(&ctor_ty, ctor_args).ok_or_else(|| bad(CTOR))?;

    // **`⟦d⃗ᵢⱼ⟧` and `⊢ ⟦dₖ⟧ ∈ ⟦Iₖ⟧`, per recursive field.** They exist nowhere
    // but here: the index expressions live in the constructor's own Lean binder
    // type, and only inference produces their typings. Step 4 and every
    // recursive atom want them.
    let mut childs: Vec<Vec<(Term, Thm)>> = Vec::with_capacity(m);
    for (j, sl) in spec.order.iter().enumerate() {
        if *sl != Slot::Rec {
            continue
        }
        let ds_e = crate::zoneb::ind_spine_at(&ind_name, &c_doms[np + j], &ctor_args[..np], ni)
            .ok_or_else(|| bad(MAJOR))?;
        childs.push(crate::ctor_ix::infer_indices(c, &ds_e).ok_or_else(|| bad(MAJOR))?);
    }
    if childs.len() != m {
        return Err(bad(SHAPE))
    }

    let former = c.stored_term(&ind_name, &ind_inst).ok_or_else(|| bad(CARRIER))?;
    let mut ctor_formers = Vec::with_capacity(n);
    for name in &ctors {
        ctor_formers.push(c.stored_term(name, &ind_inst).ok_or_else(|| bad(CARRIER))?);
    }
    let elim = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.dep_elims
            .get(&(*rec, rec_inst.to_vec()))
            .cloned()
            .ok_or_else(|| bad(ABBREV))?
    };

    let goal = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let s = ip.prelude.tower.sums.clone();
        derived::inductive::family::motive_app(
            &s,
            &arg_tms[np],
            &arg_tms[np + 1 + n..depth - 1],
            &major_tm,
        )
    };
    let at = At {
        ps: arg_tms[..np].to_vec(),
        param_mems: mems[..np].to_vec(),
        c_tm: arg_tms[np].clone(),
        s_tms: arg_tms[np + 1..np + 1 + n].to_vec(),
        s_mems: mems[np + 1..np + 1 + n].to_vec(),
        xs: arg_tms[np + 1 + n..depth - 1].to_vec(),
        x_mems: mems[np + 1 + n..depth - 1].to_vec(),
        t_tm: major_tm.clone(),
        t_mem: mems[depth - 1].clone(),
        former,
        ctor_formers,
        goal,
        // The use site mints no name: `rec_ix_dep` kept the eliminator's own
        // abbreviation ahead of this consumer, which is the whole reason step 1
        // can land on `app(irec, ⟦major⟧)`.
        vars: Vec::new(),
        all: arg_tms.to_vec(),
    };

    // The minors' Lean-syntax frames: the recursor's own declared binder with
    // the actual arguments substituted, and the parameters as the expressions
    // the use site applied them at.
    let sources: Vec<Source> = (0..n)
        .map(|j| Source { mty: doms[np + 1 + j], params: args[..np].to_vec() })
        .collect();

    let ix =
        crate::rec_ix_dep::premise_at(c, &site, &at, Some(&sources), &mems[np], &m_ty_mem, lvl)?;

    // ── everything below is kernel work at terms already in hand ────────────
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let ap = ip.prelude.tower.sums.ap.clone();
    let ap_sym = ap.app;
    let dr = ix.dr.clone();
    let irec = derived::subst_term(&dr.rec, &ix.sub);

    // ── step 1: down the eliminator's nest and off mini's own name ──────────
    let (bottom, beta_eq) = ip.beta_spine(head_tm, arg_tms, &mems).ok_or_else(|| bad(NEST))?;
    if bottom != ip.mk(elim.sym, arg_tms.to_vec()) {
        return Err(bad(NEST))
    }
    let unfold = derived::inst_all(&elim.ax, arg_tms).ok_or_else(|| bad(ABBREV))?;
    let step1 = eq_trans(ip, &beta_eq, &unfold).ok_or_else(|| bad(ABBREV))?;
    if *step1.concl()
        != Formula::eq(spine(&ap, head_tm, arg_tms), ap.apply(irec.clone(), major_tm.clone()))
    {
        return Err(bad(NEST))
    }

    // ── step 2: the major, down `⟦T.ctorᵢ⟧`'s nest and onto `ctor_term` ─────
    let (_, ctor_beta) =
        ip.beta_spine(&ctor_former, &ctor_tms, &c_mems).ok_or_else(|| bad(CTOR))?;
    // `IndexedTranslation::ctor_abbrev` is stated over `p⃗ ++ f⃗`, which is
    // `ctor_tms` entire — the same widening `Translated::ctor_abbrev` took, and
    // for the same reason: under `RecArg::general` the constructor term
    // mentions the parameters through its fibre summands. At `np = 0` the two
    // spellings are the same list.
    let cabbrev = tr.ctor_abbrev.get(i).ok_or_else(|| bad(CTOR))?;
    let cax = derived::inst_all(&cabbrev.1, &ctor_tms).ok_or_else(|| bad(CTOR))?;
    let ceq = eq_trans(ip, &ctor_beta, &cax).ok_or_else(|| bad(CTOR))?;
    let (ceq_lhs, ctor_term) = ceq.concl().as_eq().ok_or_else(|| bad(CTOR))?;
    if ceq_lhs != major_tm {
        return Err(bad(CTOR))
    }
    let cong = derived::congr(&mut ip.env_mut(), ap_sym, &[Thm::eq_refl(irec.clone()), ceq.clone()])
        .ok_or_else(|| bad(CTOR))?;
    let step2 = eq_trans(ip, &step1, &cong).ok_or_else(|| bad(CTOR))?;

    // ── `Hᵢ`, in **declared** field order, at the sets `derived` states it at ─
    let (mut ys, mut ts) = (Vec::with_capacity(k), Vec::with_capacity(m));
    for (j, sl) in spec.order.iter().enumerate() {
        match sl {
            Slot::Plain => ys.push(ctor_tms[np + j].clone()),
            Slot::Rec => ts.push(ctor_tms[np + j].clone()),
        }
    }
    // The rule's own variables at this call's terms — read off `iota_vars`,
    // which is exported precisely so the association is not reconstructed.
    let (yvs, tvs) = dr.iota_vars.get(i).cloned().ok_or_else(|| bad(RULE))?;
    if yvs.len() != k || tvs.len() != m {
        return Err(bad(RULE))
    }
    let mut hsub = ix.sub.clone();
    hsub.extend(yvs.iter().copied().zip(ys.iter().cloned()));
    hsub.extend(tvs.iter().copied().zip(ts.iter().cloned()));
    let iota_atoms = dr.iota_atoms.get(i).ok_or_else(|| bad(RULE))?;
    if iota_atoms.len() != k + m {
        return Err(bad(RULE))
    }

    let mut atoms: Vec<Thm> = Vec::with_capacity(k + m);
    // The raw field typings of the recursive slots, kept for step 4 — there the
    // child is a *major premise* and the β chain wants the interpretation's own
    // domain, not the set `Hᵢ` states.
    let mut t_raw: Vec<Thm> = Vec::with_capacity(m);
    let (mut plains, mut recs) = (0usize, 0usize);
    for (j, sl) in spec.order.iter().enumerate() {
        let mem = c_mems[np + j].clone();
        let out = match sl {
            Slot::Plain => {
                let mut a = at.ps.clone();
                a.extend(ys[..plains].iter().cloned());
                let ax = tr
                    .field_abbrev
                    .get(i)
                    .and_then(|f| f.get(plains))
                    .ok_or_else(|| bad(ATOM))?;
                let unfold = derived::inst_all(ax, &a).ok_or_else(|| bad(ATOM))?;
                let back = derived::eq_symm(&mut ip.env_mut(), &unfold).ok_or_else(|| bad(ATOM))?;
                plains += 1;
                ip.retarget_set(&mem, &back).ok_or_else(|| bad(ATOM))?
            }
            Slot::Rec => {
                // `tⱼ ∈ ⟦T p⃗ d⃗⟧`  ↦  `tⱼ ∈ ind(p⃗, ⟦d⃗⟧)`  ↦  `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ)`.
                let ds = childs.get(recs).ok_or_else(|| bad(ATOM))?.clone();
                let mut a = at.ps.clone();
                a.extend(ds.iter().map(|(t, _)| t.clone()));
                let mut sm = at.param_mems.clone();
                sm.extend(ds.iter().map(|(_, t)| t.clone()));
                let (_, beta) = ip.beta_spine(&at.former, &a, &sm).ok_or_else(|| bad(ATOM))?;
                let held = mem.concl().as_mem().ok_or_else(|| bad(ATOM))?.1;
                if beta.concl().as_eq().ok_or_else(|| bad(ATOM))?.0 != held {
                    return Err(bad(ATOM))
                }
                let onto = ip.retarget_set(&mem, &beta).ok_or_else(|| bad(ATOM))?;
                let before = tr.ii.spec.plains_before(i, recs).ok_or_else(|| bad(ATOM))?;
                let mut ia = at.ps.clone();
                ia.extend(ys.get(..before).ok_or_else(|| bad(ATOM))?.iter().cloned());
                let axs = tr
                    .ax
                    .ctors
                    .get(i)
                    .and_then(|cx| cx.rec_args.get(recs))
                    .ok_or_else(|| bad(ATOM))?;
                let cg = crate::ctor_ix::index_congr(ip, tr.ii.carrier.ty, &at.ps, &ds, axs, &ia)
                    .ok_or_else(|| bad(ATOM))?;
                let back = derived::eq_symm(&mut ip.env_mut(), &cg).ok_or_else(|| bad(ATOM))?;
                t_raw.push(mem.clone());
                recs += 1;
                ip.retarget_set(&onto, &back).ok_or_else(|| bad(ATOM))?
            }
        };
        if *out.concl() != subst_f(&iota_atoms[j], &hsub) {
            return Err(bad(ATOM))
        }
        atoms.push(out);
    }
    let hyp = atoms.iter().rev().cloned().reduce(|acc, t| derived::and_intro(&t, &acc));

    // ── step 3: the ι rule itself, at the caller's own terms ────────────────
    let mut rargs = at.ps.clone();
    rargs.push(at.c_tm.clone());
    rargs.extend(at.s_tms.iter().cloned());
    rargs.push(ix.target.clone());
    let rule = derived::inst_all(dr.iota.get(i).ok_or_else(|| bad(RULE))?, &rargs)
        .ok_or_else(|| bad(RULE))?;
    let over = Thm::mp(&rule, &ix.pre).ok_or_else(|| bad(RULE))?;
    let mut prefix = ys.clone();
    prefix.extend(ts.iter().cloned());
    let at_fields = derived::inst_all(&over, &prefix).ok_or_else(|| bad(RULE))?;
    let iota = match &hyp {
        None => at_fields,
        Some(h) => Thm::mp(&at_fields, h).ok_or_else(|| bad(RULE))?,
    };
    let vs: Vec<Term> = ts.iter().map(|t| ap.apply(irec.clone(), t.clone())).collect();
    let s_i = at.s_tms.get(i).ok_or_else(|| bad(SHAPE))?.clone();
    let base = applied_minor(&ap, &spec.order, &s_i, &ys, &ts, &[]);
    let landed = applied_minor(&ap, &spec.order, &s_i, &ys, &ts, &vs);
    if *iota.concl() != Formula::eq(ap.apply(irec.clone(), ctor_term), landed.clone()) {
        return Err(bad(RULE))
    }
    let step3 = eq_trans(ip, &step2, &iota).ok_or_else(|| bad(RULE))?;
    if landed == want {
        return Ok((step3, want))
    }

    // ── step 4: put the recursive results back in the Lean spelling ─────────
    //
    // `⟦rhs⟧` calls the eliminator again at the child's **own** index vector —
    // `Sᵢ y⃗ t⃗ (T.rec p⃗ C S⃗ d⃗ᵢ₀ t₀) …` — so the equation that closes each of
    // the `mᵢ` differences is step 1 again, at `d⃗ᵢⱼ` and `tⱼ`.
    let mut acc = Thm::eq_refl(base);
    for (j, t) in ts.iter().enumerate() {
        let ds = childs.get(j).ok_or_else(|| bad(RHS))?;
        let mut jargs = arg_tms[..np + 1 + n].to_vec();
        jargs.extend(ds.iter().map(|(t, _)| t.clone()));
        jargs.push(t.clone());
        let mut jmems = mems[..np + 1 + n].to_vec();
        jmems.extend(ds.iter().map(|(_, m)| m.clone()));
        jmems.push(t_raw.get(j).ok_or_else(|| bad(RHS))?.clone());
        let (_, jbeta) = ip.beta_spine(head_tm, &jargs, &jmems).ok_or_else(|| bad(NEST))?;
        let jax = derived::inst_all(&elim.ax, &jargs).ok_or_else(|| bad(ABBREV))?;
        let leg = eq_trans(ip, &jbeta, &jax).ok_or_else(|| bad(NEST))?;
        acc = derived::congr(&mut ip.env_mut(), ap_sym, &[acc, leg]).ok_or_else(|| bad(RHS))?;
    }
    let back = derived::eq_symm(&mut ip.env_mut(), &acc).ok_or_else(|| bad(RHS))?;
    let out = eq_trans(ip, &step3, &back).ok_or_else(|| bad(RHS))?;
    if out.concl().as_eq().map(|(_, r)| r) != Some(want.clone()) {
        return Err(bad(RHS))
    }
    Ok((out, want))
}

/// The binder types of a Π-telescope with the caller's arguments substituted as
/// the walk descends — so every entry is stated in the *use site's* frame and
/// no de Bruijn arithmetic leaks out of this function.
fn binder_types(ty: &E, args: &[E]) -> Option<Vec<E>> {
    let mut out = Vec::with_capacity(args.len());
    let mut cur = *ty;
    for a in args {
        let crate::expr::Expr::Forall { ty: dom, body } = &cur.clone().view() else { return None };
        out.push(*dom);
        cur = crate::expr::subst(body, a);
    }
    Some(out)
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
    use crate::expr::{app, app_n, bvar, konst, lam, Level};
    use crate::kernel::Checker;
    use std::rc::Rc;

    fn nm(s: &str) -> Name { Name::simple(s) }
    fn no() -> Rc<[Level]> { Vec::<Level>::new().into() }

    /// `T.rec.{1} B C S⃗ x y major`, at the synthetic indexed family
    /// [`crate::rec_ix_prop::tests::indexed_env`] declares:
    ///
    /// ```text
    /// inductive B : Type    | b0 | b1
    /// inductive T (α : Type) : B → B → Type
    ///   | c0 : T α b0 b0
    ///   | c1 : ∀ (x : B), T α x b0 → T α b1 x
    ///   | c2 : ∀ (x y : B), T α x y → T α y x → T α b0 b1
    /// ```
    ///
    /// The motive is constant (`λ x y t. B`) and **both recursive minors use an
    /// induction hypothesis**, so step 4 has something to do at each of them —
    /// and `c2`'s takes the *second*, whose child sits at the reversed index
    /// vector, which is the pairing `MINI-HANDOFF.md` §8 says a mispaired build
    /// gets wrong.
    fn elim(x: E, y: E, major: E) -> E {
        let (b, t) = (nm("B"), nm("T"));
        let bt = konst(b, no());
        let tap = |a: E, i: E, j: E| app(app(app(konst(t, no()), a), i), j);
        let b0 = konst(Name::str(&b, "b0"), no());
        // `C := λ (x y : B) (t : T B x y). B`
        let motive =
            lam(bt, lam(bt, lam(tap(bt, bvar(1), bvar(0)), bt)));
        // `c0`'s minor: `k + m = 0`, so `Hᵢ` is empty and the ι rule is applied
        // with no `mp` at all.
        let s0 = b0;
        // `c1`'s: `λ (x : B) (r : T B x b0) (ih : C x b0 r). ih`
        let s1 = lam(
            bt,
            lam(tap(bt, bvar(0), b0), lam(bt, bvar(0))),
        );
        // `c2`'s: `λ (x y : B) (r₁ : T B x y) (r₂ : T B y x) ih₁ ih₂. ih₂`
        let s2 = lam(
            bt,
            lam(
                bt,
                lam(
                    tap(bt, bvar(1), bvar(0)),
                    lam(
                        tap(bt, bvar(1), bvar(2)),
                        lam(bt, lam(bt, bvar(0))),
                    ),
                ),
            ),
        );
        app_n(konst(Name::str(&t, "rec"), vec![Level::zero().succ()].into()), &[
            bt, motive, s0, s1, s2, x, y, major,
        ])
    }

    /// The three majors, with the index vector each is eliminated at.
    fn majors() -> Vec<(&'static str, E, E, E)> {
        let (b, t) = (nm("B"), nm("T"));
        let bt = konst(b, no());
        let b0 = konst(Name::str(&b, "b0"), no());
        let b1 = konst(Name::str(&b, "b1"), no());
        let c = |s: &str| konst(Name::str(&t, s), no());
        // `c0 B : T B b0 b0`
        let c0 = app(c("c0"), bt);
        // `c1 B b0 (c0 B) : T B b1 b0`
        let c1 = app_n(c("c1"), &[bt, b0, c0]);
        // `c2 B b0 b0 (c0 B) (c0 B) : T B b0 b1`
        let c2_inner =
            app_n(c("c2"), &[bt, b0, b0, c0, c0]);
        // `c2 B b1 b0 (c1 …) (c2 …) : T B b0 b1` — the two children at
        // **different** index vectors, `(b1,b0)` and `(b0,b1)`.
        let c2 = app_n(c("c2"), &[bt, b1, b0, c1, c2_inner]);
        vec![
            ("c0", b0, b0, c0),
            ("c1", b1, b0, c1),
            ("c2", b0, b1, c2),
        ]
    }

    /// **The indexed ι rule fires with a certificate at every field shape** —
    /// `kᵢ = mᵢ = 0`, `(1,1)` and `(2,2)`.
    ///
    /// Non-vacuity, three ways, and they are `crate::iota_dep`'s: the two
    /// endpoints must differ, so nothing passes on reflexivity; the conclusion
    /// must be exactly `⟦T.rec …⟧ = ⟦whnf's reduct⟧`, so a composite that
    /// stopped at `app(irec, ctorᵢ)` — where three of the four steps stop — is a
    /// failure and not a pass; and `Γ` must be empty, since no binder is open.
    ///
    /// The `c2` row is the one that costs something: `whnf` runs the rule three
    /// times over (`c2` at the outer major, `c2` again at its second child,
    /// `c0` at the bottom), so a single gapped step anywhere in the chain
    /// leaves `conv.ev` without a theorem.
    #[test]
    fn the_indexed_iota_fires_at_a_use_site_at_every_field_shape() {
        let (env, t, _) = crate::rec_ix_prop::tests::indexed_env();
        for (what, x, y, major) in majors() {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            c.infer_type(&konst(t, no())).expect("infer ⟦T⟧");
            let e = elim(x, y, major);
            let ty = c.infer_type(&e).unwrap_or_else(|x| panic!("{what}: infer ⟦e⟧: {x}"));
            let tm = ty.tm.clone().unwrap_or_else(|| panic!("{what}: ⟦e⟧ is absent: {:?}", ty.ev));
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
    /// from the certificate assertion for `crate::iota_dep`'s reason: `whnf`
    /// chooses the reduct without consulting the evidence, so a wiring that
    /// certified the wrong equation and one that reduced wrongly are different
    /// failures and this is about acceptance.
    ///
    /// Every chain bottoms out at `c0`'s minor, `B.b0`, because the motive is
    /// constant and each recursive minor returns an induction hypothesis.
    #[test]
    fn every_major_reduces_through_the_declared_field_order_to_the_nullary_minor() {
        let (env, _, _) = crate::rec_ix_prop::tests::indexed_env();
        for (what, x, y, major) in majors() {
            let mut ip = Interp::new();
            let mut c = Checker::threaded(&env, &mut ip);
            let reduct = c.whnf(&elim(x, y, major)).unwrap_or_else(|e| panic!("{what}: {e}"));
            assert_eq!(
                reduct,
                konst(Name::str(&nm("B"), "b0"), no()),
                "{what}: the reduct is not the nullary minor"
            );
        }
    }
}
