//! **The indexed class-(T) eliminator at a value motive** — `⟦T.rec.{u₁,σ}⟧`
//! at `u₁ ≥ 1` for a family [`crate::zoneb::build_indexed`] translated
//! (`INDEXED-DESIGN.md` §5.1, and D8).
//!
//! # Interface
//!
//! ```text
//! rec_ix_dep::ensure(checker, T, σ_T, T.rec, σ_rec, np, n, ni, rec ty)
//! ```
//!
//! Called from [`crate::rec_dep::ensure`]'s `num_indices != 0` branch and from
//! nowhere else, on a recursor whose motive binder lands in `Sort u₁`, `u₁ ≥ 1`.
//! On success `⟦T.rec.{σ_rec}⟧` and its typing are in the store.
//!
//! # The obligation
//!
//! ```text
//! ⊢ ⟦T.rec⟧ ∈ ⟦Π p⃗ (C : Π x⃗ (t : T p⃗ x⃗). Sort u₁) (S⃗ : minors) x⃗ (t : T p⃗ x⃗). C x⃗ t⟧
//! ```
//!
//! `C x⃗ t` is a **fibre** varying with `t`, which is why no target policy
//! reaches it and why this waited on
//! [`IndexedDepRecursor`](derived::inductive::family::IndexedDepRecursor):
//!
//! ```text
//! ⊢ ∀p⃗ ∀m ∀S⃗ ∀T. ( ICOD(m,T) ∧ IDEP(m,S⃗) →
//!       ∀x⃗ ∀t. ( t ∈ ind(p⃗,x⃗) → app(irec,t) ∈ app(m,x⃗,t) ) )
//! ```
//!
//! with `irec := grec(p⃗, gmin⃗, T)` — §5.1's own term, `x⃗` nowhere in it. So
//! this module is [`crate::rec_ix_prop`] with three differences and a term:
//! [`crate::minor_ix`] transports `IDEPᵢ` instead of `MINORᵢ` (one
//! [`Clause`](crate::minor_ix::Clause)), `ICOD` has to be discharged, and the
//! bottom is `app(irec,t)` under a name of mini's own rather than `•`.
//!
//! # `T` is the rung the **motive** lives in, not the one its values live in
//!
//! `T` is a bound variable constrained only by `ICOD`, so the consumer chooses
//! it — and the obvious choice, [`crate::rec_dep::cod_at_rung`]'s `⟦Sort u₁⟧`,
//! is the wrong one here. That is worth stating because it is exactly the
//! interface risk D8's header flagged, and it is what makes the risk cost
//! nothing.
//!
//! `ICOV(m,T) := ∀x⃗ ∀z. (z ∈ W → ∀y. (y ∈ app(m,x⃗,z) → y ∈ T))` bounds `z` and
//! **not** `x⃗`. At `⟦Sort u₁⟧` the only route to `app(m,x⃗,z) ∈ T` is
//! [`Interp::fs_app`](crate::interp::Interp::fs_app) / `dprod_app`, both of
//! which consume a *domain membership* per level — and at a junk `x₀ ∉ ⟦I₀⟧`
//! there is none, so the discharge would need `app_off_domain` and a case split
//! per index.
//!
//! One rung up there is no case at all. [`derived::tower::Rung::app`] is
//! `⊢ ∀f ∀x. (f ∈ Uₙ → app(f,x) ∈ Uₙ)` — **unconditional in the argument**,
//! because `app(f,x)` is `∅` off the domain and `∅ ∈ Uₙ`. So with
//! `T := ⟦Sort ℓ⟧` for the `ℓ` the motive's own *type* inhabits, one
//! `Rung::transitive` puts `⟦C⟧` in `Uℓ`, `ni + 1` applications of `Rung::app`
//! walk the whole spine at *arbitrary* arguments, and one more `transitive`
//! finishes `ICOV`. No excluded middle, no `app_off_domain`, and the junk
//! indices are never distinguished from the real ones.
//!
//! So D8's flag is real and the alternative interface it proposes is not needed
//! *for this consumer*: the cost is the choice of rung, and the choice is
//! forced by which lemma is unconditional. `∅ ∈ T` is
//! [`derived::tower::Rung::empty_mem`].
//!
//! # The term needs a name of mini's own
//!
//! `irec` is assembled inside `derived`, so its applicative structure was never
//! recorded through [`Interp::mk`](crate::interp::Interp::mk) and the `λ`s
//! above it could not skeletonise a body that mentions the nest's binders. One
//! [`derived::define_abbrev`] over those binders fixes it, exactly as
//! [`crate::rec_dep`]'s value clause and [`crate::ctor_ix`] do.
//!
//! # What this does not give
//!
//! The **ι rule**. `INDEXED-DESIGN.md` §5.1 argues the indexed ι is the erased
//! one with `ni` dead binders, so `GenRecursor::iota` plus
//! `IndexedGuardedMinors::fires` should be all of it — but that is a separate
//! theorem with its own antecedent and D8 states plainly that it is neither
//! built nor tested. A use site that reduces `T.rec` at a constructor will
//! reach `Gap::Iota` and must, until it exists.
//!
//! # Nothing here searches
//!
//! The rule comes from a memo keyed on the declaration
//! ([`IndApparatus::indexed_dep_recursor`](crate::interp::IndApparatus)); each
//! minor is compared against `IDEPᵢ` rebuilt at mini's own terms, `ICOD`
//! against `ICOD` and their conjunction against `PRE`; and the bottom's
//! membership against `⟦C x⃗ t⟧` inferred from the recursor's declared codomain.

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::family::{minor_atoms_at, motive_app, IndexedDepRecursor};

use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::interp::Interp;
use crate::kernel::{Checker, Typing, R};
use crate::minor_ix::{self, At, Clause, Site};
use crate::rec_dep::{subst_f, subst_term};
use crate::scope::Scopes;

const ARITY: &str = "indexed value recursor: arity";
const DISAGREE: &str = "indexed value recursor: the recursor and the carrier disagree";
const MINOR: &str = "indexed value recursor: a minor premise does not transport";
const CARRIER: &str = "indexed value recursor: the carrier at the index binders";
const CODOMAIN: &str = "indexed value recursor: the codomain is not the motive at x⃗ and t";
const SORTS: &str = "indexed value recursor: the motive's sort and its codomain disagree";
const MOTIVE_TY: &str = "indexed value recursor: the motive's own type does not place";
const ICOD: &str = "indexed value recursor: ICOD at the motive's own rung";
const PREMISE: &str = "indexed value recursor: the premise is not IndexedDepRecursor's";
const TERM: &str = "indexed value recursor: naming the eliminator's term";

/// **`IndexedDepRecursor::over_family` declined this declaration** — the one
/// `Cause::Library` exit of this module.
pub const RULE: &str = "indexed value recursor: IndexedDepRecursor::over_family declined";

/// Make `⟦T.rec.{σ_rec}⟧` available for an indexed class-(T) declaration whose
/// motive lands in `Sort u₁`, `u₁ ≥ 1`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
    np: usize,
    n: usize,
    ni: usize,
    rec_ty: &E,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(ind_name.clone(), w, Cause::Threading);
    let ctors = match c.environment().get(ind_name) {
        Some(ConstantInfo::Inductive { ctors, .. }) => ctors.clone(),
        _ => return Err(Gap::NoInterpretation(ind_name.clone(), ind_inst.to_vec())),
    };
    let depth = np + 1 + n + ni + 1;
    let codomain = crate::zoneb::peel(rec_ty, depth).ok_or_else(|| bad(ARITY))?;

    let key = (ind_name.clone(), ind_inst.to_vec());
    let tr = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        app.indexed
            .get(&key)
            .cloned()
            .ok_or_else(|| bad("indexed value recursor: the family is not translated"))?
    };
    if tr.ii.spec.len() != n
        || tr.ii.spec.params() != np
        || tr.ii.spec.num_indices() != ni
        || ctors.len() != n
        || tr.base.params.len() != np
    {
        return Err(bad(DISAGREE))
    }

    let site = Site {
        ind: ind_name.clone(),
        inst: ind_inst.to_vec(),
        rec: rec_name.clone(),
        rec_inst: rec_inst.to_vec(),
        ctors,
        np,
        n,
        ni,
        depth,
        codomain,
        fam: minor_ix::Fam::ClassT(tr),
        minor_gap: MINOR,
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// The bottom of `⟦T.rec⟧`'s nest: `⊢ app(irec, ⟦t⟧) ∈ ⟦C x⃗ t⟧`.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let (np, n, ni, depth) = (site.np, site.n, site.ni, site.depth);

    // §6.2's split, taken twice and required to agree: `rec_dep` read it off
    // the motive's declared sort to get here, and this is the codomain the nest
    // actually reached. A `Prop` here is `crate::rec_ix_prop`'s clause.
    match c.is_prop(&site.codomain) {
        Ok(false) => (),
        Ok(true) => return gap(bad(SORTS)),
        Err(_) => return gap(Gap::Classifier),
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((tms, mems)) = c.binders(depth) else { return gap(Gap::NoEndpoint) };
    let Some(vars) = c.scope_vars(depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let mut ctor_formers = Vec::with_capacity(n);
    for name in &site.ctors {
        match c.stored_term(name, &site.inst) {
            Some(t) => ctor_formers.push(t),
            None => return gap(Gap::NoEndpoint),
        }
    }

    // **The motive's own type, inferred** — the rung `T` is read off it rather
    // than off `u₁`; see the module header.
    let motive_idx = match u32::try_from(depth - 1 - np) {
        Ok(v) => v,
        Err(_) => return gap(bad(DISAGREE)),
    };
    let Ok(m_ty_e) = c.local_type(motive_idx) else { return gap(bad(MOTIVE_TY)) };
    let Ok(m_ty) = c.infer_type(&m_ty_e) else { return gap(Gap::Classifier) };
    let Some(lvl) = crate::rec_dep::sort_of(&m_ty.ty) else { return gap(bad(MOTIVE_TY)) };
    let Some(m_ty_mem) = m_ty.ev.thm().cloned() else {
        return gap(m_ty.ev.reason(Gap::NoEndpoint))
    };

    let at = At {
        ps: tms[..np].to_vec(),
        param_mems: mems[..np].to_vec(),
        c_tm: tms[np].clone(),
        s_tms: tms[np + 1..np + 1 + n].to_vec(),
        s_mems: mems[np + 1..np + 1 + n].to_vec(),
        xs: tms[np + 1 + n..depth - 1].to_vec(),
        x_mems: mems[np + 1 + n..depth - 1].to_vec(),
        t_tm: tms[depth - 1].clone(),
        t_mem: mems[depth - 1].clone(),
        former,
        ctor_formers,
        goal,
        vars,
        all: tms.clone(),
    };
    if at.xs.len() != ni {
        return gap(bad(DISAGREE))
    }
    let c_mem = mems[np].clone();
    let _ = (n, ni);

    let pre = match premise_at(c, site, &at, None, &c_mem, &m_ty_mem, lvl) {
        Ok(p) => p,
        Err(g) => return gap(g),
    };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    match fire(ip, site, &pre, &at) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// **`PRE = ICOD(⟦C⟧,T) ∧ IDEP(⟦C⟧,⟦S⃗⟧)` at whatever terms the caller holds**,
/// with the rule it is stated about and the substitution that brought it here.
///
/// The eliminator's nest ([`rec_bottom`]) and the ι rule at a use site
/// ([`crate::iota_ix_dep`]) want the *same* premise about *different* terms —
/// binders in one case and arbitrary Lean arguments in the other — which is why
/// this takes an [`At`] and not a nest position. It is the indexed counterpart
/// of [`crate::rec_dep::pre_at`], and the reason it could not be written until
/// now is [`minor_ix::transport_at`]: at `ni > 0` a minor's transport reads
/// index expressions out of Lean syntax, and until that frame became a
/// parameter the walk could only be run at the eliminator's own telescope
/// (`MINI-HANDOFF.md` §8, construction 3).
///
/// `sources` is `None` at the eliminator's nest — the frame is read off the
/// checker telescope — and `Some` at a use site, one [`minor_ix::Source`] per
/// constructor.
pub(crate) fn premise_at(
    c: &mut Checker<'_, '_>,
    site: &Site,
    at: &At,
    sources: Option<&[minor_ix::Source]>,
    c_mem: &Thm,
    m_ty_mem: &Thm,
    lvl: u32,
) -> Result<IxPre, Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let (n, ni) = (site.n, site.ni);
    let tr = site.fam.class_t().ok_or_else(|| bad(DISAGREE))?.clone();
    if let Some(ss) = sources {
        if ss.len() != n {
            return Err(bad(DISAGREE))
        }
    }

    // The rule, once per declaration — a `w_rect` Separation, the guarded
    // minors' own, and a `GenRecursor` per build.
    let dr = {
        let (base, fam) = (tr.base.clone(), &tr.ii);
        let key = (site.ind.clone(), site.inst.clone());
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        app.indexed_dep_recursor(kenv, &key, &base, fam)
            .ok_or_else(|| Gap::Recursor(site.ind.clone(), RULE, Cause::Library))?
    };
    if dr.minors.len() != n || dr.xvs.len() != ni || dr.guards.dep_parts.len() != n {
        return Err(bad(DISAGREE))
    }

    let target = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        ip.sort(lvl)
    };
    let mut sub: Vec<(FreeVar, Term)> =
        tr.base.params.iter().copied().zip(at.ps.iter().cloned()).collect();
    sub.push((dr.motive, at.c_tm.clone()));
    for (v, t) in dr.minors.iter().zip(at.s_tms.iter()) {
        sub.push((*v, t.clone()));
    }
    sub.push((dr.target, target.clone()));

    // ── `IDEP`, one conjunct per constructor ────────────────────────────────
    let mut minors = Vec::with_capacity(n);
    for i in 0..n {
        let cs = tr.ii.spec.base.ctors.get(i).ok_or_else(|| bad(DISAGREE))?.clone();
        let (k, m) = (cs.args.len(), cs.recs);
        let (yvs, tvs, vvs) = dr.guards.vars.get(i).cloned().ok_or_else(|| bad(DISAGREE))?;
        // `IDEPᵢ`'s antecedent is `minor_atoms_at` — the same builder the
        // `Prop` rule's is, at the bound `vⱼ`. Rebuilt here at `derived`'s own
        // variables so that the walk's substitution is the only thing between
        // it and this nest's terms.
        let (src, mvars) = {
            let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
            let s = ip.prelude.tower.sums.clone();
            let ps: Vec<Term> = tr.base.params.iter().map(|v| Term::var(*v)).collect();
            let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
            let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
            let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();
            let atoms = minor_atoms_at(
                &s,
                &tr.ii.spec,
                &tr.ii.carrier,
                i,
                &Term::var(dr.motive),
                &ps,
                &ys,
                &ts,
                &vs,
            )
            .ok_or_else(|| bad(DISAGREE))?;
            let mut mv = derived::inductive::family::lean_order_of(&cs.order, &yvs, &tvs)
                .ok_or_else(|| bad(DISAGREE))?;
            mv.extend(vvs.iter().copied());
            (atoms, mv)
        };
        let clause = Clause { nvars: k + 2 * m, proof: false, motive: dr.motive, trunc: false };
        let t = match sources {
            None => minor_ix::transport(c, site, at, i, &src, &mvars, clause)?,
            Some(ss) => {
                minor_ix::transport_at(c, site, at, i, &ss[i], &src, &mvars, clause)?
            }
        };
        if *t.thm.concl() != subst_f(&dr.guards.dep_parts[i], &sub) {
            return Err(bad(MINOR))
        }
        minors.push(t.thm);
    }

    // ── `ICOD`, and each half compared against `derived`'s ──────────────────
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let icod =
        icod_at_rung(ip, site, &sub, c_mem, m_ty_mem, lvl, &target).ok_or_else(|| bad(ICOD))?;
    if *icod.concl() != subst_f(&dr.guards.cod, &sub) {
        return Err(bad(ICOD))
    }
    let dep_all = minors
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| bad("indexed value recursor: a declaration with no constructors"))?;
    if *dep_all.concl() != subst_f(&dr.guards.dep, &sub) {
        return Err(bad(MINOR))
    }
    let pre = derived::and_intro(&icod, &dep_all);
    if *pre.concl() != subst_f(&dr.premise, &sub) {
        return Err(bad(PREMISE))
    }
    Ok(IxPre { dr, pre, sub, target })
}

/// The rule, its premise discharged at the caller's own terms, and the two
/// things a consumer needs to instantiate it: the substitution `derived`'s
/// statements travel along and the target rung they were derived at.
pub(crate) struct IxPre {
    pub(crate) dr: Rc<IndexedDepRecursor>,
    pub(crate) pre: Thm,
    pub(crate) sub: Vec<(FreeVar, Term)>,
    pub(crate) target: Term,
}

/// The rule at `(⟦p⃗⟧, ⟦C⟧, ⟦S⃗⟧, T)` discharged at the major, and the bottom's
/// term.
fn fire(ip: &mut Interp, site: &Site, ix: &IxPre, at: &At) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind.clone(), w, Cause::Threading);
    let IxPre { dr, pre, sub, target } = ix;
    let s = ip.prelude.tower.sums.clone();
    let ap = s.ap.clone();

    // `⟦C x⃗ t⟧` is the motive's own curried spine — checked, because a recursor
    // concluding at some *fixed* index or constructor is a well-typed `Π`.
    if at.goal != motive_app(&s, &at.c_tm, &at.xs, &at.t_tm) {
        return Err(bad(CODOMAIN))
    }

    // ── the rule, instantiated and discharged ───────────────────────────────
    let mut args = at.ps.clone();
    args.push(at.c_tm.clone());
    args.extend(at.s_tms.iter().cloned());
    args.push(target.clone());
    let rule = derived::inst_all(&dr.typing, &args).ok_or_else(|| bad(DISAGREE))?;
    let over = Thm::mp(&rule, pre).ok_or_else(|| bad(PREMISE))?;

    let mut ia = at.xs.clone();
    ia.push(at.t_tm.clone());
    let at_t = derived::inst_all(&over, &ia).ok_or_else(|| bad(CARRIER))?;

    // The scope holds `⟦t⟧ ∈ ⟦T p⃗ x⃗⟧`, the applied spine; the rule speaks of
    // `ind(p⃗,⟦x⃗⟧)`. One β, with the equation's left-hand side required to be
    // the set the scope actually holds.
    let mut sa = at.ps.clone();
    sa.extend(at.xs.iter().cloned());
    let mut sm = at.param_mems.clone();
    sm.extend(at.x_mems.iter().cloned());
    let (_, beta) = ip.beta_spine(&at.former, &sa, &sm).ok_or_else(|| bad(CARRIER))?;
    let held = at.t_mem.concl().as_mem().ok_or_else(|| bad(CARRIER))?.1;
    if beta.concl().as_eq().ok_or_else(|| bad(CARRIER))?.0 != held {
        return Err(bad(CARRIER))
    }
    let t_in = ip.retarget_set(&at.t_mem, &beta).ok_or_else(|| bad(CARRIER))?;
    let mem = Thm::mp(&at_t, &t_in).ok_or_else(|| bad(CARRIER))?;

    // ── the term, under a name of mini's own ────────────────────────────────
    let raw = ap.apply(subst_term(&dr.rec, sub), at.t_tm.clone());
    let (sym, ax) = {
        let (kenv, _, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        derived::define_abbrev(kenv, &at.vars, &raw).ok_or_else(|| bad(TERM))?
    };
    let unfold = derived::inst_all(&ax, &at.all).ok_or_else(|| bad(TERM))?;
    let term = ip.mk(sym, at.all.clone());
    let out = ip.retarget_subject(&mem, &unfold).ok_or_else(|| bad(TERM))?;
    if *out.concl() != Formula::mem(term.clone(), at.goal.clone()) {
        return Err(bad("indexed value recursor: the eliminator did not land in the codomain"))
    }
    // **Kept, not spent** — the same move `crate::rec_dep`'s value clause makes,
    // stored *ahead of its consumer* rather than after it. `ax` is
    // `∀p⃗ C S⃗ x⃗ t. sym(…) = app(irec, t)` over the nest's own binders, so it
    // instantiates anywhere; `define_abbrev` mints a fresh symbol per call, so
    // re-minting it later gives a second name related to this one by nothing.
    // `crate::iota_dep` is the non-indexed consumer and the indexed ι
    // (`SCOPING.md` §8, construction 3) is the one this is for — see
    // `MINI-HANDOFF.md` §8 for why that row's remaining obstacle is
    // `minor_ix::transport` and *not* this.
    if let Some(app) = ip.ind_apparatus() {
        let key = (site.rec.clone(), site.rec_inst.clone());
        app.dep_elims
            .insert(key, Rc::new(crate::interp::DepElim { sym, ax, target: target.clone() }));
    }
    Ok((term, out))
}

/// `Γ ⊢ ICOD(⟦C⟧, ⟦Sort ℓ⟧)` — the target premise, at the rung the **motive's
/// own type** inhabits.
///
/// See the module header for why this rung and not `⟦Sort u₁⟧`. The whole of it
/// is: [`derived::tower::Rung::app`] is unconditional in the argument, so the
/// `ni` unbounded index binders of `ICOV` cost nothing and are never
/// distinguished from the reachable ones. The `∀`/`→` shape is
/// [`Closed::discharge`](crate::scope::Closed::discharge)'s, which is `ICOV`'s
/// on the nose for the two *bounded* binders; the `ni` unbounded ones are plain
/// [`kernel::Thm::gen_checked`].
#[allow(clippy::too_many_arguments)]
fn icod_at_rung(
    ip: &mut Interp,
    site: &Site,
    sub: &[(FreeVar, Term)],
    c_mem: &Thm,
    m_ty_mem: &Thm,
    lvl: u32,
    target: &Term,
) -> Option<Thm> {
    let rung = ip.prelude.tower.at(lvl as usize)?;
    if rung.set != *target {
        return None
    }
    // `⟦C⟧ ∈ Uℓ`: the motive's type is in `Uℓ` and `Uℓ` is transitive.
    let m_ty = m_ty_mem.concl().as_mem()?.0;
    let trans = derived::inst_all(&rung.transitive, std::slice::from_ref(&m_ty))?;
    let c_in = Thm::mp(&trans, m_ty_mem)?;
    let c_tm = c_mem.concl().as_mem()?.0;
    let c_in_rung = Thm::mp(&derived::inst_all(&c_in, std::slice::from_ref(&c_tm))?, c_mem)?;

    // The `ni` index binders, **unbounded** — `ICOV` does not restrict them and
    // `Rung::app` does not need them restricted.
    let mut xvs: Vec<kernel::FreeVar> = Vec::with_capacity(site.ni);
    let mut cur = c_in_rung;
    for _ in 0..site.ni {
        let v = ip.env.fresh_var();
        xvs.push(v);
        cur = app_in_rung(ip, &rung.app, &cur, &Term::var(v))?;
    }

    // …then the two bounded ones, which are scopes.
    let mut scopes = Scopes::new();
    let tok_z = scopes.open(&mut ip.env, subst_term(&site.fam.class_t().expect("class (T)").base.wty, sub));
    let (zt, _) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };
    let spine = app_in_rung(ip, &rung.app, &cur, &zt)?;
    let set = spine.concl().as_mem()?.0;

    let tok_y = scopes.open(&mut ip.env, set.clone());
    let (yt, ym) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };
    let trans = derived::inst_all(&rung.transitive, std::slice::from_ref(&set))?;
    let over = Thm::mp(&trans, &spine)?;
    let inner = Thm::mp(&derived::inst_all(&over, std::slice::from_ref(&yt))?, &ym)?;

    let fam = scopes.close(tok_y).discharge(&inner).ok()?;
    let mut covers = scopes.close(tok_z).discharge(&fam).ok()?;
    for v in xvs.iter().rev() {
        covers = Thm::gen_checked(*v, &covers)?;
    }
    Some(derived::and_intro(&covers, &rung.empty_mem))
}

/// `Γ ⊢ app(f,a) ∈ Uₙ` from `Γ ⊢ f ∈ Uₙ` — [`derived::tower::Rung::app`], which
/// asks nothing of `a`.
fn app_in_rung(ip: &mut Interp, rule: &Thm, f_mem: &Thm, a: &Term) -> Option<Thm> {
    let f = f_mem.concl().as_mem()?.0;
    let at = derived::inst_all(rule, &[f.clone(), a.clone()])?;
    let out = Thm::mp(&at, f_mem)?;
    let want = ip.app(f, a.clone());
    (out.concl().as_mem()?.0 == want).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{konst, Level};
    use std::rc::Rc;

    /// **The value clause reaches its own rule**, at the synthetic family
    /// [`crate::rec_ix_prop`]'s tests use — three constructors, two indices,
    /// and `c2`'s two recursive arguments at each other's reversed index
    /// vector.
    ///
    /// The three assertions are the ones every stored typing owes, and the
    /// third is the one this clause exists for: the set must be `⟦the
    /// recursor's declared type⟧` **inferred**, so a derivation that landed in
    /// the motive at some other index — or in the *target* `T` rather than in
    /// the fibre, which is exactly what `GenRecursor` alone would give — fails
    /// it. `⟦T.rec.{1}⟧` must also come apart again as a λ-nest, which a
    /// decline would leave as an opaque symbol and pass a weaker assertion.
    #[test]
    fn the_value_motive_indexed_eliminator_is_interpreted_with_its_typing() {
        let (env, t, rec) = crate::rec_ix_prop::tests::indexed_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        c.infer_type(&konst(t, Vec::new().into())).expect("infer ⟦T⟧");
        let at: Rc<[Level]> = vec![Level::Zero.succ()].into();
        let got = c.infer_type(&konst(rec.clone(), at)).expect("infer ⟦T.rec.{1}⟧");
        let m = got
            .ev
            .thm()
            .unwrap_or_else(|| panic!("⟦{rec}.{{1}}⟧ has no typing: {:?}", got.ev))
            .clone();
        assert!(m.hyps().is_empty(), "a stored typing is unconditional");
        let tm = got.tm.clone().expect("interpreted");
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, tm, "the typing must be about ⟦T.rec⟧ itself");
        let want = c.infer_type(&got.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…and about the recursor's own declared type");

        // The nest comes apart: `α, C, c0, c1, c2, x, y, t`.
        let mut cur = tm;
        let ip = c.interp().expect("threaded");
        for lv in 0..8 {
            let (site, _) =
                ip.as_lam(&cur).unwrap_or_else(|| panic!("not a λ at level {lv}"));
            let (skel, holes) = (site.skel.clone(), site.holes.clone());
            let x = Term::var(ip.env.fresh_var());
            cur = ip.rebuild(&skel, &holes, &x);
        }
    }
}
