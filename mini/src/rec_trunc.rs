//! **The class-(P) eliminator** — `⟦T.rec.{σ}⟧` for a `Prop` that is not
//! small-eliminating (MINI-DESIGN.md §9, `RECURSOR-DESIGN.md`).
//!
//! # Interface
//!
//! ```text
//! rec_trunc::ensure(checker, T, σ_T, T.rec, σ_rec, translation) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::recursor::ensure`] and nowhere else, on a declaration
//! whose **class-(P)** translation is in the store — a store read on the key
//! this call was handed, so the eliminator and the carrier cannot disagree
//! about which clause the declaration took. On success `⟦T.rec.{σ_rec}⟧` and
//! its typing are stored under the recursor's own instantiation.
//!
//! # The obligation, and why it is one clause rather than two
//!
//! ```text
//! ⊢ ⟦T.rec⟧ ∈ ⟦Π p⃗ (C : T p⃗ → Sort u₁) (S⃗ : minors) (t : T p⃗). C t⟧
//! ```
//!
//! [`crate::rec_dep`] splits on `u₁` because a class-(T) motive may land
//! anywhere. A class-(P) one may not: the declaration is a `Prop` that failed
//! Lean's subsingleton test, so its eliminator is **small** and `u₁` is `0` at
//! every σ. `C t` is then a proposition, `⟦T.rec⟧` is `•` by §6.2's left
//! column, and the whole obligation is that `⟦C t⟧` is *inhabited*. A recursor
//! whose motive lands above `Prop` is not this rule and is declined by
//! [`LARGE`] rather than given a typing — the check is on the recursor's own
//! motive binder, not on the carrier route that got us here.
//!
//! # What carries it
//!
//! [`derived::inductive::family::TruncRecursor`], one theorem per declaration:
//!
//! ```text
//! ⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) → ∀t. (t ∈ ‖ind(p⃗)‖ → • ∈ app(m, t)) )
//! ```
//!
//! so this module supplies three things and nothing else: the carrier
//! equation, the major premise moved along it, and Lean's minor premises
//! transported into `MINORᵢ`.
//!
//! # The transport, and the three ways it is *smaller* than `rec_dep`'s
//!
//! The walk is [`crate::rec_dep::minor_at`](crate::rec_dep)'s: one scope per
//! binder of the minor's own `Π`-interpretation, the matching application rule
//! read off [`Interp::as_pi`], then discharge and re-instantiate at the
//! statement's own arguments. Three things drop out that the class-(T) version
//! has to work for:
//!
//! * **No constructor spine.** `T p⃗` is a `Prop`, so `ctorᵢ y⃗ t⃗` is a *proof*
//!   and `⟦ctorᵢ y⃗ t⃗⟧` is `•` outright. The walk's last membership is already
//!   `• ∈ app(⟦C⟧, •)`; there is no `ctor_abbrev`, no `beta_spine` over the
//!   constructor and no Leibniz onto the motive's argument.
//! * **No `∀r⃗`, and no `∀ih⃗`.** A recursive argument of a `Prop` is a proof,
//!   so `MINORᵢ` states it as the *atom* `• ∈ ‖ind(p⃗)‖` rather than
//!   quantifying it; the induction hypotheses are the constant `• ∈ app(m,•)`
//!   for the same reason. Lean still binds all `kᵢ + 2mᵢ`, so those levels are
//!   re-instantiated at `•` and only the `kᵢ` plain fields are generalised.
//! * **The atom order is Lean's.** `TruncRecursor::minor_atoms` is already the
//!   declared field mask followed by the hypotheses, where `rect_step`'s is
//!   plains-then-recs — so level `l` of the walk answers atom `l`, and there
//!   is no permutation to get wrong. The atoms are *substituted from the
//!   theorem* rather than rebuilt, which is what its header asks a consumer to
//!   do.
//!
//! Two atoms still move between a set the interpretation names and one
//! `derived` names, each along an equation that was **kept** rather than
//! re-derived: a plain field's `⟦βⱼ⟧` along
//! [`TruncTranslation::field_abbrev`], and a recursive field's `⟦T p⃗⟧` along
//! the carrier abbreviation. Both live on the declaration's translation for
//! exactly this reason.
//!
//! # Nothing here searches, and the result is compared
//!
//! Each transported minor is checked against `TruncRecursor::minors`
//! rebuilt at mini's own terms before it is used, and the bottom's membership
//! against `• ∈ ⟦C t⟧` before it is returned. A recursor that is not of this
//! shape cannot make those comparisons succeed.

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::family::TruncRecursor;
use derived::inductive::Slot;

use crate::env::ConstantInfo;
use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::ground;
use crate::interp::{Interp, PiShape, TruncTranslation};
use crate::kernel::{Checker, Typing, R};
use crate::rec_dep::{gen_all_checked, hyp_inst, motive_level, subst_f};
use crate::scope::Scopes;

/// A class-(P) recursor whose motive lands above `Prop`. Not reachable from an
/// accepted export — Lean's `large_elim_test` is what put the declaration on
/// this route — but the route is chosen by the *carrier* and the level is read
/// off the *recursor*, and the two are independent claims.
const LARGE: &str = "class (P) eliminator: the motive is not Prop-valued";
const ARITY: &str = "class (P) eliminator: arity";
const MOTIVE: &str = "class (P) eliminator: the motive's binder is not a Lean motive";
const MOTIVE_TY: &str = "class (P) eliminator: the motive's type is not T p⃗ → Prop";
const DISAGREE: &str = "class (P) eliminator: the recursor and the carrier disagree";
const CARRIER: &str = "class (P) eliminator: the carrier equation";
const MINOR: &str = "class (P) eliminator: a minor premise does not transport";
const RULE: &str = "class (P) eliminator: TruncRecursor does not discharge here";

/// Make `⟦T.rec.{σ_rec}⟧` available for a class-(P) declaration, or say what
/// the wiring could not transport.
pub(crate) fn ensure(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind_inst: &[u32],
    rec_name: &Name,
    rec_inst: &[u32],
    tt: Rc<TruncTranslation>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::Recursor(*ind_name, w, Cause::Threading);
    let env = c.environment();
    let Some(ConstantInfo::Recursor { lparams, ty, num_params, num_minors, num_indices, .. }) =
        env.get(rec_name)
    else {
        return Err(Gap::NoInterpretation(*rec_name))
    };
    // An indexed class-(P) family is a different construction and not a
    // relaxed guard on this one — `TruncRecursor`'s header says why: its `φ` is
    // not constant in `z`, so none of the simplifications above hold. There is
    // no corpus witness, and the carrier route would not have produced a
    // non-indexed `tc` for one anyway.
    if *num_indices != 0 {
        return Err(Gap::IndexedFamily(*ind_name, "a class-(P) indexed eliminator"))
    }
    if rec_inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(*rec_name))
    }
    let (np, n) = (*num_params as usize, *num_minors as usize);
    let rec_ty = ground::subst_ground(ty, lparams, rec_inst);
    let depth = np + 1 + n + 1;
    let codomain = crate::zoneb::peel(&rec_ty, depth).ok_or_else(|| bad(ARITY))?;
    if motive_level(&rec_ty, np, 0).ok_or_else(|| bad(MOTIVE))? != 0 {
        return Err(bad(LARGE))
    }
    if tt.ind.spec.ctors.len() != n || tt.ind.params.len() != np || tt.tc.ctors.len() != n {
        return Err(bad(DISAGREE))
    }

    let site = Site { ind: *ind_name, inst: ind_inst.to_vec(), np, n, depth, codomain, tt };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(rec_bottom(c, &site)) };
    let t = c.lam_nest(&rec_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, rec_name, rec_inst, t)
}

/// Everything read off the declaration before a binder is opened.
struct Site {
    ind: Name,
    inst: Vec<u32>,
    np: usize,
    n: usize,
    /// `np + 1 + n + 1` — parameters, motive, minors, major premise.
    depth: usize,
    codomain: E,
    tt: Rc<TruncTranslation>,
}

/// The bottom of `⟦T.rec⟧`'s nest: `•`, with `⊢ • ∈ ⟦C t⟧`.
fn rec_bottom(c: &mut Checker<'_, '_>, site: &Site) -> Typing {
    let ty = site.codomain;
    let gap = |g: Gap| Typing { ty, tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);

    // §6.2's split, taken twice and required to agree: once from the motive's
    // declared sort (in `ensure`), once from the codomain the nest reached.
    match c.is_prop(&site.codomain) {
        Ok(true) => {}
        Ok(false) => return gap(bad("class (P) eliminator: the codomain is not a Prop")),
        Err(_) => return gap(Gap::Classifier),
    }
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some((xs, mems)) = c.binders(site.depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    match build(ip, site, &At { xs, mems, former, goal }) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

/// What the nest's own scopes hold at the bottom, plus the store read.
struct At {
    /// `⟦p⃗⟧, ⟦C⟧, ⟦S⃗⟧, ⟦t⟧`, outermost first.
    xs: Vec<Term>,
    /// Their scope typings, in the same order.
    mems: Vec<Thm>,
    former: Term,
    /// `⟦C t⟧`, the set the bottom's membership must be about.
    goal: Term,
}

/// The bottom's working context, at mini's own terms.
struct Cx {
    ps: Vec<Term>,
    c_tm: Term,
    s_tms: Vec<Term>,
    s_mems: Vec<Thm>,
    t_tm: Term,
    /// `Γ ⊢ ⟦t⟧ ∈ ‖ind(p⃗)‖`.
    t_in_carrier: Thm,
    /// `Γ ⊢ ‖ind(p⃗)‖ = ⟦T p⃗⟧` — the carrier equation the way a recursive
    /// atom needs it, which is the only direction a minor premise wants.
    from_trunc: Thm,
    /// `Γ ⊢ app(⟦C⟧, •) ∈ ⟦Prop⟧` — what proof irrelevance costs at a
    /// field-free minor.
    cx_pt_mem: Thm,
    /// The declaration's parameter variables at `⟦p⃗⟧`.
    psub: Vec<(FreeVar, Term)>,
}

fn build(ip: &mut Interp, site: &Site, at: &At) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::Recursor(site.ind, w, Cause::Threading);
    let (np, n, depth) = (site.np, site.n, site.depth);
    let tt = site.tt.clone();
    let point = ip.point();

    let ps = at.xs[..np].to_vec();
    let param_mems = at.mems[..np].to_vec();
    let c_tm = at.xs[np].clone();
    let c_mem = at.mems[np].clone();
    let s_tms = at.xs[np + 1..np + 1 + n].to_vec();
    let s_mems = at.mems[np + 1..np + 1 + n].to_vec();
    let t_tm = at.xs[depth - 1].clone();
    let t_mem = at.mems[depth - 1].clone();

    // ── the one equation everything downstream travels on ───────────────────
    //
    // `⟦T p⃗⟧ = sym(p⃗)` is the type former's own β at these parameters and
    // `sym(p⃗) = ‖ind(p⃗)‖` the abbreviation `zoneb::build_trunc` minted; their
    // composite is the only bridge between what the nest holds and what
    // `TruncCarrier` states.
    let (_, beta) = ip.beta_spine(&at.former, &ps, &param_mems).ok_or_else(|| bad(CARRIER))?;
    let ax_at = derived::inst_all(&tt.abbrev, &ps).ok_or_else(|| bad(CARRIER))?;
    let to_trunc = derived::eq_trans(&mut ip.env_mut(), &beta, &ax_at).ok_or_else(|| bad(CARRIER))?;
    let from_trunc = derived::eq_symm(&mut ip.env_mut(), &to_trunc).ok_or_else(|| bad(CARRIER))?;
    let (spine, _) = to_trunc.concl().as_eq().ok_or_else(|| bad(CARRIER))?;
    let t_in_carrier = ip.retarget_set(&t_mem, &to_trunc).ok_or_else(|| bad(CARRIER))?;

    // ── `• ∈ ⟦T p⃗⟧`, from the major premise and `only_point` ────────────────
    //
    // The truncation is inhabited *because the nest is standing in it*: `t` is
    // the major premise's own binder, and every inhabitant of `‖ind(p⃗)‖` is the
    // point. Nothing about the constructors is needed for this.
    let mut op_args = ps.clone();
    op_args.push(t_tm.clone());
    let op = derived::inst_all(&tt.tc.only_point, &op_args).ok_or_else(|| bad(CARRIER))?;
    let t_is_pt = Thm::mp(&op, &t_in_carrier).ok_or_else(|| bad(CARRIER))?;
    let back = derived::eq_symm(&mut ip.env_mut(), &t_is_pt).ok_or_else(|| bad(CARRIER))?;
    let pt_in_spine = ip.retarget_subject(&t_mem, &back).ok_or_else(|| bad(CARRIER))?;

    // ── the motive is a function into `⟦Prop⟧` ──────────────────────────────
    //
    // `C : T p⃗ → Sort 0` is binder-free in its codomain and `Sort 0` is not a
    // `Prop`, so §6.2's clause for it is the **dependent product at the
    // constant fibre** — there is no binder-free clause (`SCOPING.md` §10).
    // Read off the binder's own scope typing rather than assumed, and the one
    // thing it is spent on is `app(C,•) ∈ ⟦Prop⟧`, which is what proof
    // irrelevance wants at a minor with no fields.
    //
    // **This is the one of the four that also moves an application rule.** The
    // motive is not only *named* here, it is *applied*, so `fs_app` becomes
    // `dprod_app` at the same site — which is why `const_fibre_site` exists
    // beside `const_dprod` rather than the term-former being enough.
    let u0 = ip.sort(0);
    let set = c_mem.concl().as_mem().ok_or_else(|| bad(MOTIVE_TY))?.1;
    let fsite = ip.const_fibre_site(&u0).ok_or_else(|| bad(MOTIVE_TY))?;
    if set != ip.dprod_term(&fsite, spine.clone()) {
        return Err(bad(MOTIVE_TY))
    }
    let cx_pt_mem = ip
        .dprod_app(&fsite, &spine, &c_tm, &point, &c_mem, &pt_in_spine)
        .ok_or_else(|| bad(MOTIVE_TY))?;

    let psub: Vec<(FreeVar, Term)> =
        tt.ind.params.iter().copied().zip(ps.iter().cloned()).collect();
    let cx = Cx {
        ps,
        c_tm,
        s_tms,
        s_mems,
        t_tm,
        t_in_carrier,
        from_trunc,
        cx_pt_mem,
        psub,
    };

    // ── the rule, one per declaration ───────────────────────────────────────
    let key = (site.ind, crate::ground::ground_levels(&site.inst));
    let tr = {
        let (mut kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let kenv = &mut *kenv;
        app.trunc_recursor(kenv, &key, &tt).ok_or({
            Gap::Recursor(
                site.ind,
                "class (P) eliminator: TruncRecursor::over_declaration declined",
                Cause::Library,
            )
        })?
    };

    // ── Lean's minor premises, transported ──────────────────────────────────
    let mut sub = cx.psub.clone();
    sub.push((tr.motive, cx.c_tm.clone()));
    let mut minors = Vec::with_capacity(n);
    for i in 0..n {
        let got = minor_at(ip, site, &cx, &tr, i).ok_or_else(|| bad(MINOR))?;
        if *got.concl() != subst_f(tr.minors.get(i).ok_or_else(|| bad(DISAGREE))?, &sub) {
            return Err(bad(MINOR))
        }
        minors.push(got);
    }
    let all = minors
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| bad("class (P) eliminator: a declaration with no constructors"))?;

    // ── discharged at these parameters and this motive ──────────────────────
    let mut args = cx.ps.clone();
    args.push(cx.c_tm.clone());
    let rule = derived::inst_all(&tr.rec, &args).ok_or_else(|| bad(RULE))?;
    let over = Thm::mp(&rule, &all).ok_or_else(|| bad(RULE))?;
    let at_t = derived::inst_all(&over, std::slice::from_ref(&cx.t_tm)).ok_or_else(|| bad(RULE))?;
    let mem = Thm::mp(&at_t, &cx.t_in_carrier).ok_or_else(|| bad(RULE))?;
    if *mem.concl() != Formula::mem(point.clone(), at.goal.clone()) {
        return Err(bad("class (P) eliminator: the rule did not land in the codomain"))
    }
    Ok((point, mem))
}

/// `⊢ MINORᵢ(⟦C⟧)` from the minor binder's own scope typing.
///
/// One scope per binder of the minor's `Π`-interpretation, the matching
/// application rule, then discharge and re-instantiate — `rec_dep::minor_at`'s
/// walk, with the three simplifications the module header lists. The `kᵢ + mᵢ`
/// field levels are Lean's declared order, which is also
/// `TruncRecursor::minor_atoms`' order, so level `l` answers atom `l`.
fn minor_at(ip: &mut Interp, site: &Site, cx: &Cx, tr: &TruncRecursor, i: usize) -> Option<Thm> {
    let ap = ip.prelude.tower.sums.ap.clone();
    let point = ip.point();
    let tt = site.tt.clone();
    let order = tt.ind.spec.ctors.get(i)?.order.clone();
    let tcc = tt.tc.ctors.get(i)?;
    let (k, m) = (tcc.yvs.len(), tcc.tvs.len());
    if order.len() != k + m {
        return None
    }
    let nlev = k + 2 * m;

    // ── one scope per binder of the minor's Π-interpretation ────────────────
    let mut scopes = Scopes::new();
    let mut toks = Vec::new();
    let (mut ws, mut wvs) = (Vec::new(), Vec::new());
    let mut f_tm = cx.s_tms[i].clone();
    let mut f_mem = cx.s_mems[i].clone();
    for _ in 0..nlev {
        let set = f_mem.concl().as_mem()?.1;
        let shape = ip.as_pi(&set)?;
        let tok = scopes.open(&mut ip.env_mut(), shape.dom());
        let (wv, wt, wm) = {
            let sc = scopes.get(0)?;
            (sc.var(), sc.term(), sc.assumption().clone())
        };
        toks.push(tok);
        let out = match &shape {
            PiShape::Dep { site, dom } => ip.dprod_app(site, dom, &f_tm, &wt, &f_mem, &wm),
            PiShape::Prop { site, dom } => ip.cond_app(site, dom, &f_mem, &wt, &wm),
        }?;
        f_tm = out.concl().as_mem()?.0;
        f_mem = out;
        ws.push(wt);
        wvs.push(wv);
    }

    // ── the conclusion: `• ∈ app(⟦C⟧, •)`, with no spine to chase ───────────
    //
    // `ctorᵢ y⃗ t⃗ : T p⃗` is a *proof*, so its interpretation is `•` outright
    // and the motive's argument is already the point. What may not be `•` is
    // the *subject*: at a constructor with no fields no application rule fires
    // at all and the minor binder's own scope variable is still there. §6.2
    // gives it `•` by proof irrelevance, which is `app(C,•) ∈ ⟦Prop⟧` away.
    let (subject, set) = f_mem.concl().as_mem()?;
    if set != ap.apply(cx.c_tm.clone(), point.clone()) {
        return None
    }
    let mut chain = f_mem.clone();
    if subject != point {
        let pt = ip.point_of_proof(&cx.cx_pt_mem, &f_mem)?;
        let back = derived::eq_symm(&mut ip.env_mut(), &pt)?;
        chain = ip.retarget_subject(&chain, &back)?;
    }

    // ── discharge, innermost first ──────────────────────────────────────────
    for _ in 0..nlev {
        let closed = scopes.close(toks.pop()?);
        chain = closed.discharge(&chain).ok()?;
    }

    // ── the statement's own arguments and atoms ─────────────────────────────
    //
    // A recursive field and an induction hypothesis are proofs, so `MINORᵢ`
    // names `•` where Lean binds a variable; only the plain fields survive as
    // arguments, and only they are generalised at the end.
    let plain = |l: usize| l < k + m && matches!(order[l], Slot::Plain);
    let args: Vec<Term> =
        (0..nlev).map(|l| if plain(l) { ws[l].clone() } else { point.clone() }).collect();
    let (mut ys, mut yvs) = (Vec::new(), Vec::new());
    for l in 0..k + m {
        if plain(l) {
            ys.push(ws[l].clone());
            yvs.push(wvs[l]);
        }
    }
    if ys.len() != k {
        return None
    }

    // The atoms are **substituted from the theorem**, not rebuilt: its header
    // asks a consumer to do exactly that, so that the association and the order
    // are the ones it carries rather than the ones this site guessed.
    let mut sub = cx.psub.clone();
    sub.push((tr.motive, cx.c_tm.clone()));
    for (v, y) in tcc.yvs.iter().zip(ys.iter()) {
        sub.push((*v, y.clone()));
    }
    let atoms: Vec<Formula> =
        tr.minor_atoms.get(i)?.iter().map(|a| subst_f(a, &sub)).collect();
    if atoms.len() != nlev {
        return None
    }

    // The equation that moves level `l`'s set onto the one the atom names.
    let mut set_eq: Vec<Option<Thm>> = Vec::with_capacity(nlev);
    let mut plains = 0usize;
    for l in 0..nlev {
        if l >= k + m {
            // An induction hypothesis is `• ∈ app(m,•)` on both sides.
            set_eq.push(None);
        } else if plain(l) {
            let mut a = cx.ps.clone();
            a.extend(ys[..plains].iter().cloned());
            set_eq.push(derived::inst_all(tt.field_abbrev.get(i)?.get(plains)?, &a));
            plains += 1;
        } else {
            set_eq.push(Some(cx.from_trunc.clone()));
        }
    }

    // ── re-instantiate, discharging each antecedent from the conjunction ────
    let hyp = derived::conj_of(&atoms);
    let mut cur = match &hyp {
        None => chain,
        Some(h) => derived::a1i(&chain, h.clone()),
    };
    for (l, arg) in args.iter().enumerate() {
        cur = hyp_inst(&cur, arg)?;
        let ante = cur.concl().as_imp()?.1.as_imp()?.0;
        let step = at_atom(ip, &atoms, l, &ante, set_eq[l].as_ref())?;
        cur = derived::hyp_mp(&cur, &step)?;
    }
    gen_all_checked(&yvs, &cur)
}

/// `⊢ H → ante`, where `ante` is `atoms[i]` up to the set it is stated at.
///
/// [`crate::rec_dep`]'s is the same rule at the same three cases; it is not
/// shared because that one is private to a module whose `Cx` this one does not
/// have, and a `pub(crate)` on it would export a helper whose contract is two
/// lines longer than its body.
fn at_atom(
    ip: &mut Interp,
    atoms: &[Formula],
    i: usize,
    ante: &Formula,
    eq: Option<&Thm>,
) -> Option<Thm> {
    let base = derived::conj_proj(atoms, i)?;
    if atoms[i] == *ante {
        return Some(base)
    }
    let (subj, s1) = atoms[i].as_mem()?;
    let (subj2, s2) = ante.as_mem()?;
    if subj != subj2 {
        return None
    }
    let eq = eq?;
    if eq.concl().as_eq()? != (s1.clone(), s2.clone()) {
        return None
    }
    let hole = ip.fresh_var();
    let leib = Thm::eq_leibniz(s1, s2, hole, Formula::mem(subj, Term::var(hole)));
    derived::syl(&base, &Thm::mp(&leib, eq)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use crate::interp::Interp;
    use std::rc::Rc;

    /// **A class-(P) eliminator over a constructor with `mᵢ > 0`, at an
    /// interleaved field mask** — the half of this module no export reaches.
    ///
    /// `069`'s `BoolProp` has `np = kᵢ = mᵢ = 0` and `070`'s `Exists` has
    /// `kᵢ = 2, mᵢ = 0`, so between them the corpus exercises the plain fields
    /// and nothing else. Three things are live only here:
    ///
    /// * a **recursive** minor level, which `MINORᵢ` states at `•` rather than
    ///   quantifying, so the walk's binder is re-instantiated at the point and
    ///   its atom travels along the carrier abbreviation;
    /// * the **induction hypotheses**, likewise at `•`, whose atom is the
    ///   constant `φ` and needs no equation at all;
    /// * the **mask**, `Plain Rec Plain Rec`, which is the only thing that
    ///   tells Lean's declared order apart from plains-then-recs. Two fields
    ///   would pass under a wrong split; four with two distinct plains do not.
    ///
    /// ```text
    /// inductive R (α : Type) : Prop | leaf : R α | node : α → R α → α → R α → R α
    /// ```
    ///
    /// `R` is class (P) and not class (S): two constructors, so it is not a
    /// subsingleton, and its eliminator is small. The assertions are the three
    /// every stored typing owes, plus the one that makes the parameter
    /// load-bearing — the set is `⟦R.rec⟧`'s own declared type, inferred, so a
    /// build that landed in the truncation at some other parameter fails it.
    #[test]
    fn a_class_p_eliminator_over_a_recursive_interleaved_constructor() {
        let r = Name::simple("R");
        let leaf = Name::str(&r, "leaf");
        let node = Name::str(&r, "node");
        let no: Rc<[Level]> = Vec::new().into();
        let k = || konst(r, no.clone());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: r,
                lparams: vec![],
                num_params: 1,
                ty: forall(sort(Level::zero().succ()), sort(Level::zero())),
                ctors: vec![
                    (leaf, forall(sort(Level::zero().succ()), app(k(), bvar(0)))),
                    (
                        node,
                        forall(
                            sort(Level::zero().succ()),
                            forall(
                                bvar(0),
                                forall(
                                    app(k(), bvar(1)),
                                    forall(
                                        bvar(2),
                                        forall(app(k(), bvar(3)), app(k(), bvar(4))),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ],
            },
        )
        .expect("R is accepted");

        let rec = Name::str(&r, "rec");
        let lparams = match env.get(&rec) {
            Some(ConstantInfo::Recursor { lparams, .. }) => lparams.len(),
            other => panic!("R.rec is not a recursor: {other:?}"),
        };
        assert_eq!(lparams, 0, "a class-(P) eliminator is small, so its motive has no level");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        c.infer_type(&konst(r, no.clone())).expect("infer ⟦R⟧");
        let got = c.infer_type(&konst(rec, no)).expect("infer ⟦R.rec⟧");
        let m = got
            .ev
            .thm()
            .unwrap_or_else(|| panic!("⟦{rec}⟧ has no typing: {:?}", got.ev))
            .clone();
        assert!(m.hyps().is_empty(), "a stored typing is unconditional");
        let tm = got.tm.clone().expect("⟦R.rec⟧ interprets");
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, tm, "the typing must be about ⟦R.rec⟧ itself");
        let want = c.infer_type(&got.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…and about its own Lean type");
        assert_eq!(
            tm,
            c.interp().expect("threaded").point(),
            "a class-(P) eliminator's codomain is a Prop, so the whole constant is a proof"
        );
        // **And it went through *this* route.** A typing alone would not say
        // so: `⟦R.rec⟧ = •` is what every small eliminator's bottom returns, so
        // the class-(S) rule would satisfy every assertion above. The two store
        // entries are `zoneb::build_trunc`'s and this module's own answers.
        let key = (r, Vec::new());
        let app = c.interp().expect("threaded").ind_apparatus().expect("apparatus");
        assert!(app.truncs.contains_key(&key), "R took the class-(P) carrier route");
        assert!(app.stored_trunc_rec(&key).is_some(), "…and TruncRecursor is what typed it");
    }
}
