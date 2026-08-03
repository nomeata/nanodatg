//! **The class-(S) clause at an index** — Carneiro §5.3's subsingleton carrier
//! when the declaration has indices.
//!
//! # Interface
//!
//! ```text
//! class_s_ix::build(checker, T, σ, np, ni, ty, ctor tys, walk, level) -> Result<(), Gap>
//! class_s_ix::of(checker, T, σ)                                       -> Option<Rc<ClassSIx>>
//! ```
//!
//! [`build`] is called from [`crate::zoneb::ensure`] on the branch that used to
//! decline, and stores `⟦T.{σ}⟧` and every `⟦T.ctor.{σ}⟧` exactly as
//! [`crate::class_s`] does at `ni = 0`.
//!
//! # What is different from `ni = 0`, and it is only the carrier
//!
//! [`crate::class_s`] reads `A_φ(p⃗)` as a conditional singleton directly,
//! because at `ni = 0` the index space is one point and `A_φ` **is** the truth
//! value. At `ni ≥ 1` it is not: `A_φ` is a subset of a genuine `Σ` nest, and
//! the carrier at `x⃗` is the *proposition* `[tup(x⃗) ∈ acc(A_φ,R)]` — a set
//! that has to be minted. `derived::inductive::family::LeIndexCarrier` mints
//! it, one `prop::conditional_singleton` of arity `np + ni`, and everything
//! else on this route is the non-indexed one with `x⃗` threaded through.
//!
//! Two consequences worth stating because they are what a reader expects to
//! find and does not:
//!
//! * **`in_u0` is unconditional**, exactly as `LeProp`'s and
//!   `TruncCarrier`'s are — `χ ⊆ 1` whatever the condition is — so the former's
//!   typing needs no `H`, no size argument and no parameter typings. The index
//!   does not cost a rung.
//! * **`ulift_ℓ` is nothing.** `thesis.txt:1886` writes the carrier with a
//!   `ulift_ℓ` around it and `:2106`/`:2284` say `⟦ulift α⟧ = ⟦α⟧`; the level
//!   survives only in the *universe statement*, which is one
//!   [`Interp::raise_in_gamma`](crate::interp::Interp::raise_in_gamma) here as
//!   it is at `ni = 0`.
//!
//! # The constructor is the interesting half, and it is the walk's evidence
//!
//! `LeCarrier::intro[i]`'s antecedent is `Hᵢ ∧ Eᵢ` — the `kᵢ` plain-field
//! typings **followed by the `ni` result-index typings**, and at `ni ≥ 1` it is
//! never empty. The field half is [`crate::class_s`]'s verbatim. The index half
//! is `⊢ eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, e⃗<ₖ)`, at the *symbols*, while what a nest holds is
//! the codomain's index expressions **inferred** — `⊢ ⟦eₖ⟧ ∈ ⟦Iₖ⟧`. Moving
//! between the two is [`crate::ctor_ix`]'s step and is done by calling into it:
//! the subject travels along `CtorIndexAx::result[k]` and the set along
//! `IndexAx::indices[k]` plus one
//! [`index_congr`](crate::ctor_ix::index_congr), because `ιₖ` has arity
//! `np + k` and may mention the earlier index *expressions*.
//!
//! **Those axioms are the boundary walk's, and they are here only because the
//! walk's products now outlive the decline** ([`crate::zoneb::IndexedWalk`]).
//! They record which *field* each index slot's expression came from, which
//! `IndexedDeclSpec` does not, and `SortElimProp.mk : ∀ b b1 b2.
//! SortElimProp b b2 b1` puts its two fields into its two slots swapped — so
//! this is not a hypothetical dependence.
//!
//! # What this route declines
//!
//! * **a recursive constructor** — `LeIndexCarrier::ctor_intro` is `None` for
//!   the whole vector, not empty, and its header says why: the rule would need
//!   `Acc::acc_intro`'s *universally quantified* premise plus an inversion of
//!   `LeCarrier::rel_ax`, and there is **no recursive class-(S) declaration
//!   anywhere in this repository**. Declined by name here rather than
//!   improvised. If a witness ever appears, that is a finding and the decline
//!   is where it will surface.
//! * **`ni = 0`** — [`crate::class_s`]'s, and `LeIndexCarrier::build` refuses
//!   it too, so the two cannot both claim a declaration.
//!
//! # Nothing here searches
//!
//! The route is `zoneb::ensure`'s trichotomy on the declaration's own level and
//! the recursor's level-parameter count. Inside, every theorem is composed
//! forward and compared against the statement it is supposed to be — and the
//! carrier's own accessors ([`LeIndexCarrier::at`], `chi_at`) are used rather
//! than the raw fields, because a checker holds Lean index expressions and the
//! module's `x⃗` are its own fresh variables.

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::family::{IndexSpace, LeCarrier, LeIndexCarrier};
use derived::inductive::Slot;
use derived::inst_all;

use crate::ev::{Cause, Ev, Gap};
use crate::expr::{Name, E};
use crate::kernel::{Checker, Typing, R};
use crate::zoneb::IndexedWalk;

/// A recursive class-(S) declaration at an index. See the header: the rule is
/// `le_rec`-shaped and has no witness, so it is named rather than approximated.
pub const RECURSIVE: &str =
    "class (S) at an index: a recursive constructor, which LeIndexCarrier declines";


/// One translated class-(S) **indexed** declaration, at one instantiation.
///
/// Kept whole for the reason [`crate::class_s::ClassS`] is: the eliminator is a
/// second build over the *same* `A_φ` and the same `χ`, and rebuilding either
/// there would mint a second Separation that no equation relates to the one the
/// type former was stored at.
pub struct ClassSIx {
    /// The boundary walk, retained across what used to be this route's decline
    /// — the spec, the index abbreviations' defining axioms, and the field
    /// families. See [`crate::zoneb::IndexedWalk`].
    pub walk: Rc<IndexedWalk>,
    /// The `Σ` nest the indices range over.
    pub ix: IndexSpace,
    /// `A_φ`, `R`, `acc(A_φ,R)` and the introduction rules.
    pub lc: LeCarrier,
    /// `χ`, the carrier at an index, and everything `derived` proved about it.
    pub lic: LeIndexCarrier,
    /// The kernel variables `p⃗` every theorem above is stated at.
    pub params: Vec<FreeVar>,
}

impl ClassSIx {
    pub fn np(&self) -> usize { self.walk.spec.params() }
    pub fn ni(&self) -> usize { self.walk.spec.num_indices() }
}

/// The built objects for `(T, σ)`, if this route built them.
///
/// The consumer is [`crate::rec_s_ix`], which needs the *same* `A_φ` and the
/// *same* `χ` this carrier was stored at — a second build would mint a second
/// Separation that no equation relates to the one the type former is about.
/// Stored ahead of that consumer for one commit, as `zoneb::IndexAx` was, and
/// read by it in the next.
pub(crate) fn of(c: &mut Checker<'_, '_>, ind_name: &Name, inst: &[u32]) -> Option<Rc<ClassSIx>> {
    let ip = c.interp()?;
    let app = ip.ind_apparatus()?;
    app.props_ix.get(&(ind_name.clone(), inst.to_vec())).cloned()
}

/// `⟦T.{σ}⟧` and `⟦T.ctor.{σ}⟧` for one class-(S) declaration with indices.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ni: usize,
    ctor_tys: &[(Name, E)],
    ind_ty: &E,
    level: u32,
    walk: Rc<IndexedWalk>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndexedFamily(ind_name.clone(), w);
    if walk.spec.base.ctors.iter().any(|cs| cs.recs != 0) {
        return Err(bad(RECURSIVE))
    }
    if walk.spec.params() != np || walk.spec.num_indices() != ni {
        return Err(bad("class (S) at an index: the walk and the declaration disagree"))
    }

    let built = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let tower = ip.prelude.tower.clone();
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let params: Vec<FreeVar> = (0..np).map(|_| kenv.fresh_var()).collect();
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        let ix = IndexSpace::build(kenv, &mut app.mach, &walk.spec, &ps)
            .ok_or_else(|| bad("class (S) at an index: the index space"))?;
        let ac = app.acc(kenv).ok_or(Gap::IndApparatus)?;
        // One reason, because there is one shape left that could fail here.
        // The `kᵢ ≥ 1` special case this used to carry named a `derived` bug
        // (a variable capture in the existential closure, fixed at `8d9c94c`);
        // it is deleted rather than pinned at zero, because a reason string
        // nothing emits is a trap for whoever greps for it next.
        let lc = LeCarrier::build(kenv, &app.mach, &ac, &walk.spec, &ix, &params)
            .ok_or_else(|| bad("class (S) at an index: the carrier"))?;
        // `ac` rather than the index space: nothing in `le_index` speaks about
        // `Idx(p⃗)`, and taking the `Acc` lets it pin `lc.acc_set` against it.
        let lic =
            LeIndexCarrier::build(kenv, &app.mach, &tower, &ac, &walk.spec, &lc, &params)
                .ok_or_else(|| bad("class (S) at an index: the conditional singleton"))?;
        if lic.ctor_intro.is_none() {
            return Err(bad(RECURSIVE))
        }
        Rc::new(ClassSIx { walk: walk.clone(), ix, lc, lic, params })
    };

    former(c, ind_name, inst, ind_ty, np, ni, level, &built)?;
    for (i, (cname, cty)) in ctor_tys.iter().enumerate() {
        constructor(c, ind_name, inst, cname, cty, i, &built)?;
    }
    if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
        app.props_ix.insert((ind_name.clone(), inst.to_vec()), built);
    }
    Ok(())
}

/// **The type former.** `⟦T.{σ}⟧` is the `np + ni`-deep λ-nest whose bottom is
/// `χ(p⃗, x⃗)`, and whose typing is `⊢ χ(p⃗,x⃗) ∈ ⟦Sort ℓ⟧`.
///
/// `LeIndexCarrier::in_u0` is unconditional, so the only thing between it and
/// the obligation is the cumulativity raise that carries `Prop` up to the
/// declaration's own resultant sort — the `ulift_ℓ` of `thesis.txt:1886`, which
/// is a raise and not a set operation.
#[allow(clippy::too_many_arguments)]
fn former(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    ind_ty: &E,
    np: usize,
    ni: usize,
    level: u32,
    cs: &Rc<ClassSIx>,
) -> Result<(), Gap> {
    let cs = cs.clone();
    let name = ind_name.clone();
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        let ty = crate::expr::sort(crate::zoneb::level_numeral(level));
        let gap = |g: Gap| Ok(Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) });
        let Some((all, _)) = c.binders(np + ni) else { return gap(Gap::NoEndpoint) };
        let (ps, xs) = all.split_at(np);
        let (ps, xs) = (ps.to_vec(), xs.to_vec());
        let ip = c.interp().expect("threaded");
        // Through the accessor, and then rebuilt through `Interp::mk` so the
        // term is *decomposable* later; the two are compared rather than one
        // being assumed to be the other.
        let Some(want) = cs.lic.at(&ps, &xs) else {
            return gap(Gap::IndexedFamily(name.clone(), "class (S) at an index: arity"))
        };
        let mut args = ps.clone();
        args.extend(xs.iter().cloned());
        let carrier = ip.mk(cs.lic.sym, args.clone());
        if carrier != want {
            return gap(Gap::IndexedFamily(name.clone(), "class (S) at an index: the carrier term"))
        }
        let Some(at) = inst_all(&cs.lic.in_u0, &args) else {
            return gap(Gap::IndexedFamily(name.clone(), "class (S) at an index: the typing"))
        };
        let raised = if level == 0 { Some(at) } else { ip.raise_in_gamma(0, level as usize, &at) };
        match raised {
            Some(t) if *t.concl() == Formula::mem(carrier.clone(), ip.sort(level)) => {
                Ok(Typing { ty, tm: Some(carrier), ev: Ev::Proved(t) })
            }
            _ => gap(Gap::IndUniverseHeight(name.clone(), level)),
        }
    };
    let t = c.lam_nest(ind_ty, np + ni, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, ind_name, inst, t)
}

/// One class-(S) indexed constructor: which declaration, which constructor,
/// and the codomain read off its Lean type.
struct CtorSite {
    ind: Name,
    ctor: Name,
    inst: Vec<u32>,
    i: usize,
    np: usize,
    ni: usize,
    nf: usize,
    codomain: E,
    cs: Rc<ClassSIx>,
}

fn constructor(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    cname: &Name,
    cty: &E,
    i: usize,
    cs: &Rc<ClassSIx>,
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(cname.clone(), w, Cause::Threading);
    let nf = cs.walk.spec.base.ctors.get(i).ok_or_else(|| bad("constructor shape"))?.order.len();
    let (np, ni) = (cs.np(), cs.ni());
    let depth = np + nf;
    let codomain = crate::zoneb::peel(cty, depth).ok_or_else(|| bad("constructor arity"))?;
    let site = CtorSite {
        ind: ind_name.clone(),
        ctor: cname.clone(),
        inst: inst.to_vec(),
        i,
        np,
        ni,
        nf,
        codomain,
        cs: cs.clone(),
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(ctor_bottom(c, &site)) };
    let t = c.lam_nest(cty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, cname, inst, t)
}

/// The bottom of a class-(S) indexed constructor's nest: `•`, with
/// `LeIndexCtor::mem` at this nest's own binders.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    let (np, ni, nf) = (site.np, site.ni, site.nf);
    let cs = site.cs.clone();

    if cs.walk.spec.base.ctors[site.i].order.iter().any(|s| *s != Slot::Plain) {
        return gap(Gap::IndexedFamily(site.ind.clone(), RECURSIVE))
    }
    let Some((all, mems)) = c.binders(np + nf) else { return gap(Gap::NoEndpoint) };
    let Some(store_ty) = c.stored_term(&site.ind, &site.inst) else {
        return gap(Gap::NoEndpoint)
    };
    // The codomain's own index expressions, inferred — the only place
    // `⊢ ⟦eₖ⟧ ∈ ⟦Iₖ⟧` exists.
    let Some(result_e) = crate::zoneb::ind_spine(&site.ind, &site.codomain, np, ni, nf) else {
        return gap(bad("the codomain is not the family at its own indices"))
    };
    let Some(result) = crate::ctor_ix::infer_indices(c, &result_e) else {
        return gap(bad("the result indices"))
    };

    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    match build_ctor(ip, site, &all, &mems, &store_ty, &result) {
        Ok((tm, thm)) => Typing { ty, tm: Some(tm), ev: Ev::Proved(thm) },
        Err(g) => gap(g),
    }
}

fn build_ctor(
    ip: &mut crate::interp::Interp,
    site: &CtorSite,
    all: &[Term],
    mems: &[Thm],
    store_ty: &Term,
    result: &[(Term, Thm)],
) -> Result<(Term, Thm), Gap> {
    let bad = |w: &'static str| Gap::IndexedCtor(site.ctor.clone(), w, Cause::Threading);
    let (np, ni, i) = (site.np, site.ni, site.i);
    let cs = site.cs.clone();
    let point = ip.point();
    let (ps, ys) = all.split_at(np);
    let (param_mems, field_mems) = mems.split_at(np);
    let (ps, ys) = (ps.to_vec(), ys.to_vec());

    // ── `Hᵢ`: the field typings, onto the telescope's own symbols ───────────
    let mut atoms: Vec<Thm> = Vec::with_capacity(ys.len() + ni);
    for (j, m) in field_mems.iter().enumerate() {
        let mut args: Vec<Term> = ps.clone();
        args.extend(ys[..j].iter().cloned());
        let ax = cs
            .walk
            .field_abbrev
            .get(i)
            .and_then(|v| v.get(j))
            .ok_or_else(|| bad("a field abbreviation"))?;
        let at = inst_all(ax, &args).ok_or_else(|| bad("a field abbreviation instance"))?;
        let back = derived::eq_symm(&mut ip.env, &at).ok_or_else(|| bad("a field typing"))?;
        atoms.push(ip.retarget_set(m, &back).ok_or_else(|| bad("a field typing"))?);
    }

    // ── `Eᵢ`: the result-index typings, onto `eᵢₖ` and `ιₖ` ─────────────────
    //
    // `crate::ctor_ix`'s step, and the axioms are the boundary walk's — which
    // exist here only because the walk now outlives the decline this route used
    // to be. `ιₖ` is instantiated at the earlier *interpretations* and carried
    // to the symbols by one congruence, for the reason `ctor_ix` gives: an
    // index type may mention the earlier index expressions.
    let e_axs = cs.walk.ax.ctors.get(i).map(|cx| &cx.result).ok_or_else(|| bad("the result indices"))?;
    let mut e_args: Vec<Term> = ps.clone();
    e_args.extend(ys.iter().cloned());
    let mut interps: Vec<(Term, Thm)> = Vec::with_capacity(ni);
    for (k, (e_tm, mem)) in result.iter().enumerate() {
        let e_ax = e_axs.get(k).ok_or_else(|| bad("the result indices"))?;
        let e_at = inst_all(e_ax, &e_args).ok_or_else(|| bad("the result indices"))?;
        let subj = ip.retarget_subject(mem, &e_at).ok_or_else(|| bad("the result indices"))?;
        let i_ax = cs.walk.ax.indices.get(k).ok_or_else(|| bad("an index type"))?;
        let mut i_args: Vec<Term> = ps.clone();
        i_args.extend(interps.iter().map(|(t, _)| t.clone()));
        let i_at = inst_all(i_ax, &i_args).ok_or_else(|| bad("an index type"))?;
        let back = derived::eq_symm(&mut ip.env, &i_at).ok_or_else(|| bad("an index type"))?;
        let onto = ip.retarget_set(&subj, &back).ok_or_else(|| bad("an index type"))?;
        let i_sym = cs.walk.spec.indices.get(k).copied().ok_or_else(|| bad("an index type"))?;
        let cong = crate::ctor_ix::index_congr(ip, i_sym, &ps, &result[..k], &e_axs[..k], &e_args)
            .ok_or_else(|| bad("an index type"))?;
        let to_syms = derived::eq_symm(&mut ip.env, &cong).ok_or_else(|| bad("an index type"))?;
        atoms.push(ip.retarget_set(&onto, &to_syms).ok_or_else(|| bad("an index type"))?);
        interps.push((e_tm.clone(), mem.clone()));
    }

    // ── `LeIndexCtor::mem`, discharged ──────────────────────────────────────
    //
    // At `ni ≥ 1` the antecedent is never empty, which is
    // `LeCarrier::intro_is_conditional` at every constructor — so unlike
    // `crate::class_s` there is no second shape to carry, and the `mp` is
    // unconditional.
    let ctors = cs.lic.ctor_intro.as_ref().ok_or(Gap::IndexedFamily(site.ind.clone(), RECURSIVE))?;
    let rule = ctors.get(i).ok_or_else(|| bad("the introduction rule"))?;
    let at = inst_all(&rule.mem, &e_args).ok_or_else(|| bad("the introduction rule"))?;
    let conj = atoms
        .iter()
        .rev()
        .cloned()
        .reduce(|acc, t| derived::and_intro(&t, &acc))
        .ok_or_else(|| bad("the introduction rule's antecedent"))?;
    let mem = Thm::mp(&at, &conj).ok_or_else(|| bad("the introduction rule's antecedent"))?;

    // ── `χ(p⃗, e⃗ᵢ)` back onto `⟦T p⃗ e⃗⟧` ──────────────────────────────────────
    //
    // Two moves, the same pair `ctor_ix` makes: the rule concludes at the
    // *symbols* `e⃗ᵢ(p⃗,y⃗)` and the goal is at the interpretations, and the goal
    // is the stored former's applied spine rather than `χ` at all.
    let mut goal_args: Vec<Term> = ps.clone();
    goal_args.extend(result.iter().map(|(t, _)| t.clone()));
    let goal_set = crate::zoneb::store_spine(ip, store_ty, &goal_args);
    let mut sp_mems: Vec<Thm> = param_mems.to_vec();
    sp_mems.extend(result.iter().map(|(_, m)| m.clone()));
    let (_, beta) =
        ip.beta_spine(store_ty, &goal_args, &sp_mems).ok_or_else(|| bad("the former's spine"))?;
    let cong = crate::ctor_ix::index_congr(ip, cs.lic.sym, &ps, result, e_axs, &e_args)
        .ok_or_else(|| bad("the result indices"))?;
    let onto = ip.retarget_set(&mem, &cong).ok_or_else(|| bad("the former's spine"))?;
    let to_spine = derived::eq_symm(&mut ip.env, &beta).ok_or_else(|| bad("the former's spine"))?;
    let out = ip.retarget_set(&onto, &to_spine).ok_or_else(|| bad("the former's spine"))?;
    if *out.concl() != Formula::mem(point.clone(), goal_set) {
        return Err(bad("the constructor did not land in its own codomain"))
    }
    Ok((point, out))
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{app, bvar, forall, konst, sort, Level};
    use crate::interp::Interp;

    /// Build one synthetic indexed `Prop` and report what `⟦T⟧` came out as.
    fn route(name: &str, np: u32, ty: E, ctor: E) -> (bool, Option<Gap>, bool) {
        let n = Name::simple(name);
        let mk = Name::str(&n, "mk");
        let no: std::rc::Rc<[Level]> = Vec::new().into();
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: n.clone(),
                lparams: vec![],
                num_params: np,
                ty,
                ctors: vec![(mk.clone(), ctor)],
            },
        )
        .unwrap_or_else(|e| panic!("{name} is accepted: {e}"));
        let mut ip = Interp::new();
        let mut c = crate::kernel::Checker::threaded(&env, &mut ip);
        let t = c.infer_type(&konst(n, no.clone())).expect("infer the former");
        // Whether the *constructor* also landed — only asked when the carrier did.
        let ctor_ok = t.tm.is_some()
            && c.infer_type(&konst(mk, no)).map(|x| x.tm.is_some()).unwrap_or(false);
        (t.tm.is_some(), t.ev.gap().cloned(), ctor_ok)
    }

    /// **The four corners of `(np, kᵢ)` at `ni = 1`** — mini's side of the
    /// class-(S)-at-an-index seam, all four of which now build.
    ///
    /// # Rewritten at `8d9c94c`; the version at `0b105f5` said the opposite
    ///
    /// This test was written to record a **decline**: `kᵢ ≥ 1` at `ni ≥ 1`
    /// stopped in `LeCarrier::build`, and the two failing rows were pinned with
    /// a `PLAIN_FIELDS` reason and the note "when that guard lifts, the two rows
    /// flip and this test says so". It did, and they did. What the walk had
    /// found was not a limitation but a **variable capture** in `LeCarrier`'s
    /// existential closure — the disjunct body had `q := tup(e⃗ᵢ(p⃗,y⃗))`
    /// substituted *before* `∃yⱼ` was wrapped around it, so the binder
    /// abstracted the `y⃗` inside the tuple too and the disjunct came out as a
    /// reflexivity under the binders instead of an instance at the fixed index
    /// vector. `derived` fixed it; the rationale is rewritten here rather than
    /// appended to, with the prior revision named so the reversal is findable.
    ///
    /// **The lesson survives the reversal and is the reason to keep the test.**
    /// The corner existed because `derived`'s fixture for this carrier was
    /// `np = 0, kᵢ = 0` — and, as it turned out, the *same* fixture in
    /// `family_le.rs`, copied along with its name. Walking `(np, kᵢ)` cost one
    /// build and told a two-variable question apart; three hypotheses had
    /// preceded it and all three were wrong.
    ///
    /// **And the decline was protecting itself.** Had the captured reading been
    /// let through, the disjunct would have been `q`-independent, `A_φ` would
    /// have been all of `Idx(p⃗)`, and the carrier would have excluded nothing —
    /// a carrier true of every index. A `None` was the right failure mode for a
    /// derivation that had silently stopped being about its own subject.
    ///
    /// What the four rows assert now: carrier, type former **and** constructor,
    /// end to end through `LeIndexCarrier`, `LeIndexCtor::mem` and the
    /// result-index transport, with a plain field and with a parameter and with
    /// both. `derived/tests/family_le_index.rs` covers the *carrier* at
    /// `np = 1, ni = 3, kᵢ = 3` with the fields 3-cycled and pins `χ` at six
    /// index vectors; **this** test covers no shape that deep and is not a
    /// second copy of it — what it covers and that one does not is mini's side
    /// of the seam, the nest and the two abbreviation transports.
    #[test]
    fn the_index_route_is_wired_and_the_nest_reaches_the_constructor() {
        let ty0 = || sort(Level::Zero.succ());
        let k = |n: &str| konst(Name::simple(n), Vec::new().into());

        // `Qa : Type → Prop | mk : Qa Prop` — np = 0, kᵢ = 0.
        let (ok, gap, ctor) =
            route("Qa", 0, forall(ty0(), sort(Level::Zero)), app(k("Qa"), sort(Level::Zero)));
        assert!(ok && ctor, "np = 0, kᵢ = 0: the carrier and the constructor build ({gap:?})");

        // `Qc (α : Type) : Type → Prop | mk : Qc α α` — a **parameter**.
        let (ok, gap, ctor) = route(
            "Qc",
            1,
            forall(ty0(), forall(ty0(), sort(Level::Zero))),
            forall(ty0(), app(app(k("Qc"), bvar(0)), bvar(0))),
        );
        assert!(ok && ctor, "np = 1, kᵢ = 0: a parameter is not what stops it ({gap:?})");

        // `Qb : Type → Prop | mk : ∀ (a : Type), Qb a` — a **plain field**,
        // which is what the capture used to stop.
        let (ok, gap, ctor) = route(
            "Qb",
            0,
            forall(ty0(), sort(Level::Zero)),
            forall(ty0(), app(k("Qb"), bvar(0))),
        );
        assert!(ok && ctor, "np = 0, kᵢ = 1: a plain field builds ({gap:?})");

        // `Qd (α : Type) : Type → Prop | mk : ∀ (a : Type), Qd α a` — both.
        let (ok, gap, ctor) = route(
            "Qd",
            1,
            forall(ty0(), forall(ty0(), sort(Level::Zero))),
            forall(ty0(), forall(ty0(), app(app(k("Qd"), bvar(1)), bvar(0)))),
        );
        assert!(ok && ctor, "np = 1, kᵢ = 1: a parameter and a field together ({gap:?})");
    }
}
