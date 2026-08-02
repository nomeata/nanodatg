//! **The class-(S) clause** — Carneiro §5.3's subsingleton carrier, for a
//! non-indexed declaration, as the general rule rather than as a table of
//! names.
//!
//! # Interface
//!
//! ```text
//! class_s::build(checker, T, σ, np, ty, ctor tys) -> Result<(), Gap>
//! class_s::of(checker, T, σ)                      -> Option<Rc<ClassS>>
//! ```
//!
//! [`build`] is called from [`crate::zoneb::build`] on the branch the
//! eliminator trichotomy sends here, and it stores `⟦T.{σ}⟧` and every
//! `⟦T.ctor.{σ}⟧` exactly as the class-(T) walk does — the same
//! [`Checker::lam_nest`](crate::kernel::Checker::lam_nest), the same
//! [`crate::zoneb::store`], the same `Gap` vocabulary. [`of`] hands the built
//! objects back to [`crate::recursor`], which needs the *same* `A_φ` the
//! carrier was stored at.
//!
//! # What §5.3 collapses to when there are no indices
//!
//! The class-(S) carrier is
//!
//! ```text
//! ⟦T p⃗ x⃗⟧ = [ tup(x⃗) ∈ acc(A_φ(p⃗), R(p⃗)) ]
//! ```
//!
//! and two collapses apply here at once. With **no recursive argument** `R` is
//! provably empty and `acc` is the identity
//! ([`LeCarrier::degenerate`](derived::inductive::family::LeCarrier)); with
//! **no index** the index space is the one point, so `A_φ(p⃗)` is a subset of
//! `1` — a proposition — whose truth value
//! [`derived::inductive::family::LeProp`] reads off as
//!
//! ```text
//! ψ := ⋁ᵢ ∃y⃗ᵢ. ( ⋀ⱼ yⱼ ∈ βᵢⱼ(p⃗, y⃗<ⱼ)  ∧  • = • )
//! ```
//!
//! — "some constructor's fields can all be inhabited". For `And a b` that is
//! `∃y₀ ∃y₁. (y₀ ∈ a ∧ (y₁ ∈ b ∧ • = •))`; for `PUnit` and `True` it is
//! `• = •`; for `ProjDataIndex p` it is `∃y₀. (y₀ ∈ p ∧ • = •)`.
//!
//! **This module writes none of that down.** `derived` does, once, and the four
//! declarations above reach it by the same code path a fifth would. That is the
//! whole point of the change that created this file: `And` and `PUnit` used to
//! have hand-written closed forms in [`crate::direct`] — `and_set(a,b)` and `1`
//! — with a delete-by attached, and the delete-by was met when
//! `IndexSpace::build` accepted `ni = 0`. `Eq` stays in [`crate::direct`]
//! because it is a member of Carneiro's §6.2 menagerie with its own
//! interpretation clause, not because its collapse is more convenient.
//!
//! # The trichotomy's second and third branches, told apart by the eliminator
//!
//! `INDEXED-DESIGN.md` §2.1: a declaration whose resultant level is not
//! provably nonzero is class (S) if its recursor is **large-eliminating** and
//! class (P) otherwise, and the test is "does the recursor carry one more
//! universe parameter than the declaration" — the motive's. That is what
//! `zoneb::large_eliminating` computes, and it is deliberately *computed* from
//! the declaration (Carneiro §2.6.2) rather than
//! recomputed: reproducing Lean's subsingleton-elimination analysis here would
//! be re-implementing the thing being checked. `SortElimProp` and
//! `SortElimProp2` have the same constructor shape and differ only in it.
//!
//! Class (P) — `Or`, `Exists`, `Nonempty`, `BoolProp`, `PropStructure`,
//! `PredWithTypeField` — keeps [`Gap::PropInductive`], which is now a statement
//! about **one** class rather than about two. Its clause is the truncation
//! `‖·‖` (`derived::inductive::family::trunc`), which exists and is not wired.
//!
//! # What this route declines, and why each is the shape and not a defence
//!
//! * **an index** — [`crate::zoneb::build`] declines it one step earlier as
//!   [`Gap::IndexedFamily`]. `LeProp` is stated at `ni = 0`; with an index
//!   `A_φ` is a subset of a genuine `Σ` nest and every lemma it exports is
//!   false. That case is `derived::inductive::family::le_rec`'s.
//! * **a recursive field** — the interpretation would have to be the `acc`,
//!   not `A_φ`, and `LeProp` describes `A_φ`. `INDEXED-DESIGN.md` §6.2 records
//!   that a recursive class-(S) declaration has no witness in the 91 files.
//! * **anything the [`crate::zoneb`] boundary walk already refuses** — this
//!   route shares that walk rather than owning a second copy of it, so a nested
//!   occurrence or a function-typed recursive argument is declined with the
//!   reason it already had.
//!
//! It does **not** decline a declaration with no constructors: ψ is then `⊥`,
//! `A_φ` is provably empty, and `⊢ A_φ(p⃗) ∈ U₀` holds anyway. There is nothing
//! to build for its constructors, and its eliminator is ex falso —
//! `LePropRecursor::build` refuses it, which is where that is said.
//!
//! # No summand legs
//!
//! [`crate::zoneb::spec_of`] is asked for [`Legs::Skip`](crate::zoneb::Legs).
//! A leg is `⊢ … βⱼ(p⃗,y⃗<ⱼ) ∈ U₁`, and the only consumer is class (T)'s
//! universe placement through `derived::cumul`'s summand induction. Class (S)
//! has no summand and no tag sum: `⊢ A_φ(p⃗) ∈ U₀` is one
//! [`Tower::cond_in_u0`](derived::tower::Tower::cond_in_u0) at ψ, and it is
//! **unconditional** — no `H`, no parameter typings to discharge, whatever the
//! fields are. Deriving legs here would be work with no consumer that could
//! also decline a declaration for a class-(T) reason.
//!
//! # The eliminator does not come with the carrier
//!
//! [`crate::rec_prop`] is that second build, and it is wired: `⟦T.rec⟧` for
//! `And`, `PUnit` and `ProjDataIndex` is derived with its typing at both σ.
//! What it needs from *this* module is [`ClassS::field_sort`] and
//! [`ClassS::abbrev`] —
//! [`LePropFields`](derived::inductive::family::LePropFields) takes
//! `Pⱼ : βⱼ(p⃗,•⃗<ⱼ) ⊆ 1`, which follows from the field type's own sort typing
//! at `ℓⱼ = 0`, and the boundary walk is the only place that typing exists.
//!
//! A declaration with **no constructors** still gets its carrier here and does
//! not get an eliminator: that is `¬ψ`,
//! [`LeProp::false_`](derived::inductive::family::LeProp) and ex falso, which
//! shares no step with the one-constructor rule and so has its own label,
//! [`crate::recursor::CLASS_S_EMPTY`].
//!
//! # Nothing here searches
//!
//! The route is chosen by the trichotomy, on the declaration's own level
//! expression and the recursor's own level-parameter count — two reads of data
//! already in hand, keyed on the name [`crate::zoneb::ensure`] was asked about.
//! Inside, every theorem is composed forward out of what the boundary walk
//! returned and what `derived` handed back, and every one of them is compared
//! against the statement it is supposed to be before it is used. The empty
//! antecedent at a fieldless constructor is read from
//! [`LeCarrier::intro_is_conditional`](derived::inductive::family::LeCarrier::intro_is_conditional)
//! — a question about the *spec* — rather than by pattern-matching on an
//! implication that might be one of `Hᵢ`'s own conjuncts.

use std::rc::Rc;

use kernel::{Formula, FreeVar, Term, Thm};

use derived::inductive::family::{CtorIndices, IndexSpace, IndexedDeclSpec, LeCarrier, LeProp};
use derived::inductive::Slot;
use derived::{gen_all, inst_all};

use crate::ev::{Ev, Gap};
use crate::expr::{Name, E};
use crate::kernel::{Checker, Typing, R};
use crate::zoneb::Legs;

/// One translated class-(S) declaration, at one ground instantiation.
///
/// Kept whole in [`crate::interp::IndApparatus`] for the same reason the
/// class-(T) carriers are: the eliminator is a **second** build over the same
/// `A_φ`, and rebuilding the carrier there would mint a second Separation that
/// no equation relates to the one in the store.
pub struct ClassS {
    /// The non-indexed spec: the erased declaration, `indices` empty, and one
    /// [`CtorIndices::nonrecursive`] with no result index per constructor.
    pub spec: IndexedDeclSpec,
    /// The one-point index space.
    pub ix: IndexSpace,
    /// `A_φ`, `R`, `acc(A_φ,R)` and the introduction rules.
    pub lc: LeCarrier,
    /// The same `A_φ`, read as a conditional singleton over ψ.
    pub lp: LeProp,
    /// The kernel variables `p⃗` every theorem above is stated at.
    pub params: Vec<FreeVar>,
    /// `⊢ ∀p⃗. A_φ(p⃗) ∈ U₀` — [`LeProp::chi_at_params`] through
    /// `Tower::cond_in_u0`, generalised so it can be instantiated at a nest's
    /// own binders.
    pub in_u0: Thm,
    /// Per constructor, per plain field: `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`.
    ///
    /// The bridge every consumer needs and none can rebuild: `derived` states
    /// each field fact at the `define_abbrev` **symbol**, while a checker's
    /// scope holds it at the interpretation that symbol abbreviates.
    pub abbrev: Vec<Vec<Thm>>,
    /// Per constructor, per plain field: `⊢ ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧` as the boundary
    /// walk derived it, under the scopes that walk had open.
    ///
    /// Retained because the **recursor** needs `Pⱼ : βⱼ(p⃗,•⃗<ⱼ) ⊆ 1` and this
    /// is where the fact exists — `Legs::Skip` used to drop it, which is the
    /// standing rule broken at the one site that was breaking it. Note the
    /// theorems are *scope-dependent*: for the three corpus declarations the
    /// field types are parameters, so each carries its parameter binder's own
    /// assumption, and a consumer at a nest that reopens the parameters has
    /// the same fact there without instantiating these. Kept anyway, because
    /// the general field type is not a parameter and this is the only place it
    /// is ever in hand.
    pub field_sort: Vec<Vec<Thm>>,
}

impl ClassS {
    /// `np`, read off the spec rather than carried a second time.
    pub fn np(&self) -> usize { self.spec.params() }
}

/// The built objects for `(T, σ)`, if this route built them.
pub(crate) fn of(c: &mut Checker<'_, '_>, ind_name: &Name, inst: &[u32]) -> Option<Rc<ClassS>> {
    let ip = c.interp()?;
    let app = ip.ind_apparatus()?;
    app.props.get(&(ind_name.clone(), inst.to_vec())).cloned()
}

/// `⟦T.{σ}⟧` and `⟦T.ctor.{σ}⟧` for one class-(S) declaration.
///
/// The declaration data is handed in rather than re-read: [`crate::zoneb::build`]
/// has already substituted σ into the type and every constructor type, and
/// reading them a second time would be a second chance to disagree.
pub(crate) fn build(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ind_ty: &E,
    ctor_tys: &[(Name, E)],
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndSpec(ind_name.clone(), w);

    // ── the `FnSym` boundary, shared with the class-(T) walk ──────────────
    // `ni = 0`: `zoneb::build` routes an indexed declaration to its own decline
    // before the trichotomy, so class (S) only ever sees a non-indexed one, and
    // the empty index data below is that fact rather than a simplification.
    let (shape, base, _) = crate::zoneb::spec_of(c, ind_name, np, 0, ind_ty, ctor_tys, Legs::Skip)?;
    if base.ctors.iter().any(|cs| cs.recs != 0) {
        // The interpretation would be the `acc` and not `A_φ`; see the header.
        return Err(bad("class (S): recursive constructor"))
    }
    let ctors_idx: Vec<CtorIndices> =
        base.ctors.iter().map(|_| CtorIndices::nonrecursive(Vec::new())).collect();
    let spec = IndexedDeclSpec::new(base, Vec::new(), ctors_idx);
    if !spec.well_formed() {
        return Err(bad("spec not well formed"))
    }

    // ── the carrier ───────────────────────────────────────────────────────
    let built = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let tower = ip.prelude.tower.clone();
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let params: Vec<FreeVar> = (0..np).map(|_| kenv.fresh_var()).collect();
        let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        let ix = IndexSpace::build(kenv, &mut app.mach, &spec, &ps)
            .ok_or_else(|| bad("index space"))?;
        let ac = app.acc(kenv).ok_or(Gap::IndApparatus)?;
        let lc = LeCarrier::build(kenv, &app.mach, &ac, &spec, &ix, &params)
            .ok_or_else(|| bad("class (S) carrier"))?;
        let lp = LeProp::build(kenv, &app.mach, &spec, &ix, &lc, &params)
            .ok_or_else(|| bad("class (S) truth value"))?;
        // `⊢ A_φ(p⃗) ∈ U₀`, from the *same* three arguments every other
        // conditional singleton's typing is built from. It is unconditional —
        // `A_φ ⊆ 1` whatever ψ is — and that is checked before it is
        // generalised, because `gen_all` over a hypothetical theorem is not a
        // thing this kernel can say.
        let in_u0 = tower
            .cond_in_u0(kenv, &lp.psi, &lp.set, &lp.chi_at_params)
            .ok_or_else(|| bad("denotation typing"))?;
        if !derived::establishes(&in_u0, &Formula::mem(lp.set.clone(), tower.u(0))) {
            return Err(bad("denotation typing"))
        }
        let in_u0 = gen_all(&params, &in_u0);
        Rc::new(ClassS {
            spec,
            ix,
            lc,
            lp,
            params,
            in_u0,
            abbrev: shape.ctors.iter().map(|(.., ev)| ev.abbrev.clone()).collect(),
            field_sort: shape.ctors.iter().map(|(.., ev)| ev.field_sort.clone()).collect(),
        })
    };

    // ── the Lean-facing layer ─────────────────────────────────────────────
    let level = shape.result_level;
    former(c, ind_name, inst, ind_ty, np, level, &built)?;
    for (i, (cname, cty)) in ctor_tys.iter().enumerate() {
        constructor(c, ind_name, inst, cname, cty, i, &built)?;
    }
    if let Some(ip) = c.interp() {
        if let Some(app) = ip.ind_apparatus() {
            app.props.insert((ind_name.clone(), inst.to_vec()), built);
        }
    }
    Ok(())
}

/// **The type former.** `⟦T.{σ}⟧` is the `np`-deep λ-nest whose bottom is
/// `A_φ(p⃗)`, and whose typing is `⊢ A_φ(p⃗) ∈ ⟦Sort ℓ⟧` at the declaration's
/// **own** resultant sort.
///
/// The raise through the cumulativity table is what makes `PUnit.{u}` land in
/// `⟦Sort u⟧` and not only in `⟦Prop⟧`: the carrier is a subset of `1` at every
/// `u`, and the level survives only in the universe statement.
fn former(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    ind_ty: &E,
    np: usize,
    level: u32,
    cs: &Rc<ClassS>,
) -> Result<(), Gap> {
    let cs = cs.clone();
    let name = ind_name.clone();
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        let ty = crate::expr::sort(crate::zoneb::level_numeral(level));
        let gap = |g: Gap| Ok(Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) });
        let Some((ps, _)) = c.binders(np) else { return gap(Gap::NoEndpoint) };
        let ip = c.interp().expect("threaded");
        let carrier = ip.mk(cs.lc.phi, ps.clone());
        let Some(at) = inst_all(&cs.in_u0, &ps) else {
            return gap(Gap::IndSpec(name.clone(), "denotation typing instance"))
        };
        let raised = if level == 0 { Some(at) } else { ip.raise_in_gamma(0, level as usize, &at) };
        match raised {
            Some(t) if *t.concl() == Formula::mem(carrier.clone(), ip.sort(level)) => {
                Ok(Typing { ty, tm: Some(carrier), ev: Ev::Proved(t) })
            }
            _ => gap(Gap::IndUniverseHeight(name.clone(), level)),
        }
    };
    let t = c.lam_nest(ind_ty, np, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, ind_name, inst, t)
}

/// One class-(S) constructor: which declaration, which constructor, and the
/// codomain read off its Lean type.
struct CtorSite {
    ind: Name,
    inst: Vec<u32>,
    i: usize,
    codomain: E,
    np: usize,
    cs: Rc<ClassS>,
}

/// **A constructor.** `⟦T.ctor.{σ}⟧` is the `np + k`-deep λ-nest whose bottom is
/// `•` — the carrier is a subset of `1`, so there is nothing else it could be —
/// and whose membership is `LeCarrier::intro[i]` at this nest's own binders.
fn constructor(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    cname: &Name,
    cty: &E,
    i: usize,
    cs: &Rc<ClassS>,
) -> Result<(), Gap> {
    let nf = cs.spec.base.ctors[i].order.len();
    let depth = cs.np() + nf;
    let codomain =
        crate::zoneb::peel(cty, depth).ok_or_else(|| Gap::IndSpec(ind_name.clone(), "ctor arity"))?;
    let site = CtorSite {
        ind: ind_name.clone(),
        inst: inst.to_vec(),
        i,
        codomain,
        np: cs.np(),
        cs: cs.clone(),
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(ctor_bottom(c, &site)) };
    let t = c.lam_nest(cty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    crate::zoneb::store(c, cname, inst, t)
}

/// The bottom of a class-(S) constructor's nest.
///
/// Three things are read off rather than assumed, and each is where a
/// declaration that is not what the route thinks it is gets refused:
///
/// * whether `LeCarrier::intro[i]` has an antecedent at all —
///   [`LeCarrier::intro_is_conditional`], a question about the spec, because at
///   `kᵢ = ni = 0` (`PUnit.unit`, `True.intro`) `Hᵢ ∧ Eᵢ` is *empty* and this
///   kernel has no `⊤` to weaken it to;
/// * `⟦T p⃗⟧`, which is `⟦T⟧`'s nest β-reduced at the parameters' own scope
///   typings by [`crate::interp::Interp::beta_spine`], and which must come out
///   as `A_φ(p⃗)` — the set the rule concludes about;
/// * the field typings, which the nest's scopes hold at `⟦βⱼ⟧` while the rule
///   states them at the `define_abbrev` symbol `βⱼ(p⃗,y⃗<ⱼ)`.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let CtorSite { ind, inst, i, codomain, np, cs } = site;
    let (i, np) = (*i, *np);
    let ty = codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::IndSpec(ind.clone(), w);
    let spec = &cs.spec.base.ctors[i];
    let nf = spec.order.len();
    if spec.order.iter().any(|s| *s != Slot::Plain) {
        return gap(bad("class (S): recursive constructor"))
    }
    let Some((all, mems)) = c.binders(np + nf) else { return gap(Gap::NoEndpoint) };
    let (ps, ys) = all.split_at(np);
    let (param_mems, field_mems) = mems.split_at(np);
    let (ps, ys) = (ps.to_vec(), ys.to_vec());
    let (param_mems, field_mems) = (param_mems.to_vec(), field_mems.to_vec());

    let Some(store_ty) = c.stored_term(ind, inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let point = ip.point();

    // Each field typing moves from `⟦βⱼ⟧` onto the telescope's own symbol,
    // along that symbol's defining axiom at *this* nest's variables.
    let mut atoms: Vec<Thm> = Vec::with_capacity(nf);
    for (j, m) in field_mems.iter().enumerate() {
        let mut args: Vec<Term> = ps.clone();
        args.extend(ys[..j].iter().cloned());
        let Some(ax) = cs.abbrev.get(i).and_then(|v| v.get(j)) else {
            return gap(bad("field abbreviation"))
        };
        let Some(at) = inst_all(ax, &args) else { return gap(bad("field abbreviation instance")) };
        let Some(back) = derived::eq_symm(&mut ip.env, &at) else {
            return gap(Gap::ConvCompose("class-s-field-symm"))
        };
        match ip.retarget_set(m, &back) {
            Some(t) => atoms.push(t),
            None => return gap(Gap::ConvCompose("class-s-field")),
        }
    }

    // `LeCarrier::intro[i]` at `(p⃗, y⃗)`, with its antecedent — if it has one —
    // discharged from those typings. `conj_of` is right-nested, so the
    // conjunction is folded from the last field back.
    let Some(rule) = cs.lc.intro.get(i) else { return gap(bad("intro rule")) };
    let mut args: Vec<Term> = ps.clone();
    args.extend(ys.iter().cloned());
    let Some(at) = inst_all(rule, &args) else { return gap(bad("intro instantiation")) };
    let conditional = match LeCarrier::intro_is_conditional(&cs.spec, i) {
        Some(b) => b,
        None => return gap(bad("intro rule")),
    };
    let mem = if conditional {
        let Some(mut conj) = atoms.pop() else { return gap(bad("intro antecedent")) };
        while let Some(a) = atoms.pop() {
            conj = derived::and_intro(&a, &conj);
        }
        match Thm::mp(&at, &conj) {
            Some(t) => t,
            None => return gap(bad("intro antecedent")),
        }
    } else {
        at
    };

    // `⟦T⟧` applied to the parameters, β-reduced. The premise each level
    // consumes is the parameter's own scope typing.
    let Some((carrier, spine_eq)) = ip.beta_spine(&store_ty, &ps, &param_mems) else {
        return gap(bad("type former spine"))
    };
    if carrier != ip.mk(cs.lc.phi, ps.clone()) {
        return gap(bad("spine bottom"))
    }
    if *mem.concl() != Formula::mem(point.clone(), carrier) {
        return gap(bad("ctor is not about its own codomain"))
    }
    let back = match derived::eq_symm(&mut ip.env, &spine_eq) {
        Some(t) => t,
        None => return gap(Gap::ConvCompose("class-s-spine-symm")),
    };
    match ip.retarget_set(&mem, &back) {
        Some(t) => Typing { ty, tm: Some(point), ev: Ev::Proved(t) },
        None => gap(Gap::ConvCompose("class-s-codomain")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{bvar, forall, konst, sort, Level};
    use crate::interp::Interp;

    fn nm(s: &str) -> Name { Name::simple(s) }

    /// `And (a b : Prop) : Prop`, with `And.intro : ∀ a b, a → b → And a b`.
    fn and_env() -> (Environment, Name, Name) {
        let (a, i) = (nm("And"), Name::str(&nm("And"), "intro"));
        let p = sort(Level::Zero);
        let ty = forall(p.clone(), forall(p.clone(), sort(Level::Zero)));
        let at = |f: E, x: E, y: E| crate::expr::app(crate::expr::app(f, x), y);
        let cty = forall(
            p.clone(),
            forall(
                p,
                forall(
                    bvar(1),
                    forall(bvar(1), at(konst(a.clone(), Vec::new().into()), bvar(3), bvar(2))),
                ),
            ),
        );
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: a.clone(),
                lparams: vec![],
                num_params: 2,
                ty,
                ctors: vec![(i.clone(), cty)],
            },
        )
        .expect("the declaration is accepted");
        (env, a, i)
    }

    /// **`And` goes through the general clause**, carrier and constructor, and
    /// the typing is about the term the store actually holds.
    #[test]
    fn and_is_interpreted_by_the_general_class_s_clause() {
        let (env, a, i) = and_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let none: std::rc::Rc<[Level]> = Vec::new().into();

        let t = c.infer_type(&konst(a.clone(), none.clone())).expect("infer ⟦And⟧");
        let m = t.ev.thm().unwrap_or_else(|| panic!("⟦And⟧ has no typing: {:?}", t.ev)).clone();
        assert!(m.hyps().is_empty(), "a closed declaration's typing is unconditional");
        assert!(t.tm.is_some(), "⟦And⟧ must interpret");

        let ct = c.infer_type(&konst(i, none)).expect("infer ⟦And.intro⟧");
        let cm = ct.ev.thm().unwrap_or_else(|| panic!("⟦And.intro⟧ has no typing: {:?}", ct.ev));
        assert!(cm.hyps().is_empty());
        let (subj, _) = cm.concl().as_mem().expect("a membership");
        assert_eq!(subj, ct.tm.clone().unwrap(), "the typing is about ⟦And.intro⟧ itself");
        assert_eq!(subj, c.interp().unwrap().point(), "a subsingleton's inhabitant is •");

        // The route really was this one: the built objects are in the
        // apparatus under the declaration's own key.
        assert!(of(&mut c, &a, &[]).is_some(), "And was not built by the class-(S) route");
    }

    /// **The trichotomy is read, not recomputed.** Two `Prop`-valued
    /// declarations of the *same* shape but different eliminators take
    /// different branches, and the one that is not large-eliminating keeps its
    /// own reason.
    #[test]
    fn class_p_is_told_apart_from_class_s_by_the_eliminator() {
        // `S : Prop` with one fieldless constructor — large-eliminating.
        // `P : Prop` with two fieldless constructors — not.
        let mut env = Environment::empty();
        for (n, k) in [("S", 1usize), ("P", 2)] {
            let t = nm(n);
            let ty = konst(t.clone(), Vec::new().into());
            crate::kernel::add(
                &mut env,
                &Declaration::Inductive {
                    name: t.clone(),
                    lparams: vec![],
                    num_params: 0,
                    ty: sort(Level::Zero),
                    ctors: (0..k)
                        .map(|j| (Name::str(&t, &format!("c{j}")), ty.clone()))
                        .collect(),
                },
            )
            .expect("accepted");
        }
        let mut ipc = Interp::new();
        {
            let mut cc = Checker::threaded(&env, &mut ipc);
            assert!(crate::zoneb::large_eliminating(&mut cc, &nm("S")));
            assert!(!crate::zoneb::large_eliminating(&mut cc, &nm("P")));
        }

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let none: std::rc::Rc<[Level]> = Vec::new().into();
        let s = c.infer_type(&konst(nm("S"), none.clone())).expect("infer ⟦S⟧");
        assert!(s.ev.is_proved(), "a class-(S) declaration is built: {:?}", s.ev);
        let p = c.infer_type(&konst(nm("P"), none)).expect("infer ⟦P⟧");
        assert!(p.ev.is_proved(), "a class-(P) declaration is built too: {:?}", p.ev);

        // **Both are built, by different clauses, and the carriers must not be
        // the same term.** That is the assertion the eliminator split is
        // actually about: `S` gets §5.3's `A_φ` and `P` gets `‖ind()‖`, and a
        // dispatch that sent both to one clause would still pass every
        // membership check above — two `Prop`s are both subsingletons, so the
        // *typings* cannot tell them apart. Only the terms can.
        let (st, pt) = (s.tm.expect("⟦S⟧"), p.tm.expect("⟦P⟧"));
        assert_ne!(st, pt, "class (S) and class (P) must not collapse to one carrier");
        // And both are `Prop`s: each lands in `U₀`, which is what the `Π` split
        // and `point_of_proof` downstream consume.
        let u0 = c.interp().unwrap().sort(0);
        for (n, t, ev) in [("S", &st, &s.ev), ("P", &pt, &p.ev)] {
            let m = ev.thm().unwrap_or_else(|| panic!("{n} has no typing")).clone();
            assert!(m.hyps().is_empty(), "{n}'s typing must be unconditional");
            assert_eq!(*m.concl(), Formula::mem(t.clone(), u0.clone()), "{n} must be a Prop");
        }
    }

    /// **`False`** — a `Prop` with no constructors. The header claims this
    /// route does not decline it; ψ is `⊥`, `A_φ` is provably empty, and the
    /// typing holds anyway. Pinned, because "not declined" is a claim about
    /// `LeCarrier` at an empty disjunction and not an obvious one.
    #[test]
    fn a_constructorless_prop_still_gets_a_carrier() {
        let f = nm("False");
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: f.clone(),
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::Zero),
                ctors: vec![],
            },
        )
        .expect("accepted");
        {
            let mut ipc = Interp::new();
            let mut cc = Checker::threaded(&env, &mut ipc);
            assert!(
                crate::zoneb::large_eliminating(&mut cc, &f),
                "no constructors means large elimination"
            );
        }
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let t = c.infer_type(&konst(f, Vec::new().into())).expect("infer ⟦False⟧");
        assert!(t.ev.is_proved(), "⟦False⟧ has no typing: {:?}", t.ev);
        assert!(t.tm.is_some());
    }
}
