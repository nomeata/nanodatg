//! **Zone B — the inductive interpretation** (MINI-DESIGN.md §9).
//!
//! # Interface
//!
//! ```text
//! zoneb::ensure(checker, name, ground levels) -> Result<(), Gap>
//! ```
//!
//! Called from [`crate::kernel::Checker`]'s constant clause on a **store
//! miss**, and from nowhere else. It resolves `name` to the declaration it
//! belongs to — the type itself, or one of its constructors — translates that
//! declaration at those ground levels, and puts `⟦T.{ℓ⃗}⟧` and every
//! `⟦T.ctor.{ℓ⃗}⟧` into the store with its typing. A second lookup then hits.
//!
//! # This is a construction on a miss, not a search
//!
//! The claim MINI-DESIGN.md §0 is built on — *no function looks for a fact it
//! was not handed or cannot compute forward* — survives here, and it is worth
//! saying exactly why, because "build it when it is missing" can be made to
//! sound like a retry.
//!
//! * The key is `(name, ground levels)`, the same key the store is keyed on.
//!   Nothing is looked up by shape, by conclusion, or by trying alternatives.
//! * The declaration is fetched from the syntactic environment **by that
//!   name**; a constructor reaches its declaration by
//!   [`crate::env::Environment::owner`], an index built when the declaration
//!   was added, not by scanning for a type whose constructor list contains it.
//! * Everything below runs forward: the parameter and field types are
//!   interpreted by *inference* on the declaration's own expressions, and every
//!   theorem is composed out of what that inference returned.
//! * A shape this module cannot express is **declined**, with its own reason,
//!   and the decline is stored so the second lookup reports that reason rather
//!   than a bare miss (§0.4: the gap names the cause, not the site).
//!
//! # The branch decider is the eliminator, and nothing else
//!
//! `WIRING-DESIGN.md` §4 and `LEVEL-POLYMORPHIC-INDUCTIVES.md` §2–3: the
//! translation branch is fixed **per declaration** by Lean's own eliminator
//! trichotomy, read off the declaration's *own* level expression, never off the
//! instantiated numeral. [`provably_nonzero`] is that predicate. A declaration
//! whose resultant sort is not provably nonzero is class (S) or (P) — §5.3's
//! subsingleton elimination or the truncation clause — and gets a W-type from
//! nobody, not even at a `Type` instantiation, because a per-instantiation
//! branch is the design error that note closes.
//!
//! # What this reaches, and what it declines
//!
//! Reached: a **non-indexed, non-nested, single** declaration whose resultant
//! sort is provably nonzero, whose constructors have no function-typed
//! recursive argument, and whose carrier `derived::cumul::decl` can place in
//! `U₁`. Everything else is a counted decline. The declines are not a
//! defensive list: each is a shape `derived::inductive::DeclSpec` cannot
//! express, or a `derived/` construction that does not exist yet, and each says
//! which.

use std::rc::Rc;

use kernel::{Formula, Term, Thm};

use crate::env::ConstantInfo;
use crate::ev::{Ev, Gap, Sealed};
use crate::expr::{Expr, Level, Name, E};
use crate::ground;
use crate::interp::ConstInterp;
use crate::kernel::{Checker, Typing, R};

use derived::inductive::{CtorSpec, DeclSpec, Inductive, Slot};

/// **The eliminator trichotomy's first branch**, on a declaration's *own*
/// resultant level expression.
///
/// `WIRING-DESIGN.md` §4, from thesis §2.6.2. `Succ` is nonzero; a `Max` is
/// nonzero if either side is; an `IMax` is nonzero exactly when its right side
/// is, because `imax l 0 = 0`. `Zero` and a bare `Param` are not — a parameter
/// may be instantiated at `0`, and the whole point of deciding per declaration
/// rather than per σ is that `PUnit.{u}` must take one branch at every `u`.
pub fn provably_nonzero(l: &Level) -> bool {
    match l {
        Level::Succ(_) => true,
        Level::Max(a, b) => provably_nonzero(a) || provably_nonzero(b),
        Level::IMax(_, b) => provably_nonzero(b),
        Level::Zero | Level::Param(_) => false,
    }
}

/// Peel `n` `Π` binders, returning the body. `None` if there are fewer.
fn peel(ty: &E, n: usize) -> Option<E> {
    let mut cur = ty.clone();
    for _ in 0..n {
        let Expr::Forall { body, .. } = &*cur.clone() else { return None };
        cur = body.clone();
    }
    Some(cur)
}

/// Make the interpretation of `name` at `inst` available, or say why not.
///
/// Idempotent: a second call after a successful build is a store hit and
/// returns without doing anything, and a second call after a decline returns
/// the same reason.
pub fn ensure(c: &mut Checker<'_, '_>, name: &Name, inst: &[u32]) -> Result<(), Gap> {
    let env = c.environment();
    // Which declaration does this constant belong to? By index, not by scan.
    let ind_name = match env.get(name) {
        Some(ConstantInfo::Inductive { .. }) => name.clone(),
        _ => match env.owner(name) {
            Some(n) => n.clone(),
            None => return Err(Gap::NoInterpretation(name.clone(), inst.to_vec())),
        },
    };
    // **The declaration's own σ, which is not the constant's.** A constructor
    // shares its declaration's universe parameters; a recursor carries one
    // more — the motive's — *prepended*, so the declaration's instantiation is
    // the trailing suffix. Keying the store on the recursor's own list would
    // put `Bool` at `[0]` when `Bool` has no parameters at all, and every later
    // lookup would miss with a reason naming the wrong thing.
    let nl = match env.get(&ind_name) {
        Some(ci) => ci.lparams().len(),
        None => return Err(Gap::NoInterpretation(ind_name.clone(), inst.to_vec())),
    };
    if inst.len() < nl {
        return Err(Gap::NoInterpretation(name.clone(), inst.to_vec()))
    }
    let ind_inst: Vec<u32> = inst[inst.len() - nl..].to_vec();
    let inst = &ind_inst[..];
    let key = (ind_name.clone(), inst.to_vec());
    {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        if let Some(g) = app.declined.get(&key) {
            return Err(g.clone())
        }
        if app.decls.contains_key(&key) {
            return stored_or_reason_after(c, name, &ind_name, inst)
        }
    }
    match build(c, &ind_name, inst) {
        Ok(()) => stored_or_reason_after(c, name, &ind_name, inst),
        Err(g) => {
            if let Some(ip) = c.interp() {
                if let Some(app) = ip.ind_apparatus() {
                    app.declined.insert(key, g.clone());
                }
            }
            Err(g)
        }
    }
}

/// After a successful translation, is the constant that was *asked for* in the
/// store — and if not, what is actually missing?
///
/// §0.4 in its sharpest form. A translated declaration puts `⟦T⟧` and every
/// `⟦T.ctor⟧` in the store; `⟦T.rec⟧` needs the recursor wiring — the currying
/// nest over `GenRecursor`, the `T`-policy and the pointwise-`HYP` bridging —
/// which is a *different* piece of work. Reporting it as a bare store miss
/// would name the constant and say nothing; naming the recursor says which
/// work is outstanding.
fn stored_or_reason_after(
    c: &mut Checker<'_, '_>,
    name: &Name,
    ind_name: &Name,
    inst: &[u32],
) -> Result<(), Gap> {
    if c.stored_term(name, inst).is_some() {
        return Ok(())
    }
    if matches!(c.environment().get(name), Some(ConstantInfo::Recursor { .. })) {
        return Err(Gap::Recursor(ind_name.clone()))
    }
    Err(Gap::NoInterpretation(name.clone(), inst.to_vec()))
}

/// What the boundary walk read off the declaration, before anything is derived.
struct Shape {
    /// The declaration's `np` parameters: their Lean types at σ.
    param_tys: Vec<E>,
    /// `Sort ℓ`, the resultant sort, as a ground numeral.
    result_level: u32,
    /// One entry per constructor: its Lean type at σ, and its field mask.
    ctors: Vec<(Name, E, CtorSpec)>,
}

/// Translate one declaration at one ground instantiation.
fn build(c: &mut Checker<'_, '_>, ind_name: &Name, inst: &[u32]) -> Result<(), Gap> {
    let env = c.environment();
    let Some(ConstantInfo::Inductive { lparams, ty, num_params, num_indices, ctors, .. }) =
        env.get(ind_name)
    else {
        return Err(Gap::NoInterpretation(ind_name.clone(), inst.to_vec()))
    };
    let (np, ni) = (*num_params as usize, *num_indices as usize);
    if inst.len() != lparams.len() {
        return Err(Gap::NoInterpretation(ind_name.clone(), inst.to_vec()))
    }
    // ── the declaration-level scope checks, all positive ──────────────────
    if ni != 0 {
        return Err(Gap::IndexedFamily(ind_name.clone()))
    }
    // The branch decider, on the declaration's **own** level expression.
    let own = peel(ty, np + ni).ok_or_else(|| Gap::IndSpec(ind_name.clone(), "type shape"))?;
    let Expr::Sort(l) = &*own else {
        return Err(Gap::IndSpec(ind_name.clone(), "resultant sort"))
    };
    if !provably_nonzero(l) {
        return Err(Gap::PropInductive(ind_name.clone()))
    }
    let ind_ty = ground::subst_ground(ty, lparams, inst);
    let ctor_tys: Vec<(Name, E)> = ctors
        .iter()
        .map(|n| {
            let t = env.get(n).map(|ci| ground::subst_ground(ci.ty(), lparams, inst));
            (n.clone(), t)
        })
        .map(|(n, t)| t.map(|t| (n, t)).ok_or_else(|| Gap::IndSpec(ind_name.clone(), "ctor type")))
        .collect::<Result<_, _>>()?;

    // ── the `FnSym` boundary (WIRING-DESIGN.md §3.2) ──────────────────────
    let (shape, spec) = spec_of(c, ind_name, np, &ind_ty, &ctor_tys)?;
    if !spec.well_formed() {
        return Err(Gap::IndSpec(ind_name.clone(), "spec not well formed"))
    }

    // **The universe the declaration lands in, before anything is built.**
    // `derived::cumul::Chain` pins `U₁`: `Chain::over` sets `u1` from
    // `tower.at(1)` and every universe-placing entry reads that one field, so
    // a declaration resident above `Type 0` — or a σ that raises one there —
    // has nowhere to land, whatever its constructors look like. Checked here
    // rather than at the type former so that the reason reported is the one
    // that is true of the *declaration*, not whichever obligation happened to
    // be tried first (§0.4).
    if shape.result_level != 1 {
        return Err(Gap::IndUniverseHeight(ind_name.clone(), shape.result_level))
    }

    // ── the carrier ───────────────────────────────────────────────────────
    let ind = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        Rc::new(
            Inductive::build(kenv, &mut app.mach, &spec)
                .ok_or_else(|| Gap::IndSpec(ind_name.clone(), "carrier"))?,
        )
    };

    // ── `⊢ ∀p⃗. ind(p⃗) ∈ U₁` ───────────────────────────────────────────────
    let ty_in_u1 = decl_universe(c, ind_name, &ind)?;

    // ── the Lean-facing layer ─────────────────────────────────────────────
    let key = (ind_name.clone(), inst.to_vec());
    former(c, ind_name, inst, &shape, &ind, &ty_in_u1)?;
    let at = Decl { name: ind_name.clone(), inst: inst.to_vec(), np, ind: ind.clone() };
    for (i, (cname, cty, _)) in shape.ctors.iter().enumerate() {
        constructor(c, &at, cname, cty, i)?;
    }
    if let Some(ip) = c.interp() {
        if let Some(app) = ip.ind_apparatus() {
            app.decls.insert(key, ind);
        }
    }
    Ok(())
}

/// **The `FnSym` boundary**: walk the declaration's own type and each
/// constructor's, and produce the [`DeclSpec`] `derived::inductive` consumes.
///
/// All checks are positive: the walk verifies the covered shape rather than
/// enumerating exclusions. The scopes the parameters open stay open for the
/// whole walk, so every `βⱼ` body is stated at **one** set of variables — which
/// is what makes `define_abbrev` over `[p⃗, y₀…y_{j-1}]` the right abstraction
/// and what `DeclSpec::well_formed`'s arity check then confirms.
fn spec_of(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    np: usize,
    ind_ty: &E,
    ctor_tys: &[(Name, E)],
) -> Result<(Shape, DeclSpec), Gap> {
    let bad = |w: &'static str| Gap::IndSpec(ind_name.clone(), w);
    c.in_scope(|c| {
        // 1. the parameters, opened once.
        let mut param_tys = Vec::with_capacity(np);
        let mut cur = ind_ty.clone();
        for _ in 0..np {
            let Expr::Forall { ty, body } = &*cur.clone() else { return Err(bad("parameters")) };
            let dom = c.interpret_and_open(ty).map_err(|_| bad("parameter type"))?;
            dom.ok_or_else(|| bad("parameter type uninterpretable"))?;
            param_tys.push(ty.clone());
            cur = body.clone();
        }
        let Expr::Sort(l) = &*cur else { return Err(bad("resultant sort")) };
        let result_level = ground::eval(l, &Default::default()).ok_or_else(|| bad("level"))?;

        // 2. each constructor, at the same parameter variables.
        let mut ctors = Vec::with_capacity(ctor_tys.len());
        let mut specs = Vec::with_capacity(ctor_tys.len());
        for (cname, cty) in ctor_tys {
            let body = peel(cty, np).ok_or_else(|| bad("constructor parameters"))?;
            let spec = ctor_spec(c, ind_name, np, &body)?;
            ctors.push((cname.clone(), cty.clone(), spec.clone()));
            specs.push(spec);
        }
        Ok((Shape { param_tys, result_level, ctors }, DeclSpec::new(np, specs)))
    })
}

/// One constructor's fields, in declared order.
fn ctor_spec(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    np: usize,
    body: &E,
) -> Result<CtorSpec, Gap> {
    let bad = |w: &'static str| Gap::IndSpec(ind_name.clone(), w);
    let mut order = Vec::new();
    let mut args = Vec::new();
    let mut recs = 0usize;
    let mut cur = body.clone();
    // `d` counts the field binders opened so far, so parameter `i` is
    // `bvar(d + np - 1 - i)` at every point of the walk.
    let mut d = 0usize;
    // The kernel variables `βⱼ` is abstracted over: the parameters, then the
    // **plain** fields only. A recursive field is deliberately absent, so a
    // later field type that mentions one is refused by `define_abbrev` itself
    // rather than by a hand-written check.
    let mut abstraction: Vec<kernel::FreeVar> =
        c.scope_vars(np).ok_or_else(|| bad("parameter variables"))?;
    while let Expr::Forall { ty, body } = &*cur.clone() {
        if is_ind_spine(ind_name, ty, np, d) {
            order.push(Slot::Rec);
            recs += 1;
            // No interpretation and no kernel variable: the carrier is not
            // built yet, and nothing may depend on this field.
            c.open_uninterpreted(ty.clone());
        } else if is_function_typed_rec(ind_name, ty) {
            return Err(Gap::FunTypedRecArg(ind_name.clone()))
        } else if crate::expr::has_const(ind_name, ty) {
            // The declaration occurring anywhere other than as the bare
            // recursive spine: a nested or non-strictly-positive occurrence,
            // which `DeclSpec` cannot express. Tested **before** the field type
            // is interpreted, because interpreting a self-mentioning type would
            // re-enter `ensure` on the declaration being built.
            return Err(Gap::IndSpec(ind_name.clone(), "nested occurrence"))
        } else {
            let dom = c.interpret_and_open(ty).map_err(|_| bad("field type"))?;
            let dom = dom.ok_or_else(|| bad("field type uninterpretable"))?;
            let sym = {
                let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
                derived::define_abbrev(&mut ip.env, &abstraction, &dom)
                    .ok_or_else(|| bad("field type depends on a recursive field"))?
                    .0
            };
            args.push(sym);
            order.push(Slot::Plain);
            abstraction.push(c.scope_vars(1).ok_or_else(|| bad("field variable"))?[0]);
        }
        d += 1;
        cur = body.clone();
    }
    // The codomain must be the declaration applied to its own parameters.
    if !is_ind_spine(ind_name, &cur, np, d) {
        return Err(bad("constructor codomain"));
    }
    CtorSpec::with_order(args, recs, order).ok_or_else(|| bad("field mask"))
}

/// Is `e` the inductive itself applied to exactly the `np` parameters, in
/// order, at binder depth `d`?
fn is_ind_spine(ind_name: &Name, e: &E, np: usize, d: usize) -> bool {
    let (head, args) = crate::expr::get_app(e);
    let Expr::Const(n, _) = &*head else { return false };
    if n != ind_name || args.len() != np {
        return false
    }
    args.iter().enumerate().all(|(i, a)| {
        matches!(&**a, Expr::BVar(k) if *k as usize == d + np - 1 - i)
    })
}

/// Is `e` a `Π` whose ultimate codomain mentions the declaration — a
/// **function-typed recursive argument** (`RTree.node`, `Acc.intro`)?
///
/// `thesis.txt:1800`'s `Σ(z :: γ)` collapses to `1` only for a non-nested,
/// non-function-typed recursive argument, and `CtorSpec::recs` being a count is
/// exactly the assumption that it does. So this is a decline, and it is the
/// `derived/`-side item MINI-DESIGN.md §10 names.
fn is_function_typed_rec(ind_name: &Name, ty: &E) -> bool {
    match &**ty {
        Expr::Forall { body, .. } => crate::expr::has_const(ind_name, body),
        _ => false,
    }
}

/// `⊢ ∀p⃗. ind(p⃗) ∈ U₁`, via `derived::cumul`.
///
/// Only the **closed** route is wired: every constructor nullary in the sense
/// that matters here — no non-recursive fields — so no `arg_in_u1` obligation
/// arises and the whole chain is unconditional. A declaration with a plain
/// field needs `cumul::summand_in_u1`, whose obligations are stated as
/// `∀y⃗. (Dⱼ → βⱼ ∈ U₁)` over the *declaration's own* parameter variables; that
/// is a genuine piece of wiring and it is declined here by name rather than
/// approximated.
fn decl_universe(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ind: &Inductive,
) -> Result<Thm, Gap> {
    if ind.spec.ctors.iter().any(|s| !s.args.is_empty()) {
        return Err(Gap::IndSummand(ind_name.clone()))
    }
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
    let summands = derived::cumul::nullary_summands_in_u1(kenv, &app.chain, &app.mach, ind)
        .ok_or_else(|| Gap::IndSummand(ind_name.clone()))?;
    let tags = derived::cumul::tags_in_u1(kenv, &app.chain, &app.mach, ind, None, &summands)
        .ok_or_else(|| Gap::IndSummand(ind_name.clone()))?;
    let du = derived::cumul::DeclUniverse::over(kenv, &app.chain, &app.mach, ind, None, &tags)
        .ok_or_else(|| Gap::IndUniverseHeight(ind_name.clone(), 1))?;
    if !du.rests_on_nothing() {
        return Err(Gap::IndUniverseHeight(ind_name.clone(), 1))
    }
    Ok(du.ty_in_u1)
}

/// **The type former.** `⟦T.{ℓ⃗}⟧` is the `np`-deep λ-nest whose bottom is the
/// carrier `ind(p⃗)`, and its typing is that nest's own λ rule.
///
/// The nest is built by [`Checker::lam_nest`], which is `infer_type`'s `Lam`
/// arm with the recursion replaced at the bottom — so the `Π` clause at each
/// level is decided by the same `is_prop` the rest of the checker uses, and the
/// term produced is the one a use site's `⟦Π p⃗. Sort ℓ⟧` will be compared
/// against.
fn former(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    shape: &Shape,
    ind: &Rc<Inductive>,
    ty_in_u1: &Thm,
) -> Result<(), Gap> {
    let np = shape.param_tys.len();
    let lean_ty = c.environment().get(ind_name).map(|ci| ci.ty().clone());
    let lparams: Vec<Name> = c
        .environment()
        .get(ind_name)
        .map(|ci| ci.lparams().to_vec())
        .unwrap_or_default();
    let lean_ty = ground::subst_ground(
        &lean_ty.ok_or_else(|| Gap::NoInterpretation(ind_name.clone(), inst.to_vec()))?,
        &lparams,
        inst,
    );
    let ind2 = ind.clone();
    let u1 = ty_in_u1.clone();
    let name = ind_name.clone();
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        let level = crate::expr::sort(Level::Zero.succ());
        let Some((ps, _)) = c.binders(np) else {
            return Ok(Typing { ty: level, tm: None, ev: Ev::Gap(Gap::NoEndpoint) })
        };
        let ip = c.interp().expect("threaded");
        let carrier = ip.mk(ind2.ty, ps.clone());
        let ev = match derived::inst_all(&u1, &ps) {
            Some(t) if *t.concl() == Formula::mem(carrier.clone(), ip.sort(1)) => Ev::Proved(t),
            _ => Ev::Gap(Gap::IndUniverseHeight(name.clone(), 1)),
        };
        Ok(Typing { ty: level, tm: Some(carrier), ev })
    };
    let t = c.lam_nest(&lean_ty, np, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    store(c, ind_name, inst, t)
}

/// **A constructor.** `⟦T.ctor.{ℓ⃗}⟧` is the `np + k + m`-deep λ-nest whose
/// bottom is `ctor_i(y⃗, r⃗)`, and whose bottom membership is `Ctor::mem`
/// discharged at the field typings the nest's own scopes hold.
///
/// Two things have to be bridged and both are read off, never searched for:
///
/// * the antecedent `H` is **plains then recs**, while the Lean fields are in
///   declared order, so the atoms are permuted by the [`Slot`] mask;
/// * `Ctor::mem` concludes membership in `ind(p⃗)`, while the Lean codomain
///   interprets to the *applied spine* `app(…app(⟦T⟧, p₀)…)`. The two are
///   related by [`crate::interp::Interp::beta_spine`], whose premises are the
///   parameters' own scope assumptions.
fn constructor(
    c: &mut Checker<'_, '_>,
    at: &Decl,
    cname: &Name,
    cty: &E,
    i: usize,
) -> Result<(), Gap> {
    let spec = at.ind.spec.ctors[i].clone();
    let depth = at.np + spec.order.len();
    // The codomain is read off the declaration, not synthesised: it is the one
    // expression whose interpretation the bottom's membership must be about.
    let codomain =
        peel(cty, depth).ok_or_else(|| Gap::IndSpec(at.name.clone(), "ctor arity"))?;
    let site = CtorSite { at: at.clone(), i, codomain, spec };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(ctor_bottom(c, &site)) };
    let t = c.lam_nest(cty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    store(c, cname, &at.inst, t)
}

/// One translated declaration, at one ground instantiation: everything the
/// Lean-facing layer needs and nothing it does not.
#[derive(Clone)]
struct Decl {
    name: Name,
    inst: Vec<u32>,
    np: usize,
    ind: Rc<Inductive>,
}

/// …plus which constructor, and the two things read off its Lean type.
struct CtorSite {
    at: Decl,
    i: usize,
    codomain: E,
    spec: CtorSpec,
}

/// The bottom of a constructor's nest: `ctor_i(y⃗,r⃗)` and its membership in the
/// applied spine of `⟦T⟧`.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let CtorSite { at, i, codomain, spec } = site;
    let (ind_name, inst, np, ind) = (&at.name, &at.inst[..], at.np, &at.ind);
    let i = *i;
    let nf = spec.order.len();
    let ty = codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::Gap(g) };
    let Some((all, mems)) = c.binders(np + nf) else { return gap(Gap::NoEndpoint) };
    let Some(field_vars) = c.scope_vars(nf) else { return gap(Gap::NoEndpoint) };
    let (ps, fields) = all.split_at(np);
    let (_, field_mems) = mems.split_at(np);
    let param_mems = &mems[..np];
    // Split the Lean fields by the mask into the plain and recursive halves —
    // the order `Ctor::mem` states its prefix and its antecedent in.
    let mut ys = Vec::new();
    let mut rs = Vec::new();
    let mut y_mems = Vec::new();
    let mut r_mems = Vec::new();
    for (j, slot) in spec.order.iter().enumerate() {
        match slot {
            Slot::Plain => {
                ys.push(fields[j].clone());
                y_mems.push(field_mems[j].clone());
            }
            Slot::Rec => {
                rs.push(fields[j].clone());
                r_mems.push(field_mems[j].clone());
            }
        }
    }
    // `⟦T⟧` applied to the parameters, and the equation taking it to `ind(p⃗)`.
    let Some(store_ty) = c.stored_term(ind_name, inst) else { return gap(Gap::NoEndpoint) };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let raw = {
        let Some((_, app, _)) = ip.ind_parts() else { return gap(Gap::IndApparatus) };
        match ind.ctor_term(&app.mach, i, &ys, &rs) {
            Some(t) => t,
            None => return gap(Gap::IndSpec(ind_name.clone(), "ctor term")),
        }
    };
    // **The carrier term has to be given a name of mini's own**, and this is
    // not decoration.
    //
    // `⟨Injᵢ⟨y⃗⟩, f(r⃗)⟩` is assembled inside `derived`, so its applicative
    // structure was never recorded through [`crate::interp::Interp::mk`] — and
    // an unrecorded term that mentions a binder cannot be *skeletonised*, so the
    // very next `λ` over a constructor field fails to abstract its body. That
    // is a `Gap::Skeleton` at every recursive constructor, which is what the
    // first measurement of this wiring showed.
    //
    // One `define_abbrev` over the fields **in declared order** fixes it: the
    // symbol is applied through `mk`, hence decomposable, and its own defining
    // equation carries the membership across. The declared order is the right
    // one because that is the order the Lean λ-nest binds them in.
    let (term, unfold) = {
        let (kenv, _, _) = match ip.ind_parts() {
            Some(t) => t,
            None => return gap(Gap::IndApparatus),
        };
        let Some((sym, ax)) = derived::define_abbrev(kenv, &field_vars, &raw) else {
            return gap(Gap::IndSpec(ind_name.clone(), "ctor abbreviation"))
        };
        let at = match derived::inst_all(&ax, fields) {
            Some(t) => t,
            None => return gap(Gap::IndSpec(ind_name.clone(), "ctor abbreviation instance")),
        };
        (ip.mk(sym, fields.to_vec()), at)
    };
    let Some((carrier, spine_eq)) = ip.beta_spine(&store_ty, ps, param_mems) else {
        return gap(Gap::IndSpec(ind_name.clone(), "type former spine"))
    };
    if carrier != ip.mk(ind.ty, ps.to_vec()) {
        return gap(Gap::IndSpec(ind_name.clone(), "spine bottom"))
    }
    // `Ctor::mem` at `(p⃗, y⃗, r⃗)`, with its antecedent discharged from the
    // scopes' own assumptions. The recursive fields' typings are at the applied
    // spine and must first travel to `ind(p⃗)` along the same equation.
    let mut inst_args: Vec<Term> = ps.to_vec();
    inst_args.extend(ys.iter().cloned());
    inst_args.extend(rs.iter().cloned());
    let Some(at) = derived::inst_all(&ind.ctors[i].mem, &inst_args) else {
        return gap(Gap::IndSpec(ind_name.clone(), "ctor mem instantiation"))
    };
    let mut atoms: Vec<Thm> = y_mems;
    for m in &r_mems {
        match ip.retarget_set(m, &spine_eq) {
            Some(t) => atoms.push(t),
            None => return gap(Gap::ConvCompose("ctor-rec-field")),
        }
    }
    let mem = if atoms.is_empty() {
        at
    } else {
        let mut conj = atoms.pop().expect("non-empty");
        while let Some(a) = atoms.pop() {
            conj = derived::and_intro(&a, &conj);
        }
        match Thm::mp(&at, &conj) {
            Some(t) => t,
            None => return gap(Gap::IndSpec(ind_name.clone(), "ctor antecedent")),
        }
    };
    // The subject moves onto mini's own symbol, along that symbol's own
    // defining equation…
    let mem = match ip.retarget_subject(&mem, &unfold) {
        Some(t) => t,
        None => return gap(Gap::ConvCompose("ctor-abbrev")),
    };
    // …and the set back onto the applied spine, which is what the Lean codomain
    // interprets to.
    let back = match derived::eq_symm(&mut ip.env, &spine_eq) {
        Some(t) => t,
        None => return gap(Gap::ConvCompose("ctor-spine-symm")),
    };
    match ip.retarget_set(&mem, &back) {
        Some(t) if *t.concl() == Formula::mem(term.clone(), store_spine(ip, &store_ty, ps)) => {
            Typing { ty, tm: Some(term), ev: Ev::Proved(t) }
        }
        _ => gap(Gap::ConvCompose("ctor-codomain")),
    }
}

/// `app(…app(⟦T⟧, p₀)…, p_{np-1})` — the term a use site's `⟦T p⃗⟧` is.
fn store_spine(ip: &mut crate::interp::Interp, former: &Term, ps: &[Term]) -> Term {
    let mut out = former.clone();
    for p in ps {
        out = ip.app(out, p.clone());
    }
    out
}

/// Put a finished interpretation into the store.
fn store(
    c: &mut Checker<'_, '_>,
    name: &Name,
    inst: &[u32],
    t: Typing,
) -> Result<(), Gap> {
    let (tm, ev) = (t.tm, t.ev);
    let Some(term) = tm else { return Err(ev.reason(Gap::NoEndpoint)) };
    let typing = match ev {
        Ev::Proved(th) => match Sealed::new(th) {
            Ok(s) => Ok(s),
            Err(_) => Err(Gap::IndSpec(name.clone(), "hypothesis escaped the nest")),
        },
        Ev::Gap(g) => Err(g),
    };
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    ip.put_const((name.clone(), inst.to_vec()), ConstInterp { term, typing, defeq: None });
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{forall, konst, sort};
    use crate::interp::Interp;

    fn p(s: &str) -> Level { Level::Param(Name::simple(s)) }

    /// **The eliminator trichotomy, at the shapes the corpus actually
    /// presents.** Each line is a real declaration's resultant sort, and the
    /// two that matter most are the ones a "is it `Sort 0`?" test gets wrong:
    /// `PUnit.{u} : Sort u` is *not* provably nonzero even though `u := 1` is a
    /// `Type`, and `PProd.{u,v} : Sort (max (max 1 u) v)` *is*, because Lean
    /// spells the `1` into the level.
    ///
    /// Deciding this per instantiation instead of per declaration is the design
    /// error `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3 closes, and the `PUnit` row
    /// is exactly where it would show up.
    #[test]
    fn the_branch_is_decided_by_the_declarations_own_level() {
        // Class (T): a W-type.
        assert!(provably_nonzero(&Level::Zero.succ()), "Bool : Type 0");
        assert!(provably_nonzero(&p("u").succ()), "List at Type u");
        assert!(
            provably_nonzero(&Level::max(Level::max(Level::Zero.succ(), p("u")), p("v"))),
            "PProd at Sort (max (max 1 u) v) — the 1 is what decides it"
        );
        assert!(
            provably_nonzero(&Level::max(p("u").succ(), p("v").succ())),
            "Prod at Type (max u v)"
        );
        // Class (S) or (P): never a W-type, at any σ.
        assert!(!provably_nonzero(&Level::Zero), "And : Prop");
        assert!(!provably_nonzero(&p("u")), "PUnit at Sort u — a Prop when u is 0");
        assert!(
            !provably_nonzero(&Level::imax(p("u").succ(), p("v"))),
            "an imax is zero exactly when its right side is"
        );
        assert!(
            provably_nonzero(&Level::imax(p("u"), p("v").succ())),
            "…and nonzero when the right side is"
        );
    }

    /// A three-constructor, genuinely recursive declaration, translated through
    /// the whole boundary:
    ///
    /// ```text
    /// inductive T : Type | c0 | c1 (r : T) | c2 (r₁ r₂ : T)
    /// ```
    ///
    /// **Three constructors and three distinct arities**, because two of either
    /// cannot distinguish an ordering from its reverse: the masks are `[]`,
    /// `[Rec]` and `[Rec, Rec]`, so a builder that mixed up the constructor
    /// index or the field count would produce a `c1` where `c2` belongs and the
    /// arity check below would not catch it.
    fn three_ctor_env() -> (Environment, Name, Vec<Name>) {
        let t = Name::simple("T");
        let ty = konst(t.clone(), Vec::new().into());
        let ctors = vec![
            (Name::str(&t, "c0"), ty.clone()),
            (Name::str(&t, "c1"), forall(ty.clone(), ty.clone())),
            (Name::str(&t, "c2"), forall(ty.clone(), forall(ty.clone(), ty.clone()))),
        ];
        let names: Vec<Name> = ctors.iter().map(|(n, _)| n.clone()).collect();
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::Zero.succ()),
                ctors,
            },
        )
        .expect("the declaration is accepted");
        (env, t, names)
    }

    /// The carrier and all three constructors are interpreted, and **every
    /// typing concludes the statement it claims** — `⟦T⟧ ∈ ⟦Type 0⟧` and
    /// `⟦T.cᵢ⟧ ∈ ⟦its own Lean type⟧`.
    #[test]
    fn a_three_constructor_declaration_translates_with_its_typings() {
        let (env, t, ctors) = three_ctor_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);

        let ty = c.infer_type(&konst(t.clone(), Vec::new().into())).expect("infer ⟦T⟧");
        assert!(ty.tm.is_some(), "the carrier must interpret");
        let mem = ty.ev.thm().expect("⊢ ⟦T⟧ ∈ ⟦Type 0⟧").clone();
        assert!(mem.hyps().is_empty(), "a closed declaration's typing is unconditional");
        let want = Formula::mem(ty.tm.clone().unwrap(), c.interp().unwrap().sort(1));
        assert_eq!(*mem.concl(), want, "the carrier's typing must be about ⟦Type 0⟧");

        // Each constructor, at its own arity. `c1` and `c2` are λ-nests over
        // the recursive fields; `c0` is the bare carrier element.
        for (i, n) in ctors.iter().enumerate() {
            let ct = c.infer_type(&konst(n.clone(), Vec::new().into())).expect("infer ctor");
            let m = ct.ev.thm().unwrap_or_else(|| panic!("{n} has no typing: {:?}", ct.ev)).clone();
            assert!(m.hyps().is_empty(), "{n}'s typing must be unconditional");
            let (subj, _) = m.concl().as_mem().expect("a membership");
            assert_eq!(
                subj,
                ct.tm.clone().unwrap(),
                "{n}'s typing must be about {n}'s own interpretation"
            );
            let _ = i;
        }
    }

    /// **Non-vacuity.** Memberships alone are satisfied by a one-element
    /// carrier, so the test that matters is the negative one: the three
    /// constructor interpretations are pairwise **provably distinct**, which
    /// makes the carrier provably not a singleton — and `c1`'s injectivity
    /// makes it provably infinite.
    ///
    /// The distinctness is derived, not compared: `Inductive::distinct` proves
    /// `⊢ ¬(ctor_i(…) = ctor_j(…))`, and mini's own abbreviations are equal to
    /// those terms by their defining equations. Comparing the two `Term`s would
    /// prove nothing at all — two different symbols can denote one set.
    #[test]
    fn the_three_constructors_are_provably_distinct() {
        let (env, t, ctors) = three_ctor_env();
        let mut ip = Interp::new();
        {
            let mut c = Checker::threaded(&env, &mut ip);
            c.infer_type(&konst(t.clone(), Vec::new().into())).expect("build");
            for n in &ctors {
                c.infer_type(&konst(n.clone(), Vec::new().into())).expect("build");
            }
        }
        let key = (t.clone(), Vec::new());
        let (kenv, app, _) = ip.ind_parts().expect("apparatus");
        let ind = app.decls.get(&key).expect("translated").clone();
        for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
            let d = ind
                .distinct(kenv, &app.mach, i, j)
                .unwrap_or_else(|| panic!("no distinctness for ({i},{j})"));
            assert!(d.hyps().is_empty(), "distinctness must be unconditional");
        }
        // …and the constructors really are three, with the arities the mask
        // says: `[]`, `[Rec]`, `[Rec, Rec]`.
        assert_eq!(ind.spec.ctors.len(), 3);
        let recs: Vec<usize> = ind.spec.ctors.iter().map(|s| s.recs).collect();
        assert_eq!(recs, vec![0, 1, 2], "the constructor order and arities must survive the walk");
    }

    /// A **`Prop`-valued** declaration is declined by name, at every σ, and the
    /// carrier is never built for it. This is the per-declaration branch: a
    /// class-(S)/(P) declaration must not acquire a W-type even where its
    /// instantiation looks like a `Type`.
    #[test]
    fn a_prop_declaration_is_declined_rather_than_given_a_w_type() {
        let t = Name::simple("P");
        let ty = konst(t.clone(), Vec::new().into());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::Zero),
                ctors: vec![(Name::str(&t, "intro"), ty)],
            },
        )
        .expect("accepted");
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let r = c.infer_type(&konst(t.clone(), Vec::new().into())).expect("infer");
        assert!(r.tm.is_none(), "a Prop declaration must not acquire an interpretation");
        assert_eq!(
            r.ev.gap(),
            Some(&Gap::PropInductive(t.clone())),
            "and the gap must name the cause, not the site"
        );
        // The decline is recorded, so a second lookup reports the same reason
        // rather than a bare store miss.
        let r2 = c.infer_type(&konst(t.clone(), Vec::new().into())).expect("infer");
        assert_eq!(r2.ev.gap(), Some(&Gap::PropInductive(t)));
    }
}
