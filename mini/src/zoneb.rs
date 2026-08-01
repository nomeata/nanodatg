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
//! Reached by the general walk: a **non-indexed, non-nested, single**
//! declaration whose resultant sort is provably nonzero, whose constructors
//! have no function-typed recursive argument, and each of whose non-recursive
//! field types lands in `U₁` — the level `derived::cumul::sigma_n`'s summand
//! induction is stated at. The *declaration's own* level is no longer a
//! constraint: `cumul::DeclUniverse::over_at` places a carrier anywhere in the
//! tower, so `Type n` is reached for every `n` the cumulativity table covers.
//!
//! Reached by a named clause: [`crate::direct`]'s three, which are class (S)
//! and would be declined by [`provably_nonzero`] otherwise.
//!
//! Everything else is a counted decline. The declines are not a defensive
//! list: each is a shape `derived::inductive::DeclSpec` cannot express, or a
//! `derived/` construction that does not exist yet, and each says which.

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

/// `Sort ℓ` at a ground numeral, as a mini expression.
pub(crate) fn level_numeral(n: u32) -> Level {
    let mut l = Level::Zero;
    for _ in 0..n {
        l = l.succ();
    }
    l
}

/// Peel `n` `Π` binders, returning the body. `None` if there are fewer.
pub(crate) fn peel(ty: &E, n: usize) -> Option<E> {
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
    // The constant's **own** σ, kept apart from the declaration's: a recursor's
    // store key is this one, and using the declaration's would put
    // `⟦PUnit.rec.{w,u}⟧` where `⟦PUnit.rec.{u}⟧` belongs.
    let own_inst = inst.to_vec();
    let ind_inst: Vec<u32> = inst[inst.len() - nl..].to_vec();
    let inst = &ind_inst[..];
    let key = (ind_name.clone(), inst.to_vec());
    {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let app = ip.ind_apparatus().ok_or(Gap::IndApparatus)?;
        if let Some(g) = app.declined.get(&key) {
            return Err(g.clone())
        }
    }
    // **Already translated** is `⟦T.{σ}⟧` being in the store, not a second
    // bookkeeping table. Every route — the class-(T) walk and every
    // [`crate::direct`] clause — puts the type former there first, so this one
    // test covers both, and it is the same key on the same store.
    if c.stored_term(&ind_name, inst).is_none() {
        if let Err(g) = build(c, &ind_name, inst) {
            if let Some(ip) = c.interp() {
                if let Some(app) = ip.ind_apparatus() {
                    app.declined.insert(key, g.clone());
                }
            }
            return Err(g)
        }
    }
    stored_or_reason_after(c, name, &ind_name, inst, &own_inst)
}

/// After a successful translation, is the constant that was *asked for* in the
/// store — and if not, what is actually missing?
///
/// §0.4 in its sharpest form. A translated declaration puts `⟦T⟧` and every
/// `⟦T.ctor⟧` in the store; `⟦T.rec⟧` is a **second** build over the finished
/// carrier, at the recursor's own σ, and it is [`crate::recursor`]'s. That
/// module either stores the eliminator or returns the name of the `derived/`
/// construction its typing waits on — so the reason reported here is never this
/// site's own label.
///
/// The two `inst`s are different lists and both are needed: `inst` is the
/// declaration's, which `⟦T⟧` and `⟦T.ctor⟧` are keyed on, and `own` is the
/// constant's, which for a recursor carries the motive's level in front.
fn stored_or_reason_after(
    c: &mut Checker<'_, '_>,
    name: &Name,
    ind_name: &Name,
    inst: &[u32],
    own: &[u32],
) -> Result<(), Gap> {
    if matches!(c.environment().get(name), Some(ConstantInfo::Recursor { .. })) {
        if c.stored_term(name, own).is_some() {
            return Ok(())
        }
        return crate::recursor::ensure(c, ind_name, inst, name, own)
    }
    if c.stored_term(name, inst).is_some() {
        return Ok(())
    }
    Err(Gap::NoInterpretation(name.clone(), inst.to_vec()))
}

/// What the boundary walk read off the declaration, before anything is derived.
pub(crate) struct Shape {
    /// The declaration's `np` parameters: their Lean types at σ.
    pub(crate) param_tys: Vec<E>,
    /// `Sort ℓ`, the resultant sort, as a ground numeral.
    pub(crate) result_level: u32,
    /// One entry per constructor: its Lean type at σ, its field mask, and the
    /// `k` **summand legs** [`ctor_spec`] derived while it had the binders open.
    ///
    /// A leg is `⊢ ∀q⃗. (qᵢ ∈ ⟦Pᵢ⟧ → … ∀y₀. (y₀ ∈ β₀ → … βⱼ ∈ U₁ …))` — the
    /// declaration's parameters and the constructor's plain fields as
    /// *alternating* `∀`/`→` layers, which is the shape a checker that opens
    /// and closes one binder at a time produces.
    /// `derived::cumul::summand_obligation` is what turns it into the prenex
    /// shape `sigma_n::arg_obligations` states, and it is applied in
    /// [`decl_universe`] rather than here because the collapse's last step
    /// instantiates the parameter prefix at `Inductive::params`, which do not
    /// exist until the carrier is built.
    pub(crate) ctors: Vec<(Name, E, CtorSpec, CtorEvidence)>,
}

/// What [`ctor_spec`] derived about one constructor's **plain** fields, in
/// declared plain order.
///
/// Both entries exist because `derived::inductive` and `derived::cumul` state
/// every field fact at the `define_abbrev` **symbol** `βⱼ(p⃗,y⃗<ⱼ)`, while a
/// checker's scope holds it at the interpretation `⟦βⱼ⟧` that symbol
/// abbreviates. The two are the same set by that symbol's own defining axiom,
/// and carrying the axiom is what lets every consumer make the move in one
/// Leibniz step instead of re-deriving the fact at the other term.
#[derive(Clone, Default)]
pub(crate) struct CtorEvidence {
    /// The interleaved summand obligation per plain field — see [`Shape`].
    /// Empty when the walk was asked for [`Legs::Skip`].
    legs: Vec<Thm>,
    /// `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`, per plain field.
    pub(crate) abbrev: Vec<Thm>,
}

/// **Whether the boundary walk derives the summand legs**, which is a question
/// about the route and not about the declaration.
///
/// A leg is `⊢ … βⱼ(p⃗,y⃗<ⱼ) ∈ U₁`, and it exists for one consumer:
/// [`decl_universe`], which places a **class-(T)** carrier by
/// `derived::cumul`'s summand induction. Class (S) has no summand and no tag
/// sum — `⊢ A_φ(p⃗) ∈ U₀` is one `Tower::cond_in_u0` whatever the fields are —
/// so deriving a leg there would be work with no consumer, and, worse, could
/// **decline a declaration for a reason that does not apply to it**: the leg's
/// last step raises the field's typing into `U₁` and returns
/// [`Gap::IndSummand`] when it cannot. Asking for [`Legs::Skip`] is what keeps
/// a class-(S) declaration with a `Type 1`-resident field from being refused by
/// a class-(T) obligation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Legs {
    /// Derive them — the class-(T) route.
    Derive,
    /// Do not — the class-(S) route.
    Skip,
}

/// `⊢ ∀p⃗. ([H →] ind(p⃗) ∈ Uₙ)`, and the `H` it is under.
struct DeclUniv {
    /// The theorem the type former's bottom consumes.
    ty_in_un: Thm,
    /// The antecedent, when the declaration has one: the conjunction of the
    /// parameters' own typings, left-nested, at `Inductive::params`. `None`
    /// for a closed declaration, whose chain is unconditional.
    hyp: Option<Formula>,
    /// Which `Uₙ` — the ground numeral `ℓ` of the declaration's resultant sort.
    level: u32,
}

/// Translate one declaration at one ground instantiation.
pub(crate) fn build(c: &mut Checker<'_, '_>, ind_name: &Name, inst: &[u32]) -> Result<(), Gap> {
    // **`Eq`'s direct clause comes first**, and the dispatch is one lookup on
    // the name this call was already keyed on ([`crate::direct::clause_for`]).
    // Before the trichotomy rather than after it, because `Eq` is class (S) —
    // its resultant sort is not provably nonzero — *and* it is indexed, so both
    // of the declaration-level checks below would decline it before the
    // trichotomy could route it anywhere.
    if let Some(cl) = crate::direct::clause_for(ind_name) {
        return crate::direct::build(c, cl, ind_name, inst)
    }
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
    let ind_ty = ground::subst_ground(ty, lparams, inst);
    let ctor_tys: Vec<(Name, E)> = ctors
        .iter()
        .map(|n| {
            let t = env.get(n).map(|ci| ground::subst_ground(ci.ty(), lparams, inst));
            (n.clone(), t)
        })
        .map(|(n, t)| t.map(|t| (n, t)).ok_or_else(|| Gap::IndSpec(ind_name.clone(), "ctor type")))
        .collect::<Result<_, _>>()?;
    // **The second and third branches of the trichotomy**
    // (`INDEXED-DESIGN.md` §2.1). A resultant level that is not provably
    // nonzero is class (S) or class (P), and *which* is read off the
    // eliminator, not recomputed: [`crate::class_s::large_eliminating`] is one
    // store lookup on the recursor's own level-parameter list. Class (S) is
    // §5.3's subsingleton carrier and is built; class (P) is the truncation
    // clause and is not wired, so it keeps [`Gap::PropInductive`] — which is
    // now a statement about one class rather than about two.
    if !provably_nonzero(l) {
        if !crate::class_s::large_eliminating(c.environment(), ind_name) {
            return Err(Gap::PropInductive(ind_name.clone()))
        }
        return crate::class_s::build(c, ind_name, inst, np, &ind_ty, &ctor_tys)
    }

    // ── the `FnSym` boundary (WIRING-DESIGN.md §3.2) ──────────────────────
    let (shape, spec) = spec_of(c, ind_name, np, &ind_ty, &ctor_tys, Legs::Derive)?;
    if !spec.well_formed() {
        return Err(Gap::IndSpec(ind_name.clone(), "spec not well formed"))
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

    // ── `⊢ ∀p⃗. ([H →] ind(p⃗) ∈ U_ℓ)` ──────────────────────────────────────
    let du = decl_universe(c, ind_name, &shape, &ind)?;

    // ── the Lean-facing layer ─────────────────────────────────────────────
    let key = (ind_name.clone(), inst.to_vec());
    former(c, ind_name, inst, &shape, &ind, &du)?;
    let at = Decl { name: ind_name.clone(), inst: inst.to_vec(), np, ind: ind.clone() };
    for (i, (cname, cty, _, ev)) in shape.ctors.iter().enumerate() {
        constructor(c, &at, cname, cty, i, &ev.abbrev)?;
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
pub(crate) fn spec_of(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    np: usize,
    ind_ty: &E,
    ctor_tys: &[(Name, E)],
    legs: Legs,
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
        //
        // **In its own scope.** A constructor's field binders were once left
        // open for the next constructor's walk, which put the wrong entries on
        // the de Bruijn telescope for every declaration with two constructors
        // and a plain field. It never bit, because the only such declarations
        // in the corpus stopped one step earlier at `ind-summand`; deriving the
        // legs is what makes them get this far.
        let mut ctors = Vec::with_capacity(ctor_tys.len());
        let mut specs = Vec::with_capacity(ctor_tys.len());
        for (cname, cty) in ctor_tys {
            let body = peel(cty, np).ok_or_else(|| bad("constructor parameters"))?;
            let (spec, ev) = c.in_scope(|c| ctor_spec(c, ind_name, np, &body, legs))?;
            ctors.push((cname.clone(), cty.clone(), spec.clone(), ev));
            specs.push(spec);
        }

        // 3. the parameter scopes, discharged over every leg of every
        //    constructor at once — so that one `⟦Pᵢ⟧` serves them all, and the
        //    `H` read off any leg is the `H` read off every other.
        for i in (0..np).rev() {
            let closed = c.close_one().ok_or_else(|| bad("parameter scope"))?;
            for (.., ev) in ctors.iter_mut() {
                for leg in ev.legs.iter_mut() {
                    *leg = closed.discharge(leg).map_err(|_| bad("parameter discharge"))?;
                }
            }
            let _ = i;
        }
        Ok((Shape { param_tys, result_level, ctors }, DeclSpec::new(np, specs)))
    })
}

/// One constructor's fields, in declared order, and its `k` summand legs.
///
/// The legs are the reason this walk derives anything at all rather than only
/// reading a shape off. `cumul::sigma_n` asks the caller for
/// `⊢ ∀y⃗. (Dⱼ → βⱼ(p⃗,y⃗) ∈ U₁)` per plain field, and *this* is the one place
/// where all of `⟦βⱼ⟧`, its typing, its abbreviation's defining axiom and the
/// scopes the earlier fields opened are in hand simultaneously. Deriving them
/// in a second walk after the carrier exists would have to re-interpret every
/// field type at a second set of variables and then argue that the two agree.
///
/// Two conversions happen per field and neither is a search:
///
/// * the typing is `⊢ ⟦βⱼ⟧ ∈ ⟦Sort ℓ⟧` at whatever `ℓ` the field's type has,
///   and `U₁` is where the summand induction wants it — so it is **raised**
///   through the cumulativity table, which is a decline when `ℓ > 1`;
/// * the subject is `⟦βⱼ⟧` while the obligation is about `βⱼ(p⃗,y⃗)`, the
///   `define_abbrev` symbol, and the two are related by that symbol's own
///   defining axiom at the very variables it was abstracted over.
///
/// The **guard** needs the same move one level out: `Closed::discharge` states
/// `∀yᵢ. (yᵢ ∈ ⟦βᵢ⟧ → …)` because that is the domain the scope was opened at,
/// and `arg_obligations` states `yᵢ ∈ βᵢ(p⃗,y⃗)`. One Leibniz step on the set
/// position converts it, and the formula it is applied at is built from the
/// theorem's own pre-discharge conclusion, so nothing is guessed about the
/// body.
fn ctor_spec(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    np: usize,
    body: &E,
    legs: Legs,
) -> Result<(CtorSpec, CtorEvidence), Gap> {
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
    // `⊢ βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧`, per plain field, at the abstraction's own
    // variables — and the `βⱼ(p⃗,y⃗<ⱼ)` term itself, which the guard conversion
    // one level out needs.
    let mut unfolds: Vec<(Term, Thm)> = Vec::new();
    let mut ev = CtorEvidence::default();
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
            // The field type's own typing, before the binder is opened — the
            // leg's body, and the only place it is available.
            let t1 = c.infer_type(ty).map_err(|_| bad("field type"))?;
            let (s1, _, t1) = c.whnf_typing(t1).map_err(|_| bad("field type sort"))?;
            let l = crate::kernel::as_sort(&s1).map_err(|_| bad("field type sort"))?;
            let l = ground::eval(&l, &Default::default()).ok_or_else(|| bad("field level"))?;
            let dom = t1.tm.clone().ok_or_else(|| bad("field type uninterpretable"))?;
            let mem = t1.ev.thm().cloned().ok_or_else(|| bad("field type typing"))?;
            let sym_args: Vec<Term> = abstraction.iter().map(|v| Term::var(*v)).collect();
            let (sym, unfold) = {
                let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
                let (sym, ax) = derived::define_abbrev(&mut ip.env, &abstraction, &dom)
                    .ok_or_else(|| bad("field type depends on a recursive field"))?;
                let at = derived::inst_all(&ax, &sym_args)
                    .ok_or_else(|| bad("field abbreviation instance"))?;
                if legs == Legs::Derive {
                    // `⊢ βⱼ(p⃗,y⃗) ∈ U₁`: the typing raised to the universe the
                    // summand induction is stated in, then carried onto the
                    // abbreviation's own symbol. A field type resident above
                    // `Type 0` is where the raise stops, and it stops by name.
                    let raised = ip
                        .raise_in_gamma(l as usize, 1, &mem)
                        .ok_or_else(|| Gap::IndSummand(ind_name.clone()))?;
                    let leg = ip
                        .retarget_subject(&raised, &at)
                        .ok_or(Gap::ConvCompose("summand-leg-subject"))?;
                    ev.legs.push(leg);
                }
                ev.abbrev.push(ax);
                (sym, at)
            };
            args.push(sym);
            order.push(Slot::Plain);
            unfolds.push((Term::apply(sym, sym_args), unfold));
            c.push_interpreted(ty.clone(), dom);
            abstraction.push(c.scope_vars(1).ok_or_else(|| bad("field variable"))?[0]);
        }
        d += 1;
        cur = body.clone();
    }
    // The codomain must be the declaration applied to its own parameters.
    if !is_ind_spine(ind_name, &cur, np, d) {
        return Err(bad("constructor codomain"));
    }
    let spec = CtorSpec::with_order(args, recs, order).ok_or_else(|| bad("field mask"))?;
    // Close every binder this walk opened, discharging each leg through the
    // scopes it was derived under — leg `j` under field scopes `0 … j-1` and no
    // others, so the `∀`/`→` alternation comes out at the right depth.
    let mut plain_left = unfolds.len();
    for _ in 0..d {
        // A recursive field opened no kernel scope, so it discharges nothing.
        let Some(closed) = c.close_one() else { continue };
        plain_left -= 1;
        let (sym_app, unfold) = unfolds[plain_left].clone();
        for leg in ev.legs.iter_mut().skip(plain_left + 1) {
            *leg = discharge_at_symbol(c, &closed, &sym_app, &unfold, leg)
                .ok_or(Gap::ConvCompose("summand-leg-guard"))?;
        }
    }
    Ok((spec, ev))
}

/// One field scope discharged, with its guard stated at the abbreviation
/// symbol rather than at the interpretation it abbreviates.
///
/// `Closed::discharge` produces `∀w. (w ∈ ⟦βᵢ⟧ → φ)`; `arg_obligations` wants
/// `∀w. (w ∈ βᵢ(p⃗,y⃗) → φ)`. The two sets are equal by `βᵢ`'s own defining
/// axiom, and `φ` is taken from the theorem's conclusion *before* the
/// discharge, so the formula the Leibniz step is applied at is the one the
/// discharge is about and not a reconstruction of it.
fn discharge_at_symbol(
    c: &mut Checker<'_, '_>,
    closed: &crate::scope::Closed,
    sym_app: &Term,
    unfold: &Thm,
    inner: &Thm,
) -> Option<Thm> {
    let phi = inner.concl().clone();
    let dom = closed.domain().clone();
    let w = closed.var();
    let discharged = closed.discharge(inner).ok()?;
    let ip = c.interp()?;
    let x = ip.env.fresh_var();
    let at = Formula::forall(w, Formula::imp(Formula::mem(Term::var(w), Term::var(x)), phi));
    // `unfold` is `βᵢ(p⃗,y⃗) = ⟦βᵢ⟧`; the substitution runs the other way.
    let back = derived::eq_symm(&mut ip.env, unfold)?;
    let leib = Thm::eq_leibniz(dom, sym_app.clone(), x, at);
    Thm::mp(&Thm::mp(&leib, &back)?, &discharged)
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

/// `⊢ ∀p⃗. ([H →] ind(p⃗) ∈ Uₙ)`, via `derived::cumul`.
///
/// Two things that used to be declines are now compositions, and both were
/// closed on the `derived/` side:
///
/// * **a constructor with a non-recursive field.** `cumul::summand_in_u1`'s
///   obligations are stated prenex, `∀y⃗. (Dⱼ → βⱼ ∈ U₁)`, while a checker that
///   opens and closes one binder at a time produces the *interleaved*
///   `∀y₀. (H₀ → ∀y₁. (H₁ → …))`. `cumul::summand_obligation` is the bridge,
///   and it doubles as the collapse of the **parameter** prefix: the legs
///   [`ctor_spec`] hands back carry the parameters as `np` further alternating
///   layers, one call turns those into the single conjunction `H`, and
///   instantiating at `Inductive::params` is what puts the whole thing at the
///   variables `arg_obligations` speaks about.
/// * **a declaration above `Type 0`.** `DeclUniverse::over_at` takes the level,
///   so the height is no longer a decline; what is checked here is only that
///   the tower has that level and that the tag membership can be raised to it.
///   `⟦Sort ℓ⟧ is Uℓ`, so the level is the resultant sort's own numeral.
///
/// The `H` is read off a leg rather than rebuilt, and every leg of every
/// constructor is discharged through **one** set of parameter scopes
/// ([`spec_of`] step 3), so "the same `H`" is a fact about the derivation
/// rather than a comparison that has to be made.
fn decl_universe(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    shape: &Shape,
    ind: &Inductive,
) -> Result<DeclUniv, Gap> {
    let level = shape.result_level;
    let short = |_: ()| Gap::IndSummand(ind_name.clone());
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let np = ps.len();

    // The legs, collapsed to the prenex shape and moved onto the carrier's own
    // parameter variables. `H` is whatever antecedent that leaves behind.
    let mut per_ctor: Vec<Vec<Thm>> = Vec::with_capacity(shape.ctors.len());
    let mut hyp: Option<Formula> = None;
    {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        for (.., ev) in &shape.ctors {
            let mut out = Vec::with_capacity(ev.legs.len());
            for leg in &ev.legs {
                let collapsed = derived::cumul::summand_obligation(&mut ip.env, leg, None, np)
                    .ok_or_else(|| short(()))?;
                let at = derived::inst_all(&collapsed, &ps).ok_or_else(|| short(()))?;
                if np > 0 {
                    let h = at.concl().as_imp().ok_or_else(|| short(()))?.0;
                    match &hyp {
                        Some(prev) if *prev != h => return Err(short(())),
                        _ => hyp = Some(h),
                    }
                }
                out.push(at);
            }
            per_ctor.push(out);
        }
    }

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let tower = ip.prelude.tower.clone();
    let tags = {
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let mut summands = Vec::with_capacity(per_ctor.len());
        for (ci, legs) in per_ctor.iter().enumerate() {
            let obligations = derived::cumul::summand_obligations(
                kenv,
                &app.chain,
                &app.mach,
                ind,
                ci,
                hyp.as_ref(),
                legs,
            )
            .ok_or_else(|| short(()))?;
            summands.push(
                derived::cumul::summand_in_u1(
                    kenv,
                    &app.chain,
                    &app.mach,
                    ind,
                    ci,
                    hyp.as_ref(),
                    &obligations,
                )
                .ok_or_else(|| short(()))?,
            );
        }
        derived::cumul::tags_in_u1(kenv, &app.chain, &app.mach, ind, hyp.as_ref(), &summands)
            .ok_or_else(|| short(()))?
    };
    // `⊢ [H →] A ∈ Uₙ`. Unconditionally that is one instance of the cumulativity
    // table; under an `H` the antecedent lives in the *conclusion*, so the
    // inclusion is composed rather than applied.
    let tags = if level == 1 {
        tags
    } else {
        let n = level as usize;
        match &hyp {
            None => ip
                .raise_in_gamma(1, n, &tags)
                .ok_or_else(|| Gap::IndUniverseHeight(ind_name.clone(), level))?,
            Some(_) => {
                let a = tags
                    .concl()
                    .as_imp()
                    .and_then(|(_, c)| c.as_mem().map(|(x, _)| x))
                    .ok_or_else(|| Gap::IndUniverseHeight(ind_name.clone(), level))?;
                let lift = ip
                    .cumul_lift(1, n)
                    .and_then(|t| derived::inst_all(t, std::slice::from_ref(&a)))
                    .ok_or_else(|| Gap::IndUniverseHeight(ind_name.clone(), level))?;
                derived::syl(&tags, &lift)
                    .ok_or_else(|| Gap::IndUniverseHeight(ind_name.clone(), level))?
            }
        }
    };

    let lvl = tower.at(level as usize).ok_or(Gap::SortTowerHeight)?;
    let want = ip.sort(level);
    let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
    let du = derived::cumul::DeclUniverse::over_at(
        kenv,
        &app.chain,
        &app.mach,
        ind,
        hyp.as_ref(),
        &lvl,
        &tags,
    )
    .ok_or_else(|| Gap::IndUniverseHeight(ind_name.clone(), level))?;
    // The level asked for is the level got: `⟦Sort ℓ⟧` and nothing else.
    if !du.rests_on_nothing() || du.universe != want {
        return Err(Gap::IndUniverseHeight(ind_name.clone(), level))
    }
    Ok(DeclUniv { ty_in_un: du.ty_in_u1, hyp, level })
}

/// **The type former.** `⟦T.{ℓ⃗}⟧` is the `np`-deep λ-nest whose bottom is the
/// carrier `ind(p⃗)`, and its typing is that nest's own λ rule.
///
/// The nest is built by [`Checker::lam_nest`], which is `infer_type`'s `Lam`
/// arm with the recursion replaced at the bottom — so the `Π` clause at each
/// level is decided by the same `is_prop` the rest of the checker uses, and the
/// term produced is the one a use site's `⟦Π p⃗. Sort ℓ⟧` will be compared
/// against.
///
/// **The bottom is where `H` is discharged.** `DeclUniverse` states
/// `∀p⃗. (H → ind(p⃗) ∈ Uₙ)` for a declaration whose summands need its
/// parameters to be small; the nest's own scopes hold exactly the atoms `H` is
/// the conjunction of, in the same order and the same left-nesting, so
/// discharging it is one fold and no search.
fn former(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    shape: &Shape,
    ind: &Rc<Inductive>,
    du: &DeclUniv,
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
    let u1 = du.ty_in_un.clone();
    let conditional = du.hyp.is_some();
    let n = du.level;
    let name = ind_name.clone();
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        let level = crate::expr::sort(level_numeral(n));
        let gap = |g: Gap| Ok(Typing { ty: level.clone(), tm: None, ev: Ev::Gap(g) });
        let Some((ps, mems)) = c.binders(np) else { return gap(Gap::NoEndpoint) };
        let ip = c.interp().expect("threaded");
        let carrier = ip.mk(ind2.ty, ps.clone());
        let at = derived::inst_all(&u1, &ps);
        let ev = match at.and_then(|t| {
            if !conditional {
                return Some(t)
            }
            // `H` is `(…(h₀ ∧ h₁) … ∧ h_{np-1})`, left-nested, because that is
            // how `summand_obligation` accumulates it.
            let mut conj = mems.first()?.clone();
            for m in &mems[1..] {
                conj = derived::and_intro(&conj, m);
            }
            Thm::mp(&t, &conj)
        }) {
            Some(t) if *t.concl() == Formula::mem(carrier.clone(), ip.sort(n)) => Ev::Proved(t),
            _ => return gap(Gap::IndUniverseHeight(name.clone(), n)),
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
/// * a plain field's atom is `yⱼ ∈ βⱼ(p⃗,y⃗<ⱼ)` at the `define_abbrev` symbol,
///   while the nest's scope holds `yⱼ ∈ ⟦βⱼ⟧`; the symbol's own defining axiom
///   at this nest's variables moves it, and [`CtorEvidence::abbrev`] is where
///   that axiom was kept;
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
    abbrev: &[Thm],
) -> Result<(), Gap> {
    let spec = at.ind.spec.ctors[i].clone();
    let depth = at.np + spec.order.len();
    // The codomain is read off the declaration, not synthesised: it is the one
    // expression whose interpretation the bottom's membership must be about.
    let codomain =
        peel(cty, depth).ok_or_else(|| Gap::IndSpec(at.name.clone(), "ctor arity"))?;
    let site = CtorSite { at: at.clone(), i, codomain, spec, abbrev: abbrev.to_vec() };
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
    /// `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`, per plain field — see [`CtorEvidence`].
    abbrev: Vec<Thm>,
}

/// The bottom of a constructor's nest: `ctor_i(y⃗,r⃗)` and its membership in the
/// applied spine of `⟦T⟧`.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let CtorSite { at, i, codomain, spec, abbrev } = site;
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
    // **A plain field's atom has to move onto the telescope's own symbol.**
    // The nest's scope holds `yⱼ ∈ ⟦βⱼ⟧`; `Ctor::mem`'s antecedent is about
    // `βⱼ(p⃗,y⃗<ⱼ)`, which is `⟦βⱼ⟧`'s abbreviation. Without this the modus
    // ponens below fails at every declaration with a non-recursive field — and
    // it failed at exactly those four the moment `cumul::summand_obligations`
    // let their carriers get built at all.
    for (j, m) in y_mems.iter_mut().enumerate() {
        let mut args: Vec<Term> = ps.to_vec();
        args.extend(ys[..j].iter().cloned());
        let Some(at) = abbrev.get(j).and_then(|ax| derived::inst_all(ax, &args)) else {
            return gap(Gap::IndSpec(ind_name.clone(), "field abbreviation instance"))
        };
        let Some(back) = derived::eq_symm(&mut ip.env, &at) else {
            return gap(Gap::ConvCompose("ctor-field-symm"))
        };
        match ip.retarget_set(m, &back) {
            Some(t) => *m = t,
            None => return gap(Gap::ConvCompose("ctor-plain-field")),
        }
    }
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
pub(crate) fn store(
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

    /// **A constructor with non-recursive fields**, which is what
    /// `cumul::summand_obligations` unblocked: three parameters, three plain
    /// fields, one per parameter.
    ///
    /// Three of each, not two, because the summand legs are a *telescope*: leg
    /// `j` is quantified over the first `j` fields and guarded by their
    /// domains, so a builder that emitted the guards in the wrong order, or at
    /// the wrong depth, is only distinguishable once there are three. The three
    /// field types are `bvar 2` at three different depths, so the check that
    /// bites is `summand_obligations`' own `establishes` against
    /// `arg_obligations` — a permuted leg is about the wrong `βⱼ` and is
    /// refused there rather than here.
    ///
    /// The typings must be **unconditional**: `⊢ ∀p⃗. (H → ind(p⃗) ∈ U₁)` is
    /// what `DeclUniverse` produces for this declaration, and the `H` is
    /// discharged inside the nest from the parameters' own scope assumptions.
    #[test]
    fn a_constructor_with_plain_fields_translates_and_its_typings_are_unconditional() {
        let t = Name::simple("T");
        let u1 = || sort(Level::Zero.succ());
        let ty = forall(u1(), forall(u1(), forall(u1(), u1())));
        let spine = crate::expr::app(
            crate::expr::app(
                crate::expr::app(konst(t.clone(), Vec::new().into()), crate::expr::bvar(5)),
                crate::expr::bvar(4),
            ),
            crate::expr::bvar(3),
        );
        let fields = forall(
            crate::expr::bvar(2),
            forall(crate::expr::bvar(2), forall(crate::expr::bvar(2), spine)),
        );
        let mk = Name::str(&t, "mk");
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![],
                num_params: 3,
                ty,
                ctors: vec![(mk.clone(), forall(u1(), forall(u1(), forall(u1(), fields))))],
            },
        )
        .expect("the declaration is accepted");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        for n in [&t, &mk] {
            let r = c.infer_type(&konst(n.clone(), Vec::new().into())).expect("infer");
            let m = r.ev.thm().unwrap_or_else(|| panic!("{n} has no typing: {:?}", r.ev)).clone();
            assert!(m.hyps().is_empty(), "{n}'s typing must be unconditional");
            let (subj, _) = m.concl().as_mem().expect("a membership");
            assert_eq!(subj, r.tm.clone().unwrap(), "{n}'s typing must be about {n}");
        }
        let key = (t.clone(), Vec::new());
        let (_, app, _) = ip.ind_parts().expect("apparatus");
        let ind = app.decls.get(&key).expect("translated");
        assert_eq!(ind.spec.ctors.len(), 1);
        assert_eq!(ind.spec.ctors[0].args.len(), 3, "three plain fields, in order");
    }

    /// **A declaration above `Type 0`.** `DeclUniverse::over_at` places a
    /// carrier at any level of the tower, so `Big : Type 1` lands in `U₂` —
    /// and the test that matters is that it lands in `U₂` and not in `U₁`,
    /// because a membership in the wrong universe is a true theorem about a set
    /// no Lean sort denotes.
    ///
    /// Recursive and with three constructors, so the height is not being
    /// checked on a degenerate declaration: the carrier really is a W-type and
    /// the tag sum really is a three-way one.
    #[test]
    fn a_declaration_above_type_zero_lands_in_its_own_universe() {
        let t = Name::simple("Big");
        let self_ty = konst(t.clone(), Vec::new().into());
        let ctors = vec![
            (Name::str(&t, "z"), self_ty.clone()),
            (Name::str(&t, "s"), forall(self_ty.clone(), self_ty.clone())),
            (Name::str(&t, "d"), forall(self_ty.clone(), forall(self_ty.clone(), self_ty))),
        ];
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::Zero.succ().succ()),
                ctors,
            },
        )
        .expect("accepted");
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let r = c.infer_type(&konst(t.clone(), Vec::new().into())).expect("infer");
        let m = r.ev.thm().unwrap_or_else(|| panic!("no typing: {:?}", r.ev)).clone();
        assert!(m.hyps().is_empty());
        let want_2 = c.interp().unwrap().sort(2);
        let want_1 = c.interp().unwrap().sort(1);
        assert_ne!(want_1, want_2, "the two levels must be different terms for this to say anything");
        assert_eq!(
            *m.concl(),
            Formula::mem(r.tm.clone().unwrap(), want_2),
            "⟦Big⟧ must be in ⟦Type 1⟧ = U₂"
        );
    }

    /// A declaration whose resultant level is **possibly zero** is declined by
    /// this route at every σ, and the carrier is never built for it. This is
    /// the per-declaration branch: it must not acquire a W-type even where its
    /// instantiation looks like a `Type`, which is what `σ = [1]` is here.
    ///
    /// The declaration has **two** constructors on purpose. One fieldless
    /// constructor at `Sort u` is `PUnit`, which is class (S) and now has a
    /// conditional-singleton carrier ([`crate::class_s`]); two make the
    /// eliminator small, which is class (P), whose truncation clause is not
    /// wired. Both are refused a W-type, and the point of the test is the
    /// refusal rather than the reason — so the reason is asserted too, because
    /// a class-(S) declaration reaching this line would be a *different* fact
    /// wearing the same assertion.
    #[test]
    fn a_prop_declaration_is_declined_rather_than_given_a_w_type() {
        let t = Name::simple("P");
        let u = Name::simple("u");
        let ty = konst(t.clone(), vec![Level::Param(u.clone())].into());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![u],
                num_params: 0,
                ty: sort(Level::Param(Name::simple("u"))),
                ctors: vec![
                    (Name::str(&t, "a"), ty.clone()),
                    (Name::str(&t, "b"), ty),
                ],
            },
        )
        .expect("accepted");
        assert!(
            !crate::class_s::large_eliminating(&env, &t),
            "two constructors make the eliminator small — this must be class (P)"
        );
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        // `σ = [1]`: `Sort 1` is `Type 0`, so a *per-instantiation* branch
        // would build a W-type right here.
        let at: std::rc::Rc<[Level]> = vec![Level::Zero.succ()].into();
        let r = c.infer_type(&konst(t.clone(), at.clone())).expect("infer");
        assert!(r.tm.is_none(), "a possibly-Prop declaration must not acquire a W-type");
        assert_eq!(
            r.ev.gap(),
            Some(&Gap::PropInductive(t.clone())),
            "and the gap must name the cause, not the site"
        );
        // The decline is recorded, so a second lookup reports the same reason
        // rather than a bare store miss.
        let r2 = c.infer_type(&konst(t.clone(), at)).expect("infer");
        assert_eq!(r2.ev.gap(), Some(&Gap::PropInductive(t)));
    }
}
