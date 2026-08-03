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

use derived::inductive::family::{CtorIndices, IndexedDeclSpec};
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

/// **§5.3's subsingleton carrier at an index.** `LeCarrier` gives `A_φ`, `R`
/// and the introduction rules at every `ni`, and `LeCarrier::degenerate`
/// collapses `acc(A_φ,R)` to `A_φ` when nothing is recursive — which is every
/// witness there is. What is unwired is the carrier *term*: at `ni ≥ 1` it is
/// the conditional singleton `[tup(x⃗) ∈ acc(A_φ(p⃗),R(p⃗))]`, and `LeProp` —
/// which mints that term at `ni = 0` — is stated at `ni = 0` only.
pub const CLASS_S_INDEXED: &str = "class (S) carrier at an index";

/// **The truncation over an indexed base** — the reason this route reported
/// while it declined, kept as the record of what the decline was.
///
/// It is no longer emitted: [`crate::class_p_ix`] is that clause, and the two
/// pieces of it that were not wiring — running the §5.2 indexed chain at a
/// `Prop`-resultant declaration, and the `np + ni`-deep constructor spine over
/// index expressions in the fields — are named in its header.
#[allow(dead_code)]
pub const CLASS_P_INDEXED: &str = "class (P) truncation over an indexed base";

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
pub(crate) fn stored_or_reason_after(
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
    // **"Absent" is not a reason.** A constructor of an indexed family that the
    // constructor path *tried* and declined has its reason recorded under its
    // own key; reporting `no-interp(·)` there would be this site's fallback
    // standing in for a decline that knows exactly what it could not bridge.
    // `crate::ev::Gap::IndexedCtor` says why the distinction is worth a variant.
    if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
        if let Some(g) = app.ctor_declined.get(&(name.clone(), inst.to_vec())) {
            return Err(g.clone())
        }
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
/// **The index half of the boundary walk** — what an [`IndexedDeclSpec`] needs
/// over and above the erased [`DeclSpec`], produced by the *same* walk.
///
/// Same walk, and that is the point rather than a convenience: `ιₖ`, `e⃗ᵢ` and
/// `d⃗ᵢⱼ` are abbreviations over the declaration's parameter and plain-field
/// variables, and [`ctor_spec`] is the only place where those variables, the
/// index expressions and their interpretations are all in hand at once. A
/// second walk would have to re-open every binder at a second set of variables
/// and then argue the two agree.
#[derive(Default)]
pub(crate) struct IndexData {
    /// `ι₀ … ι_{ni−1}`, `ιₖ` of arity `np + k`.
    pub(crate) indices: Vec<kernel::FnSym>,
    /// One entry per constructor, in declaration order.
    pub(crate) ctors: Vec<CtorIndices>,
    /// `⊢ ∀p⃗∀x⃗<ₖ. (ιₖ(p⃗,x⃗<ₖ) = ⟦Iₖ⟧)`, and the same per constructor.
    pub(crate) axioms: IndexAx,
}

/// One indexed declaration, translated: the `derived` object and the index
/// abbreviations' defining axioms, which a consumer needs together.
pub struct IndexedTranslation {
    pub ii: derived::inductive::family::IndexedInductive,
    pub ax: IndexAx,
    /// The **erased** skeleton the indexed carrier is carved out of — the same
    /// [`Inductive`] `IndexedInductive::build` consumed, kept because
    /// `Inductive::ctor_term` is the only producer of `ctorᵢ(y⃗,r⃗)` and
    /// [`crate::ctor_ix`] must name *this* build's term, not a second one.
    pub base: Rc<Inductive>,
    /// `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`, per constructor, per plain field —
    /// [`CtorEvidence::abbrev`], kept for the reason
    /// [`crate::interp::Translated::field_abbrev`] keeps it on the non-indexed
    /// path: a nest's scope holds a field typing at `⟦βⱼ⟧` and (M)'s antecedent
    /// wants it at the symbol.
    pub field_abbrev: Vec<Vec<Thm>>,
    /// `cᵢ` and `⊢ ∀f⃗. (cᵢ(f⃗) = ctorᵢ(y⃗,r⃗))`, per constructor — the name
    /// `⟦T.ctorᵢ⟧`'s nest bottom is built under, and its defining equation.
    ///
    /// [`crate::ctor_ix::ctor_abbrevs`] mints it; [`crate::ctor_ix`] builds the
    /// nest with it and [`crate::rec_ix_prop`] moves a minor's conclusion along
    /// it. This is [`crate::interp::Translated::ctor_abbrev`] at the indexed
    /// shape, and it is retained for the same reason: a symbol whose defining
    /// equation did not outlive the call that minted it is a term no later
    /// consumer can get inside.
    pub ctor_abbrev: Vec<(kernel::FnSym, Thm)>,
}



/// **What the boundary walk found about an indexed declaration whose carrier
/// is not wired** — kept across the decline that would otherwise discard it.
///
/// # Why a decline is the worst place to drop evidence
///
/// `MINI-HANDOFF.md` §2 records four instances of *a value computed at the
/// bottom of a call whose site outlives nothing*, and all four were on
/// **success** paths. This is the fifth and it is on a **decline**, which is
/// strictly worse: the decline is precisely the moment at which someone will
/// later want to know what the walk found, and it is the moment the walk's
/// products were being thrown away.
///
/// The decline in [`ensure`] used to read
/// `let (_, base, ix) = spec_of(…)?;` and then build an
/// [`IndexedDeclSpec`](derived::inductive::family::IndexedDeclSpec) out of two
/// of `ix`'s three fields. Dropped with the `_` and the third field:
///
/// * `ix.axioms` — `⊢ ∀p⃗∀x⃗<ₖ. (ιₖ(p⃗,x⃗<ₖ) = ⟦Iₖ⟧)` and, per constructor,
///   `⊢ ∀p⃗∀y⃗. (eᵢₖ(p⃗,y⃗) = ⟦eₖ⟧)`. **This is the field↔index-slot
///   correspondence and it exists nowhere else.** `IndexedDeclSpec` records an
///   arity and a symbol per slot and says nothing about *which field* each
///   slot's expression came from; the walk knows, because it interpreted the
///   result spine with the field binders open, and the axioms are the record.
/// * `Shape` — every constructor's [`CtorEvidence`], including `field_sort`,
///   whose own header names the class-(S) recursor as the consumer that would
///   otherwise have to recompute it at a second set of variables.
///
/// None of it is re-derivable. Every one of those symbols came from a
/// `define_abbrev` in this walk; a second walk mints a second family, related
/// to the first by nothing.
///
/// # What needs it
///
/// `SortElimProp.mk : ∀ b b1 b2. SortElimProp b b2 b1` puts its fields into the
/// result spine **permuted**. `le_rec`'s `minor_eq` hypothesis — whose
/// discharge is §5.3's delayed elimination — cannot be stated without knowing
/// that slot 1 is field 2 and slot 2 is field 1, and `derived/` does not have
/// that: it is a fact about the Lean declaration, read once, here.
///
/// Stored **ahead of its consumer**, exactly as [`IndexAx`] was and for the
/// same reason: the consumer is unwritable until this exists.
pub struct IndexedWalk {
    /// The representability answer, already checked `well_formed`.
    pub spec: derived::inductive::family::IndexedDeclSpec,
    /// The index abbreviations' defining axioms — the correspondence above.
    pub ax: IndexAx,
    /// `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`, per constructor, per plain field.
    pub field_abbrev: Vec<Vec<Thm>>,
    /// The field types' own typings, discharged — [`CtorEvidence::field_sort`],
    /// per constructor. The class-(S) recursor's `Pⱼ : βⱼ(p⃗,•⃗<ⱼ) ⊆ 1` follows
    /// from these at `ℓⱼ = 0` and from nothing else the walk keeps.
    pub field_sort: Vec<Vec<Thm>>,
    /// Which of the two carriers this declaration is owed — `true` for class
    /// (S), `false` for class (P). Read off the *eliminator*
    /// ([`large_eliminating`]), not off the resultant sort, and recorded so the
    /// answer is the walk's own rather than a second classification later.
    pub class_s: bool,
}

/// The defining axioms of every index abbreviation, parallel to [`IndexData`].
///
/// Kept for the reason [`CtorEvidence::abbrev`] is kept: `IndexedCtor::mem_lean`
/// wants `⊢ … eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗,e⃗<ₖ)` **at the symbols**, while what inference
/// hands back is the same statement at the interpretations `⟦eₖ⟧` and `⟦Iₖ⟧`.
/// The two are related by these axioms and by nothing else, so a walk that
/// discards them makes the witness underivable — which is exactly what the
/// first attempt at a `mem_lean` consumer ran into.
/// Read today by the `mem_lean` consumer test alone; C2's constructor nest is
/// the second reader. The `allow` is the record of that rather than an
/// oversight — discarding these axioms is what made the first attempt at a
/// consumer impossible to write, so they are stored **ahead** of the code that
/// will consume them, deliberately.
#[derive(Default)]
#[allow(dead_code)]
pub struct IndexAx {
    pub indices: Vec<Thm>,
    pub ctors: Vec<CtorIndexAx>,
}

/// One constructor's index axioms, parallel to [`CtorIndices`].
#[derive(Default)]
#[allow(dead_code)]
pub struct CtorIndexAx {
    pub result: Vec<Thm>,
    pub rec_args: Vec<Vec<Thm>>,
}

#[derive(Clone, Default)]
pub(crate) struct CtorEvidence {
    /// The interleaved summand obligation per plain field — see [`Shape`].
    /// Empty when the walk was asked for [`Legs::Skip`].
    legs: Vec<Thm>,
    /// `⊢ ∀p⃗ ∀y⃗<ⱼ. (βⱼ(p⃗,y⃗<ⱼ) = ⟦βⱼ⟧)`, per plain field.
    pub(crate) abbrev: Vec<Thm>,
    /// **The field type's own typing**, per plain field, **discharged**:
    ///
    /// ```text
    /// ⊢ ∀p⃗. (p⃗ ∈ ⟦σ⃗⟧ → ∀y⃗<ⱼ. (y⃗<ⱼ ∈ ⟦β⃗<ⱼ⟧ → ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧))
    /// ```
    ///
    /// with the `∀`/`→` interleaved in binder order — the shape
    /// [`crate::scope::Closed::discharge`] produces, exactly as [`Self::legs`]
    /// is discharged and through the same two loops. No raise: the typing is at
    /// whatever `ℓⱼ` inference gave, and the consumer is the one that knows
    /// which `ℓⱼ` it can accept.
    ///
    /// Kept unconditionally, including under [`Legs::Skip`], and that is the
    /// point. The class-(S) route asks for `Legs::Skip` because it has no
    /// summand induction to feed — but its *recursor* needs
    /// `Pⱼ : βⱼ(p⃗,•⃗<ⱼ) ⊆ 1`, which follows from this typing at `ℓⱼ = 0` and
    /// from nothing else the walk keeps. Dropping it made the one place where
    /// `⟦βⱼ⟧`, its typing and the right scopes are all in hand throw away what
    /// the recursor would then have had to recompute at a second set of
    /// variables. The standing rule, at the one site that was breaking it.
    ///
    /// # Why *discharged*, and not as inference returned it
    ///
    /// It used to be kept raw — `Γ_j ⊢ ⟦βⱼ⟧ ∈ ⟦Sort ℓⱼ⟧`, carrying the walk's
    /// own scope assumptions. **A hypothesis-carrying theorem cannot be
    /// `inst_all`'d**, so no consumer at a *different* nest can use it, and the
    /// only consumer there will ever be is at a different nest. On the three
    /// corpus class-(S) declarations that shortfall is invisible: `And`'s field
    /// types are its parameters and `ProjDataIndex`'s is the closed `True`, so
    /// the same fact is available unconditioned from the consumer's own
    /// parameter binders and the retained theorem is never missed. That is the
    /// closed-index-types trap again — the corpus's degenerate witnesses
    /// agreeing with a route that does not generalise — and the discharge is
    /// what makes the retained certificate mean what its name says for a field
    /// type that is neither a parameter nor closed.
    ///
    /// The guard stays at `⟦βᵢ⟧`, the domain the scope was actually opened at,
    /// rather than being carried onto `βᵢ(p⃗,y⃗<ᵢ)` the way [`Self::legs`] is:
    /// the consumer discharges it with a membership it holds at the
    /// *interpretation* — see [`crate::rec_prop`], where the same theorem then
    /// feeds the application rule — and moving it to the symbol here would only
    /// have to be moved back.
    pub(crate) field_sort: Vec<Thm>,
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
    /// The whole `derived` object, which the **indexed** placement needs:
    /// `IndexedUniverse::over_at` takes `wty_in_u1` and checks `universe`
    /// against the rung it was asked for, so handing on only the finished
    /// theorem would lose exactly the field that makes that check possible.
    du: derived::cumul::DeclUniverse,
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
    // eliminator, computed from the declaration by [`large_eliminating`] —
    // Carneiro §2.6.2, not the export's recursor. Class (S) is
    // §5.3's subsingleton carrier and is built; class (P) is the truncation
    // clause and is not wired, so it keeps [`Gap::PropInductive`] — which is
    // now a statement about one class rather than about two.
    // ── an indexed family: walk it, *then* decline ────────────────────────
    //
    // The decline used to be a declaration-level guard at the top of this
    // function, ahead of everything. Moving it here costs one boundary walk
    // per `(declaration, σ)` — cached with the decline, so once — and buys the
    // question the guard was suppressing: **is this shape representable at
    // all?** A family whose index expressions reach past what `IndexedDeclSpec`
    // can abstract over is a permanent decline with its own name; a family that
    // produces a `well_formed` spec is waiting on wiring and nothing else. The
    // guard reported both as the second, which is the more optimistic of the
    // two and therefore the wrong default.
    //
    // `Legs::Skip`, because this asks about the *shape*. Deriving the summand
    // legs here would fold the `U₁` ceiling into the answer and report an
    // unrepresentable family and a too-tall one under one reason.
    if ni != 0 {
        // An indexed declaration that is **not** class (T) would need §5.3's
        // subsingleton carrier at an index, which `class_s::build` does not
        // take. The walk still runs, so the representability answer is not lost
        // to the decline.
        if !provably_nonzero(l) {
            let (shape, base, ix) = spec_of(c, ind_name, np, ni, &ind_ty, &ctor_tys, Legs::Skip)?;
            let spec = IndexedDeclSpec::new(base, ix.indices, ix.ctors);
            if !spec.well_formed() {
                return Err(Gap::IndSpec(ind_name.clone(), "indexed spec not well formed"))
            }
            // **Which carrier**, because the two are different constructions
            // owed at different places: class (S) at `ni ≥ 1` is
            // `LeCarrier`'s `[tup(x⃗) ∈ acc(A_φ,R)]`, and class (P) is
            // `TruncCarrier::over_family` over the §5.2 base. Both exist in
            // `derived/`; neither is wired, and they are not the same work.
            let class_s = large_eliminating(c, ind_name);
            // **The walk's products outlive the decline** — see [`IndexedWalk`].
            // Everything below was minted by `define_abbrev` inside `spec_of`
            // and is unrecoverable once this frame goes, and the
            // field↔index-slot correspondence in `ix.axioms` exists in no other
            // form anywhere: `IndexedDeclSpec` records a symbol per slot and
            // not which field's expression it abbreviates.
            let walk = Rc::new(IndexedWalk {
                spec,
                ax: ix.axioms,
                field_abbrev: shape.ctors.iter().map(|(.., ev)| ev.abbrev.clone()).collect(),
                field_sort: shape.ctors.iter().map(|(.., ev)| ev.field_sort.clone()).collect(),
                class_s,
            });
            if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
                app.indexed_walks.insert((ind_name.clone(), inst.to_vec()), walk.clone());
            }
            if class_s {
                return crate::class_s_ix::build(
                    c, ind_name, inst, np, ni, &ctor_tys, &ind_ty, shape.result_level, walk,
                )
            }
            return crate::class_p_ix::build(
                c, ind_name, inst, np, ni, &ctor_tys, shape.result_level, walk,
            )
        }
        return build_indexed(c, ind_name, inst, np, ni, &ind_ty, &ctor_tys)
    }

    if !provably_nonzero(l) {
        return if large_eliminating(c, ind_name) {
            crate::class_s::build(c, ind_name, inst, np, &ind_ty, &ctor_tys)
        } else {
            // **Class (P), the truncation clause** (thesis.txt:1813-1815).
            build_trunc(c, ind_name, inst, np, &ind_ty, &ctor_tys)
        }
    }

    // ── the `FnSym` boundary (WIRING-DESIGN.md §3.2) ──────────────────────
    let (shape, spec, _) = spec_of(c, ind_name, np, ni, &ind_ty, &ctor_tys, Legs::Derive)?;
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
    let mut ctor_abbrev = Vec::with_capacity(shape.ctors.len());
    for (i, (cname, cty, _, ev)) in shape.ctors.iter().enumerate() {
        ctor_abbrev.push(constructor(c, &at, cname, cty, i, &ev.abbrev)?);
    }
    let field_abbrev: Vec<Vec<Thm>> =
        shape.ctors.iter().map(|(.., ev)| ev.abbrev.clone()).collect();
    if let Some(ip) = c.interp() {
        if let Some(app) = ip.ind_apparatus() {
            app.decls
                .insert(key, Rc::new(crate::interp::Translated { ind, field_abbrev, ctor_abbrev }));
        }
    }
    Ok(())
}

/// **The export recursor as an oracle, not as the implementation.**
///
/// One row per inductive that the export gave a recursor: the class
/// [`large_eliminating`] computes, and the class the recursor's
/// level-parameter count implies (`|rec.lparams| == |T.lparams| + 1`). They
/// must agree, and `mini/tests/tutorial.rs` checks that over the corpus.
///
/// This is the only place mini looks at an exported recursor, and it looks at
/// it to be *checked against*. A declaration with no exported recursor
/// contributes no row: whether one was exported is not a property of the type,
/// and `bad/large-elim-param.ndjson` omits them precisely because they are
/// irrelevant to what that fixture tests.
pub fn elim_audit(
    env: &crate::env::Environment,
    ip: &mut crate::interp::Interp,
    decls: &[crate::env::Declaration],
) -> Vec<String> {
    let mut out = Vec::new();
    let mut c = Checker::threaded(env, ip);
    for d in decls {
        let crate::env::Declaration::Inductive { name, lparams, .. } = d else { continue };
        let Some(ConstantInfo::Recursor { lparams: rl, .. }) =
            c.environment().get(&Name::str(name, "rec"))
        else {
            continue
        };
        let oracle = rl.len() == lparams.len() + 1;
        let computed = large_eliminating(&mut c, name);
        out.push(format!("elim\t{name}\tcomputed={computed}\toracle={oracle}"));
    }
    out
}

/// **Carneiro §2.6.2's large-elimination judgement, computed from the
/// declaration.**
///
/// `Γ; t : F ⊢ K LE` has two reasons and mini computes both:
///
/// 1. the resultant sort is nonzero for every value of the parameters
///    ([`provably_nonzero`]); or
/// 2. the declaration has **at most one constructor**, and every non-recursive
///    argument of it is either a proposition or *directly appears in the output
///    type* — the thesis's subsingleton (SS) elimination, whose `LE ctor` rules
///    are the four this walk implements: the codomain is a base case, a
///    propositional field passes, a recursive field passes unconditionally, and
///    any other field passes only when its variable is one of the result
///    indices `e⃗`.
///
/// **"One of the result indices" means equality with an index, not occurrence
/// inside one**, and the strict reading is deliberate. `y ∈ e` in the thesis's
/// final rule is written of the *sequence* `e :: α`, so `y` must **be** an
/// element of it; a field that appears only as a subterm — `IdxUnder`, whose
/// field sits inside `Wrap.wrap a` rather than being the index — does not
/// qualify. Neither reading was obviously right in advance, and **Lean
/// adjudicated it**: `IdxUnder` classifies small in `lean4export`'s recursor
/// and small here, and `mini/tests/fixtures`'s `elim_class_trichotomy` pins the
/// agreement. Do not relax this to an occurrence check.
///
/// # Why this is computed and not read
///
/// It used to be one store lookup on `T.rec`, comparing the recursor's
/// level-parameter count against the declaration's. **That was reading the
/// export's recursor**, and mini does not do that anywhere else: it *generates*
/// its eliminators from the declaration and never consults the exported one
/// (`MINI-DESIGN.md` §2). The lookup also made the answer depend on whether a
/// recursor happened to be exported at all, which is not a property of the
/// type — `bad/large-elim-param.ndjson` omits them precisely because they are
/// irrelevant to what it tests, and a declaration with no exported recursor is
/// an ordinary declaration, not a malformed one.
///
/// The exported recursor is still worth something, as an **oracle**: where one
/// exists its level-parameter count must agree with this function, and
/// `mini/tests/tutorial.rs` checks that over the whole corpus. That is the
/// right place for it — a cross-check, not the implementation.
///
/// # The boundary this has to reproduce
///
/// `PUnit.{u} : Sort u` and `PProd.{u,v} : Sort (max (max 1 u) v)` have
/// *identical* recursor signatures and fall on opposite sides of the
/// trichotomy. Both are large-eliminating; what separates them is
/// [`provably_nonzero`] on the declaration's own resultant sort, which sends
/// `PProd` to class (T) before this question is asked and leaves `PUnit` to
/// class (S). This function must return `true` for both, and does — by reason
/// 1 for `PProd` and reason 2 for `PUnit`.
///
/// **No interpretation is built here.** Every binder is opened
/// *uninterpreted*, so this is a walk over Lean syntax and inference only; it
/// mints nothing and can be asked before the trichotomy has chosen a clause.
pub(crate) fn large_eliminating(c: &mut Checker<'_, '_>, ind_name: &Name) -> bool {
    // **The declaration's own types, never σ's.** Reading the substituted ones
    // would decide the class per instantiation, which is the design error
    // `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3 closes: `T.{u} : Sort u` at
    // `u := 1` has resultant sort `Sort 1`, so reason 1 would fire and hand a
    // W-type to a declaration that is a `Prop` at `u := 0`.
    // `zoneb::tests::a_possibly_prop_declaration_never_acquires_a_w_type` is
    // that case, and it caught exactly this while the function was being
    // written.
    let env = c.environment();
    let Some(ConstantInfo::Inductive { ty, num_params, num_indices, ctors, .. }) = env.get(ind_name)
    else {
        return false
    };
    let (np, ni) = (*num_params as usize, *num_indices as usize);
    let (ty, ctors) = (ty.clone(), ctors.clone());
    // Reason 1, on the declaration's own level expression.
    if let Some(own) = peel(&ty, np + ni) {
        if let Expr::Sort(l) = &*own {
            if provably_nonzero(l) {
                return true
            }
        }
    }
    // Reason 2: at most one constructor.
    match ctors.len() {
        0 => return true,
        1 => {}
        _ => return false,
    }
    let Some(cty) = c.environment().get(&ctors[0]).map(|ci| ci.ty().clone()) else { return false };
    c.in_scope(|c| Ok::<bool, Gap>(ctor_le(c, ind_name, np, ni, &ty, &cty))).unwrap_or(false)
}

/// The `LE ctor` half: the single constructor's fields, in order.
fn ctor_le(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    np: usize,
    ni: usize,
    ind_ty: &E,
    cty: &E,
) -> bool {
    // **The parameters have to be open**, or a field whose type is a parameter
    // — `And.intro`'s `a` and `b` — has nothing to infer against and is filed
    // as non-propositional. `And` classified as class (P) for exactly one
    // compile because of it.
    let mut pt = ind_ty.clone();
    for _ in 0..np {
        let Expr::Forall { ty, body } = &*pt.clone() else { return false };
        c.open_uninterpreted(ty.clone());
        pt = body.clone();
    }
    let Some(body) = peel(cty, np) else { return false };
    // De Bruijn depths of the fields that still have to be found among `e⃗`.
    let mut owed: Vec<usize> = Vec::new();
    let mut cur = body.clone();
    let mut d = 0usize;
    while let Expr::Forall { ty, body } = &*cur.clone() {
        if crate::expr::has_const(ind_name, ty) {
            // A recursive argument — `(∀z :: γ. t e) → β LE ctor`, with no
            // condition on it at all.
        } else {
            // Propositional fields pass; anything else owes an appearance in
            // the output indices. The sort is inference's, not a guess.
            let prop = (|| {
                let t1 = c.infer_type(ty).ok()?;
                let (s1, _, _) = c.whnf_typing(t1).ok()?;
                let l = crate::kernel::as_sort(&s1).ok()?;
                Some(ground::eval(&l, &Default::default())? == 0)
            })()
            .unwrap_or(false);
            if !prop {
                owed.push(d);
            }
        }
        c.open_uninterpreted(ty.clone());
        d += 1;
        cur = body.clone();
    }
    // The codomain, and the `y ∈ e` side condition.
    let Some(ixs) = ind_spine(ind_name, &cur, np, ni, d) else { return false };
    owed.iter().all(|j| {
        let want = d - 1 - j;
        ixs.iter().any(|e| matches!(&**e, Expr::BVar(k) if *k as usize == want))
    })
}

/// **A class-(P) declaration's type former** — `⟦T⟧ := ‖ind(p⃗)‖`
/// (thesis.txt:1813-1815, and 2110-2114 for `⟦‖α‖⟧`).
///
/// The declaration's resultant sort is not provably nonzero and its eliminator
/// is *small*, so §5.3's subsingleton carrier does not apply and neither does a
/// W-type: the interpretation is the **truncation** of the ordinary §5.2
/// carrier over the erased declaration.
///
/// # Why this needs no size argument, and what that buys
///
/// `TruncCarrier::in_u0` is `⊢ ∀p⃗. ‖a‖ ∈ U₀` **unconditionally** — a
/// truncation is a subset of `1` whatever it truncates, so there is no
/// `DeclUniverse`, no tag sum, and no summand legs. Hence [`Legs::Skip`], and
/// hence no exposure at all to the field-type raise that class (T) spends its
/// rung on. A class-(P) declaration with a `Type 37` field is as easy as one
/// with none.
///
/// # The formation theorem is the `is_prop` certificate
///
/// `⊢ ⟦T⟧ ∈ U₀` is not only this clause's output; it is exactly what steers the
/// `Π` split and what `Interp::point_of_proof` consumes downstream. The branch
/// is evidence-producing in the sense the design asks for, and the evidence it
/// produces is already the kind the rest of the checker reads.
///
/// # The walk runs first
///
/// [`spec_of`] before the carrier, and before any decline — the same
/// discipline the indexed branch adopted, for the reason `Acc` demonstrated:
/// the eliminator's level parameters pick the **class**, and the boundary walk
/// picks whether the declaration is **representable**, and the two are
/// independent. A class-(P) declaration whose shape `DeclSpec` cannot express
/// is declined by the walk under its own name, not by this clause.
fn build_trunc(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ind_ty: &E,
    ctor_tys: &[(Name, E)],
) -> Result<(), Gap> {
    let (shape, base, _) = spec_of(c, ind_name, np, 0, ind_ty, ctor_tys, Legs::Skip)?;
    if !base.well_formed() {
        return Err(Gap::IndSpec(ind_name.clone(), "spec not well formed"))
    }
    // **`TruncCarrier::in_u0` places `‖a‖` in `U₀`, and this clause asks for
    // nothing else — so a σ at which the declaration's sort is a nonzero
    // numeral is declined.**
    //
    // The case is real, not hypothetical. Class (P) does *not* force `ℓ = 0`
    // at every σ: Lean's `large_elim_test` gates on `is_nonzero(ℓ)`, a bare
    // `Sort u` is neither provably zero nor provably nonzero, so it falls
    // through to the subsingleton analysis and can come out small — and its
    // resultant sort at `u := 1` is then the numeral `1`.
    // `MyBool.{u} : Sort u | tt | ff` is such a declaration and is already in
    // the repo, as `bad/large-elim-param.ndjson`.
    //
    // **The typing is sound and is not what is in question**
    // (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.5, thesis.txt:1813-1815). At
    // `MyBool.{1}` the model gives `⟦tt⟧ = ⟦ff⟧ = •` and so validates
    // `tt = ff`, which Lean does not prove; refuting it needs a `Sort 1`-valued
    // motive, which a class-(P) recursor does not offer, so no Lean-accepted
    // judgement can observe the collapse. Nor does the guard offend §3.3: that
    // forbids the *instantiated* sort choosing a **construction**, and the
    // construction here is still chosen per declaration by
    // [`large_eliminating`] — the numeral gates only a refusal, and a refusal
    // cannot produce a wrong carrier.
    //
    // It is declined because **no accepted file can exercise it and no fixture
    // can test it**: every class-(P) declaration in `good/` has resultant sort
    // literally `Sort 0`, and the one witness that exists is in `bad/`, where
    // acceptance rejects the file before the interpretation runs. Wiring it now
    // would be untested code, which is how the `scope_vars` off-by-one lived.
    //
    // The replacement is scheduled rather than open: `TruncCarrier::in_un`,
    // `⊢ ∀p⃗∀x⃗. ‖a‖ ∈ Uₙ` for `n ≥ 1`, from `in_u0` + `Rung::u0_mem` +
    // `Rung::transitive` — all present, a signature change rather than a
    // derivation, exactly as `IndexedUniverse::over_at` was. Then this `if`
    // goes and `former_at`'s level argument becomes `shape.result_level`. A
    // `good/` `Squash.{u} (α : Sort u) : Sort u | mk : α → Squash α` is what
    // would open it.
    if shape.result_level != 0 {
        return Err(Gap::IndSpec(ind_name.clone(), "class (P) above Prop"))
    }
    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let tower = ip.prelude.tower.clone();
    let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
    let ind = Inductive::build(kenv, &mut app.mach, &base)
        .ok_or_else(|| Gap::IndSpec(ind_name.clone(), "carrier"))?;
    let tr = app.trunc(kenv).ok_or(Gap::IndApparatus)?;
    let tc = derived::inductive::family::TruncCarrier::over_declaration(
        kenv,
        &app.mach,
        &tower,
        &tr,
        &ind,
    )
    .ok_or_else(|| Gap::IndSpec(ind_name.clone(), "truncation carrier"))?;

    // **A name of mini's own for `‖ind(p⃗)‖`.** The carrier is
    // `trunc(ind(p⃗))`, a term `derived` assembled — so it was never recorded
    // through `Interp::mk` and could not be taken apart again, and its head is
    // `trunc` at arity 1 rather than the declaration at arity `np`. One
    // `define_abbrev` over the parameters fixes both: the symbol has the arity
    // the former's nest applies it at, and its defining equation carries the
    // typing across. Same move, and the same reason, as the constructor term's.
    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    let (sym, ax) = derived::define_abbrev(kenv, &ind.params, &tc.carrier)
        .ok_or_else(|| Gap::IndSpec(ind_name.clone(), "truncation abbreviation"))?;
    let at = derived::inst_all(&tc.in_u0, &ps).ok_or(Gap::ConvCompose("trunc-in-u0"))?;
    let ax_at = derived::inst_all(&ax, &ps).ok_or(Gap::ConvCompose("trunc-abbrev"))?;
    let onto = ip.retarget_subject(&at, &ax_at).ok_or(Gap::ConvCompose("trunc-subject"))?;
    let univ = derived::gen_all(&ind.params, &onto);
    let ind = Rc::new(ind);
    let tc = Rc::new(tc);
    // **The translation is stored before the former, not dropped after the
    // constructors.** `ind`, `tc` and the two abbreviation families are minted
    // here and nowhere else — a second `Inductive::build` is a second family of
    // symbols and a second `TruncCarrier` a second Separation — so a consumer
    // that cannot read them back cannot re-derive them either. The class-(P)
    // eliminator is that consumer (`crate::rec_trunc`), and for as long as this
    // call ended at `former_at` it read as `derived/` owing a construction that
    // had in fact been built and tested for a month.
    let tt = Rc::new(crate::interp::TruncTranslation {
        ind: ind.clone(),
        tc: tc.clone(),
        abbrev: ax.clone(),
        field_abbrev: shape.ctors.iter().map(|(.., ev)| ev.abbrev.clone()).collect(),
    });
    if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
        app.truncs.insert((ind_name.clone(), inst.to_vec()), tt);
    }
    former_at(c, ind_name, inst, np, 0, sym, &univ, false, 0)?;
    // **After the former, and unable to unseat it** — `crate::ctor_ix`'s rule,
    // for the same reason: the type former is a complete obligation on its own
    // and a constructor that does not build is recorded against its own name.
    trunc_constructors(c, ind_name, inst, np, ctor_tys, &shape, &tc, &ind, &ax);
    Ok(())
}

/// **A class-(P) declaration's constructors** — `⟦T.ctorᵢ.{σ}⟧`, whose whole
/// content is that the truncation is inhabited.
///
/// # Why this is so much smaller than [`constructor`]
///
/// The codomain is `T p⃗ …`, which is a `Prop`, so `imax _ 0 = 0` outwards and
/// the *whole constant* is a proof: `⟦T.ctorᵢ⟧ = •`, and
/// [`Checker::lam_nest`](crate::kernel::Checker::lam_nest) collapses the nest
/// to it. There is no carrier term to mint, no `Inductive::ctor_term`, and no
/// `Ctor::mem`-to-`beta_spine` bridge, because the bottom is a constant rather
/// than a function of the fields. What is left is
/// [`TruncCtor::mem`](derived::inductive::family::TruncCtor):
///
/// ```text
/// ⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ → • ∈ ‖ind(p⃗, e⃗ᵢ)‖)
/// ```
///
/// with `Hᵢ` the *underlying* carrier's antecedent verbatim, and at a nullary
/// constructor no antecedent at all — which [`TruncCtor`]'s header carries
/// deliberately rather than manufacturing a vacuous conjunction, and which is
/// the only shape any export reaches.
///
/// # The rules existed and were being thrown away
///
/// `TruncCarrier::over_declaration` *computes* `tc.ctors` and [`build_trunc`]
/// used to end at `former_at`, discarding them. That is the same failure as
/// `ctor_ix` dropping its constructor abbreviation and as `field_sort` before
/// it — evidence produced and then made unreachable — and it is the third
/// instance this month. `069_boolPropRec` was blocked on `no-interp(BoolProp.a)`
/// for as long as it stood.
///
/// # Only a nullary constructor on a parameterless `Prop` is reachable
///
/// A proof-valued **application** interprets to `•` without consulting its head
/// constant, so `⟦Exists.intro …⟧` is `•` and `Exists.intro` is never asked
/// for; only a bare `Expr::Const` routes to [`ensure`]. A class-(P) constructor
/// is therefore unreachable from an export exactly when it occurs *applied*,
/// which for a declaration with parameters or fields is always. `BoolProp.a`
/// and `BoolProp.b` are the only ones the tutorials reach.
///
/// So the `np`/`kᵢ`/`mᵢ` general path is **tested outside the tutorial corpus**,
/// which is the only place it can be: a bare `Const` is reachable from a test
/// even where no export produces one.
/// `zoneb`'s `a_class_p_constructor_with_a_parameter_and_a_field` covers
/// `np = 1, kᵢ = 1`, and `mini/tests/fixtures/prop_recursive_interleaved.ndjson`
/// covers the recursive case at an **interleaved** mask — `PTree.node` is
/// `Plain Rec Plain Rec Plain` with three distinct plain types. That fixture
/// matters more than it looks: `TruncCtor`'s atoms are plains-then-recs while
/// the nest's binders are in Lean order, and no export has `mᵢ > 0`, so it is
/// the only thing that makes a wrong split fail rather than pass.
///
/// `mᵢ > 0` was very nearly a named decline on the grounds that nothing reaches
/// it. Quinn's fixture reaches it, which is the argument for designed fixtures
/// in one line. The step it needed is small and is the interesting one:
/// [`TruncCtor::trunc_mem`]'s recursive atoms are `• ∈ ‖ind(p⃗)‖` — the
/// hypotheses are *proofs*, so the statement names the point and not the field
/// — and the binder's own inhabitant is moved there by
/// [`Interp::point_of_proof`](crate::interp::Interp::point_of_proof) against
/// `⊢ ⟦T p⃗⟧ ∈ U₀`, which is the codomain's own typing and already in hand.
#[allow(clippy::too_many_arguments)]
fn trunc_constructors(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ctor_tys: &[(Name, E)],
    shape: &Shape,
    tc: &Rc<derived::inductive::family::TruncCarrier>,
    ind: &Rc<Inductive>,
    ax: &Thm,
) {
    for (i, (cname, cty)) in ctor_tys.iter().enumerate() {
        let abbrev =
            shape.ctors.get(i).map(|(.., ev)| ev.abbrev.clone()).unwrap_or_default();
        if let Err(g) = trunc_one(c, ind_name, inst, np, i, cname, cty, tc, ind, ax, &abbrev) {
            if let Some(app) = c.interp().and_then(|ip| ip.ind_apparatus()) {
                app.ctor_declined.insert((cname.clone(), inst.to_vec()), g);
            }
        }
    }
}

/// One class-(P) constructor's λ-nest.
#[allow(clippy::too_many_arguments)]
fn trunc_one(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    i: usize,
    cname: &Name,
    cty: &E,
    tc: &Rc<derived::inductive::family::TruncCarrier>,
    ind: &Rc<Inductive>,
    ax: &Thm,
    abbrev: &[Thm],
) -> Result<(), Gap> {
    let bad = |w: &'static str| Gap::IndSpec(ind_name.clone(), w);
    let tcc = tc.ctors.get(i).ok_or_else(|| bad("class (P): no truncation constructor"))?;
    let (k, m) = (tcc.yvs.len(), tcc.tvs.len());
    let order = ind.spec.ctors.get(i).ok_or_else(|| bad("class (P): ctor shape"))?.order.clone();
    if order.len() != k + m {
        return Err(bad("class (P): the constructor and the truncation disagree"))
    }
    let depth = np + k + m;
    let codomain = peel(cty, depth).ok_or_else(|| bad("class (P): ctor arity"))?;
    let site = TruncCtorSite {
        ind: ind_name.clone(),
        ctor: cname.clone(),
        i,
        np,
        k,
        m,
        order,
        codomain,
        inst: inst.to_vec(),
        tc: tc.clone(),
        ax: ax.clone(),
        abbrev: abbrev.to_vec(),
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(trunc_ctor_bottom(c, &site)) };
    let t = c.lam_nest(cty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    store(c, cname, inst, t)
}

/// What [`trunc_ctor_bottom`] needs, read before a binder opens.
struct TruncCtorSite {
    ind: Name,
    ctor: Name,
    i: usize,
    np: usize,
    k: usize,
    m: usize,
    /// The declared field mask — the binders are in Lean order and
    /// `TruncCtor`'s atoms are plains-then-recs, so this is what relates them.
    order: Vec<Slot>,
    inst: Vec<u32>,
    codomain: E,
    tc: Rc<derived::inductive::family::TruncCarrier>,
    ax: Thm,
    abbrev: Vec<Thm>,
}

/// `⊢ • ∈ ⟦T p⃗⟧` under the constructor's own field binders.
fn trunc_ctor_bottom(c: &mut Checker<'_, '_>, site: &TruncCtorSite) -> Typing {
    let ty = site.codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
    let bad = |w: &'static str| Gap::TruncCtor(site.ctor.clone(), w);
    let depth = site.np + site.k + site.m;

    // `⟦T p⃗⟧`, by inference on the declared codomain — the set the membership
    // must be *about*, not one this clause synthesises. Its typing is
    // `⊢ ⟦T p⃗⟧ ∈ U₀`, which is what a recursive field's proof irrelevance
    // needs and is why it is taken here rather than rebuilt.
    let Ok(cod) = c.infer_type(&site.codomain) else { return gap(Gap::Classifier) };
    let Some(goal) = cod.tm.clone() else { return gap(cod.ev.reason(Gap::NoEndpoint)) };
    let Some(cod_mem) = cod.ev.thm().cloned() else {
        return gap(cod.ev.reason(Gap::NoEndpoint))
    };
    let Some((tms, mems)) = c.binders(depth) else { return gap(Gap::NoEndpoint) };
    let Some(former) = c.stored_term(&site.ind, &site.inst) else {
        return gap(Gap::NoEndpoint)
    };
    let Some(ip) = c.interp() else { return gap(Gap::SymbolicLevel) };
    let point = ip.point();

    let (ps, fields) = tms.split_at(site.np);
    let (param_mems, field_mems) = mems.split_at(site.np);
    let ps = ps.to_vec();

    // ── the two equations everything travels on ─────────────────────────────
    //
    // `⟦T p⃗⟧ = sym(p⃗)` is the type former's own β at these parameters, and
    // `sym(p⃗) = ‖ind(p⃗)‖` is the abbreviation `build_trunc` minted. Their
    // composite is used three times below and is computed once.
    let Some((_, beta)) = ip.beta_spine(&former, &ps, param_mems) else {
        return gap(bad("the type former's spine"))
    };
    let Some(ax_at) = derived::inst_all(&site.ax, &ps) else {
        return gap(bad("the truncation abbreviation"))
    };
    let Some(to_trunc) = derived::eq_trans(&mut ip.env, &beta, &ax_at) else {
        return gap(bad("the truncation abbreviation"))
    };

    // ── the antecedent, plains then recs — `TruncCtor`'s own order ──────────
    let (mut plain_atoms, mut rec_atoms) = (Vec::new(), Vec::new());
    let (mut ys, mut plains) = (Vec::new(), 0usize);
    for (j, slot) in site.order.iter().enumerate() {
        let mem = &field_mems[j];
        match slot {
            Slot::Plain => {
                // The scope holds `yⱼ ∈ ⟦βⱼ⟧`; `Hᵢ` wants it at the symbol.
                let mut a: Vec<Term> = ps.clone();
                a.extend(ys.iter().cloned());
                let Some(axj) = site.abbrev.get(plains) else {
                    return gap(bad("a plain field's typing"))
                };
                let Some(unfold) = derived::inst_all(axj, &a) else {
                    return gap(bad("a plain field's typing"))
                };
                let Some(back) = derived::eq_symm(&mut ip.env, &unfold) else {
                    return gap(bad("a plain field's typing"))
                };
                let Some(out) = ip.retarget_set(mem, &back) else {
                    return gap(bad("a plain field's typing"))
                };
                plain_atoms.push(out);
                ys.push(fields[j].clone());
                plains += 1;
            }
            Slot::Rec => {
                // **`trunc_mem` states a recursive hypothesis at `•`**, because
                // it is a *proof*: the field's type is the declaration, which is
                // a `Prop`. So the binder's own inhabitant is moved onto the
                // point first — `⊢ ⟦T p⃗⟧ ∈ U₀` is `cod`'s typing, already in
                // hand — and only then does the set travel.
                let Some((_, set)) = mem.concl().as_mem() else {
                    return gap(bad("a recursive argument's typing"))
                };
                if set != goal {
                    return gap(bad("a recursive argument is not at the declaration"))
                }
                let Some(pt) = ip.point_of_proof(&cod_mem, mem) else {
                    return gap(bad("a recursive argument's proof irrelevance"))
                };
                let Some(back) = derived::eq_symm(&mut ip.env, &pt) else {
                    return gap(bad("a recursive argument's proof irrelevance"))
                };
                let Some(at_pt) = ip.retarget_subject(mem, &back) else {
                    return gap(bad("a recursive argument's proof irrelevance"))
                };
                let Some(out) = ip.retarget_set(&at_pt, &to_trunc) else {
                    return gap(bad("a recursive argument's typing"))
                };
                rec_atoms.push(out);
            }
        }
    }
    if plains != site.k || rec_atoms.len() != site.m {
        return gap(bad("the constructor and the truncation disagree"))
    }
    let mut atoms = plain_atoms;
    atoms.extend(rec_atoms);

    // ── the rule, instantiated and discharged ───────────────────────────────
    //
    // `mem` quantifies `∀p⃗∀y⃗∀r⃗`; `trunc_mem` quantifies `∀p⃗∀y⃗` only — the
    // recursive arguments are gone from its statement, which is the point of
    // it, and its atoms name `•` where `mem`'s name `rⱼ`.
    let tcc = &site.tc.ctors[site.i];
    let mut args: Vec<Term> = ps.clone();
    args.extend(ys.iter().cloned());
    if site.m == 0 {
        args.extend(fields.iter().skip(site.k).cloned());
    }
    let rule = if site.m == 0 { &tcc.mem } else { &tcc.trunc_mem };
    let Some(rule_at) = derived::inst_all(rule, &args) else {
        return gap(bad("TruncCtor::mem does not instantiate here"))
    };
    let mem = match atoms.iter().rev().cloned().reduce(|acc, t| derived::and_intro(&t, &acc)) {
        None => rule_at,
        Some(h) => match Thm::mp(&rule_at, &h) {
            Some(t) => t,
            None => return gap(bad("TruncCtor::mem does not discharge here")),
        },
    };

    // ── `‖ind(p⃗)‖` back onto `⟦T p⃗⟧` ────────────────────────────────────────
    let Some(back) = derived::eq_symm(&mut ip.env, &to_trunc) else {
        return gap(bad("the truncation abbreviation"))
    };
    let Some(out) = ip.retarget_set(&mem, &back) else {
        return gap(bad("the type former's spine"))
    };
    if *out.concl() != Formula::mem(point.clone(), goal) {
        return gap(bad("the constructor did not land in its own codomain"))
    }
    Typing { ty, tm: Some(point), ev: Ev::Proved(out) }
}

/// **An indexed family's type former** (`INDEXED-DESIGN.md` §3–5).
///
/// `⟦T.{ℓ⃗}⟧` for a class-(T) declaration with `ni > 0`. The chain is
/// `derived`'s and is driven once, forward:
///
/// ```text
/// spec_of            -> IndexedDeclSpec   (the erased spec, plus ι, e⃗ᵢ, d⃗ᵢⱼ)
/// Inductive::build   -> the erased skeleton W
/// decl_universe      -> DeclUniverse      ⊢ [H →] W ∈ Uₙ
/// IndexedInductive   -> IndexedCarrier    ind(p⃗,x⃗) ⊆ W, carved by `good`
/// IndexedUniverse    -> ⊢ ∀p⃗∀x⃗. ([H →] ind(p⃗,x⃗) ∈ Uₙ)      (C₂: a subset of a
///                                                          small set is small)
/// former_at          -> the (np+ni)-deep λ-nest and its typing
/// ```
///
/// **The constructors are not built here**, and their absence is a decline
/// rather than a silence: `ensure` reports `⟦T.ctor⟧` missing by name. The
/// type former is a complete obligation on its own — `042_rbTreeDef` is
/// `def rbTreeDef := RBTree`, which asks for the former and nothing else — and
/// the constructor path needs `IndexedCtor::mem_lean`, which is its own piece.
///
/// # The rung is checked twice, by two different objects
///
/// `decl_universe` already refuses a `DeclUniverse` whose `universe` is not
/// `⟦Sort ℓ⟧`, and `IndexedUniverse::over_at` refuses a `du` whose `universe`
/// is not the rung it was handed. That is not redundant: the first says the
/// placement is where *Lean* says the declaration lives, the second says the
/// two `derived` objects were built at the *same* rung as each other. A
/// mismatch in the second is the failure mode to suspect first if this ever
/// returns `Gap::IndUniverseHeight` at a declaration whose non-indexed
/// skeleton places fine.
fn build_indexed(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ni: usize,
    ind_ty: &E,
    ctor_tys: &[(Name, E)],
) -> Result<(), Gap> {
    let (shape, base, ixd) = spec_of(c, ind_name, np, ni, ind_ty, ctor_tys, Legs::Derive)?;
    let IndexData { indices, ctors, axioms } = ixd;
    let spec = IndexedDeclSpec::new(base, indices, ctors);
    if !spec.well_formed() {
        return Err(Gap::IndSpec(ind_name.clone(), "indexed spec not well formed"))
    }
    // The erased skeleton, exactly as the non-indexed path builds it: the
    // indexed carrier is carved *out of* it, so it must be the same object.
    let ind = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        Rc::new(
            Inductive::build(kenv, &mut app.mach, &spec.base)
                .ok_or_else(|| Gap::IndSpec(ind_name.clone(), "carrier"))?,
        )
    };
    let du = decl_universe(c, ind_name, &shape, &ind)?;

    let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
    let tower = ip.prelude.tower.clone();
    let lvl = tower.at(du.level as usize).ok_or(Gap::SortTowerHeight)?;
    // Before the translation exists, because the translation carries it.
    let ctor_abbrev = crate::ctor_ix::ctor_abbrevs(ip, &ind, &spec.base)
        .ok_or_else(|| Gap::IndSpec(ind_name.clone(), "naming a constructor's term"))?;
    let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
    let wrec = app.wrec(kenv).ok_or(Gap::IndApparatus)?;
    let ii = derived::inductive::family::IndexedInductive::build(
        kenv,
        &mut app.mach,
        &ind,
        &spec,
        &wrec.rc,
        &wrec.iota,
        &wrec.funspace,
    )
    .ok_or_else(|| Gap::IndSpec(ind_name.clone(), "indexed carrier"))?;
    let iu = derived::inductive::family::IndexedUniverse::over_at(
        kenv,
        &app.chain,
        &app.mach,
        &ind,
        &ii.carrier,
        &du.du,
        du.hyp.as_ref(),
        &lvl,
    )
    .ok_or_else(|| Gap::IndUniverseHeight(ind_name.clone(), du.level))?;
    let (ty_sym, univ) = (ii.carrier.ty, iu.ty_in_u1.clone());
    // **Kept, not dropped.** `IndexedCtor::mem_lean` is stated at this build's
    // working variables and about this build's `ind(p⃗,x⃗)`; the constructor
    // path (C2) must consume *this* object or its theorems are about a carrier
    // nothing relates to the one now in the store.
    let field_abbrev: Vec<Vec<Thm>> =
        shape.ctors.iter().map(|(.., ev)| ev.abbrev.clone()).collect();
    let tr =
        Rc::new(IndexedTranslation { ii, ax: axioms, base: ind.clone(), field_abbrev, ctor_abbrev });
    app.indexed.insert((ind_name.clone(), inst.to_vec()), tr.clone());
    former_at(c, ind_name, inst, np, ni, ty_sym, &univ, du.hyp.is_some(), du.level)?;
    // **After the former, and unable to unseat it.** The type former is a
    // complete obligation on its own and `042_rbTreeDef` asks for it and
    // nothing else, so a constructor that does not build is recorded against
    // its own name rather than returned — see `crate::ctor_ix`.
    crate::ctor_ix::constructors(c, ind_name, inst, np, ni, ctor_tys, &tr);
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
    ni: usize,
    ind_ty: &E,
    ctor_tys: &[(Name, E)],
    legs: Legs,
) -> Result<(Shape, DeclSpec, IndexData), Gap> {
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
        // 1b. the **indices**, in their own nested scope: `ιₖ` is abstracted
        //     over the parameters and the *earlier* indices, so index `k`'s
        //     type is interpreted with `x⃗<ₖ` open and nothing more. The scopes
        //     close again before the constructors are walked, which are stated
        //     at the parameters alone.
        //
        //     Nothing derived here survives the close, and nothing needs to: a
        //     defining axiom `⊢ ∀p⃗ ∀x⃗<ₖ. ιₖ(p⃗,x⃗<ₖ) = ⟦Iₖ⟧` is unconditional,
        //     so it is unaffected by a scope that opened after it.
        let mut indices = Vec::with_capacity(ni);
        let mut index_axs = Vec::with_capacity(ni);
        cur = c.in_scope(|c| {
            let mut cur = cur.clone();
            for _ in 0..ni {
                let Expr::Forall { ty, body } = &*cur.clone() else { return Err(bad("indices")) };
                // **Read the abstraction before opening the binder.**
                // `scope_vars(n)` is the `n` *innermost* scopes, so taking it
                // after the push would drop the outermost parameter and pick up
                // this index's own variable — an off-by-one at both ends that
                // `RBTree` cannot see, because its index types (`Color`, `N`)
                // are closed and `define_abbrev` accepts any parameter list for
                // a closed body. `Acc`'s index type is the parameter `α`, and
                // it is what caught this.
                let abstraction =
                    c.scope_vars(np + indices.len()).ok_or_else(|| bad("index variables"))?;
                let dom = c
                    .interpret_and_open(ty)
                    .map_err(|_| bad("index type"))?
                    .ok_or_else(|| bad("index type uninterpretable"))?;
                let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
                let (sym, ax) = derived::define_abbrev(&mut ip.env, &abstraction, &dom)
                    .ok_or_else(|| bad("index type mentions a later binder"))?;
                indices.push(sym);
                index_axs.push(ax);
                cur = body.clone();
            }
            Ok(cur)
        })?;
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
        let mut ctors_idx = Vec::with_capacity(ctor_tys.len());
        let mut ctor_index_axs = Vec::with_capacity(ctor_tys.len());
        for (cname, cty) in ctor_tys {
            let body = peel(cty, np).ok_or_else(|| bad("constructor parameters"))?;
            let (spec, ev, idx, iax) =
                c.in_scope(|c| ctor_spec(c, ind_name, np, ni, result_level, &body, legs))?;
            ctors.push((cname.clone(), cty.clone(), spec.clone(), ev));
            specs.push(spec);
            ctors_idx.push(idx);
            ctor_index_axs.push(iax);
        }

        // 3. the parameter scopes, discharged over every leg and every field
        //    typing of every constructor at once — so that one `⟦Pᵢ⟧` serves
        //    them all, and the `H` read off any leg is the `H` read off every
        //    other.
        for i in (0..np).rev() {
            let closed = c.close_one().ok_or_else(|| bad("parameter scope"))?;
            for (.., ev) in ctors.iter_mut() {
                for leg in ev.legs.iter_mut() {
                    *leg = closed.discharge(leg).map_err(|_| bad("parameter discharge"))?;
                }
                for fs in ev.field_sort.iter_mut() {
                    *fs = closed.discharge(fs).map_err(|_| bad("parameter discharge"))?;
                }
            }
            let _ = i;
        }
        Ok((
            Shape { param_tys, result_level, ctors },
            DeclSpec::new(np, specs),
            IndexData {
                indices,
                ctors: ctors_idx,
                axioms: IndexAx { indices: index_axs, ctors: ctor_index_axs },
            },
        ))
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
    ni: usize,
    rung: u32,
    body: &E,
    legs: Legs,
) -> Result<(CtorSpec, CtorEvidence, CtorIndices, CtorIndexAx), Gap> {
    let bad = |w: &'static str| Gap::IndSpec(ind_name.clone(), w);
    // `d⃗ᵢⱼ`, one row per `Slot::Rec`, accumulated as the walk meets them, and
    // the defining axioms beside them — kept for the same reason
    // `CtorEvidence::abbrev` keeps the field ones: a consumer has to move a
    // statement from `⟦e⟧` onto the symbol, and the axiom is the only thing
    // that does it. Discarding them made `IndexedCtor::mem_lean`'s witnesses
    // underivable, which is what the first attempt at a consumer discovered.
    let mut rec_args: Vec<Vec<kernel::FnSym>> = Vec::new();
    let mut rec_arg_axs: Vec<Vec<Thm>> = Vec::new();
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
        if let Some(ixs) = ind_spine(ind_name, ty, np, ni, d) {
            // **The recursive argument's own indices**, abstracted over the
            // parameters and the plain fields *preceding this slot* — which is
            // exactly what `abstraction` holds right now, and the reason they
            // are read here rather than in a second pass.
            let (syms, axs) = index_syms(c, ind_name, &ixs, &abstraction, "recursive argument index")?;
            rec_arg_axs.push(axs);
            rec_args.push(syms);
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
                // Kept whatever the leg mode is — see `CtorEvidence::field_sort`.
                ev.field_sort.push(mem.clone());
                if legs == Legs::Derive {
                    // `⊢ βⱼ(p⃗,y⃗) ∈ Uₙ`: the typing raised to the universe the
                    // summand induction is run at, then carried onto the
                    // abbreviation's own symbol.
                    //
                    // **`n` is the declaration's own resultant rung, not `1`.**
                    // It used to be `1`, which is where `Prod` at
                    // `u := 1, v := 1` and `RBTree` at `u := 1` stopped: their
                    // fields live in `Sort 2`, and the cumulativity table
                    // raises, it does not lower. A Lean inductive's resultant
                    // sort is the max over its field levels, so the raise this
                    // asks for always exists; a declaration where it does not
                    // still stops here, by name.
                    let raised = ip
                        .raise_in_gamma(l as usize, rung as usize, &mem)
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
    let Some(ixs) = ind_spine(ind_name, &cur, np, ni, d) else {
        return Err(bad("constructor codomain"));
    };
    // `e⃗ᵢ`, over the parameters and **all** the plain fields — `abstraction`
    // at the end of the walk.
    let (result, result_axs) = index_syms(c, ind_name, &ixs, &abstraction, "result index")?;
    let spec = CtorSpec::with_order(args, recs, order).ok_or_else(|| bad("field mask"))?;
    // Close every binder this walk opened, discharging each leg and each field
    // typing through the scopes it was derived under — entry `j` under field
    // scopes `0 … j-1` and no others, so the `∀`/`→` alternation comes out at
    // the right depth. The two families are parallel and are discharged
    // together; they differ only in that a leg's guard is carried onto the
    // abbreviation symbol and a field typing's is not
    // ([`CtorEvidence::field_sort`] says why).
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
        for fs in ev.field_sort.iter_mut().skip(plain_left + 1) {
            *fs = closed.discharge(fs).map_err(|_| Gap::ConvCompose("field-sort-guard"))?;
        }
    }
    Ok((spec, ev, CtorIndices { result, rec_args }, CtorIndexAx { result: result_axs, rec_args: rec_arg_axs }))
}

/// Interpret each index expression and abbreviate it over `abstraction`.
///
/// **The dependence restriction is not checked here, and deliberately so.** No
/// index expression may mention a *recursive* field — the thesis's recursive
/// argument rule does not extend `Γ` (`thesis.txt:1798-1801`), and
/// `IndexedDeclSpec` encodes that as an arity. Two mechanisms already refuse
/// it, both of them general rules rather than a hand-written scan:
///
/// * a recursive field opens an **uninterpreted** scope, so an expression
///   mentioning one has no `⟦·⟧` at all and fails at `infer_type`;
/// * `kernel::thm::define` rejects a body with a free variable that is not one
///   of the parameters, because such a symbol would not be a conservative
///   extension — so `define_abbrev` returns `None` for an index that reaches
///   past `abstraction`.
///
/// Writing the scan by hand would be a third statement of a rule the kernel
/// already enforces, and the one most likely to disagree with the other two.
fn index_syms(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    ixs: &[E],
    abstraction: &[kernel::FreeVar],
    what: &'static str,
) -> Result<(Vec<kernel::FnSym>, Vec<Thm>), Gap> {
    let bad = move |_: ()| Gap::IndSpec(ind_name.clone(), what);
    let (mut out, mut axs) = (Vec::with_capacity(ixs.len()), Vec::with_capacity(ixs.len()));
    for e in ixs {
        let t = c.infer_type(e).map_err(|_| bad(()))?;
        let tm = t.tm.clone().ok_or_else(|| t.ev.reason(bad(())))?;
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let (sym, ax) =
            derived::define_abbrev(&mut ip.env, abstraction, &tm).ok_or_else(|| bad(()))?;
        out.push(sym);
        axs.push(ax);
    }
    Ok((out, axs))
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

/// Is `e` the inductive applied to exactly the `np` parameters in order at
/// binder depth `d`, followed by `ni` **index expressions** — and if so, what
/// are they?
///
/// The parameters are pinned to their own de Bruijn positions because a
/// constructor may not instantiate them; the indices are arbitrary
/// expressions, and reading them out here is the whole of the difference
/// between an indexed declaration and a non-indexed one at the boundary.
/// `ni == 0` recovers the original predicate exactly.
///
/// This is the *telescope* spelling: the wrapper around
/// [`ind_spine_at`] that builds the `np` pinned `BVar`s. Every caller that
/// reads a declaration's own nest wants this one.
pub(crate) fn ind_spine(ind_name: &Name, e: &E, np: usize, ni: usize, d: usize) -> Option<Vec<E>> {
    let np32 = u32::try_from(np).ok()?;
    let d32 = u32::try_from(d).ok()?;
    ind_spine_at(ind_name, e, &crate::expr::bvars(np32, d32), ni)
}

/// The same predicate against **parameter expressions** rather than a binder
/// depth: is `e` the inductive applied to exactly `params`, in order, followed
/// by `ni` index expressions?
///
/// [`ind_spine`] is the case where the parameters are the telescope's own
/// `BVar`s, and it is the only case a declaration's nest can present. A *use*
/// site instantiates the parameters at arbitrary expressions, and there the
/// depth arithmetic says nothing — so the honest generalisation is to take the
/// expressions to match. Matching is syntactic and deliberately so: it is the
/// same equality the depth version tested, one constructor wider.
///
/// **The caller owns the de Bruijn frame.** `e` and `params` must be stated in
/// the *same* context; a caller walking under binders shifts `params` itself
/// (`crate::expr::shift(p, 0, l)` under `l` open binders), because only it
/// knows how many are open.
pub(crate) fn ind_spine_at(ind_name: &Name, e: &E, params: &[E], ni: usize) -> Option<Vec<E>> {
    let (head, args) = crate::expr::get_app(e);
    let Expr::Const(n, _) = &*head else { return None };
    let np = params.len();
    if n != ind_name || args.len() != np + ni {
        return None
    }
    let params_matched = args[..np].iter().zip(params).all(|(a, p)| a == p);
    params_matched.then(|| args[np..].to_vec())
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
    // **The rung the whole chain runs at**, read off the declaration rather
    // than fixed at `U₁` and raised afterwards. The `_at` family is stated at
    // any rung; running at `U₁` and lifting the finished tag sum worked only
    // when every *field* could be lowered into `U₁` first, which is the one
    // step cumulativity cannot do.
    let lvl = tower.at(level as usize).ok_or(Gap::SortTowerHeight)?;
    let want = ip.sort(level);
    let tags = {
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let mut summands = Vec::with_capacity(per_ctor.len());
        for (ci, legs) in per_ctor.iter().enumerate() {
            let obligations = derived::cumul::summand_obligations_at(
                kenv,
                &app.chain,
                &app.mach,
                ind,
                ci,
                hyp.as_ref(),
                &lvl,
                legs,
            )
            .ok_or_else(|| short(()))?;
            summands.push(
                derived::cumul::summand_at(
                    kenv,
                    &app.chain,
                    &app.mach,
                    ind,
                    ci,
                    hyp.as_ref(),
                    &lvl,
                    &obligations,
                )
                .ok_or_else(|| short(()))?,
            );
        }
        derived::cumul::tags_at(kenv, &app.chain, &app.mach, ind, hyp.as_ref(), &lvl, &summands)
            .ok_or_else(|| short(()))?
    };
    // No raise: `tags_at` already states `⊢ [H →] A ∈ Uₙ` at the rung asked
    // for, so the tag sum arrives where the placement wants it.
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
    Ok(DeclUniv { ty_in_un: du.ty_in_u1.clone(), du, hyp, level })
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
    former_at(
        c,
        ind_name,
        inst,
        shape.param_tys.len(),
        0,
        ind.ty,
        &du.ty_in_un,
        du.hyp.is_some(),
        du.level,
    )
}

/// The type former at `np + ni` binders, over a carrier symbol of that arity.
///
/// [`former`] is this at `ni = 0`, and the indexed path is this at `ni > 0`
/// with [`IndexedCarrier::ty`] and [`IndexedUniverse::ty_in_u1`] in place of
/// the erased pair. **One nest, not two**, because the difference between an
/// indexed declaration and a non-indexed one at this layer is exactly the
/// depth and which symbol sits at the bottom: the `Π` clause at each level is
/// still decided by the same `is_prop`, and the bottom's membership is still
/// its universe theorem instantiated at the nest's own variables.
///
/// **`H` is over the parameters only**, at either arity: it is the conjunction
/// of the *parameters'* typings, so the fold below takes the first `np`
/// memberships and the index scopes contribute nothing to it.
#[allow(clippy::too_many_arguments)]
pub(crate) fn former_at(
    c: &mut Checker<'_, '_>,
    ind_name: &Name,
    inst: &[u32],
    np: usize,
    ni: usize,
    ty_sym: kernel::FnSym,
    univ: &Thm,
    conditional: bool,
    level: u32,
) -> Result<(), Gap> {
    let depth = np + ni;
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
    let u1 = univ.clone();
    let n = level;
    let name = ind_name.clone();
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> {
        let level = crate::expr::sort(level_numeral(n));
        let gap = |g: Gap| Ok(Typing { ty: level.clone(), tm: None, ev: Ev::missing(g) });
        let Some((ps, mems)) = c.binders(depth) else { return gap(Gap::NoEndpoint) };
        // `H` is the *parameters*' conjunction; the index scopes are not in it.
        let mems = &mems[..np];
        let ip = c.interp().expect("threaded");
        // Through `Interp::mk`, not `Term::apply`: a term the checker will have
        // to take apart later must be in the `Parts` hint table, and
        // `IndexedCarrier::ty_of` builds it raw.
        let carrier = ip.mk(ty_sym, ps.clone());
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
    let t = c.lam_nest(&lean_ty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
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
///
/// Returns the constructor symbol's own defining axiom,
/// `⊢ ∀f⃗. (ctor_symᵢ(f⃗) = ctorᵢ(y⃗,t⃗))`, for [`crate::interp::Translated`] to
/// keep — see there for why dropping it is not an option.
fn constructor(
    c: &mut Checker<'_, '_>,
    at: &Decl,
    cname: &Name,
    cty: &E,
    i: usize,
    abbrev: &[Thm],
) -> Result<Thm, Gap> {
    let spec = at.ind.spec.ctors[i].clone();
    let depth = at.np + spec.order.len();
    // The codomain is read off the declaration, not synthesised: it is the one
    // expression whose interpretation the bottom's membership must be about.
    let codomain =
        peel(cty, depth).ok_or_else(|| Gap::IndSpec(at.name.clone(), "ctor arity"))?;
    // **The carrier term's name is minted here, not at the bottom**, over
    // variables of this call's own — so that the defining axiom survives the
    // nest. `Inductive::ctor_term` is a function of its arguments alone, so
    // instantiating the axiom at the nest's fields is the nest's own term.
    let (ctor_sym, ctor_ax) = {
        let ip = c.interp().ok_or(Gap::SymbolicLevel)?;
        let (kenv, app, _) = ip.ind_parts().ok_or(Gap::IndApparatus)?;
        let fvs: Vec<kernel::FreeVar> =
            (0..spec.order.len()).map(|_| kenv.fresh_var()).collect();
        let (mut ys, mut rs) = (Vec::new(), Vec::new());
        for (j, slot) in spec.order.iter().enumerate() {
            match slot {
                Slot::Plain => ys.push(Term::var(fvs[j])),
                Slot::Rec => rs.push(Term::var(fvs[j])),
            }
        }
        let raw = at
            .ind
            .ctor_term(&app.mach, i, &ys, &rs)
            .ok_or_else(|| Gap::IndSpec(at.name.clone(), "ctor term"))?;
        derived::define_abbrev(kenv, &fvs, &raw)
            .ok_or_else(|| Gap::IndSpec(at.name.clone(), "ctor abbreviation"))?
    };
    let site = CtorSite {
        at: at.clone(),
        i,
        codomain,
        spec,
        abbrev: abbrev.to_vec(),
        ctor_sym,
        ctor_ax: ctor_ax.clone(),
    };
    let mut bottom = move |c: &mut Checker<'_, '_>| -> R<Typing> { Ok(ctor_bottom(c, &site)) };
    let t = c.lam_nest(cty, depth, &mut bottom).map_err(|_| Gap::NotDecomposable)?;
    store(c, cname, &at.inst, t)?;
    Ok(ctor_ax)
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
    /// The symbol mini names the carrier term by, and its defining axiom
    /// `⊢ ∀f⃗. (ctor_symᵢ(f⃗) = ctorᵢ(y⃗,t⃗))` at the fields in declared order.
    ctor_sym: kernel::FnSym,
    ctor_ax: Thm,
}

/// The bottom of a constructor's nest: `ctor_i(y⃗,r⃗)` and its membership in the
/// applied spine of `⟦T⟧`.
fn ctor_bottom(c: &mut Checker<'_, '_>, site: &CtorSite) -> Typing {
    let CtorSite { at, i, codomain, spec, abbrev, ctor_sym, ctor_ax } = site;
    let (ind_name, inst, np, ind) = (&at.name, &at.inst[..], at.np, &at.ind);
    let i = *i;
    let nf = spec.order.len();
    let ty = codomain.clone();
    let gap = |g: Gap| Typing { ty: ty.clone(), tm: None, ev: Ev::missing(g) };
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
    // one because that is the order the Lean λ-nest binds them in. The symbol is
    // [`constructor`]'s, minted before the nest so that the axiom outlives it.
    let _ = field_vars;
    let (term, unfold) = {
        let at = match derived::inst_all(ctor_ax, fields) {
            Some(t) => t,
            None => return gap(Gap::IndSpec(ind_name.clone(), "ctor abbreviation instance")),
        };
        // The symbol names *this* nest's carrier term, and nothing else: the
        // axiom's right-hand side at these fields must be the term just built.
        if at.concl().as_eq().map(|(_, r)| r) != Some(raw.clone()) {
            return gap(Gap::IndSpec(ind_name.clone(), "ctor abbreviation instance"))
        }
        (ip.mk(*ctor_sym, fields.to_vec()), at)
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
pub(crate) fn store_spine(ip: &mut crate::interp::Interp, former: &Term, ps: &[Term]) -> Term {
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
    use crate::expr::{app, bvar, forall, konst, sort};
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

    /// **`ind_spine` is `ind_spine_at` at the pinned `BVar`s, and nothing
    /// else** — plus the three properties the general form must keep.
    ///
    /// The depth version's whole content is "the parameters are the telescope's
    /// own variables, in order"; the general one takes the expressions. Three
    /// parameters, not two, because the claim under test is an *order* claim
    /// and a rotation is invisible at two (`MEMORY`: two atoms cannot
    /// distinguish).
    ///
    /// **Failing loudly is the deliverable here.** A use site instantiates the
    /// parameters at arbitrary expressions, and the danger of the
    /// generalisation is that it silently accepts a spine applied to *other*
    /// parameters — which would pass on this corpus, where every occurrence is
    /// the nest's own, and be wrong at the first use site that carries
    /// different ones. So the three declines below are the point, and the two
    /// acceptances are the control.
    #[test]
    fn the_spine_predicate_pins_the_parameters_wherever_they_come_from() {
        let t = Name::simple("T");
        let ls: std::rc::Rc<[Level]> = std::rc::Rc::from(Vec::new());
        let sp = |args: &[E]| crate::expr::app_n(konst(t.clone(), ls.clone()), args);
        let (np, ni, d) = (3usize, 1usize, 4usize);
        let pinned = crate::expr::bvars(3, 4); // #6 #5 #4

        // (1) The wrapper agrees with the general form on the nest's own shape.
        let e = sp(&[bvar(6), bvar(5), bvar(4), bvar(0)]);
        let want = [bvar(0)];
        assert_eq!(ind_spine(&t, &e, np, ni, d).as_deref(), Some(&want[..]));
        assert_eq!(ind_spine_at(&t, &e, &pinned, ni).as_deref(), Some(&want[..]));

        // (2) …and on a spine whose parameters are *not* the pinned ones: both
        // decline, and the general form declines only because it was handed the
        // pinned list.
        let other = sp(&[bvar(6), bvar(4), bvar(5), bvar(0)]);
        assert_eq!(ind_spine(&t, &other, np, ni, d), None, "a swap is not the nest's spine");
        assert_eq!(ind_spine_at(&t, &other, &pinned, ni), None);
        // A rotation, which two parameters cannot tell from a swap.
        let rot = sp(&[bvar(5), bvar(4), bvar(6), bvar(0)]);
        assert_eq!(ind_spine_at(&t, &rot, &pinned, ni), None, "order is pinned, not the set");

        // (3) Non-variable parameters — the case the depth version cannot
        // state at all, and the reason the general one exists.
        let a = konst(Name::simple("A"), ls.clone());
        let b = app(konst(Name::simple("F"), ls.clone()), a.clone());
        let cc = sort(Level::Zero);
        let ps = vec![a.clone(), b.clone(), cc.clone()];
        let ix = app(konst(Name::simple("g"), ls.clone()), bvar(0));
        let use_site = sp(&[a.clone(), b.clone(), cc.clone(), ix.clone()]);
        assert_eq!(ind_spine_at(&t, &use_site, &ps, ni).as_deref(), Some(&[ix][..]));
        // The same head at *different* parameters is a different family
        // instance, and must not be read as this one.
        let wrong = sp(&[a.clone(), a.clone(), cc, bvar(0)]);
        assert_eq!(ind_spine_at(&t, &wrong, &ps, ni), None, "a use site's parameters are pinned too");
        // Arity is still part of the predicate.
        assert_eq!(ind_spine_at(&t, &use_site, &ps, 0), None);
        assert_eq!(ind_spine_at(&Name::simple("U"), &use_site, &ps, ni), None);
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

    /// **A second translation mints no second symbol** — the invariant every
    /// abbreviation in this module rests on, made checkable.
    ///
    /// `derived::define_abbrev` is `kernel::thm::define`, which is
    /// `Env::declare`: a fresh `FnSym` on every call, **keyed on nothing**.
    /// Nothing in the minting path can tell that it has been asked for the
    /// same thing twice. What makes that safe is a property of the *call
    /// graph* — [`ensure`] builds only on a `stored_term` miss, and
    /// `spec_of`/`ctor_spec` are reached from nowhere else — and a property of
    /// the call graph is exactly the kind of thing that stops holding when
    /// someone adds a caller.
    ///
    /// The cost of it not holding is not a wrong theorem, which is why nothing
    /// catches it: a second `⟦βⱼ⟧` symbol is a conservative extension that no
    /// equation relates to the first, so downstream conversions that should be
    /// reflexivity need a derivation instead. The last time that happened it
    /// was a measured **61.4% of wall clock**.
    ///
    /// `Env` exposes no counter, so the probe is `declare` itself: mint a
    /// throwaway symbol either side and require the ids to be adjacent. Four
    /// re-entries — the carrier and all three constructors — so the test
    /// distinguishes "nothing was minted" from "one path is idempotent".
    #[test]
    fn a_second_translation_mints_no_second_symbol() {
        let (env, t, ctors) = three_ctor_env();
        let mut ip = Interp::new();
        let fresh = ip.env.declare(0).id();
        {
            let mut c = Checker::threaded(&env, &mut ip);
            ensure(&mut c, &t, &[]).expect("the first translation succeeds");
        }
        let before = ip.env.declare(0).id();
        // **The probe can see minting.** Without this the assertion below would
        // also pass against an `ensure` that never minted anything at all, and
        // a test that cannot fail for the reason it names is worse than none.
        assert!(
            before - fresh > 10,
            "the first translation minted only {} symbols — the probe is not measuring the \
             signature",
            before - fresh - 1
        );
        {
            let mut c = Checker::threaded(&env, &mut ip);
            ensure(&mut c, &t, &[]).expect("a second ensure on the carrier");
            for n in &ctors {
                ensure(&mut c, n, &[]).expect("a second ensure on a constructor");
            }
        }
        let after = ip.env.declare(0).id();
        assert_eq!(
            after,
            before + 1,
            "four re-entries minted {} new function symbols; the translation is no longer \
             once-per-(declaration, σ) and every abbreviation in this module has just been \
             duplicated",
            after - before - 1
        );
    }

    /// **An indexed family, walked to a well-formed `IndexedDeclSpec`.**
    ///
    /// ```text
    /// inductive B : Type    | b0 | b1
    /// inductive T (α : Type) : B → B → Type
    ///   | c0 : T α b0 b0                            0 plain, 0 rec
    ///   | c1 : ∀ (x : B), T α x b0 → T α b1 x       1 plain, 1 rec
    ///   | c2 : ∀ (x y : B), T α x y → T α y x → T α b0 b1   2 plain, 2 rec
    /// ```
    ///
    /// Three constructors with **three distinct plain/rec counts**, because the
    /// thing under test is a family of *arities* — `e⃗ᵢ` at `np + kᵢ` and
    /// `d⃗ᵢⱼ` at `np + plains_before(i,j)` — and two of anything cannot tell an
    /// arity table from its reverse. `c2`'s two recursive arguments sit at the
    /// same plain prefix and its indices are *swapped* between them, which is
    /// what makes the `rec_args` rows positional rather than incidental.
    ///
    /// `IndexedDeclSpec::well_formed` is the assertion: it checks every one of
    /// those arities against what the construction will apply the symbol at.
    fn indexed_env() -> (Environment, Name) {
        let b = Name::simple("B");
        let bt = konst(b.clone(), Vec::new().into());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: b.clone(),
                lparams: vec![],
                num_params: 0,
                ty: sort(Level::Zero.succ()),
                ctors: vec![
                    (Name::str(&b, "b0"), bt.clone()),
                    (Name::str(&b, "b1"), bt.clone()),
                ],
            },
        )
        .expect("B is accepted");
        let b0 = konst(Name::str(&b, "b0"), Vec::new().into());
        let b1 = konst(Name::str(&b, "b1"), Vec::new().into());
        let t = Name::simple("T");
        // `T α i j`, with `α` at de Bruijn `d` and the indices given.
        let tap = |a: E, i: E, j: E| {
            crate::expr::app(crate::expr::app(crate::expr::app(konst(t.clone(), Vec::new().into()), a), i), j)
        };
        let ty = forall(sort(Level::Zero.succ()), forall(bt.clone(), forall(bt.clone(), sort(Level::Zero.succ()))));
        let ctors = vec![
            // c0 : ∀ α. T α b0 b0
            (Name::str(&t, "c0"), forall(sort(Level::Zero.succ()), tap(bvar(0), b0.clone(), b0.clone()))),
            // c1 : ∀ α (x : B). T α x b0 → T α b1 x
            (
                Name::str(&t, "c1"),
                forall(
                    sort(Level::Zero.succ()),
                    forall(
                        bt.clone(),
                        forall(tap(bvar(1), bvar(0), b0.clone()), tap(bvar(2), b1.clone(), bvar(1))),
                    ),
                ),
            ),
            // c2 : ∀ α (x y : B). T α x y → T α y x → T α b0 b1
            (
                Name::str(&t, "c2"),
                forall(
                    sort(Level::Zero.succ()),
                    forall(
                        bt.clone(),
                        forall(
                            bt.clone(),
                            forall(
                                tap(bvar(2), bvar(1), bvar(0)),
                                forall(
                                    tap(bvar(3), bvar(1), bvar(2)),
                                    tap(bvar(4), b0.clone(), b1.clone()),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ];
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: t.clone(),
                lparams: vec![],
                num_params: 1,
                ty,
                ctors,
            },
        )
        .expect("T is accepted");
        (env, t)
    }

    #[test]
    fn an_indexed_family_walks_to_a_well_formed_spec() {
        let (env, t) = indexed_env();
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        let ind_ty = ground::subst_ground(
            &c.environment().get(&t).unwrap().ty().clone(),
            &[],
            &[],
        );
        let ctor_tys: Vec<(Name, E)> = ["c0", "c1", "c2"]
            .iter()
            .map(|n| {
                let n = Name::str(&t, n);
                let ty = c.environment().get(&n).unwrap().ty().clone();
                (n, ty)
            })
            .collect();
        let (_, base, ix) =
            spec_of(&mut c, &t, 1, 2, &ind_ty, &ctor_tys, Legs::Skip).expect("the walk succeeds");
        let spec = IndexedDeclSpec::new(base, ix.indices, ix.ctors);
        assert!(spec.well_formed(), "the arities must be the ones the construction applies");
        assert_eq!(spec.num_indices(), 2);
        // ιₖ at `np + k`, so 1 and 2 — the check that caught the off-by-one.
        assert_eq!(
            spec.indices.iter().map(|s| s.arity()).collect::<Vec<_>>(),
            vec![1, 2],
            "ιₖ has arity np + k"
        );
        // `e⃗ᵢ` at `np + kᵢ` for kᵢ = 0, 1, 2.
        let results: Vec<Vec<u32>> = spec
            .ctors_idx
            .iter()
            .map(|ci| ci.result.iter().map(|s| s.arity()).collect())
            .collect();
        assert_eq!(results, vec![vec![1, 1], vec![2, 2], vec![3, 3]], "e⃗ᵢ has arity np + kᵢ");
        // `d⃗ᵢⱼ` at `np + plains_before(i,j)`: none, one row at 2, two rows at 3.
        let recs: Vec<Vec<Vec<u32>>> = spec
            .ctors_idx
            .iter()
            .map(|ci| {
                ci.rec_args.iter().map(|r| r.iter().map(|s| s.arity()).collect()).collect()
            })
            .collect();
        assert_eq!(
            recs,
            vec![
                Vec::<Vec<u32>>::new(),
                vec![vec![2, 2]],
                vec![vec![3, 3], vec![3, 3]],
            ],
            "d⃗ᵢⱼ has arity np + plains_before(i, j)"
        );
    }

    /// **The indexed family is translated, with its typing — and walked
    /// once.**
    ///
    /// [`build_indexed`]'s end-to-end test on the fixture above, which is
    /// chosen so that passing it certifies something: two indices, three
    /// constructors at three plain/rec counts, and `c2`'s two recursive
    /// arguments at the same plain prefix with their indices *swapped*. A
    /// family whose indices were closed constants would exercise none of the
    /// abstraction, and a family with one constructor none of the `good`
    /// recursion.
    ///
    /// The typing is checked against the interpretation of the declaration's
    /// **own Lean type**, not merely for existing: `⊢ ⟦T⟧ ∈ ⟦∀α. B → B →
    /// Type 0⟧`. A membership in some other set would be a true theorem about
    /// the wrong thing, which is the failure this project keeps finding.
    ///
    /// The mint probe rides along, because `build_indexed` mints index
    /// abbreviations and a second entry must not mint them again.
    #[test]
    fn an_indexed_family_is_translated_with_its_typing_and_walked_once() {
        let (env, t) = indexed_env();
        let mut ip = Interp::new();
        let fresh = ip.env.declare(0).id();
        {
            let mut c = Checker::threaded(&env, &mut ip);
            ensure(&mut c, &t, &[]).expect("the indexed family translates");
            let ty = c.infer_type(&konst(t.clone(), Vec::new().into())).expect("infer ⟦T⟧");
            let tm = ty.tm.clone().expect("the type former must interpret");
            let mem = ty.ev.thm().expect("the former must have a typing").clone();
            assert!(mem.hyps().is_empty(), "a closed declaration's typing is unconditional");
            // `⟦∀α. B → B → Type 0⟧`, computed from the Lean type the store
            // entry claims — so the two cannot drift apart.
            let want = c.infer_type(&ty.ty).expect("infer the Lean type").tm.expect("interprets");
            assert_eq!(
                *mem.concl(),
                Formula::mem(tm, want),
                "the former's typing must be about its own interpretation, in its own type"
            );
        }
        let before = ip.env.declare(0).id();
        assert!(before - fresh > 5, "the walk must actually mint, or the probe proves nothing");
        {
            let mut c = Checker::threaded(&env, &mut ip);
            for _ in 0..3 {
                ensure(&mut c, &t, &[]).expect("a second translation is a store hit");
            }
        }
        let after = ip.env.declare(0).id();
        assert_eq!(
            after,
            before + 1,
            "three re-entries on a translated indexed family minted {} new symbols",
            after - before - 1
        );
    }

    /// **The first consumer of `IndexedCtor::mem_lean`.**
    ///
    /// `mem_lean` is built and tested inside `derived/`, and nothing in
    /// `mini/` called it. On this project an interface with no consumer is
    /// where the mismatch lives, so this calls it for real, with witnesses
    /// **derived from mini's own store** — a test cannot fabricate a `Thm`,
    /// which is the kernel working as intended and is what forced the finding
    /// below.
    ///
    /// The witness `mem_lean` asks for is
    /// `⊢ ∀p⃗∀y⃗∀r⃗. ([Hᵢ^ind →] eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, e⃗<ₖ))` — stated at the two
    /// *symbols*. What inference hands back is the same statement at the two
    /// *interpretations*, `⟦eₖ⟧ ∈ ⟦Iₖ⟧`, and the only things relating them are
    /// the abbreviations' defining axioms. The walk used to discard those;
    /// [`IndexAx`] exists because this test could not be written without them.
    ///
    /// `c0 : T α b0 b0` is where to do it: `mem_lean` drops the antecedent
    /// entirely for a field-less constructor, so the result is unconditional
    /// and can be compared outright against `ctor₀ ∈ ind(p⃗, e⃗₀(p⃗))`.
    ///
    /// # What this pins about C2, and what it does not
    ///
    /// It pins that the two sides compose at the arity, at the order, and at
    /// the symbols. It does **not** pin the general witness: no index type in
    /// this corpus depends on an earlier index — `RBTree`'s are `Color` and
    /// `N`, this fixture's are `B` and `B`, `Acc`'s is a parameter — so a `ιₖ`
    /// whose body genuinely mentions `x⃗<ₖ` is unexercised by anything
    /// available. That sub-case must be a **named decline** in C2 rather than
    /// untested code that looks general; the `scope_vars` off-by-one is what
    /// happens otherwise, and it was invisible for exactly this reason.
    #[test]
    fn mem_lean_composes_with_the_constructor_typings_mini_already_has() {
        let (env, t) = indexed_env();
        let mut ip = Interp::new();
        let b0_mem = {
            let mut c = Checker::threaded(&env, &mut ip);
            ensure(&mut c, &t, &[]).expect("the family translates");
            let ty = c
                .infer_type(&konst(Name::str(&Name::simple("B"), "b0"), Vec::new().into()))
                .expect("infer ⟦B.b0⟧");
            ty.ev.thm().expect("B.b0 has a typing").clone()
        };
        assert!(b0_mem.hyps().is_empty(), "a closed constructor's typing is unconditional");

        let it = ip
            .ind_apparatus()
            .expect("apparatus")
            .indexed
            .get(&(t.clone(), Vec::new()))
            .expect("build_indexed kept the translation")
            .clone();
        let ctor = &it.ii.carrier.ctors[0];
        assert_eq!(ctor.index, 0);
        assert!(ctor.mem_atoms_lean().is_empty(), "c0 has no fields, so no Hᵢ^ind");

        // The two witnesses, derived: move `⊢ ⟦B.b0⟧ ∈ ⟦B⟧` onto `e₀ₖ` and
        // `ιₖ` by their own defining axioms, then generalise over `p⃗`.
        let ps: Vec<Term> = ctor.pvs.iter().map(|v| Term::var(*v)).collect();
        let mut prev: Vec<Term> = Vec::new();
        let mut ws: Vec<Thm> = Vec::new();
        for k in 0..2 {
            let e_sym = it.ii.spec.ctors_idx[0].result[k];
            let e_at = derived::inst_all(&it.ax.ctors[0].result[k], &ps).expect("e axiom at p⃗");
            let mut iargs = ps.clone();
            iargs.extend(prev.iter().cloned());
            let i_at = derived::inst_all(&it.ax.indices[k], &iargs).expect("ι axiom at p⃗, e⃗<ₖ");
            let onto_subject =
                ip.retarget_subject(&b0_mem, &e_at).expect("⊢ e₀ₖ(p⃗) ∈ ⟦B⟧");
            let back = derived::eq_symm(&mut ip.env, &i_at).expect("⟦B⟧ = ιₖ(…)");
            let both = ip.retarget_set(&onto_subject, &back).expect("⊢ e₀ₖ(p⃗) ∈ ιₖ(…)");
            ws.push(derived::gen_all(&ctor.pvs, &both));
            prev.push(Term::apply(e_sym, ps.clone()));
        }

        // Refusals first: a consumer that hands in the wrong number, or a
        // witness at the wrong statement, must be refused rather than composed
        // into a theorem about the wrong terms.
        let ctor = &it.ii.carrier.ctors[0];
        assert!(ctor.mem_lean(&[]).is_none(), "two indices, so two witnesses");
        assert!(
            ctor.mem_lean(&[ws[0].clone(), b0_mem.clone()]).is_none(),
            "a witness at the wrong statement must be refused"
        );

        // And the real thing.
        let mem = ctor.mem_lean(&ws).expect("mem_lean composes with mini's own typings");
        assert!(mem.hyps().is_empty(), "the result must rest on nothing");
        let want = it
            .ii
            .carrier
            .ty_of(&ps, &prev)
            .expect("ind(p⃗, e⃗₀(p⃗))");
        let inst = derived::inst_all(&mem, &ps).expect("at the working variables");
        let (_subj, set) = inst.concl().as_mem().expect("a membership, with no antecedent");
        assert_eq!(set, want, "c0 must land in the carrier at its own result indices");

        // The contract the constructor nest depends on: one atom per Lean
        // field, in declared order, for a constructor that has fields.
        let c2 = &it.ii.carrier.ctors[2];
        assert_eq!(
            c2.mem_atoms_lean().len(),
            c2.lean_order.len(),
            "Hᵢ^ind is positional against the Lean field spine"
        );
        assert_eq!(c2.lean_order.len(), 4, "c2 binds x, y and two recursive arguments");
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
        let ind = app.decls.get(&key).expect("translated").ind.clone();
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
        let ind = &app.decls.get(&key).expect("translated").ind;
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
    fn a_possibly_prop_declaration_never_acquires_a_w_type() {
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
        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        assert!(
            !large_eliminating(&mut c, &t),
            "two constructors make the eliminator small — this must be class (P)"
        );
        // `σ = [1]`: `Sort 1` is `Type 0`, so a *per-instantiation* branch
        // would build a W-type right here.
        let at: std::rc::Rc<[Level]> = vec![Level::Zero.succ()].into();
        let r = c.infer_type(&konst(t.clone(), at.clone())).expect("infer");
        assert!(r.tm.is_none(), "a possibly-Prop declaration must not acquire a W-type");
        assert_eq!(
            r.ev.gap(),
            Some(&Gap::IndSpec(t.clone(), "class (P) above Prop")),
            "and the gap must name the cause, not the site"
        );
        // The decline is recorded, so a second lookup reports the same reason
        // rather than a bare store miss.
        let r2 = c.infer_type(&konst(t.clone(), at)).expect("infer");
        assert_eq!(r2.ev.gap(), Some(&Gap::IndSpec(t, "class (P) above Prop")));
    }

    /// **The boundary walk's field↔index-slot correspondence outlives the
    /// branch**, and it is a *permutation* that no other artefact records.
    ///
    /// `IndexedDeclSpec` says slot `k` is a symbol of arity `np + …`; it does
    /// not say **which field's expression** that symbol abbreviates. Only
    /// [`IndexAx`] does, because only [`ctor_spec`] had the field binders open
    /// while it interpreted the result spine. `SortElimProp.mk` in the corpus
    /// puts its two fields into its two slots **swapped**, and `le_rec`'s
    /// `minor_eq` cannot be stated without knowing that.
    ///
    /// ```text
    /// inductive P3 (α : Type) : α → α → α → Prop | mk : ∀ (a b c : α), P3 α b c a
    /// ```
    ///
    /// **Three fields and a 3-cycle, deliberately.** Two would not discriminate:
    /// a swap is its own reversal, so a build that read the spine backwards
    /// would pass. `(b, c, a)` is distinguishable from identity *and* from
    /// reversal, which is what a test pinning an order owes.
    ///
    /// The assertion instantiates each slot's axiom at four distinct terms and
    /// reads the right-hand side, so it is about the correspondence itself and
    /// not about the shape of the statement carrying it.
    ///
    /// # It is not `derived`'s 3-cycle fixture, and the overlap is only the shape
    ///
    /// `derived/tests/family_le_index.rs` now carries a fixture at the same
    /// `np = 1, ni = 3, kᵢ = 3` with the fields 3-cycled, and pins `χ = 1` at
    /// the true index vector and `χ = 0` at five others. The two were arrived
    /// at independently and they cover different halves of the seam, which is
    /// worth writing down so neither reads as the other's coverage:
    ///
    /// * **That one** is about the *carrier's meaning* — which index vectors
    ///   the conditional singleton is inhabited at — and is handed its
    ///   `eᵢₖ` symbols ready-made by the fixture.
    ///   [`IndexedDeclSpec`](derived::inductive::family::IndexedDeclSpec) is
    ///   all it needs, so it cannot see a wrong field↔slot map at all: the map
    ///   *is* the fixture there.
    /// * **This one** is about where those symbols come from — mini reading a
    ///   Lean constructor's result spine with the field binders open — and it
    ///   is the only place a wrong reading is observable, because
    ///   `IndexedDeclSpec` does not record it.
    ///
    /// The two would agree with each other under a mini-side permutation bug
    /// and under a `derived`-side one alike, which is exactly why both exist.
    #[test]
    fn an_indexed_prop_keeps_its_field_to_slot_correspondence() {
        let p3 = Name::simple("P3");
        let mk = Name::str(&p3, "mk");
        let no: Rc<[Level]> = Vec::new().into();
        let k = || konst(p3.clone(), no.clone());
        let ty0 = || sort(Level::Zero.succ());
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: p3.clone(),
                lparams: vec![],
                num_params: 1,
                ty: forall(ty0(), forall(bvar(0), forall(bvar(1), forall(bvar(2), sort(Level::Zero))))),
                ctors: vec![(
                    mk,
                    forall(
                        ty0(),
                        forall(
                            bvar(0),
                            forall(
                                bvar(1),
                                forall(
                                    bvar(2),
                                    // `P3 α b c a` — the 3-cycle.
                                    app(app(app(app(k(), bvar(3)), bvar(1)), bvar(0)), bvar(2)),
                                ),
                            ),
                        ),
                    ),
                )],
            },
        )
        .expect("P3 is accepted");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        // **The walk is kept whether or not the route goes on to build.** When
        // this was written the carrier was unwired and the assertion here was
        // `got.tm.is_none()`; `crate::class_s_ix` and `derived`'s `8d9c94c`
        // between them made `P3` build, and the retention is the same retention
        // either way — `zoneb::ensure` stores before it branches.
        let got = c.infer_type(&konst(p3.clone(), no)).expect("infer ⟦P3⟧");
        assert!(got.tm.is_some(), "P3 is class (S) at an index and now builds");

        // Four distinct terms, so a wrong slot cannot coincide with a right one.
        let args: Vec<Term> = (0..4).map(|n| c.interp().expect("threaded").sort(n)).collect();
        let key = (p3, Vec::new());
        let app_ = c.interp().expect("threaded").ind_apparatus().expect("apparatus");
        let w = app_.indexed_walks.get(&key).expect("the walk outlived the decline").clone();
        assert_eq!(w.spec.num_indices(), 3);
        assert_eq!(w.field_abbrev[0].len(), 3, "three plain fields");
        assert_eq!(w.field_sort[0].len(), 3, "…and a typing for each");
        let slots = &w.ax.ctors[0].result;
        assert_eq!(slots.len(), 3, "one axiom per index slot");
        // The abstraction is `[α, a, b, c]`, so `args[1..]` are `a, b, c` and
        // the result spine `P3 α b c a` must read back as `b, c, a`.
        let rhs: Vec<Term> = slots
            .iter()
            .map(|t| {
                derived::inst_all(t, &args)
                    .expect("the axiom instantiates at the abstraction")
                    .concl()
                    .as_eq()
                    .expect("a defining equation")
                    .1
            })
            .collect();
        assert_eq!(
            rhs,
            vec![args[2].clone(), args[3].clone(), args[1].clone()],
            "slot k must name the field the constructor put there, not the k-th field"
        );
    }

    /// **A class-(P) constructor with a parameter and a plain field**, which no
    /// export can reach and which is therefore the only place the general path
    /// is exercised at all.
    ///
    /// Tara's short-circuit is why: a proof-valued *application* interprets to
    /// `•` without consulting its head constant, so a class-(P) constructor is
    /// asked for exactly when it occurs **unapplied** — which, for a
    /// declaration with parameters or fields, never happens in an export.
    /// `BoolProp.a`/`.b` (`np = 0`, `k = 0`) are the only reachable ones in the
    /// tutorials, and they pass under every wrong binder arithmetic there is.
    /// A bare `Expr::Const` is reachable from a *test*, though, so this asks
    /// for one directly.
    ///
    /// ```text
    /// inductive Q (α : Type) : Prop | mk : α → Q α
    /// ```
    ///
    /// `Q` is class (P) and not class (S): its single constructor has a
    /// `Type`-valued field, so the declaration is not a subsingleton and the
    /// truncation carrier is what it gets. `np = 1` and `k = 1`, so the nest is
    /// two deep, the field's `⟦α⟧`-to-`β₀(p⃗)` bridge actually runs, and
    /// `TruncCtor::mem`'s antecedent is discharged rather than absent — none of
    /// which `BoolProp` does.
    ///
    /// The three assertions are the ones every stored typing owes. The third is
    /// the one that makes the parameter load-bearing: the set must be `⟦Q α⟧`
    /// **inferred from the constructor's own declared codomain**, so a build
    /// that landed in the truncation at some other parameter, or that never
    /// moved off `‖ind(p⃗)‖` onto the applied spine, fails it.
    #[test]
    fn a_class_p_constructor_with_a_parameter_and_a_field() {
        let q = Name::simple("Q");
        let mk = Name::str(&q, "mk");
        let no: Rc<[Level]> = Vec::new().into();
        let mut env = Environment::empty();
        crate::kernel::add(
            &mut env,
            &Declaration::Inductive {
                name: q.clone(),
                lparams: vec![],
                num_params: 1,
                ty: forall(sort(Level::Zero.succ()), sort(Level::Zero)),
                ctors: vec![(
                    mk.clone(),
                    forall(
                        sort(Level::Zero.succ()),
                        forall(bvar(0), app(konst(q.clone(), no.clone()), bvar(1))),
                    ),
                )],
            },
        )
        .expect("Q is accepted");

        let mut ip = Interp::new();
        let mut c = Checker::threaded(&env, &mut ip);
        c.infer_type(&konst(q, no.clone())).expect("infer ⟦Q⟧");
        let got = c.infer_type(&konst(mk.clone(), no)).expect("infer ⟦Q.mk⟧");
        let m = got
            .ev
            .thm()
            .unwrap_or_else(|| panic!("⟦{mk}⟧ has no typing: {:?}", got.ev))
            .clone();
        assert!(m.hyps().is_empty(), "a stored typing is unconditional");
        let tm = got.tm.clone().expect("⟦Q.mk⟧ interprets");
        let (subj, set) = m.concl().as_mem().expect("a membership");
        assert_eq!(subj, tm, "the typing must be about ⟦Q.mk⟧ itself");
        let want = c.infer_type(&got.ty).expect("infer the Lean type").tm.expect("interprets");
        assert_eq!(set, want, "…and about its own Lean type");
        assert_eq!(
            tm,
            c.interp().expect("threaded").point(),
            "a class-(P) constructor's codomain is a Prop, so the whole constant is a proof"
        );
    }
}
