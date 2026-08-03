//! Evidence, or a named absence (MINI-DESIGN.md §5), and the persistence
//! funnel (§4.3).
//!
//! # Interface
//!
//! * [`Ev`] — `Proved(Thm)` or `Gap(Gap)`. **No third state**: there is no
//!   retry, no "admitted for now", and no search that might succeed later.
//! * [`Gap`] — every way evidence can be missing, as an enum, so that a new
//!   hole cannot be introduced without naming it. At 89-of-89-at-zero-gaps this
//!   enum is dead code on the corpus, and it is then the record of *what* was
//!   needed to get there.
//! * [`Sealed`] — a `Thm` whose hypothesis set is empty, checked by the only
//!   constructor. The type-level form of `kernel`'s "`hyps()` obligation": a
//!   `Thm` establishes its conclusion only when `hyps()` is empty.
//!
//! **Gaps propagate monotonically.** Composing anything with a `Gap` yields
//! that `Gap` ([`Ev::and_then`], [`Ev::zip`]). There is no `Dropped` ledger,
//! because nothing is discarded: a consumer either exists and takes the
//! evidence, or the operation is an acceptance gate with no downstream consumer
//! (the `let` rule of §6.3 is the one such case, and it is argued there rather
//! than counted).
//!
//! **`Err` is not `Gap`.** `Err` means the declaration is rejected and must
//! match mini-lean; `Gap` means the declaration is accepted but a derivation is
//! missing, and must reach zero. Conflating them collapses MINI-DESIGN.md §0's
//! two axes into one, which is the mistake the whole design is arranged to
//! avoid.

use crate::expr::Name;
use kernel::Thm;

/// **Which binder congruence a conversion wanted** — the discriminant of
/// [`Gap::BinderCongruence`].
///
/// [`BinderShapes::apply`](crate::kernel::BinderShapes::apply) dispatches on the
/// pair of §6.2 clauses the two sides took, and the five outcomes are not one
/// problem. Four are rules that exist and are unthreaded; the fifth is not a
/// rule at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderRule {
    /// `dprod_ext_n` — two genuine dependent products.
    DProd,
    /// `cond_ext_n` — two `Prop`-valued `∀`s, i.e. conditional singletons.
    Cond,
    /// `lam_ext_n` — two λ graphs.
    Lam,
    /// **The two sides took different clauses**, so no rule relates them: the
    /// sets are different and nothing connects them. Counting this with the
    /// four above is the mistake the discriminant exists to prevent, because it
    /// is not waiting on a wire.
    ///
    /// It carries *which* two, because that is the whole of what a scoper
    /// needs: `Dep` against `Fs` is a codomain that mentions the binder on one
    /// side and not the other, which is a **classification** question and may
    /// not be a missing theorem at all; `Prop` against anything is §6.2's
    /// proof/value split disagreeing across a conversion, which is a different
    /// question again.
    Mismatch(BinderClause, BinderClause),
}

/// Which of §6.2's clauses one side of a binder conversion took.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderClause {
    /// `dprod(q⃗,⟦A⟧)` — a genuine dependent product.
    Dep,
    /// `chi(h⃗,⟦A⟧)` — a `Prop`-valued `∀`.
    Cond,
}

impl BinderClause {
    pub fn tag(self) -> &'static str {
        match self {
            BinderClause::Dep => "dprod",
            BinderClause::Cond => "cond",
        }
    }
}

impl BinderRule {
    /// The ledger's own spelling, used inside [`Gap::BinderCongruence`]'s key.
    pub fn tag(self) -> String {
        match self {
            BinderRule::DProd => "dprod_ext_n".to_string(),
            BinderRule::Cond => "cond_ext_n".to_string(),
            BinderRule::Lam => "lam_ext_n".to_string(),
            BinderRule::Mismatch(a, b) => {
                format!("clauses differ: {} vs {}", a.tag(), b.tag())
            }
        }
    }
}

/// Every way evidence can be missing. Adding a hole means adding a variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Gap {
    /// **One of Lean's own axioms, whose model validation `derived/` does not
    /// have** — reached only once the axiom's *type* has interpreted, so that
    /// the missing thing really is the inhabitation and not the statement.
    ///
    /// Nothing else can get here: `mini::convert::is_standard_axiom` declines
    /// an export that declares an axiom of its own at the frontend, precisely
    /// because a user axiom's inhabitation is not derivable in principle and
    /// therefore is not work. What is left — `Quot.sound`, `propext`,
    /// `Classical.choice` — the set-theoretic model *validates*: a quotient is
    /// a set of equivalence classes, in which `Quot.sound` is a theorem;
    /// `Prop` is `{∅, {•}}`, in which `propext` is; and the kernel already
    /// carries `Thm::ax_choice`. So this is a **library** obligation, and
    /// `Cause::Assumption` — which used to be this variant's axis — has no
    /// occupant left and is gone.
    Axiom(Name),
    /// A constant's interpretation is not in the store at these ground levels.
    NoInterpretation(Name, Vec<u32>),
    /// **`Quot` at `u ≥ 1`** — the equivalence-class construction, which is
    /// `derived/src/quot/`'s and is a different clause from the `Sort 0` one.
    ///
    /// **The level is in the variant, and that is the whole point of the
    /// variant.** The corpus schedules every `Quot`-bearing declaration at
    /// *both* `u = 0` and `u = 1`, at all six exports, so the row is roughly
    /// seven pairs and seven and **neither clause alone closes a single
    /// export**. A reason string without the `u` reports a half-closed row as
    /// untouched, which would make progress on this row unmeasurable.
    ///
    /// Not a `NoInterpretation` on the name, for the reason `Gap::IndexedCtor`
    /// is not either: "absent" is not a reason and this one has one.
    /// `QUOT-MODEL.md` §1.2 is why the two levels are two clauses rather than
    /// one construction at two instantiations — at `Sort 0` the classes reading
    /// is *refutably* wrong (`quot(1,R) = {1} ⊄ 1`), not merely unproved.
    ///
    /// **The primitive is in the variant too, and for the same argument one
    /// level down.** *(It carried the level alone until the `u ≥ 1` formation
    /// clause landed.)* The `u ≥ 1` half is **four** clauses, not one: formation
    /// closed two of the seven pairs' type typings and the `waiting:` row was
    /// bit-identical across it at 7, which is exactly the "half-closed row reads
    /// as untouched" defect the level was added to prevent — measured, at the
    /// next level down, on the first increment.
    Quotient(u32, crate::quot::Prim),
    /// The structure's projection-membership fact.
    StructProj(Name),
    /// Structure eta.
    StructEta(Name),
    /// The unit-like subsingleton lemma.
    UnitLike(Name),
    /// Graph extensionality at a term known to be a set-function — the lemma
    /// MINI-DESIGN.md §10 adds to the backlog.
    FunEta,
    /// **An indexed family whose carrier is not wired**, with *which* carrier.
    ///
    /// The detail is not decoration. `indexed-family(X)` covered three
    /// different problems at once — the class-(S) carrier at `ni ≥ 1`, the
    /// class-(P) truncation over an indexed base, and, until
    /// [`crate::rec_dep`] took it, the indexed *eliminator*. They are owed by
    /// different people and sit on different axes, and a rolled-up label is how
    /// `Acc` sat misfiled as this very variant for the life of the project.
    IndexedFamily(Name, &'static str),
    /// A `Prop`-valued declaration — Carneiro's class (S) or (P). Its
    /// resultant level is not provably nonzero, so the eliminator trichotomy
    /// sends it to §5.3's subsingleton elimination or to the truncation clause,
    /// **never** to a W-type, and neither is wired here yet.
    PropInductive(Name),
    /// The declaration's carrier could be built, but `derived::cumul` cannot
    /// place it in the universe the Lean declaration says it lives in.
    ///
    /// No longer about the *height*: `cumul::DeclUniverse::over_at` takes the
    /// level, so a declaration resident in `Type n` lands in `Uₙ₊₁` for every
    /// `n` the cumulativity table reaches. What is left is the table's own
    /// height and the tag membership's raise to it. **A library gap.**
    IndUniverseHeight(Name, u32),
    /// A constructor with a non-recursive field whose *type* does not land in
    /// `U₁`.
    ///
    /// `cumul::summand_obligations` bridges the per-field obligation, so the
    /// field itself is no longer the problem — but `cumul::sigma_n` and
    /// `cumul::tags` are stated at `U₁` and deliberately not generalised, so a
    /// field resident in `Type n` for `n ≥ 1` has no summand to place. This is
    /// what blocks `Prod` at `Type 1`, and it is *not* the declaration's own
    /// height: the placement of the finished carrier is [`Gap::IndUniverseHeight`]
    /// and is wired.
    IndSummand(Name),
    /// The boundary walk could not express the declaration as a `DeclSpec`,
    /// with the step that refused it. Interpretation scope: each is a shape
    /// the spec's own contract excludes.
    IndSpec(Name, &'static str),
    /// The inductive-translation apparatus itself could not be built over the
    /// interpretation's tower. A mini bug: both halves exist and are supposed
    /// to compose.
    IndApparatus,
    /// A function-typed recursive constructor argument (`Σ(z::γ)` fibre).
    FunTypedRecArg(Name),
    /// The declaration's **recursor**, with what its typing is waiting on and
    /// **which axis that is**.
    ///
    /// The cause is *carried*, not imputed, and that is the correction: this
    /// variant used to map unconditionally to [`Cause::Library`], while
    /// `mini/src/recursor.rs`'s own header said in bold that the class-(S) row
    /// is "wiring, not library". Six pairs sat in the column that says *Fiona
    /// owes a construction* when what they were waiting on was mini wiring one
    /// that exists — the same shape as the `Quot.sound` mislabel, and wrong in
    /// the same direction, reporting the project further behind where the
    /// library is and further ahead where the threading is.
    ///
    /// A single imputed cause cannot be right here because the four routes
    /// genuinely differ: `Eq`'s clause and the class-(T) dependent eliminator
    /// are threading when they decline, a shape this module cannot express is
    /// scope, and a `derived/` construction that does not exist is library.
    /// Whoever writes the decline knows which; nothing downstream can.
    ///
    /// The mini-side wiring is reached — [`crate::recursor`] resolves every
    /// recursor the corpus mentions — so this is no longer "zone B has not got
    /// here". What it now names is a shortfall in `derived/`, and the detail
    /// says which; [`crate::recursor`]'s header is the register.
    ///
    /// The distinction that makes this a *library* gap is that
    /// `⊢ ⟦T.rec.{σ}⟧ ∈ ⟦its Lean type⟧` is a **dependent** obligation —
    /// `∀C ∀s⃗ ∀t ∈ ⟦T p⃗⟧. rec(t) ∈ app(C,t)` — and for a long time nothing in
    /// `derived/` stated it: `GenRecursor` is simply typed, landing in one
    /// target set. `derived::inductive::DepRecursor` does state it, and
    /// [`crate::rec_dep`] wires it, so the class-(T) declarations *with*
    /// constructors no longer reach here. What still does is `Empty`, and the
    /// class-(S) eliminator.
    Recursor(Name, &'static str, Cause),
    /// **One constructor of an indexed family**, with what its membership
    /// could not bridge and which axis that is.
    ///
    /// Its own variant rather than a `NoInterpretation` on the constructor's
    /// name, and that is the whole point of it. `no-interp(RBTree.leaf)` is
    /// `zoneb::stored_or_reason_after`'s **fallback** — "the constant is not in
    /// the store", said without saying why — so it cannot be told apart from a
    /// constant nothing ever tried to build, and nobody can size the work from
    /// it. The two are different states and only the site that declined knows
    /// which: `C2` is what makes these constructors exist, so it is the moment
    /// to make the label say "the constructor path declined for reason R"
    /// rather than "absent".
    ///
    /// The cause is carried for the reason [`Gap::Recursor`]'s is. A missing
    /// bridge in [`crate::ctor_ix`] is threading; the index-type sub-case
    /// nothing in the repository builds is scope.
    IndexedCtor(Name, &'static str, Cause),
    /// **A class-(P) constructor that did not build**, with the reason — the
    /// truncation analogue of [`Gap::IndexedCtor`], and a separate variant for
    /// the same reason that one is separate from [`Gap::IndSpec`]: it is
    /// recorded against the *constructor's* own key and must not take the type
    /// former down with it.
    ///
    /// Always `Cause::Threading`. `derived` owes this path nothing —
    /// `TruncCarrier::over_declaration` computes `tc.ctors` and
    /// `zoneb::build_trunc` used to discard them — so anything reported here is
    /// a wire, and every wire the path needs is in place: `mem` at `mᵢ = 0`,
    /// `trunc_mem` above it, the plain fields' abbreviation bridge and the
    /// recursive fields' proof irrelevance. The variant exists for the shape
    /// checks, which is where a *future* declaration would surface.
    TruncCtor(Name, &'static str),
    /// An iota rule that is not wired to its recursor's own ι theorem yet:
    /// `DepRecursor::iota` for a class-(T) declaration, or
    /// `IndexedDepRecursor`'s — which does not exist — for an indexed one.
    ///
    /// **`Eq.rec` is no longer here, and it was never a missing theorem.**
    /// `thesis.txt:2124` *interprets* the equality recursor, so its stored nest
    /// has the ι right-hand side at its bottom and the certificate is
    /// `Checker::nest_iota`'s β chain. That route has no premise, which is why
    /// it also covers the K-rule.
    ///
    /// **What is left is one shape and it always has a premise.**
    /// `DepRecursor::iota` is `PRE → ∀y⃗∀t⃗. (Hᵢ → …)`, and `PRE` is a fact
    /// about the *use site's own* minors — so what a reduction needs is not the
    /// theorem, which is stored, but `PRE` re-established at whatever terms the
    /// site supplies. See [`Gap::StuckRecursor`] for the outcome that used to
    /// wear this label and is not this at all.
    Iota(Name),
    /// **A recursor whose major premise reduced underneath it, and stayed
    /// stuck.** The expression changed, so the certificate owes a *congruence
    /// over that change* — not a computation rule.
    ///
    /// # Why this is its own variant
    ///
    /// It wore [`Gap::Iota`]'s label and **has never fired**: instrumented over
    /// all 91 exports it mints `0`, against `112` at the constructor match.
    /// Read the zero twice (`MINI-DESIGN.md` §0.5) and it is *unreached*, not
    /// solved — the branch mints unconditionally when its guard holds, so
    /// nothing can have discharged it. One label over two outcomes is the
    /// defect `Gap::BinderCongruence` was split for, and this is the same
    /// defect one module along: a row of ι conversions was evidence about a
    /// computation rule and said nothing whatever about this.
    ///
    /// Nothing is owed behind it. When it first fires, what is owed is a
    /// congruence over the major's own reduction — which `whnf` performs
    /// acceptance-only at that point and does not thread — and that is a
    /// wiring question about the traversal, not a clause of §6.2 and not a
    /// `derived/` construction.
    StuckRecursor(Name),
    /// The skeleton decomposition failed: a subterm mentioning the binder was
    /// not built through `Interp::mk`, so the body cannot be abstracted. A mini
    /// bug rather than a library gap.
    Skeleton,
    /// `body_clause`/`term_clause` could not run, because inference on the
    /// expression failed. On an accepted file this should not happen.
    Classifier,
    /// A `Π`/`λ` congruence between two *differently interpreted* binders, and
    /// **which rule was wanted** — see [`BinderRule`].
    ///
    /// The extensionality lemmas take a discharged family over a scope opened
    /// on `⟦A⟧`, and the recursive body conversion is not threaded through that
    /// scope yet. Threading incompleteness.
    ///
    /// The discriminant is not decoration. This was payload-free while it was
    /// the largest uncertified population in the checker (937 of 988
    /// conversions), so the whole row read as one problem when it spans five
    /// distinct outcomes over four rules and a non-rule. "One problem or
    /// several" is the first question anyone scoping a row asks, and five times
    /// out of five on this project the answer has not been the one the label
    /// suggested.
    BinderCongruence(BinderRule),
    /// A sort above the cumulativity table's height.
    SortTowerHeight,
    /// A composition step (`trans`, `symm`, `congr`, an instantiation) that
    /// did not fit together, tagged with **which** one. Always a mini bug
    /// rather than a library gap: the pieces exist, so a failure here means a
    /// stack was assembled wrongly, and the tag is what makes that findable
    /// instead of merely countable.
    ConvCompose(&'static str),
    /// A transparent constant with no stored defining equation.
    NoDefiningEquation(Name),
    /// The caller had no interpretation for this expression, so there is
    /// nothing to state a conversion or a membership *about*. Carried by the
    /// acceptance-only calls (`is_def_eq`, the shape zone, the `whnf` inside a
    /// K-rule check) whose results have no evidence consumer at all, and by a
    /// step whose endpoints have themselves gapped. Never a library item: it
    /// always propagates from something else, per §0.4.
    NoEndpoint,
    /// The interpretation being taken apart was not built by `Interp::mk`, or
    /// not by the clause the rule expected — a `Π` whose interpretation is an
    /// opaque constant, an application whose interpretation is `•`. Structural,
    /// and always downstream of an absent interpretation.
    NotDecomposable,
    /// The endpoint the caller handed in and the one inference computes for
    /// the same expression are **different terms** — `⟦·⟧` failed to be a
    /// function at this node. Never allowed to pass silently: a conversion
    /// built on it would be a true theorem about the wrong terms, which is the
    /// endpoint-drift bug nanoda's `certify_reduct` has a guard for.
    EndpointDrift,
    /// A `strLit`. Mini keeps the constructor inert, as mini-lean does; the
    /// tutorial corpus contains none (`mini/tests/tutorial.rs` pins that).
    StrLit,
    /// A judgement made in the declaration-shape zone, where levels are the
    /// declaration's own parameters and no §6.2 clause applies. Sanctioned:
    /// the zone's outputs are accept/reject and a syntactic spec, neither of
    /// which has an evidence consumer (MINI-DESIGN.md §9, zone A).
    SymbolicLevel,
}

/// **What kind of work a gap is waiting on** — the axis separation of
/// MINI-DESIGN.md §0, made mechanical.
///
/// A ledger that lumps these together reports the project as further behind on
/// one axis and further ahead on the other. `Scope` is work the design has not
/// reached; `Threading` is work it has reached and left undone; `Library` is a
/// named `derived/` item.
///
/// **There is no `Assumption` axis, and its absence is a decision rather than
/// an omission.** It meant "not derivable in principle, and counting it as
/// debt would misreport it as reachable" — which was the right thing to say
/// about a user-declared axiom. Such an axiom no longer reaches the ledger:
/// `mini::convert::is_standard_axiom` declines the whole export at the
/// frontend, by name and with a reason, because a run that stops at the first
/// missing derivation would otherwise stop at one for ever. The boundary is
/// now enforced where it can be acted on, and a `Cause` that could only be
/// reached by a hole in that boundary is better spelled as its absence than as
/// a row pinned at zero. Everything that still reaches here is work; the only
/// question is whose.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Cause {
    /// **Interpretation scope.** `⟦·⟧` does not reach here yet — inductives,
    /// their projections, symbolic levels. Work the design has not reached.
    Scope,
    /// **Library gap.** A named `derived/` construction that does not exist or
    /// is not general enough (MINI-DESIGN.md §10).
    Library,
    /// **Threading incompleteness.** Every piece exists; they are not wired.
    Threading,
    /// **A mini bug.** A composition that should have fitted did not, or a
    /// term that should have been decomposable was not.
    Bug,
}

impl Gap {
    /// Which axis this gap belongs to.
    pub fn cause(&self) -> Cause {
        match self {
            Gap::NoInterpretation(..)
            | Gap::Quotient(..)
            | Gap::IndexedFamily(..)
            | Gap::PropInductive(_)
            | Gap::IndSpec(..)
            | Gap::FunTypedRecArg(_)
            | Gap::StrLit
            | Gap::SymbolicLevel => Cause::Scope,
            Gap::StructProj(_) | Gap::StructEta(_) | Gap::UnitLike(_) | Gap::FunEta => {
                Cause::Library
            }
            // The `derived` items zone B runs into, all named in
            // MINI-DESIGN.md §10's worklist. `Recursor` joined them when
            // `crate::recursor` landed: the wiring reaches every corpus
            // recursor, so what is left is a construction, not a traversal.
            Gap::IndUniverseHeight(..) | Gap::IndSummand(_) => Cause::Library,
            // Carried, not imputed — see the variant.
            Gap::Recursor(_, _, c) => *c,
            Gap::IndexedCtor(_, _, c) => *c,
            Gap::TruncCtor(..) => Cause::Threading,
            // Lean's own axioms, each validated by the model — see `Gap::Axiom`.
            Gap::Axiom(_) => Cause::Library,
            Gap::IndApparatus => Cause::Bug,
            Gap::SortTowerHeight => Cause::Library,
            Gap::Iota(_)
            | Gap::StuckRecursor(_)
            | Gap::BinderCongruence(_)
            | Gap::NoDefiningEquation(_)
            | Gap::NoEndpoint
            | Gap::NotDecomposable => Cause::Threading,
            Gap::Skeleton | Gap::Classifier | Gap::EndpointDrift | Gap::ConvCompose(_) => Cause::Bug,
        }
    }
}

/// Evidence, or a named absence.
#[derive(Debug, Clone)]
pub enum Ev {
    Proved(Thm),
    Gap(Gap),
}

impl Ev {
    /// **Mint a gap**, remembering where it was minted.
    ///
    /// The only difference from writing `Ev::Gap(g)` is the bookkeeping:
    /// [`crate::blocker`] wants the source location that gave up, and
    /// `#[track_caller]` is the way to get it without a parameter at every
    /// call. Unarmed — which is every run that is not looking for the first
    /// blocker — this is one thread-local `bool` read, which matters because
    /// the failure branch of `whnf` is taken millions of times per corpus run.
    ///
    /// **Re-wrapping is not minting.** `and_then`, `zip` and the scope's
    /// discharge propagate a gap they were handed and deliberately do *not*
    /// come through here: recording them would put the propagation path in
    /// the trail and bury the site that chose the reason.
    #[track_caller]
    pub fn missing(g: Gap) -> Ev {
        if crate::blocker::is_armed() {
            crate::blocker::record(&g, std::panic::Location::caller());
        }
        Ev::Gap(g)
    }

    pub fn thm(&self) -> Option<&Thm> {
        match self {
            Ev::Proved(t) => Some(t),
            Ev::Gap(_) => None,
        }
    }

    pub fn gap(&self) -> Option<&Gap> {
        match self {
            Ev::Proved(_) => None,
            Ev::Gap(g) => Some(g),
        }
    }

    pub fn is_proved(&self) -> bool { matches!(self, Ev::Proved(_)) }

    /// The **set** side of a membership conclusion.
    ///
    /// This is where a `Typing` keeps `⟦ty⟧`: the evidence concludes
    /// `mem(tm, ⟦ty⟧)`, so the type's interpretation is read straight off it at
    /// no cost. On a `Gap` it is unavailable, which is correct rather than
    /// awkward — a step whose endpoints have no interpretation has no
    /// certificate to build either (MINI-DESIGN.md §6.4).
    pub fn mem_set(&self) -> Option<kernel::Term> {
        self.thm()?.concl().as_mem().map(|(_, s)| s)
    }

    /// The **right** endpoint of an equality conclusion — where a conversion
    /// arrived, as a term.
    pub fn eq_rhs(&self) -> Option<kernel::Term> { self.thm()?.concl().as_eq().map(|(_, b)| b) }

    /// The gap to report for a *derived* result: this evidence's own reason if
    /// it has one, else the given fallback. §0.4's rule in one function — a
    /// result that did not interpret carries the reason of the sub-result that
    /// stopped it, never the failing clause's own label.
    pub fn reason(&self, fallback: Gap) -> Gap { self.gap().cloned().unwrap_or(fallback) }

    /// Compose: run `f` on the theorem, or propagate the gap unchanged.
    pub fn and_then(self, f: impl FnOnce(Thm) -> Ev) -> Ev {
        match self {
            Ev::Proved(t) => f(t),
            Ev::Gap(g) => Ev::Gap(g),
        }
    }

    /// Compose two pieces of evidence. The **left** gap wins, so the reported
    /// reason is the first thing that was missing rather than the last.
    pub fn zip(self, other: Ev, f: impl FnOnce(Thm, Thm) -> Ev) -> Ev {
        match (self, other) {
            (Ev::Proved(a), Ev::Proved(b)) => f(a, b),
            (Ev::Gap(g), _) => Ev::Gap(g),
            (_, Ev::Gap(g)) => Ev::Gap(g),
        }
    }
}

/// A theorem with no hypotheses. **The only constructor checks it.**
///
/// Everything that outlives the declaration currently being checked — the
/// interpretation store, the per-`(name, σ)` typings, the defining equations,
/// the iota rules, the final verdict — passes through here. Mini has no
/// expression-level caches at all, so the cache-imports-`Γ` hazard that
/// motivated nanoda's `is_unconditional` guards is structurally absent; the
/// funnel enforces it anyway, because "no caches" is a fact about today's mini
/// rather than a property of the repo.
///
/// By the scope invariant I2, at top level no scopes are open, so `new` cannot
/// fail on a correctly threaded run. A failure is therefore a threading bug
/// surfaced at the funnel, which is where it should surface.
#[derive(Debug, Clone)]
pub struct Sealed(Thm);

impl Sealed {
    /// `Err(t)` hands the offending theorem back, so the caller can report
    /// *which* hypotheses escaped rather than only that some did.
    pub fn new(t: Thm) -> Result<Sealed, Thm> {
        if t.hyps().is_empty() {
            Ok(Sealed(t))
        } else {
            Err(t)
        }
    }

    pub fn thm(&self) -> &Thm { &self.0 }

    pub fn into_thm(self) -> Thm { self.0 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::{Env, Formula, Term};

    fn atom(env: &mut Env) -> Formula {
        let a = env.declare(0);
        let b = env.declare(0);
        Formula::mem(Term::apply(a, vec![]), Term::apply(b, vec![]))
    }

    #[test]
    fn sealed_refuses_a_hypothetical_theorem() {
        let mut env = Env::new();
        let phi = atom(&mut env);
        // `Thm::assume` lives in `crate::scope`; this is the same shape built
        // through it, so the test does not add a second introduction point.
        let hypothetical = crate::scope::test_support::assume(phi.clone());
        assert!(!hypothetical.hyps().is_empty());
        assert!(Sealed::new(hypothetical).is_err(), "Sealed accepted a theorem with hypotheses");

        let unconditional = kernel::Thm::eq_refl(Term::apply(env.declare(0), vec![]));
        assert!(Sealed::new(unconditional).is_ok());
    }

    #[test]
    fn gaps_propagate_and_the_left_one_wins() {
        let mut env = Env::new();
        let t = kernel::Thm::eq_refl(Term::apply(env.declare(0), vec![]));
        let proved = Ev::Proved(t.clone());
        let g1 = Ev::missing(Gap::FunEta);
        let g2 = Ev::missing(Gap::StrLit);

        assert!(proved.clone().and_then(Ev::Proved).is_proved());
        assert_eq!(g1.clone().and_then(Ev::Proved).gap(), Some(&Gap::FunEta));
        assert_eq!(
            g1.clone().zip(g2.clone(), |a, _| Ev::Proved(a)).gap(),
            Some(&Gap::FunEta),
            "the left gap must win, so the reported reason is the first thing missing"
        );
        assert_eq!(proved.zip(g2, |a, _| Ev::Proved(a)).gap(), Some(&Gap::StrLit));
    }
}
