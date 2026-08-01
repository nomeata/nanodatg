//! Evidence, or a named absence (MINI-DESIGN.md §5), and the persistence
//! funnel (§4.3).
//!
//! # Interface
//!
//! * [`Ev`] — `Proved(Thm)` or `Gap(Gap)`. **No third state**: there is no
//!   retry, no "admitted for now", and no search that might succeed later.
//! * [`Gap`] — every way evidence can be missing, as an enum, so that a new
//!   hole cannot be introduced without naming it. At 91-of-91-at-zero-gaps this
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

/// Every way evidence can be missing. Adding a hole means adding a variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Gap {
    /// An axiom's inhabitation is a model assumption, not a derivation.
    Axiom(Name),
    /// A constant's interpretation is not in the store at these ground levels.
    NoInterpretation(Name, Vec<u32>),
    /// The structure's projection-membership fact.
    StructProj(Name),
    /// Structure eta.
    StructEta(Name),
    /// The unit-like subsingleton lemma.
    UnitLike(Name),
    /// Graph extensionality at a term known to be a set-function — the lemma
    /// MINI-DESIGN.md §10 adds to the backlog.
    FunEta,
    /// An indexed family, which `derived::inductive::DeclSpec` cannot express.
    /// `derived::inductive::family` builds one; the mini-side wiring does not
    /// reach it yet.
    IndexedFamily(Name),
    /// A `Prop`-valued declaration — Carneiro's class (S) or (P). Its
    /// resultant level is not provably nonzero, so the eliminator trichotomy
    /// sends it to §5.3's subsingleton elimination or to the truncation clause,
    /// **never** to a W-type, and neither is wired here yet.
    PropInductive(Name),
    /// The declaration's carrier could be built, but `derived::cumul` cannot
    /// place it in the universe the Lean declaration says it lives in.
    /// `derived::cumul::Chain` pins `U₁`, so a declaration resident in
    /// `Type n` for `n ≥ 1` — or any `σ` that raises one there — has nowhere
    /// to land. **A library gap**, and the one MINI-DESIGN.md §10 names.
    IndUniverseHeight(Name, u32),
    /// A constructor with a non-recursive field: `⊢ Aᵢ ∈ U₁` then needs
    /// `derived::cumul::sigma_n`'s per-field obligations rather than the
    /// closed route, and that wiring is not built.
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
    /// The declaration's **recursor** interpretation. The carrier and the
    /// constructors are wired; `⟦T.rec⟧` additionally needs the currying nest
    /// over `derived::inductive::GenRecursor`, the choice of target set, and
    /// the pointwise bridging of `HYP` — MINI-DESIGN.md §9 zone B steps 2–3,
    /// which the mini-side wiring does not reach.
    Recursor(Name),
    /// An iota rule that is not wired to `GenRecursor` yet.
    Iota(Name),
    /// The skeleton decomposition failed: a subterm mentioning the binder was
    /// not built through `Interp::mk`, so the body cannot be abstracted. A mini
    /// bug rather than a library gap.
    Skeleton,
    /// `body_clause`/`term_clause` could not run, because inference on the
    /// expression failed. On an accepted file this should not happen.
    Classifier,
    /// A `Π`/`λ` congruence between two *differently interpreted* binders:
    /// `dprod_ext_n` / `cond_ext_n` / `lam_ext_n` take a discharged family over
    /// a scope opened on `⟦A⟧`, and the recursive body conversion is not
    /// threaded through that scope yet. Threading incompleteness.
    BinderCongruence,
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
/// named `derived/` item; `Assumption` is not work at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Cause {
    /// **Interpretation scope.** `⟦·⟧` does not reach here yet — inductives,
    /// their projections, symbolic levels. Work the design has not reached.
    Scope,
    /// **Library gap.** A named `derived/` construction that does not exist or
    /// is not general enough (MINI-DESIGN.md §10).
    Library,
    /// **Threading incompleteness.** Every piece exists; they are not wired.
    Threading,
    /// **A model assumption.** An axiom's inhabitation is not derivable, and
    /// counting it as debt would misreport it as reachable.
    Assumption,
    /// **A mini bug.** A composition that should have fitted did not, or a
    /// term that should have been decomposable was not.
    Bug,
}

impl Gap {
    /// Which axis this gap belongs to.
    pub fn cause(&self) -> Cause {
        match self {
            Gap::Axiom(_) => Cause::Assumption,
            Gap::NoInterpretation(..)
            | Gap::IndexedFamily(_)
            | Gap::PropInductive(_)
            | Gap::Recursor(_)
            | Gap::IndSpec(..)
            | Gap::FunTypedRecArg(_)
            | Gap::StrLit
            | Gap::SymbolicLevel => Cause::Scope,
            Gap::StructProj(_) | Gap::StructEta(_) | Gap::UnitLike(_) | Gap::FunEta => {
                Cause::Library
            }
            // The two `derived` items zone B runs into first, and both are
            // named in MINI-DESIGN.md §10's worklist.
            Gap::IndUniverseHeight(..) | Gap::IndSummand(_) => Cause::Library,
            Gap::IndApparatus => Cause::Bug,
            Gap::SortTowerHeight => Cause::Library,
            Gap::Iota(_)
            | Gap::BinderCongruence
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
        let g1 = Ev::Gap(Gap::FunEta);
        let g2 = Ev::Gap(Gap::StrLit);

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
