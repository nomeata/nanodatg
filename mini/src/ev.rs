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
    /// `⟦T⟧ ∈ ⟦Type n⟧` for a general-path inductive: blocked on `derived`'s
    /// cumulativity generalisation past its `B(a) ∈ ω` demand.
    IndInUniverse(Name),
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
    IndexedFamily(Name),
    /// A function-typed recursive constructor argument (`Σ(z::γ)` fibre).
    FunTypedRecArg(Name),
    /// An iota rule that is not wired to `GenRecursor` yet.
    Iota(Name),
    /// The skeleton decomposition failed: a subterm mentioning the binder was
    /// not built through `Interp::mk`, so the body cannot be abstracted. A mini
    /// bug rather than a library gap.
    Skeleton,
    /// `body_clause`/`term_clause` could not run, because inference on the
    /// expression failed. On an accepted file this should not happen.
    Classifier,
    /// A composition step (`trans`, `symm`, `congr`, an instantiation) that
    /// did not fit together. Always a mini bug rather than a library gap: the
    /// pieces exist, so a `None` here means a stack was assembled wrongly.
    ConvCompose,
    /// A transparent constant with no stored defining equation.
    NoDefiningEquation(Name),
    /// A `strLit`. Mini keeps the constructor inert, as mini-lean does; the
    /// tutorial corpus contains none (`mini/tests/tutorial.rs` pins that).
    StrLit,
    /// A judgement made in the declaration-shape zone, where levels are the
    /// declaration's own parameters and no §6.2 clause applies. Sanctioned:
    /// the zone's outputs are accept/reject and a syntactic spec, neither of
    /// which has an evidence consumer (MINI-DESIGN.md §9, zone A).
    SymbolicLevel,
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
