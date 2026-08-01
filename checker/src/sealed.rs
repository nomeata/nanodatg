//! The persistence funnel: a `Thm` that may outlive the derivation that built it.
//!
//! # Interface
//!
//! * [`Sealed`] — a `kernel::Thm` whose hypothesis set is empty, **checked by
//!   the only constructor**. The type-level form of the kernel's "`hyps()`
//!   obligation": a `Thm` establishes its conclusion only when `hyps()` is
//!   empty, so anything read back under a key that does not mention `Γ` has to
//!   have no `Γ`.
//! * [`Sealed::seal`] — the memo-shaped constructor, `Option<Thm> → Option<Sealed>`.
//!
//! # Why a type and not another predicate
//!
//! `certify::is_unconditional` and `certify::hypothesis_free` already ask this
//! question, and they are the right shape for what they guard: a
//! [`crate::tg::TgCert`] in flight, where the answer decides whether a *cache*
//! may keep a copy. But a predicate has to be *called*, and the way a store
//! acquires an unchecked theorem is that somebody adds a store, or an insertion
//! point, and does not call it. That is how `ci/check-boundary.sh` rule 6 came
//! to be load-bearing: it banned hypotheses outright rather than making the
//! stores refuse them, so the stores never learned to.
//!
//! [`Sealed`] moves the question into the value's type. `Shared`'s cross-
//! declaration theorem stores hold `Sealed`, so a new entry does not compile
//! until its author has said what happens to a hypothetical theorem, and the
//! answer that costs nothing — [`Sealed::seal`], which declines it — is the one
//! that fails closed.
//!
//! # What it covers, and what it deliberately does not
//!
//! **Covers:** every `Thm` in `tg::Shared` — the per-thread stores that hand a
//! theorem back in a *later declaration* than the one that derived it. Those
//! are keyed by interpreted terms and names, never by a hypothesis set, so a
//! hypothetical entry would be re-asserted silently at the point of use. This
//! is the hazard `certify::is_unconditional`'s doc describes, closed by
//! construction rather than by remembering to ask.
//!
//! **Does not cover:**
//!
//! * **Certificates in flight.** [`crate::tg::TgCert`] still carries a bare
//!   `Thm`, guarded at the two caches that keep one by
//!   `certify::is_unconditional` (the union-find edges, `TcCache::infer_cache_*`)
//!   and `certify::hypothesis_free` (`reduct::Trace::cert`). Sealing the
//!   certificate type itself was considered and **rejected**: threading kernel
//!   hypotheses through `whnf`/`def_eq` is the point of the evidence work that
//!   follows this, and a `TgCert` that cannot hold a hypothetical theorem would
//!   forbid exactly that. The rule is *stores*, not *values*.
//! * **Per-backend memos**, e.g. `TgBackend::has_types`, `TgBackend::ind_syms`.
//!   They live and die inside one declaration. `has_type_a`'s single-exit guard
//!   nevertheless reads `hyps()` alongside the conclusion, because a memo keyed
//!   on `(expr, type, assumptions)` does not mention `Γ` either, and inside one
//!   declaration is exactly where an open binder scope would put something there.
//! * **`derived/`'s own apparatus structs.** Their house rule is the predicate
//!   form — every public entry checks `hyps().is_empty()` as well as pinning its
//!   conclusion, via `derived::establishes` and `derived::all_unconditional`.
//!
//! By construction nothing in `checker/` builds a hypothetical `Thm` today
//! ([`crate::scope`] is the only module that could, and has no caller yet), so
//! every `Sealed::new` in the crate succeeds and this module is a no-op on every
//! measured number. That is the point: it turns a property of today's callers
//! into a property of the code, and it fails closed as callers are added.

use kernel::{Formula, Thm};

/// A theorem with no hypotheses. **The only constructor checks it.**
///
/// There is no `From<Thm>`, no public field and no second constructor: the two
/// entry points are [`Sealed::new`] and [`Sealed::seal`], and both go through
/// the same test.
#[derive(Debug, Clone)]
pub struct Sealed(Thm);

impl Sealed {
    /// `Err(t)` hands the offending theorem back, so a caller that wants to
    /// report *which* hypotheses escaped can, rather than only that some did.
    pub fn new(t: Thm) -> Result<Sealed, Thm> {
        if t.hyps().is_empty() {
            Ok(Sealed(t))
        } else {
            Err(t)
        }
    }

    /// The memo-shaped constructor: a derivation that failed and a derivation
    /// that carries hypotheses are both "nothing this store can hand back".
    ///
    /// The two are deliberately conflated. A `HashMap<K, Option<Sealed>>` entry
    /// reads "the shareable answer for `K`", and `None` records that there is
    /// none — whether because the derivation did not go through, or because it
    /// went through only under assumptions that this key does not carry. The
    /// consequence of the conflation is that a hypothetical derivation is not
    /// retried for a later declaration, i.e. a *gap*; it is never a claim.
    pub fn seal(t: Option<Thm>) -> Option<Sealed> { t.and_then(|t| Sealed::new(t).ok()) }

    /// The theorem. Sound to read as establishing its conclusion outright,
    /// which is the whole content of this type.
    pub fn thm(&self) -> &Thm { &self.0 }

    /// The theorem, by value.
    pub fn into_thm(self) -> Thm { self.0 }

    /// The conclusion — safe to compare against a wanted formula without a
    /// second `hyps()` read, unlike a bare `Thm`.
    pub fn concl(&self) -> &Formula { self.0.concl() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::{Env, Term};

    fn atom(env: &mut Env) -> Formula {
        let a = env.declare(0);
        let b = env.declare(0);
        Formula::mem(Term::apply(a, vec![]), Term::apply(b, vec![]))
    }

    #[test]
    fn sealed_refuses_a_hypothetical_theorem() {
        let mut env = Env::new();
        let phi = atom(&mut env);
        // `Thm::assume` lives in `crate::scope`; going through it keeps the
        // single-introduction-point invariant a one-file property.
        let hypothetical = crate::scope::test_support::assume(phi);
        assert!(!hypothetical.hyps().is_empty());
        assert!(Sealed::new(hypothetical.clone()).is_err(), "Sealed accepted a theorem with hypotheses");
        assert!(Sealed::seal(Some(hypothetical)).is_none(), "seal accepted a theorem with hypotheses");

        let unconditional = Thm::eq_refl(Term::apply(env.declare(0), vec![]));
        let sealed = Sealed::new(unconditional.clone()).expect("an unconditional theorem seals");
        assert_eq!(sealed.concl(), unconditional.concl());
        assert!(Sealed::seal(Some(unconditional)).is_some());
        assert!(Sealed::seal(None).is_none(), "a failed derivation is not a shareable answer");
    }
}
