//! # `kernel` — the trusted computing base
//!
//! This crate is the **only** component that must be correct for the whole
//! system to be sound. The threat model (see `CLAUDE.md`) is a single one: a
//! bug in Lean's kernel lets someone derive `False`. Everything outside this
//! crate — the parser, the Lean type checker, the interpretation into set
//! theory — is *untrusted*. A bug there produces a *rejection*, never a false
//! theorem.
//!
//! ## What lives here
//!
//! In the final system this crate is a small LCF-style kernel for
//! Tarski–Grothendieck set theory: an opaque [`Thm`] whose only constructors
//! are the sound inference rules, so an ill-formed proof cannot be expressed.
//! That kernel arrives in milestone 3.
//!
//! In milestone 1 the trusted surface is just two things:
//!
//! * the [`Certifier`] trait — the *proof-backend boundary*. Every place in the
//!   untrusted checker that concludes "these two Lean terms are definitionally
//!   equal" must obtain a [`Certifier::Cert`] explaining *why*. This is what
//!   makes the eventual set-theoretic backend a drop-in: the checker already
//!   threads a certificate through every definitional-equality conclusion.
//! * [`NullCertifier`] — the milestone-1 backend whose certificate is `()`. It
//!   makes the checker behave like an ordinary trusted checker (à la nanoda)
//!   while we build the real backend.
//!
//! ## Boundary rules (enforced in CI, see `ci/check-boundary.sh`)
//!
//! * No `unsafe` anywhere. This is enforced at compile time by the crate-level
//!   `#![forbid(unsafe_code)]` below, *and* by the CI grep.
//! * No external crate dependencies (one sanctioned future exception: a vetted
//!   bignum crate for native arithmetic in milestone 4).
//! * `Thm`'s fields are private and it has no public constructor.
//! * No I/O, no serialization, no printing of derivations.

// The kernel must never contain `unsafe`. Enforced by the compiler, not just by
// a grep over the source.
#![forbid(unsafe_code)]
// The kernel is dependency-free and must not silently pull in `std` conveniences
// that would complicate an eventual audit; `core`/`alloc` is all it needs. We do
// use `std` for `HashMap` in later milestones, so this stays as documentation of
// intent rather than `#![no_std]` for now.
#![deny(missing_docs)]

use core::marker::PhantomData;

/// A proof backend for definitional-equality (and, later, typing) judgements
/// about **Lean** terms.
///
/// The trait is generic over the term representation ([`Certifier::Term`]) so
/// that this trusted crate needs no knowledge of the untrusted checker's `Expr`
/// type. The checker instantiates `Term` with its interned expression id; the
/// real set-theoretic backend (milestone 3) will hold whatever context it needs
/// (the interner, the interpretation tables) inside the implementing struct and
/// produce genuine [`Thm`]-backed certificates.
///
/// ## Design obligation
///
/// Every method returns a certificate *value*. Certificates are threaded
/// through the checker, never conjured as phantom markers. If any code path in
/// the checker can conclude "definitionally equal" without holding a `Cert`,
/// the design is wrong — that is the invariant this trait exists to force.
///
/// The combinators below are exactly those the milestone-1 definitional
/// equality procedure needs: reflexivity, the equivalence closure, congruence
/// for each expression former, one-step beta and eta, and equality of two
/// sorts whose universe levels are equal. Delta (definition unfolding) and the
/// rest arrive with their milestones.
pub trait Certifier {
    /// The untrusted term representation these judgements are about.
    type Term: Copy + Eq;
    /// A certificate witnessing a definitional-equality judgement `a ≡ b`.
    ///
    /// In an LCF discipline the certificate is opaque to the checker: it can
    /// only be produced by these combinators and consumed by the backend.
    type Cert: Clone;

    /// `a ≡ a`.
    fn refl(&self, a: Self::Term) -> Self::Cert;

    /// From `a ≡ b` conclude `b ≡ a`.
    fn symm(&self, c: Self::Cert) -> Self::Cert;

    /// From `a ≡ b` and `b ≡ c` conclude `a ≡ c`.
    fn trans(&self, ab: Self::Cert, bc: Self::Cert) -> Self::Cert;

    /// Congruence for application: from `f ≡ f'` and `a ≡ a'` conclude
    /// `f a ≡ f' a'`.
    fn app_cong(&self, f: Self::Cert, a: Self::Cert) -> Self::Cert;

    /// Congruence for `λ`: from `t ≡ t'` (domains) and `b ≡ b'` (bodies,
    /// compared under the binder) conclude `(λ_:t. b) ≡ (λ_:t'. b')`.
    fn lam_cong(&self, dom: Self::Cert, body: Self::Cert) -> Self::Cert;

    /// Congruence for `∀`/`Π`: as [`Certifier::lam_cong`] but for the pi former.
    fn pi_cong(&self, dom: Self::Cert, body: Self::Cert) -> Self::Cert;

    /// One beta step: `(λx:t. b) a ≡ b[a/x]`. The checker passes the redex and
    /// the already-computed reduct.
    fn beta(&self, redex: Self::Term, reduct: Self::Term) -> Self::Cert;

    /// One eta step relating `a` and `b` where one is the eta-expansion of the
    /// other (`λx. f x ≡ f`).
    fn eta(&self, a: Self::Term, b: Self::Term) -> Self::Cert;

    /// `Sort u ≡ Sort v` when the universe levels `u` and `v` are equal. Sort
    /// (and, with levels, const) equality is where the level algebra enters the
    /// definitional-equality certificate.
    fn sort(&self, a: Self::Term, b: Self::Term) -> Self::Cert;

    /// Two constant occurrences `c.{us} ≡ c.{vs}` with pointwise-equal universe
    /// levels.
    fn const_eq(&self, a: Self::Term, b: Self::Term) -> Self::Cert;
}

/// The milestone-1 proof backend: certificates carry no information (`Cert =
/// ()`), so the checker degenerates to an ordinary trusted type checker.
///
/// It is generic over the term type only so that it satisfies [`Certifier`];
/// the [`PhantomData`] records that choice without storing anything.
///
/// **Milestone 3 obligation:** once the real backend exists, `NullCertifier`
/// must be unreachable in a release build. It currently lives behind the
/// default-on `null-certifier` cargo feature so that gate is a one-line change
/// (drop it from `default`, switch callers to `#[cfg(test)]`).
#[cfg(feature = "null-certifier")]
#[derive(Debug, Default, Clone, Copy)]
pub struct NullCertifier<T>(PhantomData<T>);

#[cfg(feature = "null-certifier")]
impl<T> NullCertifier<T> {
    /// Create the null backend.
    pub fn new() -> Self {
        NullCertifier(PhantomData)
    }
}

#[cfg(feature = "null-certifier")]
impl<T: Copy + Eq> Certifier for NullCertifier<T> {
    type Term = T;
    type Cert = ();

    fn refl(&self, _a: T) {}
    fn symm(&self, _c: ()) {}
    fn trans(&self, _ab: (), _bc: ()) {}
    fn app_cong(&self, _f: (), _a: ()) {}
    fn lam_cong(&self, _dom: (), _body: ()) {}
    fn pi_cong(&self, _dom: (), _body: ()) {}
    fn beta(&self, _redex: T, _reduct: T) {}
    fn eta(&self, _a: T, _b: T) {}
    fn sort(&self, _a: T, _b: T) {}
    fn const_eq(&self, _a: T, _b: T) {}
}
