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

pub mod term;
pub mod thm;

pub use term::{FnSym, Formula, FreeVar, Term};
pub use thm::{Env, Thm};

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
    ///
    /// The checker instantiates this with its interned expression id. For a
    /// hash-consed representation that id is small and `Copy`, which is what
    /// makes passing terms around by value affordable.
    type Term: Copy + Eq;

    /// A certificate witnessing a definitional-equality judgement `a ≡ b`.
    ///
    /// In an LCF discipline the certificate is opaque to the checker: it can
    /// only be produced by these combinators and consumed by the backend.
    type Cert: Clone;

    /// Whatever the backend needs in order to *read* a [`Certifier::Term`].
    ///
    /// A `Term` is only an index; interpreting it as a set-theoretic formula
    /// requires the checker's interning arena. Rather than teach the kernel
    /// what that arena is — which would put Lean's syntax in the TCB — the
    /// backend names its own requirement here and the checker supplies it at
    /// each call.
    ///
    /// This is why the methods take `&mut self` and a context: a real backend
    /// builds a genuine [`Thm`] *eagerly* at every step. It cannot defer by
    /// recording a lazy derivation tree, because storing derivations is exactly
    /// what the design forbids (see the crate docs on memory being
    /// O(live theorems), not O(proof size)).
    type Ctx: ?Sized;

    /// `a ≡ a`.
    fn refl(&mut self, ctx: &mut Self::Ctx, a: Self::Term) -> Self::Cert;

    /// Conclude `a ≡ b` from a certificate for `b ≡ a`.
    ///
    /// `a` and `b` are the endpoints of the **conclusion**, not of the premise;
    /// the premise runs the other way. They are passed for the reason spelled
    /// out on [`Certifier::lam_cong`]: a rule handed only a sub-certificate
    /// cannot check what it is being asked to prove. Symmetry looks like the
    /// safest rule there is — it merely turns an equation around — but the
    /// equation it is handed need not be the one the checker claimed, and
    /// without `a` and `b` the backend has no way to notice.
    fn symm(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, c: Self::Cert) -> Self::Cert;

    /// Conclude `a ≡ b` from `a ≡ m` and `m ≡ b`.
    ///
    /// `a` and `b` are the endpoints the composite is claimed to relate. The
    /// midpoint `m` is deliberately *not* a parameter: it is whatever the two
    /// premises agree on, and if they do not agree the rule fails — that is
    /// transitivity's own business. What the rule cannot discover for itself is
    /// the claim, so, as for [`Certifier::lam_cong`], it is handed it. A
    /// transitivity that composed two certificates about some *other* pair of
    /// terms and returned the result as a proof of `a ≡ b` would be exactly the
    /// silent lie this trait exists to make impossible.
    fn trans(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, ab: Self::Cert, bc: Self::Cert) -> Self::Cert;

    /// Congruence for application: from `f ≡ f'` and `x ≡ x'` conclude `a ≡ b`,
    /// where `a` is `f x` and `b` is `f' x'`.
    ///
    /// The two applications are passed explicitly for the reason given on
    /// [`Certifier::lam_cong`]. Without them this rule could only assume its
    /// sub-certificates were about the function and argument positions of the
    /// terms in question; a certificate about something else propagated upwards
    /// unchallenged, and the rules above — which do check — were left reporting
    /// a gap for a claim that had been bent out of shape several levels below.
    /// The backend measures how often that happened, and the answer is worth
    /// recording: on the checker's own corpora it is rare (single digits), and
    /// rarer still for [`Certifier::trans`] and [`Certifier::symm`], which never
    /// missed at all. A rule is not given its conclusion because the failure is
    /// frequent; it is given it because a rule that cannot check is one whose
    /// output nobody can audit.
    fn app_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, f: Self::Cert, arg: Self::Cert) -> Self::Cert;

    /// Congruence for `λ`: from `t ≡ t'` (domains) and `b ≡ b'` (bodies,
    /// compared under the binder) conclude `a ≡ b`, where `a` and `b` are the
    /// two lambdas themselves.
    ///
    /// The two terms are passed explicitly, and that is not incidental: without
    /// them a backend receives only sub-certificates and **cannot check what it
    /// is being asked to prove**. A rule that cannot compare its result against
    /// the claim can only guess, and a wrong guess returned as a proof is worse
    /// than an honest gap. Every rule here that concludes something about two
    /// specific terms is given those terms for exactly this reason.
    fn lam_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, dom: Self::Cert, body: Self::Cert) -> Self::Cert;

    /// Congruence for `∀`/`Π`: as [`Certifier::lam_cong`] but for the pi former.
    fn pi_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, dom: Self::Cert, body: Self::Cert) -> Self::Cert;

    /// One beta step: `(λx:t. b) a ≡ b[a/x]`. The checker passes the redex and
    /// the already-computed reduct.
    fn beta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> Self::Cert;

    /// One zeta step: `let x := v; b ≡ b[v/x]`.
    fn zeta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> Self::Cert;

    /// One delta step: unfolding a definition to its value.
    fn delta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> Self::Cert;

    /// One eta step relating `a` and `b` where one is the eta-expansion of the
    /// other (`λx. f x ≡ f`).
    fn eta(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term) -> Self::Cert;

    /// `Sort u ≡ Sort v` when the universe levels `u` and `v` are equal. Sort
    /// (and, with levels, const) equality is where the level algebra enters the
    /// definitional-equality certificate.
    fn sort(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term) -> Self::Cert;

    /// Two constant occurrences `c.{us} ≡ c.{vs}` with pointwise-equal universe
    /// levels.
    fn const_eq(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term) -> Self::Cert;

    /// An equality the checker believes but cannot yet justify to the backend.
    ///
    /// **This is a hole in the proof.** It exists so that certificate plumbing
    /// can be introduced incrementally across a 1300-line type checker without
    /// a flag day, and so that the places still lacking a real justification are
    /// *named in the type system* rather than hidden behind a `bool`.
    ///
    /// `reason` is a static string identifying the call site. A real backend is
    /// expected to either produce a genuine derivation or refuse; the count of
    /// surviving `admit` sites is the honest measure of how far the milestone-3
    /// work has to go, and it must reach zero before the TG backend can be
    /// trusted. `checker/src/certify.rs` tracks the live sites.
    fn admit(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, reason: &'static str) -> Self::Cert;
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
/// It is generic over the context type as well as the term type so that a
/// client can drop it in wherever the real backend will eventually go, without
/// the surrounding code having to change shape — the checker uses
/// `NullCertifier<ExprPtr, TcCtx>` and passes its real arena at every call,
/// exactly as it will to the TG backend.
#[cfg(feature = "null-certifier")]
#[derive(Debug)]
pub struct NullCertifier<T, X: ?Sized>(PhantomData<fn() -> (T, *const X)>);

#[cfg(feature = "null-certifier")]
impl<T, X: ?Sized> NullCertifier<T, X> {
    /// Create the null backend.
    pub fn new() -> Self {
        NullCertifier(PhantomData)
    }
}

#[cfg(feature = "null-certifier")]
impl<T, X: ?Sized> Default for NullCertifier<T, X> {
    fn default() -> Self { Self::new() }
}

#[cfg(feature = "null-certifier")]
impl<T, X: ?Sized> Clone for NullCertifier<T, X> {
    fn clone(&self) -> Self { Self::new() }
}

#[cfg(feature = "null-certifier")]
impl<T: Copy + Eq, X: ?Sized> Certifier for NullCertifier<T, X> {
    type Term = T;
    type Cert = ();
    type Ctx = X;

    fn refl(&mut self, _: &mut X, _a: T) {}
    fn symm(&mut self, _: &mut X, _a: T, _b: T, _c: ()) {}
    fn trans(&mut self, _: &mut X, _a: T, _b: T, _ab: (), _bc: ()) {}
    fn app_cong(&mut self, _: &mut X, _a: T, _b: T, _f: (), _arg: ()) {}
    fn lam_cong(&mut self, _: &mut X, _a: T, _b: T, _dom: (), _body: ()) {}
    fn pi_cong(&mut self, _: &mut X, _a: T, _b: T, _dom: (), _body: ()) {}
    fn beta(&mut self, _: &mut X, _redex: T, _reduct: T) {}
    fn zeta(&mut self, _: &mut X, _redex: T, _reduct: T) {}
    fn delta(&mut self, _: &mut X, _redex: T, _reduct: T) {}
    fn eta(&mut self, _: &mut X, _a: T, _b: T) {}
    fn sort(&mut self, _: &mut X, _a: T, _b: T) {}
    fn const_eq(&mut self, _: &mut X, _a: T, _b: T) {}
    fn admit(&mut self, _: &mut X, _a: T, _b: T, _reason: &'static str) {}
}
