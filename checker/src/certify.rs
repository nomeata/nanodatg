//! The proof-backend boundary: the [`Certifier`] trait, the null backend that
//! implements it trivially, selection of the active backend, and the result
//! type that carries certificates out of definitional-equality checks.
//!
//! # Why the boundary lives here and not in the kernel
//!
//! [`Certifier`] is an *interface*, not a rule. It constructs no
//! [`kernel::Thm`], no method of it mentions a kernel type, and adding a method
//! to it adds no proving power — a backend can still only reach a `Thm` through
//! the kernel's primitive rules. So it is not part of the trusted computing
//! base, and keeping it out of `kernel/` leaves that crate exporting nothing but
//! the type theory: `Thm`, `Formula`, `Term`, the rules and the axioms.
//!
//! The dependency still points untrusted → trusted only. What changed is that
//! the boundary is now stated in the checker's own vocabulary: because every
//! implementation instantiates the judgement's term type as [`ExprPtr`] and its
//! context as [`TcCtx`], the trait names those directly instead of abstracting
//! over them with associated types that had exactly one inhabitant each.
//!
//! # Why `def_eq` cannot return `bool`
//!
//! The point of the project is that "these two Lean terms are definitionally
//! equal" must come with evidence. A `bool` loses the evidence, and — worse —
//! makes it impossible to tell, by reading the code, whether a given conclusion
//! *has* a justification. So every definitional-equality path returns
//! [`DefEq`], which is `Option`-shaped: `Some(cert)` carries the reason, `None`
//! means "not shown equal".
//!
//! # Backend selection
//!
//! Exactly one backend is active per build. [`Backend`] is the alias every
//! other module refers to; without `--features tg` it is `NullCertifier`, whose
//! `Cert` is `()` and therefore free. The `tg` feature swaps this alias for the
//! Tarski–Grothendieck backend and nothing else in the checker changes shape.
//!
//! Note that the null backend is still handed the checker's *real* context at
//! every call. It ignores it, but the code is already in the shape the real
//! backend needs. That is deliberate: the failure mode this design is guarding
//! against is discovering at milestone 3 that certificates were never
//! obtainable at the places that claimed them.

use crate::util::{ExprPtr, TcCtx};

/// A proof backend for definitional-equality (and, later, typing) judgements
/// about **Lean** terms.
///
/// The judgements are about the checker's interned expressions ([`ExprPtr`]),
/// read through the checker's arena ([`TcCtx`]). Both are named concretely: an
/// `ExprPtr` is only an index, so interpreting it as a set-theoretic formula
/// requires the arena, and a backend therefore has to be handed it at every
/// call. That is why the methods take `&mut self` *and* a context: a real
/// backend builds a genuine [`kernel::Thm`] **eagerly** at every step. It cannot
/// defer by recording a lazy derivation tree, because storing derivations is
/// exactly what the design forbids (memory is O(live theorems), not
/// O(proof size)).
///
/// ## Design obligation
///
/// Every method returns a certificate *value*. Certificates are threaded
/// through the checker, never conjured as phantom markers. If any code path in
/// the checker can conclude "definitionally equal" without holding a
/// [`Certifier::Cert`], the design is wrong — that is the invariant this trait
/// exists to force.
///
/// The combinators below are exactly those the definitional equality procedure
/// needs: reflexivity, the equivalence closure, congruence for each expression
/// former, the reduction rules, and equality of two sorts whose universe levels
/// are equal.
///
/// ## Why this is still a trait with one live implementation
///
/// Exactly one backend is compiled per build ([`Backend`] selects it), so the
/// trait is never used polymorphically. It earns its place as a *conformance
/// check* between the two feature-gated alternatives: adding a method to one
/// and forgetting the other is a compile error rather than a silently
/// unimplemented rule.
pub trait Certifier<'t, 'p> {
    /// A certificate witnessing a definitional-equality judgement `a ≡ b`.
    ///
    /// In an LCF discipline the certificate is opaque to the checker: it can
    /// only be produced by these combinators and consumed by the backend.
    type Cert: Clone;

    /// `a ≡ a`.
    fn refl(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>) -> Self::Cert;

    /// Conclude `a ≡ b` from a certificate for `b ≡ a`.
    ///
    /// `a` and `b` are the endpoints of the **conclusion**, not of the premise;
    /// the premise runs the other way. They are passed for the reason spelled
    /// out on [`Certifier::lam_cong`]: a rule handed only a sub-certificate
    /// cannot check what it is being asked to prove. Symmetry looks like the
    /// safest rule there is — it merely turns an equation around — but the
    /// equation it is handed need not be the one the checker claimed, and
    /// without `a` and `b` the backend has no way to notice.
    fn symm(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, c: Self::Cert) -> Self::Cert;

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
    fn trans(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, ab: Self::Cert, bc: Self::Cert) -> Self::Cert;

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
    fn app_cong(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, f: Self::Cert, arg: Self::Cert) -> Self::Cert;

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
    fn lam_cong(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, dom: Self::Cert, body: Self::Cert) -> Self::Cert;

    /// Congruence for `∀`/`Π`: as [`Certifier::lam_cong`] but for the pi former.
    fn pi_cong(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, dom: Self::Cert, body: Self::Cert) -> Self::Cert;

    /// One beta step: `(λx:t. b) a ≡ b[a/x]`. The checker passes the redex and
    /// the already-computed reduct.
    fn beta(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> Self::Cert;

    /// One zeta step: `let x := v; b ≡ b[v/x]`.
    fn zeta(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> Self::Cert;

    /// One delta step: unfolding a definition to its value.
    fn delta(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> Self::Cert;

    /// One iota step: a recursor applied to a constructor application, reduced
    /// to the matching minor premise re-applied to the recursor's arguments.
    ///
    /// The checker passes the redex and the reduct **it actually computed** —
    /// not the reduct a backend might expect — for the reason spelled out on
    /// [`Certifier::lam_cong`]: a rule that cannot compare its result against
    /// the claim can only guess.
    ///
    /// ## Why this is a trait method and not `admit(_, _, "iota")`
    ///
    /// [`Certifier::admit`]'s contract is "I cannot justify this". A backend
    /// that recognised the reason string and returned a real derivation would
    /// be reading a diagnostic label as an instruction, and the count of
    /// surviving `admit` sites — the project's honest measure of how much is
    /// still taken on trust — would stop meaning what it says.
    ///
    /// Adding a method to this trait adds **no proving power**: the trait is an
    /// interface, [`kernel::Thm`] still has no public constructor, and a backend
    /// can only answer this by producing a certificate the way it produces every
    /// other one. The default implementation delegates to [`Certifier::admit`],
    /// so a backend that has nothing to say about iota keeps reporting a gap and
    /// needs no change at all.
    fn iota(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> Self::Cert {
        self.admit(ctx, redex, reduct, Admit::Iota.name())
    }

    /// One eta step relating `a` and `b` where one is the eta-expansion of the
    /// other (`λx. f x ≡ f`).
    fn eta(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>) -> Self::Cert;

    /// `Sort u ≡ Sort v` when the universe levels `u` and `v` are equal. Sort
    /// (and, with levels, const) equality is where the level algebra enters the
    /// definitional-equality certificate.
    fn sort(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>) -> Self::Cert;

    /// Two constant occurrences `c.{us} ≡ c.{vs}` with pointwise-equal universe
    /// levels.
    fn const_eq(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>) -> Self::Cert;

    /// **The declaration has been checked**: `val` inhabits `ty` at the
    /// universe parameters `uparams`, and the checker is about to admit the
    /// constant `name` to the environment.
    ///
    /// This is the one hook that is not about a definitional equality. It exists
    /// because a constant's *typing* is established exactly once — here, where
    /// `check_declar` does the work — and was previously thrown away, forcing
    /// every later use of the constant to re-derive it by recursing into the
    /// constant's value and, transitively, down the whole delta graph. That
    /// recursion is what `TgBackend::MAX_TYPE_DEPTH` existed to bound.
    ///
    /// A backend that can form `⟦name.{uparams}⟧ ∈ ⟦ty⟧` from this may store it;
    /// one that cannot does nothing, which is the default.
    ///
    /// `typing` is the evidence inference itself produced for `⟦val⟧ ∈ ⟦ty⟧` —
    /// the composition of the derivation `infer` built for `⟦val⟧ ∈ ⟦T'⟧` with
    /// the conversion along `⟦T'⟧ = ⟦T⟧`. It is handed over rather than
    /// re-derived because re-deriving it is what the whole typing search used to
    /// be, and the search is the thing this parameter exists to remove.
    fn declar_checked(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: crate::util::NamePtr<'t>,
        uparams: crate::util::LevelsPtr<'t>,
        ty: ExprPtr<'t>,
        val: ExprPtr<'t>,
        typing: Self::Typing,
    ) {
        let _ = (ctx, name, uparams, ty, val, typing);
    }

    // ── The typing judgement ─────────────────────────────────────────────────
    //
    // `def_eq` returns evidence; `infer` returns a *type*, and for a long time
    // returned nothing to justify it. That asymmetry had a price, and it was
    // measured: of `init-prelude`'s 1645 declarations with a value, the typing
    // `⟦val⟧ ∈ ⟦T⟧` had to be searched for from scratch after inference had
    // already established it, because inference threw the evidence away.
    //
    // So inference carries a certificate too. The methods below are Lean's
    // typing rules, one apiece, each handed the premises the corresponding
    // inference rule has *already computed* — which is the point: a rule here
    // does no search and no recursion. It composes what it is given, checks the
    // result is the judgement being claimed, and otherwise reports a gap.
    //
    // Every method has a default that delegates to [`Certifier::ty_gap`], for
    // the same reason [`Certifier::iota`] does: adding a rule adds no proving
    // power, and a backend with nothing to say about a rule keeps reporting a
    // hole rather than needing a change.

    /// A certificate witnessing a **typing** judgement `⟦e⟧ ∈ ⟦ty⟧`.
    ///
    /// Like [`Certifier::Cert`] it is opaque to the checker and can only be
    /// produced by the rules below. Unlike `Cert` it is not `Option`-shaped:
    /// "no evidence" is [`Certifier::ty_gap`], a *value*, so that a rule handed
    /// an unjustified premise still has something to propagate and the place
    /// the evidence ran out is named.
    type Typing: Clone;

    /// **No evidence** for `⟦e⟧ ∈ ⟦ty⟧`, tagged with why — see [`TyGap`].
    ///
    /// This is the typing judgement's counterpart to [`Certifier::admit`], and
    /// it means the same thing: a hole. It is deliberately not silent.
    fn ty_gap(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: ExprPtr<'t>, reason: &'static str)
        -> Self::Typing;

    /// **The premise `TcCache::infer_cache_*` rests on**, as a question the
    /// backend can answer: are every free variable of `t`'s assumptions, and of
    /// its conclusion, among the free variables of `⟦e⟧` and `⟦ty⟧`?
    ///
    /// The two inference memos are keyed on the `ExprPtr` alone and they
    /// deliberately store *conditional* typings, on the written argument that
    /// "a typing's hypotheses are always about locals occurring in the very
    /// expression the entry is keyed on, so a hit under a different context asks
    /// about the same locals or does not mention them at all". That argument is
    /// what makes the omission of the context from the key safe, and it has
    /// never been enforced — while `ty_conv` merges the *equation's* hypotheses
    /// into the typing's, and an equation's hypotheses are not confined to the
    /// subject's locals in the way a typing's are.
    ///
    /// So the premise is checked, under `debug_assert`, at the one insertion
    /// point. It is a diagnostic and not a guard: a release build does not call
    /// it, and if it ever fires the fix is to key or refuse, not to weaken the
    /// assertion. The default is `true` for the null backend, which stores no
    /// evidence and therefore has no premise to violate.
    fn typing_is_confined(
        &mut self,
        _ctx: &mut TcCtx<'t, 'p>,
        _e: ExprPtr<'t>,
        _ty: ExprPtr<'t>,
        _t: &Self::Typing,
    ) -> bool {
        true
    }

    /// `Π A B : Sort (imax u v)` — the universe a `Π` lands in.
    ///
    /// `which` is [`TyGap::Pi`] or [`TyGap::PiProp`] according to whether
    /// `imax u v` simplified to zero; the backend needs it because the two are
    /// different clauses of the interpretation, not two instances of one.
    fn ty_pi(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        which: TyGap,
    ) -> Self::Typing {
        self.ty_gap(ctx, e, ty, which.name())
    }

    /// `Sort u : Sort (u+1)` — the interpretation makes `⟦Sort (u+1)⟧` the
    /// universe over `⟦Sort u⟧`, so this is `∀x. x ∈ U(x)` at one instance.
    fn ty_sort(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: ExprPtr<'t>) -> Self::Typing {
        self.ty_gap(ctx, e, ty, TyGap::Sort.name())
    }

    /// `c.{us} : ty`, the declared type — a **lookup** in whatever the backend
    /// stored when the declaration was checked, not a walk down the delta
    /// graph.
    fn ty_const(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: ExprPtr<'t>) -> Self::Typing {
        self.ty_gap(ctx, e, ty, TyGap::Const.name())
    }

    /// `x : A` for a context local — the ambient hypothesis, acquired as an
    /// antecedent, to be discharged at the binder that introduced it.
    fn ty_local(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: ExprPtr<'t>) -> Self::Typing {
        self.ty_gap(ctx, e, ty, TyGap::Local.name())
    }

    /// **Conversion**: from `⟦e⟧ ∈ ⟦from⟧` and a certificate relating `from` and
    /// `to`, conclude `⟦e⟧ ∈ ⟦to⟧`.
    ///
    /// This is the rule that consumes the definitional-equality certificate the
    /// checker used to discard: `assert_def_eq` confirmed one existed and threw
    /// it away, at every application, every `let`, and at the top of every
    /// declaration.
    ///
    /// `eq` is borrowed, not taken. A conditional certificate handed to a rule
    /// is *accounted for* by the escape ledger, and folding one into a typing
    /// would account for it against a ledger it is not in; borrowing leaves the
    /// ledger's over-report in the safe direction.
    fn ty_conv(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        from: ExprPtr<'t>,
        to: ExprPtr<'t>,
        typing: Self::Typing,
        eq: &Self::Cert,
    ) -> Self::Typing {
        let _ = (typing, eq, from);
        self.ty_gap(ctx, e, to, TyGap::Conv.name())
    }

    /// **Application**: from `⟦f⟧ ∈ ⟦Π x:A. B⟧` and `⟦a⟧ ∈ ⟦A⟧` conclude
    /// `⟦f a⟧ ∈ ⟦B[a/x]⟧`.
    ///
    /// `fun_ty` is the `Π` inference read off `f`, passed explicitly so the rule
    /// need not go looking for it, and `ty` is `B[a/x]` — the claim, so the rule
    /// can check its result against it.
    #[allow(clippy::too_many_arguments)]
    fn ty_app(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        app: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        fun: ExprPtr<'t>,
        fun_ty: ExprPtr<'t>,
        arg: ExprPtr<'t>,
        f: Self::Typing,
        a: Self::Typing,
    ) -> Self::Typing {
        let _ = (fun, fun_ty, arg, f, a);
        self.ty_gap(ctx, app, ty, TyGap::App.name())
    }

    /// **Lambda**: from `⟦b⟧ ∈ ⟦B⟧` under the hypothesis `⟦x⟧ ∈ ⟦A⟧` conclude
    /// `⟦λx:A. b⟧ ∈ ⟦Π x:A. B⟧`.
    ///
    /// `local` is the checker's own free variable standing for `x` and `body`
    /// the body opened at it, so the rule can see exactly which hypothesis it is
    /// discharging rather than having to open the binder its own way.
    #[allow(clippy::too_many_arguments)]
    fn ty_lam(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        lam: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        local: ExprPtr<'t>,
        body: ExprPtr<'t>,
        b: Self::Typing,
    ) -> Self::Typing {
        let _ = (local, body, b);
        self.ty_gap(ctx, lam, ty, TyGap::Lam.name())
    }

    /// **Projection**: `s.i : F`, where `F` is the `i`-th binder of the
    /// structure's single constructor, with the parameters instantiated at the
    /// structure type's arguments and the earlier fields at projections of `s`.
    ///
    /// `structure` is the subject `s`, passed so the rule can check `e` really
    /// is a projection out of it and recompute `F` for itself rather than
    /// taking the checker's word for the claim.
    fn ty_proj(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        structure: ExprPtr<'t>,
    ) -> Self::Typing {
        let _ = structure;
        self.ty_gap(ctx, e, ty, TyGap::Proj.name())
    }

    /// **Let**: a `let` denotes its expansion, and the interpretation introduces
    /// it as an explicit definition of exactly that, so the typing of the
    /// expansion carries across the defining equation.
    fn ty_let(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        expansion: ExprPtr<'t>,
        b: Self::Typing,
    ) -> Self::Typing {
        let _ = (expansion, b);
        self.ty_gap(ctx, e, ty, TyGap::Let.name())
    }

    /// An equality the checker believes but cannot yet justify to the backend.
    ///
    /// **This is a hole in the proof.** It exists so that certificate plumbing
    /// can be introduced incrementally across a 1300-line type checker without
    /// a flag day, and so that the places still lacking a real justification are
    /// *named in the type system* rather than hidden behind a `bool`.
    ///
    /// `reason` is a static string identifying the call site — see [`Admit`],
    /// which enumerates them. A real backend is expected to either produce a
    /// genuine derivation or refuse; the count of surviving `admit` sites is the
    /// honest measure of how far the milestone-3 work has to go, and it must
    /// reach zero before the TG backend can be trusted.
    fn admit(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, reason: &'static str) -> Self::Cert;
}

/// The milestone-1 proof backend: certificates carry no information (`Cert =
/// ()`), so the checker degenerates to an ordinary trusted type checker.
///
/// **Milestone 3 obligation:** once the real backend exists, `NullCertifier`
/// must be unreachable in a release build. It is compiled only when the `tg`
/// feature is *off*, so in a `--features tg` build it does not exist at all —
/// which is that obligation enforced rather than merely intended.
///
/// It carries no data: it ignores the context it is handed, but every call site
/// passes the genuine arena, so the code is already in the shape the real
/// backend needs.
#[cfg(not(feature = "tg"))]
#[derive(Debug, Clone, Default)]
pub struct NullCertifier;

#[cfg(not(feature = "tg"))]
impl NullCertifier {
    /// Create the null backend.
    pub fn new() -> Self { NullCertifier }
}

#[cfg(not(feature = "tg"))]
impl<'t, 'p> Certifier<'t, 'p> for NullCertifier {
    type Cert = ();

    fn refl(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>) {}
    fn symm(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>, _c: ()) {}
    fn trans(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>, _ab: (), _bc: ()) {}
    fn app_cong(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>, _f: (), _arg: ()) {}
    fn lam_cong(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>, _dom: (), _body: ()) {}
    fn pi_cong(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>, _dom: (), _body: ()) {}
    fn beta(&mut self, _: &mut TcCtx<'t, 'p>, _redex: ExprPtr<'t>, _reduct: ExprPtr<'t>) {}
    fn zeta(&mut self, _: &mut TcCtx<'t, 'p>, _redex: ExprPtr<'t>, _reduct: ExprPtr<'t>) {}
    fn delta(&mut self, _: &mut TcCtx<'t, 'p>, _redex: ExprPtr<'t>, _reduct: ExprPtr<'t>) {}
    fn eta(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>) {}
    fn sort(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>) {}
    fn const_eq(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>) {}
    fn admit(&mut self, _: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>, _reason: &'static str) {}

    type Typing = ();

    fn ty_gap(&mut self, _: &mut TcCtx<'t, 'p>, _e: ExprPtr<'t>, _ty: ExprPtr<'t>, _reason: &'static str) {}
}

/// The proof backend in force for this build.
#[cfg(not(feature = "tg"))]
pub type Backend<'x, 't, 'p> = NullCertifier;

/// The real Tarski–Grothendieck backend, whose `Cert` is a genuine kernel
/// theorem. Enable with `--features tg`.
///
/// It is opt-in rather than default for now because it is strictly more
/// expensive — it interprets every Lean expression into a first-order term and
/// builds an actual derivation at every step — and because the parts it cannot
/// yet prove (beta, delta, zeta, eta) are reported rather than assumed, so the
/// two backends answer different questions. `NullCertifier` answers "does this
/// development check?"; `TgBackend` answers "and was every step derived?".
#[cfg(feature = "tg")]
pub type Backend<'x, 't, 'p> = crate::tg::TgBackend<'x, 't, 'p>;

/// Build the active backend.
///
/// The `Env` is what lets the TG backend resolve a constant to its *value*, so
/// that `⟦c⟧` can be introduced as an explicit definition `⟦c⟧ := ⟦value⟧`
/// rather than as an opaque symbol. Without it, delta reduction could never be
/// justified: there would be nothing relating the constant to what it unfolds
/// to. The null backend ignores it.
#[cfg(feature = "tg")]
pub fn new_backend<'x, 't: 'x, 'p: 't>(env: &'x crate::env::Env<'x, 't>) -> Backend<'x, 't, 'p> {
    crate::tg::TgBackend::new(env)
}

/// Build the active backend (null variant; the environment is unused).
#[cfg(not(feature = "tg"))]
pub fn new_backend<'x, 't: 'x, 'p: 't>(_env: &'x crate::env::Env<'x, 't>) -> Backend<'x, 't, 'p> {
    NullCertifier::new()
}

/// The certificate type of the active backend.
#[cfg(feature = "tg")]
pub type Cert<'t, 'p> = crate::tg::TgCert;

/// The certificate type of the active backend (null variant: no information).
#[cfg(not(feature = "tg"))]
pub type Cert<'t, 'p> = ();

/// The typing-certificate type of the active backend.
#[cfg(feature = "tg")]
pub type Typing<'t, 'p> = crate::tg::TgTyping;

/// The typing-certificate type of the active backend (null variant).
#[cfg(not(feature = "tg"))]
pub type Typing<'t, 'p> = ();

/// Whether a typing certificate carries **no evidence at all**.
///
/// The inference rules use this as a short-circuit: a rule whose premise is a
/// hole cannot conclude anything, so the terms it would otherwise have to build
/// (the partial applications of a spine, the `Π` at each binder of a lambda
/// chain) are not built. Under the null backend every typing is a hole, so the
/// whole apparatus costs that build exactly nothing.
#[cfg(feature = "tg")]
pub fn typing_is_gap(t: &Typing<'_, '_>) -> bool { t.is_gap() }

/// Whether a typing certificate carries no evidence (null variant: never any).
#[cfg(not(feature = "tg"))]
pub fn typing_is_gap(_t: &Typing<'_, '_>) -> bool { true }

/// Whether a certificate rests on nothing — a complete derivation of the
/// equation, not of an implication and not a step taken on trust.
///
/// This exists for the *caches*. A certificate parked in a cache is a second
/// copy of whatever it is, and for a conditional derivation that means a second
/// undischarged obligation: the assumptions of the copy are discharged at the
/// binder the copy's own derivation passes through, and a copy sitting in a
/// global cache passes through no binder. The escape ledger counts it, rightly.
/// So the equality cache remembers the *derived* equalities and lets the rest
/// be re-derived — which is the same trade the checker's own `failure_cache`
/// makes, and the opposite of remembering everything and paying for it in
/// obligations nothing can discharge.
///
/// Measured: caching conditional certificates on the union-find's edges took
/// the tutorial corpus from 49 escapes to 96 and knocked `028_peano2`,
/// `029_peano3`, `073_boolRecEqns` and `081_PSigma.snd` off zero gaps — 265
/// gaps became 291, a net *loss*, even though it closed more `eq_cache` gaps
/// than the unconditional-only rule does. Caching only the unconditional ones
/// closes 415 of `init-prelude`'s 687 `eq_cache` gaps and costs no escapes.
///
/// # It is `hyps().is_empty()`, not `is_proved()`, and the difference is
/// soundness
///
/// This predicate used to read `c.is_proved()`, and that was correct for exactly
/// as long as a `Thm` was valid **absolutely**. It is not any more:
/// `kernel::Thm` is now a sequent `Γ ⊢ φ`, and `Γ ⊢ a = b` asserts the equation
/// only where `Γ` holds. A cache whose key is the `Expr` pair does not mention
/// `Γ`, so retrieving such a theorem under that key *silently imports `Γ`* — and
/// the kernel cannot catch it, because the theorem handed back is perfectly
/// good. The error would be entirely in what the checker concluded from it.
///
/// `TgCert::Proved` still means "derived, full stop" at the level of the
/// *variant*, but the variant no longer implies it at the level of the theorem:
/// `Proved(Γ ⊢ a = b)` with `Γ` non-empty would answer `true` to `is_proved()`.
/// So the predicate asks the theorem instead. Today no rule in `tg.rs` builds a
/// hypothetical `Thm` — [`crate::scope`] is the only module in the crate that
/// can, and has no caller yet — and this is therefore a no-op on every measured
/// number; that is the point. It turns a property of the current callers into a
/// property of the code, and it **fails closed** as certificate-producing rules
/// are added.
///
/// The same question has to be asked of every store that hands a `Thm` back
/// later, not only this one, and for the cross-declaration ones it is asked **by
/// type**: every `Thm` in `tg::Shared` is a [`crate::sealed::Sealed`], whose only
/// constructor checks `hyps().is_empty()`. This predicate and [`hypothesis_free`]
/// remain the `Cert`-level form, for the stores that hold a certificate in flight
/// rather than a theorem: [`crate::reduct::Trace::cert`], guarded at its one
/// write site in `TypeChecker::certify_reduct` by [`hypothesis_free`]; the
/// union-find's edges; and `TcCache::infer_cache_*`, which deliberately admits
/// *conditional* typings and is discussed at its insertion point. Sealing
/// `TgCert` itself was considered and rejected — see [`crate::sealed`].
#[cfg(feature = "tg")]
pub fn is_unconditional(c: &Cert<'_, '_>) -> bool { c.thm().is_some_and(|t| t.hyps().is_empty()) }

/// Whether a certificate's kernel theorem stands under **no hypotheses** —
/// `Γ = ∅` — whichever variant it is.
///
/// Weaker than [`is_unconditional`], and for a different job. A
/// [`crate::tg::TgCert::Conditional`] carries its assumptions *inside* the
/// formula it proves (`⊢ conj(hs) → a = b`, a closed statement), so storing one
/// imports nothing into a later context — it is an accounting question, which
/// the escape ledger answers. Kernel hypotheses are the opposite: they sit
/// outside the formula, and a store keyed on anything that does not mention them
/// re-asserts them silently. So a memo that is willing to hold a conditional
/// certificate still must not hold a hypothetical one.
#[cfg(feature = "tg")]
pub fn hypothesis_free(c: &Cert<'_, '_>) -> bool { c.hyps().is_empty() }

/// Whether a certificate stands under no hypotheses (null variant: it carries no
/// theorem, so there are none).
#[cfg(not(feature = "tg"))]
pub fn hypothesis_free(_c: &Cert<'_, '_>) -> bool { true }

/// Whether a certificate rests on nothing (null variant: it carries no
/// information, so there is nothing it could rest on).
#[cfg(not(feature = "tg"))]
pub fn is_unconditional(_c: &Cert<'_, '_>) -> bool { true }

/// The result of a definitional-equality check.
///
/// `Some(cert)` means the two terms were shown equal, and `cert` is why.
/// `None` means they were not shown equal — which, for a *checker*, is the
/// same as "reject": we never assert an equality we cannot justify.
pub type DefEq<'t, 'p> = Option<Cert<'t, 'p>>;

/// The places that still conclude an equality without a real justification,
/// i.e. that call [`Certifier::admit`].
///
/// Every variant *was* a hole that milestone 3 must close. Several have since
/// been closed and are annotated as such at the variant; a variant that says so
/// is kept only so that the label it names stays enumerable and a reappearance
/// would be visible, not because the hole exists. They are an enum rather than
/// scattered string literals so that the remaining work is enumerable, a new
/// hole cannot be added without naming it here, and each site can be counted
/// (see [`admit_report`]).
///
/// The plumbing was introduced from the *outside in*: the top-level `def_eq`
/// entry points and the rules that map directly onto backend primitives
/// (reflexivity, sort equality, constant equality, eta) threaded real
/// certificates first, while the deeper structural comparisons — which upstream
/// nanoda expresses as plain `bool`-returning recursion — admitted. That
/// inside-out remainder is gone: the two structural comparisons named below,
/// `Binder` and `App`, are both certified now.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum Admit {
    /// Structural/alpha comparison of two binder chains (`def_eq_binder_aux`).
    ///
    /// **No longer raised.** `def_eq_binder_aux` folds real `pi_cong`/`lam_cong`
    /// certificates over the chain and calls `bump_certified()`; this variant is
    /// constructed nowhere in the crate. Kept so the label stays enumerable and
    /// a reappearance in [`admit_report`] would be visible as a regression.
    Binder,
    /// Congruence over a spine of applications (`def_eq_app`).
    ///
    /// **No longer raised**, for the same reason: `def_eq_app` folds `app_cong`
    /// over the spine. Constructed nowhere in the crate.
    App,
    /// Two `Local`s with the same id (`def_eq_local`).
    Local,
    /// Two projections of def-eq structures (`def_eq_proj`).
    Proj,
    /// Proof irrelevance: two proofs of def-eq propositions.
    ProofIrrel,
    /// Eta for structures.
    EtaStruct,
    /// String literal expanded to constructor form.
    StringLit,
    /// Elements of a subsingleton structure.
    UnitLike,
    /// Recovered from the union-find equality cache.
    ///
    /// The proof-producing union-find that replaces this now exists
    /// (`crate::union_find`): each union edge carries the certificate for the
    /// pair it was created from, and a hit composes along the explain path.
    /// What is left under this reason is a path through an edge whose
    /// certificate the cache declined to keep because it was *conditional* —
    /// see [`is_unconditional`] for why keeping those costs more than it buys.
    /// 687 of these on `init-prelude` became 272, and 6 on the tutorials became
    /// 4.
    Cache,
    /// `Bool.true`-normalisation shortcut in `def_eq`.
    BoolTrue,
    /// Weak-head normalisation: `e` reduces to `whnf(e)`, reason unrecorded.
    ///
    /// A reduct memo entry now carries the reduction that produced it
    /// (`crate::reduct`), so the individual rules below account for every
    /// reduction whatever kind of call first populated the entry. This variant
    /// survives only as the report for a **broken record**: a trace whose
    /// endpoints are not the claim's, or whose two halves do not meet. That is
    /// a bug rather than a missing rule, so it is reported once, about the
    /// equation actually claimed, instead of being passed off. It is at zero
    /// corpus-wide, and a non-zero count here should be read as a bug report.
    Whnf,
    /// Projection of a constructor application: `(mk a₁ … aₙ).i ⟶ aᵢ`.
    ProjRed,
    /// Iota: a recursor applied to a constructor application.
    ///
    /// No longer raised by the checker — iota is a rule on the backend
    /// boundary (`Certifier::iota`) rather than an admission. The variant is
    /// kept because `Certifier::iota`'s *default* implementation delegates to
    /// `admit` under exactly this reason string, so a backend with nothing to
    /// say about iota still reports its gaps here.
    Iota,
    /// Quotient computation: `Quot.lift`/`Quot.ind` applied to a `Quot.mk`.
    Quot,
    /// Native arithmetic on literals (`Nat.add`, `Nat.succ`, …). Milestone 4
    /// replaces this with the kernel's primitive `ℕ` and its rule schemas.
    NatRed,
    /// Equality of two natural-number literals held in different
    /// representations (`Nat.zero` versus `0`, `Nat.succ n` versus `n+1`).
    NatEq,
}

/// Number of [`Admit`] variants.
pub const N_ADMITS: usize = 16;

impl Admit {
    /// A stable name, used in the report and passed to the backend.
    pub const fn name(self) -> &'static str {
        match self {
            Admit::Binder => "def_eq_binder",
            Admit::App => "def_eq_app",
            Admit::Local => "def_eq_local",
            Admit::Proj => "def_eq_proj",
            Admit::ProofIrrel => "proof_irrel",
            Admit::EtaStruct => "eta_struct",
            Admit::StringLit => "string_lit",
            Admit::UnitLike => "unit_like",
            Admit::Cache => "eq_cache",
            Admit::BoolTrue => "bool_true",
            Admit::Whnf => "whnf",
            Admit::ProjRed => "proj_reduce",
            Admit::Iota => "iota",
            Admit::Quot => "quot",
            Admit::NatRed => "nat_reduce",
            Admit::NatEq => "nat_eq",
        }
    }

    /// All variants, for reporting.
    pub const ALL: [Admit; N_ADMITS] = [
        Admit::Binder,
        Admit::App,
        Admit::Local,
        Admit::Proj,
        Admit::ProofIrrel,
        Admit::EtaStruct,
        Admit::StringLit,
        Admit::UnitLike,
        Admit::Cache,
        Admit::BoolTrue,
        Admit::Whnf,
        Admit::ProjRed,
        Admit::Iota,
        Admit::Quot,
        Admit::NatRed,
        Admit::NatEq,
    ];
}

/// The places where **inference** cannot justify the type it inferred.
///
/// The counterpart of [`Admit`] for the typing judgement, and enumerable for
/// the same reason: a hole that is not named cannot be counted, and the whole
/// point of threading a certificate through `infer` is that the places evidence
/// runs out become a list rather than a feeling.
///
/// `Rule`, `Premise` and `Claim` are not missing *rules*: they are a rule that
/// exists, was asked, and declined — because the backend could not build the
/// derivation, because a premise was itself a hole, or because what it built
/// did not match the judgement being claimed. Keeping them apart is what says
/// whether the next thing to do is add a rule or fix one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum TyGap {
    /// `Sort u : Sort (u+1)`.
    Sort,
    /// A constant's declared type.
    Const,
    /// A context local's ambient typing.
    Local,
    /// Conversion along a definitional equality.
    Conv,
    /// The application rule.
    App,
    /// The lambda rule.
    Lam,
    /// The `let` rule.
    Let,
    /// `Π A B : Sort (imax u v)` for `imax u v ≠ 0` — no rule; the universe of
    /// a `Π` is the `Sort`-encoding obstruction, not something a premise could
    /// supply.
    Pi,
    /// `Π A B : Prop`, i.e. `imax u v = 0` — split out from [`TyGap::Pi`]
    /// because it is a **different clause of the interpretation**, not a harder
    /// instance of the same one.
    ///
    /// Carneiro's §6.2 gives `∀` and `Π` two definitions:
    ///
    /// ```text
    /// ⟦∀x : α. β⟧ = {•} ∩ ⋂_{x ∈ ⟦α⟧} ⟦β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]   — Prop
    /// ⟦Π x : α. β⟧ = ∏_{x ∈ ⟦α⟧} ⟦β⟧                                — Type
    /// ```
    ///
    /// The first is a **subset of `{•}`**, the second a dependent function
    /// space. `tg`'s `interp_pi` used to implement only the second — for every
    /// `Expr::Pi`, unconditionally — and for the rows counted here the typing
    /// obligation was then not merely unproved but *unprovable as stated*, since
    /// the target is `U₀ = {0,1}` and a `dprod` is no subset of `{•}`.
    ///
    /// It now implements both, and the split has done its job: the `Prop` clause
    /// builds the conditional singleton `[∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]`, whose membership
    /// in `U₀` is `derived::tower::Tower::cond_in_u0` and falls out where the
    /// term is built. 446 of `init-prelude`'s 449 rows and 136 of the tutorial's
    /// 137 are discharged; what is still counted here is the residue. The split
    /// stays because it is what makes that measurable — and because [`TyGap::Pi`]
    /// is still 5269, waiting on `dprod_in_universe`'s n-ary port, which is a
    /// different problem entirely.
    PiProp,
    /// `Π A B : Sort (imax u v)` where the level **does not simplify**, because
    /// `v` is a universe parameter — so the `Π` is *neither* clause of §6.2
    /// until the parameter is instantiated.
    ///
    /// `imax u v` is `0` when `v` is instantiated at `0` and `max(u,v)`
    /// otherwise, and `Level::simplify` rightly leaves it alone
    /// (`checker/src/level.rs`: `IMax` reduces only when the left side is `0`
    /// or `1`, or the right side is `Zero` or a `Succ`). `Max` of two
    /// parameters is the same story. So at a level-polymorphic declaration's
    /// own parameters,
    ///
    /// ```text
    /// ⟦∀x : α. β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]   — a subset of {•}
    /// ⟦Π x : α. β⟧ = ∏_{x ∈ ⟦α⟧} ⟦β⟧      — a dependent function space
    /// ```
    ///
    /// are two **different sets** and nothing decides between them. Choosing
    /// either is choosing wrongly on some instantiation, so the backend chooses
    /// neither: it interprets such a `Π` by an axiom-free symbol of the right
    /// shape and every rule over it reports a gap.
    ///
    /// This is not a gap that a lemma closes. It bounds what *any*
    /// per-declaration interpretation can achieve, and closing it means running
    /// the backend per level-instantiation rather than once at the
    /// declaration's parameters.
    PiUndet,
    /// A structure projection.
    Proj,
    /// A `Nat` or `String` literal, whose interpretation is an opaque symbol.
    Lit,
    /// `infer` was called in `InferOnly` mode, which does not check the
    /// argument of an application and so has no premise to offer.
    InferOnly,
    /// A rule was asked and could not build the derivation.
    Rule,
    /// A rule was asked but one of its premises was itself a hole.
    Premise,
    /// A rule built a derivation that was not of the judgement claimed. This is
    /// a bug report, not a missing rule; it should stay at zero.
    Claim,
}

/// Number of [`TyGap`] variants.
pub const N_TY_GAPS: usize = 16;

impl TyGap {
    /// A stable name, used in the report and passed to the backend.
    pub const fn name(self) -> &'static str {
        match self {
            TyGap::Sort => "ty_sort",
            TyGap::Const => "ty_const",
            TyGap::Local => "ty_local",
            TyGap::Conv => "ty_conv",
            TyGap::App => "ty_app",
            TyGap::Lam => "ty_lam",
            TyGap::Let => "ty_let",
            TyGap::Pi => "ty_pi",
            TyGap::PiProp => "ty_pi_prop",
            TyGap::PiUndet => "ty_pi_undet",
            TyGap::Proj => "ty_proj",
            TyGap::Lit => "ty_lit",
            TyGap::InferOnly => "ty_infer_only",
            TyGap::Rule => "ty_rule_declined",
            TyGap::Premise => "ty_premise_missing",
            TyGap::Claim => "ty_not_the_claim",
        }
    }

    /// All variants, for reporting.
    pub const ALL: [TyGap; N_TY_GAPS] = [
        TyGap::Sort,
        TyGap::Const,
        TyGap::Local,
        TyGap::Conv,
        TyGap::App,
        TyGap::Lam,
        TyGap::Let,
        TyGap::Pi,
        TyGap::PiProp,
        TyGap::PiUndet,
        TyGap::Proj,
        TyGap::Lit,
        TyGap::InferOnly,
        TyGap::Rule,
        TyGap::Premise,
        TyGap::Claim,
    ];
}

// ── The dropped-certificate ledger ───────────────────────────────────────────
//
// "Every discarded certificate is a smell." The places that still discard one
// are named here and counted, so that the smell is a number in the report
// rather than something to be found by grepping for `.is_some()`. Dropping is
// deliberately *not* the same as handing a certificate to a rule: this counter
// does not touch the escape ledger, which continues to report an abandoned
// conditional derivation as the gap it is.

/// A place that obtains a definitional-equality certificate and does not use it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum Dropped {
    /// `quot.rs`: the quotient declarations' shapes are checked against the
    /// expected ones. No typing judgement is built from these.
    Quot,
    /// `inductive.rs`: the inductive/constructor/recursor telescope checks.
    Inductive,
    /// `tc.rs`: a side condition inside a definitional-equality rule
    /// (`def_eq_proj`, `def_eq_local`, `proof_irrel`, `eta`, `unit_like`,
    /// `eta_struct`, `to_ctor_when_k`), where the conclusion drawn is itself an
    /// admit and the side condition's evidence has nothing to compose with.
    DefEqSide,
    /// The `Π`'s domain check in `infer_pi`/`infer_lambda`: the binder type has
    /// to *be* a type, and the sort it infers as is used for the universe
    /// algebra, not for a membership.
    BinderSort,
}

/// Number of [`Dropped`] variants.
pub const N_DROPPED: usize = 4;

impl Dropped {
    /// A stable name, used in the report.
    pub const fn name(self) -> &'static str {
        match self {
            Dropped::Quot => "quotient declaration shape checks",
            Dropped::Inductive => "inductive telescope checks",
            Dropped::DefEqSide => "side conditions inside def-eq rules",
            Dropped::BinderSort => "binder domains checked to be types",
        }
    }

    /// All variants, for reporting.
    pub const ALL: [Dropped; N_DROPPED] =
        [Dropped::Quot, Dropped::Inductive, Dropped::DefEqSide, Dropped::BinderSort];
}

#[cfg(feature = "stepcount")]
static DROPPED_COUNTS: [std::sync::atomic::AtomicU64; N_DROPPED] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_DROPPED];

/// Record one certificate obtained and thrown away. Compiles to nothing without
/// `stepcount`.
#[inline(always)]
pub fn bump_dropped(site: Dropped) {
    #[cfg(feature = "stepcount")]
    DROPPED_COUNTS[site as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(feature = "stepcount"))]
    let _ = site;
}

#[cfg(feature = "stepcount")]
static ADMIT_COUNTS: [std::sync::atomic::AtomicU64; N_ADMITS] = [
    const { std::sync::atomic::AtomicU64::new(0) }; N_ADMITS
];

/// Certificates produced by a real backend rule rather than by an admit.
#[cfg(feature = "stepcount")]
static CERTIFIED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Record one use of an admit site. Compiles to nothing without `stepcount`.
#[inline(always)]
pub fn bump_admit(site: Admit) {
    #[cfg(feature = "stepcount")]
    ADMIT_COUNTS[site as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(feature = "stepcount"))]
    let _ = site;
}

/// Record one certificate produced by a genuine backend rule.
#[inline(always)]
pub fn bump_certified() {
    #[cfg(feature = "stepcount")]
    CERTIFIED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// Render the certified-vs-admitted breakdown, or `None` if counting is off.
///
/// This is the honest measure of how far the milestone-3 work has to go: the
/// admitted count must reach zero before the TG backend can be trusted.
pub fn admit_report() -> Option<String> {
    if !cfg!(feature = "stepcount") {
        return None
    }
    #[cfg(feature = "stepcount")]
    {
        use std::sync::atomic::Ordering::Relaxed;
        let certified = CERTIFIED.load(Relaxed);
        const CERT_LABEL: &str = "certified (real rule)";
        const TOTAL_LABEL: &str = "TOTAL admitted";
        // Width must cover the rendered label, which for admit rows includes the
        // "admit " prefix — otherwise those rows sit one column out.
        let width = Admit::ALL
            .iter()
            .map(|a| a.name().len() + "admit ".len())
            .chain([CERT_LABEL.len(), TOTAL_LABEL.len()])
            .max()
            .unwrap_or(0);
        let mut s = String::from("definitional-equality certificate provenance\n");
        s.push_str(&format!("  {CERT_LABEL:<width$}  {certified:>14}\n"));
        let mut total_admitted = 0u64;
        for site in Admit::ALL {
            let n = ADMIT_COUNTS[site as usize].load(Relaxed);
            total_admitted += n;
            let label = format!("admit {}", site.name());
            s.push_str(&format!("  {label:<width$}  {n:>14}\n"));
        }
        s.push_str(&format!("  {TOTAL_LABEL:<width$}  {total_admitted:>14}\n"));
        let mut total_dropped = 0u64;
        let mut rows = String::new();
        for site in Dropped::ALL {
            let n = DROPPED_COUNTS[site as usize].load(Relaxed);
            total_dropped += n;
            let label = format!("dropped {}", site.name());
            rows.push_str(&format!("  {label:<width$}  {n:>14}\n"));
        }
        if total_dropped > 0 {
            s.push_str("certificates obtained and discarded\n");
            s.push_str(&rows);
        }
        Some(s)
    }
    #[cfg(not(feature = "stepcount"))]
    None
}
