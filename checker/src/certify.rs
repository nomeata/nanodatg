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
    ///
    /// `expansion` is the term `λz. b z` the checker built, and `expanded` the
    /// certificate for `a ≡ expansion` that the recursive comparison produced.
    /// The rule takes both because the conclusion is a composite — `a ≡ λz. b z`
    /// then `λz. b z ≡ b` — and only the second half is eta proper. Handing the
    /// first half over rather than dropping it is what keeps a backend from
    /// being asked for the whole of `a ≡ b` with nothing to build it from; a
    /// backend that still cannot do the eta step reports one gap, not one gap
    /// and a transitivity over it.
    fn eta(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        expansion: ExprPtr<'t>,
        expanded: Self::Cert,
    ) -> Self::Cert;

    /// **Congruence for projection**: from `s ≡ s'` conclude `s.i ≡ s'.i`.
    ///
    /// A rule rather than an admission because it needs no axiom: a projection
    /// interprets as a signature symbol applied to the structure's
    /// interpretation, so this is congruence over that symbol and nothing more.
    /// `a` and `b` are the two projections, passed for the reason on
    /// [`Certifier::lam_cong`] — the rule has to be able to check that the
    /// premise really is about the two subjects it is claimed to be about.
    ///
    /// The default delegates to [`Certifier::admit`], so a backend with no
    /// interpretation of projections keeps reporting the same gap it did.
    fn proj_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        structures: Self::Cert,
    ) -> Self::Cert {
        let _ = structures;
        self.admit(ctx, a, b, Admit::Proj.name())
    }

    /// **Two locals with one id**: from a certificate that the declared types
    /// are definitionally equal, conclude `a ≡ b` for two `Local`s carrying the
    /// same de Bruijn level.
    ///
    /// A rule rather than an admission because the common case needs no axiom:
    /// the TG backend keys a level-local's kernel variable by its level **and
    /// its interpreted declared type** (`LocalKey`), so two same-level locals
    /// whose types interpret to the same term *are* one variable and the
    /// equation is reflexivity. The residue — same level, types definitionally
    /// equal but interpreting to different terms — is two distinct variables,
    /// and no rule relates them; a backend reports that residue as its own gap.
    ///
    /// `ty_eq` is the checker's certificate for the two declared types. It is
    /// the evidence `def_eq_local` used to establish and throw away
    /// (`THREADING-CENSUS.md`, `def_eq_local` row); it is handed over rather
    /// than dropped so the rule can consume it — the escape ledger counts
    /// receipt — and so the residue case has the premise in hand if a
    /// two-variable bridge ever exists.
    ///
    /// The default delegates to [`Certifier::admit`] under `def_eq_local`, so a
    /// backend that does not key variables this way keeps reporting the gap the
    /// checker used to report.
    fn local_eq(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        ty_eq: Self::Cert,
    ) -> Self::Cert {
        let _ = ty_eq;
        self.admit(ctx, a, b, Admit::Local.name())
    }

    /// **Projection reduction**: `(mk a₁ … aₙ).i a⃗ ≡ aⱼ a⃗`, one step of
    /// weak-head normalisation.
    ///
    /// A rule and not an [`Admit`] because there is something to ask, and until
    /// this method existed there was not. `whnf` recorded the step as
    /// `Rule::Admitted(Admit::ProjRed)`, so the *only* thing that ever saw the
    /// step was [`Certifier::admit`] — and what `admit` did with it, for as long
    /// as it had an optimistic fall-through, was rediscover on its own that both
    /// endpoints were proofs and pass the step off as derived. Twenty steps a
    /// run, filed under the label of the funnel that noticed rather than the
    /// label of the reduction. Deleting the fall-through made those twenty
    /// visible; this method is where they are supposed to be answered.
    ///
    /// ## What the premises are, and why they are these
    ///
    /// A backend that interpreted structures would want the constructor's own
    /// computation rule and would need none of the parameters below. This one
    /// does not interpret them (`INDUCTIVES.md`), so the derivation available to
    /// it is the *other* one: if both endpoints are proofs then each interprets
    /// to `•` by Carneiro's Theorem 6.7 and the step is those two equations
    /// composed. `redex_proof` and `reduct_proof` are exactly Theorem 6.7's
    /// premises per side — `⟦e⟧ ∈ ⟦α⟧` and `⟦α⟧ ∈ U₀` — and `None` means the
    /// checker's own inference does not make that side a proof.
    ///
    /// They are *computed forward by the checker* and handed over, not looked
    /// for. That distinction is the whole of the design (`MINI-DESIGN.md` §0):
    /// the backend may not re-enter the checker, so a backend asking this
    /// question for itself has to answer it with `syn_type`'s delta-only shadow
    /// walk and two `has_type_a` searches, whereas the checker can simply infer.
    ///
    /// **No type equality is passed, and none is needed.** Theorem 6.7 points
    /// each side at `•` from that side's own premises alone; the two endpoints
    /// of a reduction do have definitionally equal types, but reaching for that
    /// fact would mean calling `def_eq` from inside the certification of a whnf
    /// step, which is the one thing the reduction path must not do.
    /// [`Certifier::proof_irrel`] takes a `ty_eq` because it is *given* one —
    /// there it is a side condition the checker had to establish anyway — and
    /// it puts it to a use that does not arise here (`share_prop`).
    ///
    /// The default delegates to [`Certifier::admit`] under `proj_reduce`, so a
    /// backend with nothing to say reports the gap it always reported, under the
    /// name of the reduction rather than the name of the site that noticed.
    fn proj_red(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
        redex_proof: Option<crate::tc::Proof<'t, Self::Typing>>,
        reduct_proof: Option<crate::tc::Proof<'t, Self::Typing>>,
    ) -> Self::Cert {
        let _ = (redex_proof, reduct_proof);
        self.admit(ctx, redex, reduct, Admit::ProjRed.name())
    }

    /// **Proof irrelevance**: `a ≡ b` because both are proofs, of propositions
    /// the checker has just shown definitionally equal.
    ///
    /// Every premise is handed over, because the checker holds every one of
    /// them at the moment it asks:
    ///
    /// * `a_mem` / `b_mem` — `⟦a⟧ ∈ ⟦a_ty⟧` and `⟦b⟧ ∈ ⟦b_ty⟧`, from `infer`;
    /// * `a_prop` / `b_prop` — `⟦a_ty⟧ ∈ U₀` and `⟦b_ty⟧ ∈ U₀`, from the same
    ///   inference one level up (`⟦Sort 0⟧` *is* `U₀`, so no new derivation is
    ///   involved — only not discarding one);
    /// * `ty_eq` — `⟦a_ty⟧ = ⟦b_ty⟧`, the side condition, which is not idle: it
    ///   carries either side's `∈ U₀` across to the other when only one of the
    ///   two was derivable.
    ///
    /// Those are exactly the premises of Carneiro's Theorem 6.7, and the whole
    /// point of the method is that they arrive rather than being searched for.
    /// The default delegates to [`Certifier::admit`], as every other rule that
    /// a backend may have nothing to say about does.
    #[allow(clippy::too_many_arguments)]
    fn proof_irrel(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        a_ty: ExprPtr<'t>,
        b_ty: ExprPtr<'t>,
        a_mem: Self::Typing,
        a_prop: Self::Typing,
        b_mem: Self::Typing,
        b_prop: Self::Typing,
        ty_eq: &Self::Cert,
    ) -> Self::Cert {
        let _ = (a_ty, b_ty, a_mem, a_prop, b_mem, b_prop, ty_eq);
        self.admit(ctx, a, b, Admit::ProofIrrel.name())
    }

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

    /// **An application's argument was checked at the binder's domain** — the
    /// handoff that lets a later beta contraction of that very argument take
    /// its domain obligation from the check instead of searching for it.
    ///
    /// `infer_app` establishes `⟦arg⟧ ∈ ⟦dom⟧` for every argument of every
    /// checked application: the argument's own typing converted along the
    /// `assert_def_eq` certificate ([`Certifier::ty_conv`]). Until this method
    /// existed that composition had exactly one consumer — the application
    /// rule — and was built only when the *head's* derivation was still alive,
    /// so for the majority of applications (any whose head is an
    /// evidence-less constant) the argument's typing was established and
    /// thrown away. The beta rule then re-discovered the same fact per redex
    /// by `has_type` search, and hoisted the membership as an assumption when
    /// the search failed — `THREADING-CENSUS.md` §1.3's largest re-discovery
    /// site.
    ///
    /// A backend that keeps a store reads it back in its beta rule, checked
    /// against the claim like every recall. The default does nothing, which is
    /// correct for the null backend: its typings carry no information, so
    /// there is nothing to hand off.
    fn app_arg_checked(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        arg: ExprPtr<'t>,
        dom: ExprPtr<'t>,
        typing: &Self::Typing,
    ) {
        let _ = (ctx, arg, dom, typing);
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
    /// which enumerates them. The count of surviving `admit` sites is the honest
    /// measure of how far the milestone-3 work has to go, and it must reach zero
    /// before the TG backend can be trusted.
    ///
    /// **A backend must not try to prove the claim here.** This method is
    /// reached only when the checker concluded by a rule it cannot justify, and
    /// a backend that goes looking for a derivation anyway is optimising the
    /// wrong number: when the search succeeds it converts a specific, fixable
    /// defect — the *rule* that concluded the step should have asked for a
    /// certificate — into a green tick at the funnel that noticed. The TG
    /// backend did exactly that, and it was hiding 20 uncertified projection
    /// reductions a run on `init-prelude`. A backend that can justify a class of
    /// steps says so by implementing the rule for them, as
    /// [`Certifier::iota`], [`Certifier::proj_cong`] and
    /// [`Certifier::proof_irrel`] do.
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
    fn eta(
        &mut self,
        _: &mut TcCtx<'t, 'p>,
        _a: ExprPtr<'t>,
        _b: ExprPtr<'t>,
        _expansion: ExprPtr<'t>,
        _expanded: (),
    ) {
    }
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

/// The variable under which a process declares that it must not execute any
/// code the `stepcount` or `tg` features can change.
///
/// # Why a runtime assertion and not a comment
///
/// `ci/check.sh` used to run `cargo test --workspace` three times — plain,
/// `--features stepcount`, `--features tg` — and two thirds of that was spent
/// on crates the two features cannot reach. `kernel` and `derived` do not link
/// `nanoda_lib` at all; `mini` links it for the parser and the level pre-pass
/// and for nothing else. So the matrix is now `-p nanoda_lib` for the two
/// feature runs, which is only sound while this holds:
///
/// > Every item `stepcount` or `tg` gates lives in `certify.rs`,
/// > `stepcount.rs`, `tg.rs` or the binary's `main.rs`; and every one of them
/// > that is reachable from library code is reachable only through a
/// > [`crate::tc::TypeChecker`], which builds its backend right here, in its
/// > constructor.
///
/// That is a claim about the call graph, and a claim about a call graph decays
/// the moment somebody adds an edge. So it is enforced instead of asserted:
/// `ci/check.sh` runs the non-`checker` half of the workspace with this
/// variable set, and building a backend under it **panics**. The first `mini`
/// test that starts driving the checker turns the *plain* run red and says the
/// matrix has to widen again — rather than the coverage being lost in silence,
/// which is the failure mode the whole SKIP-is-not-PASS design exists to stop.
///
/// It costs one relaxed atomic load per backend built, which is once per
/// declaration checked; the environment is read once.
pub const FEATURE_INERT_VAR: &str = "NANODATG_ASSERT_FEATURE_INERT";

/// Cached reading of [`FEATURE_INERT_VAR`]. Unset, empty and `0` are all off,
/// matching how `ci/check.sh` treats `NANODATG_REQUIRE_CORPUS`.
static FEATURE_INERT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

#[cold]
#[inline(never)]
fn feature_inert_violated() -> ! {
    panic!(
        "{FEATURE_INERT_VAR} is set and a checker proof backend was built anyway.\n\
         \n\
         This process was run as part of the half of the workspace that \
         `ci/check.sh` does *not* re-run under `--features stepcount` and \
         `--features tg`, on the argument that it never executes any code \
         those features change. Building a backend is exactly that code. \
         Either undo the edge that reached `TypeChecker`, or widen the two \
         feature steps in `ci/check.sh` back to the crates that now need them \
         — but do not silence this, because silencing it is the lost coverage."
    )
}

/// Panic if this process promised not to execute feature-varying code.
#[inline]
fn assert_feature_inert() {
    let on = *FEATURE_INERT.get_or_init(|| {
        match std::env::var_os(FEATURE_INERT_VAR) {
            None => false,
            Some(v) => !v.is_empty() && v != "0",
        }
    });
    if on {
        feature_inert_violated()
    }
}

/// Build the active backend.
///
/// The `Env` is what lets the TG backend resolve a constant to its *value*, so
/// that `⟦c⟧` can be introduced as an explicit definition `⟦c⟧ := ⟦value⟧`
/// rather than as an opaque symbol. Without it, delta reduction could never be
/// justified: there would be nothing relating the constant to what it unfolds
/// to. The null backend ignores it.
#[cfg(feature = "tg")]
pub fn new_backend<'x, 't: 'x, 'p: 't>(env: &'x crate::env::Env<'x, 't>) -> Backend<'x, 't, 'p> {
    assert_feature_inert();
    crate::tg::TgBackend::new(env)
}

/// Build the active backend (null variant; the environment is unused).
#[cfg(not(feature = "tg"))]
pub fn new_backend<'x, 't: 'x, 'p: 't>(_env: &'x crate::env::Env<'x, 't>) -> Backend<'x, 't, 'p> {
    assert_feature_inert();
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
    ///
    /// **No longer raised by the checker.** The comparison is a rule on the
    /// backend boundary ([`Certifier::local_eq`]), fed by the binder types'
    /// own certificate — which this arm used to establish and discard. The
    /// variant stays because `local_eq`'s *default* implementation delegates
    /// to [`Certifier::admit`] under this reason string, so a backend without
    /// the rule still reports its gaps here.
    Local,
    /// Two projections of def-eq structures (`def_eq_proj`).
    ///
    /// **No longer raised by the checker.** Projection congruence is a rule on
    /// the backend boundary ([`Certifier::proj_cong`]), fed by the structures'
    /// own certificate, so `def_eq_proj` counts as a real rule. The variant
    /// stays because `proj_cong`'s *default* implementation delegates to
    /// [`Certifier::admit`] under this reason string, so a backend with no
    /// interpretation of projections still reports its gaps here.
    Proj,
    /// Proof irrelevance: two proofs of def-eq propositions.
    ///
    /// **No longer raised by the checker**, for the same reason:
    /// [`Certifier::proof_irrel`] is a rule, handed the two memberships and the
    /// two `∈ U₀` witnesses that inference established, and its default
    /// delegates to `admit` under this string.
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
    ///
    /// **No longer raised.** The shortcut's whole content is `whnf(x_n) =
    /// Bool.true`, and every leg of that was already in hand or in the trace
    /// memo: `x ≡ x_n` from the entry reduction, `x_n ≡ whnf(x_n)` from the
    /// recorded trace, and `whnf(x_n)` *is* `y_n` by hash-consing. The
    /// shortcut now composes them (`def_eq`, the `Bool.true` branch) instead
    /// of admitting; the individual reduction steps account for themselves
    /// under their own rules. Kept so the label stays enumerable and a
    /// reappearance in [`admit_report`] would be visible as a regression.
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
    ///
    /// No longer raised by the checker: projection reduction is a rule on the
    /// backend boundary ([`Certifier::proj_red`]), and this is the reason string
    /// that rule reports when it declines — as its default implementation always
    /// does, and as a backend that neither interprets structures nor can point
    /// both endpoints at `•` does too.
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
    /// `tc.rs`: a side condition inside a definitional-equality rule, where
    /// nothing downstream can take the evidence.
    ///
    /// **The justification this variant used to carry — "the conclusion drawn
    /// is itself an admit and the side condition's evidence has nothing to
    /// compose with" — was false, and stage 0 is what made that visible.** Two
    /// of the sites it named, `def_eq_proj` and `eta`, had a consumer all
    /// along: the projection congruence *is* the structures' equation, and eta's
    /// recursive comparison is half of eta's own conclusion. Both are now
    /// premises of real rules ([`Certifier::proj_cong`], [`Certifier::eta`]) and
    /// are no longer dropped. `proof_irrel`'s two typings were the same story
    /// one judgement up, and are [`Certifier::proof_irrel`]'s premises now.
    ///
    /// What is left under this label is the residue where the claim really does
    /// hold: `def_eq_local` (two locals with the same id interpret to the same
    /// variable, so the binder-type equality licenses nothing), `unit_like` and
    /// `eta_struct` (blocked on interpreting structures, not on threading), and
    /// `to_ctor_when_k` (whose equality is what a future ι-K rule will want).
    /// The general lesson is worth keeping with the variant: "nothing to
    /// compose with" is a claim about the *rules that exist today*, and it goes
    /// stale the moment a rule is added.
    DefEqSide,
    /// The `Π`'s domain check in `infer_pi`/`infer_lambda`: the binder type has
    /// to *be* a type, and the sort it infers as is used for the universe
    /// algebra, not for a membership.
    ///
    /// Still genuine, but narrower than the count suggests: the evidence has one
    /// foreseeable consumer, `point_of_proof`-style reasoning about a domain
    /// that is a proposition, and stage 0 serves that consumer from the
    /// `is_proposition` witness at far fewer sites. Note the label is *used* at
    /// one site it does not describe — `check_declar_info`, which is a
    /// declaration's type and not a binder's domain.
    BinderSort,
    /// `tc.rs`: a **shape probe** — inference run only to look at the result's
    /// head, with no judgement drawn from it.
    ///
    /// `is_proposition`/`is_proof` used when only the `bool` is wanted,
    /// `infer_proj`'s structure and `Prop`-field checks, `infer_let`'s
    /// annotation, `strong_reduce`'s. These were counted under
    /// [`Dropped::DefEqSide`], which named the wrong thing twice over: they are
    /// not side conditions and they are not inside definitional-equality rules.
    /// Keeping them apart is what lets the `DefEqSide` row above be read as the
    /// def-eq residue it claims to be.
    Probe,
    /// `tc.rs`: the same, for the two predicates specifically, where a *witness*
    /// exists and this caller has no use for it.
    ///
    /// Split from [`Dropped::Probe`] because the two say different things: a
    /// probe's evidence has no consumer anywhere, while every row here is a
    /// place that could be threaded and has not been. This is the row that
    /// should shrink as later stages find consumers, and it is deliberately not
    /// folded into a total that cannot move.
    Predicate,
}

/// Number of [`Dropped`] variants.
pub const N_DROPPED: usize = 6;

impl Dropped {
    /// A stable name, used in the report.
    pub const fn name(self) -> &'static str {
        match self {
            Dropped::Quot => "quotient declaration shape checks",
            Dropped::Inductive => "inductive telescope checks",
            Dropped::DefEqSide => "side conditions inside def-eq rules",
            Dropped::BinderSort => "binder domains checked to be types",
            Dropped::Probe => "inference run as a shape probe",
            Dropped::Predicate => "is_proposition/is_proof, witness unwanted",
        }
    }

    /// All variants, for reporting.
    pub const ALL: [Dropped; N_DROPPED] = [
        Dropped::Quot,
        Dropped::Inductive,
        Dropped::DefEqSide,
        Dropped::BinderSort,
        Dropped::Probe,
        Dropped::Predicate,
    ];
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

/// **The reduct memos, read as caches of evidence** — the audit the goal
/// clause's "including all its cache" asks for, made a standing row.
///
/// The two reduct memos store a `Reduct { reduct, trace }`, and the trace
/// carries a slot for its own certificate ([`crate::reduct::Trace::cert`]), so
/// on paper a memo hit answers with evidence. What the row measures is whether
/// that is true in practice, because the slot is filled at exactly one place
/// ([`crate::tc::TypeChecker::certify_reduct`]) and only for a trace that is a
/// memo entry's *own root*: a composite built by `whnf_reduce`'s
/// delta-unfolding loop, and every interior `Seq` node of any trace, has a slot
/// that is never written, and its certificate is rebuilt per call.
#[derive(Clone, Copy)]
#[repr(usize)]
pub enum TraceCert {
    /// A trace node answered from its own slot — the memo returning evidence.
    Recalled,
    /// A trace node's certificate was derived because the slot was empty.
    Derived,
    /// `certify_reduct` wrote the certificate back into the node.
    Parked,
    /// It did not, because the node is not the root of a live memo entry:
    /// `whnf_reduce`'s delta loop builds a composite over the no-unfolding
    /// entries, and `whnf_no_unfolding_cheap_proj` builds a trace it never
    /// memoises. Parking in the latter is what cost 843 → 5037 escapes.
    NotAMemoRoot,
    /// …or because the certificate stands under kernel hypotheses, which a
    /// memo keyed on the input `ExprPtr` alone must never import
    /// ([`hypothesis_free`]).
    Hypothetical,
    /// A `NotAMemoRoot` node that *is* the full-`whnf` memo's own root — the
    /// share of the refusals a store-back extended to that memo would convert.
    WhnfRoot,
}

impl TraceCert {
    pub const ALL: [TraceCert; 6] = [
        TraceCert::Recalled,
        TraceCert::Derived,
        TraceCert::Parked,
        TraceCert::NotAMemoRoot,
        TraceCert::Hypothetical,
        TraceCert::WhnfRoot,
    ];
    pub fn name(self) -> &'static str {
        match self {
            TraceCert::Recalled => "recalled from the trace's own slot",
            TraceCert::Derived => "derived (slot empty)",
            TraceCert::Parked => "parked back into the memo entry",
            TraceCert::NotAMemoRoot => "not parked: not a live memo entry's root",
            TraceCert::Hypothetical => "not parked: stands under kernel hypotheses",
            TraceCert::WhnfRoot => "  …of those, the full-whnf memo's own root",
        }
    }
}

#[cfg(feature = "stepcount")]
const N_TRACE_CERT: usize = 6;
#[cfg(feature = "stepcount")]
static TRACE_CERT: [std::sync::atomic::AtomicU64; N_TRACE_CERT] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_TRACE_CERT];

/// Record one reduct-memo evidence event. Compiles to nothing without
/// `stepcount`.
#[inline(always)]
pub fn bump_trace_cert(k: TraceCert) {
    #[cfg(feature = "stepcount")]
    TRACE_CERT[k as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(feature = "stepcount"))]
    let _ = k;
}

/// The reduct-memo evidence ledger, or `None` if counting is off or no
/// reduction was ever certified.
pub fn trace_cert_report() -> Option<String> {
    #[cfg(feature = "stepcount")]
    {
        use std::sync::atomic::Ordering::Relaxed;
        let total: u64 = TraceCert::ALL.iter().map(|k| TRACE_CERT[*k as usize].load(Relaxed)).sum();
        if total == 0 {
            return None
        }
        let width = TraceCert::ALL.iter().map(|k| k.name().len()).max().unwrap_or(0) + 2;
        let mut s = String::from("reduct memos, as caches of evidence\n");
        for k in TraceCert::ALL {
            let n = TRACE_CERT[k as usize].load(Relaxed);
            s.push_str(&format!("  {:<width$}  {n:>14}\n", k.name()));
        }
        return Some(s)
    }
    #[allow(unreachable_code)]
    None
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
