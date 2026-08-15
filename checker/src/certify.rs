//! The proof-backend boundary: which backend is in force, the ledgers that
//! count where evidence ran out, and the result type that carries certificates
//! out of definitional-equality checks.
//!
//! # Why the boundary lives here and not in the kernel
//!
//! The rules the checker calls are *an interface*, not a rule of the theory.
//! They construct no [`Thm`](kernel::Thm) themselves and adding one adds no
//! proving power — a backend can still only reach a `Thm` through the kernel's
//! primitive rules. So none of this is part of the trusted computing base, and
//! keeping it out of `kernel/` leaves that crate exporting nothing but the type
//! theory: `Thm`, `Formula`, `Term`, the rules and the axioms.
//!
//! The dependency points untrusted → trusted only, and the boundary is stated
//! in the checker's own vocabulary: the rules are inherent methods on
//! [`crate::tg::TgBackend`], over the checker's interned expressions
//! (`ExprPtr`) read through the checker's arena (`TcCtx`).
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
//! # There is one backend, and it is not selected
//!
//! [`Backend`] is [`crate::tg::TgBackend`], in every build. There is no second
//! implementation and no `cfg` choosing between them, which is why [`Cert`] and
//! [`Typing`] can name [`crate::tg::TgCert`] and [`crate::tg::TgTyping`]
//! outright rather than through a trait's associated types.
//!
//! It was not always so. A `NullCertifier` whose `Cert` was `()` used to be the
//! default, with the real backend behind `--features tg`, and a `Certifier`
//! trait existed to hold the two in conformance. The arrangement paid for
//! itself once — it is what kept the checker in the shape the real backend
//! needed, so that milestone 3 did not discover that certificates were never
//! obtainable at the places that claimed them — and then stopped. The trait was
//! never used polymorphically; `TgBackend` overrode **every one** of its 36
//! methods, so its defaults described only the null backend; and the feature
//! selecting between them had grown into a second build configuration whose
//! test coverage was strictly smaller (four whole suites were `cfg`-ed to
//! nothing in it, which is `TEST-INVENTORY.md` §1.2's third shape of "skip is
//! not pass").
//!
//! What replaces it is `mini`'s arrangement, which is the one that finished:
//! **one concrete evidence type, threaded directly**. Note the half of mini's
//! shape that deliberately did *not* transfer — `mini::kernel::Checker` keeps
//! its evidence in an `Option<Th>` because it has a genuine zone with no
//! interpretation at all (the declaration-shape zone, at symbolic levels).
//! `tc.rs` has no such zone: every `TypeChecker` is built at a ground
//! instantiation with an interpretation available, so an `Option` here would
//! have no inhabitant for its `None` and would be a build switch wearing a
//! runtime disguise.


/// The proof backend in force. **There is one**, in every build: the
/// Tarski–Grothendieck backend, whose [`Cert`] is a genuine kernel theorem.
///
/// The lifetimes are the checker's own: `'x` is the borrow of the [`crate::env::Env`]
/// the backend resolves constants through, `'t` the term arena and `'p` the
/// parsed export.
pub type Backend<'x, 't, 'p> = crate::tg::TgBackend<'x, 't, 'p>;

/// Build the backend.
///
/// The `Env` is what lets the backend resolve a constant to its *value*, so
/// that `⟦c⟧` can be introduced as an explicit definition `⟦c⟧ := ⟦value⟧`
/// rather than as an opaque symbol. Without it, delta reduction could never be
/// justified: there would be nothing relating the constant to what it unfolds
/// to.
pub fn new_backend<'x, 't: 'x, 'p: 't>(env: &'x crate::env::Env<'x, 't>) -> Backend<'x, 't, 'p> {
    crate::tg::TgBackend::new(env)
}

/// The certificate type: a definitional-equality judgement's evidence.
pub type Cert<'t, 'p> = crate::tg::TgCert;

/// The typing-certificate type: a typing judgement's evidence.
pub type Typing<'t, 'p> = crate::tg::TgTyping;

/// Whether a typing certificate carries **no evidence at all**.
///
/// The inference rules use this as a short-circuit: a rule whose premise is a
/// hole cannot conclude anything, so the terms it would otherwise have to build
/// (the partial applications of a spine, the `Π` at each binder of a lambda
/// chain) are not built.
pub fn typing_is_gap(t: &Typing<'_, '_>) -> bool { t.is_gap() }

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
/// write site in `TypeChecker::certify_reduct` by [`is_unconditional`]; the
/// union-find's edges; and `TcCache::infer_cache_*`, which deliberately admits
/// *conditional* typings and is discussed at its insertion point. Sealing
/// `TgCert` itself was considered and rejected — see [`crate::sealed`].
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
/// re-asserts them silently. This remains the predicate for stores whose key
/// also accounts for a conditional formula; the checker's reduction memos do
/// not, and therefore use [`is_unconditional`] instead.
pub fn hypothesis_free(c: &Cert<'_, '_>) -> bool { c.hyps().is_empty() }

/// The result of a definitional-equality check.
///
/// `Some(cert)` means the two terms were shown equal, and `cert` is why.
/// `None` means they were not shown equal — which, for a *checker*, is the
/// same as "reject": we never assert an equality we cannot justify.
pub type DefEq<'t, 'p> = Option<Cert<'t, 'p>>;

/// The places that still conclude an equality without a real justification,
/// i.e. that call [`crate::tg::TgBackend::admit`].
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
    /// **Not raised by the checker.** The comparison is a rule
    /// ([`crate::tg::TgBackend::local_eq`]), fed by the binder types' own
    /// certificate — which this arm used to establish and discard. The rule
    /// itself reports under this string, at its one decline: two locals of the
    /// same level whose declared types are definitionally equal but interpret
    /// to *different* terms are two distinct kernel variables, and no rule of
    /// the backend relates two distinct free variables.
    Local,
    /// Two projections of def-eq structures (`def_eq_proj`).
    ///
    /// **Not raised by the checker.** Projection congruence is a rule
    /// ([`crate::tg::TgBackend::proj_cong`]), fed by the structures' own
    /// certificate, so `def_eq_proj` counts as a real rule. The rule reports
    /// under this string when it declines.
    ///
    /// The label still names the *site* rather than the reason, which is the
    /// defect class this project has paid for most. It is one of three left —
    /// see the note on [`Admit::ProjRed`].
    Proj,
    /// Proof irrelevance: two proofs of def-eq propositions.
    ///
    /// **Not raised by the checker**, for the same reason:
    /// [`crate::tg::TgBackend::proof_irrel`] is a rule, handed the two
    /// memberships and the two `∈ U₀` witnesses that inference established, and
    /// it reports under this string when it declines. Site-named, like
    /// [`Admit::Proj`] — see [`Admit::ProjRed`].
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
    /// Not raised by the checker: projection reduction is a rule
    /// ([`crate::tg::TgBackend::proj_red`]), and this is what that rule reports
    /// when it declines.
    ///
    /// # These three labels name a site, not a reason
    ///
    /// `proj_reduce`, `def_eq_proj` and `proof_irrel` are the last labels in
    /// this enum that a *rule* still mints about itself rather than about what
    /// stopped it. Compare `iota`, which mints seven — "no interpretation — a
    /// K-like eliminator", "the major premise is not a constructor", "the
    /// constructor's bridge is not about this spine", and so on — and `sort`
    /// and `const_eq`, which mint "…modulo level algebra". A reader of the
    /// report can act on those and cannot act on these.
    ///
    /// Splitting them is a real improvement and is **not** free: every row in
    /// the report is ratcheted by name in `checker/tests/tg_tutorial.rs`, whose
    /// own rule 2 is "assert on `row`, never on `rows_or_zero`", precisely
    /// because a renamed row turns every `== 0` and `<= n` over it green. So a
    /// split has to move the ratchets in the same commit, and it is deliberately
    /// not bundled with a refactor whose invariant is that no row moves.
    ProjRed,
    /// Iota: a recursor applied to a constructor application.
    ///
    /// **No longer raised, by anything.** ι is a rule
    /// ([`crate::tg::TgBackend::iota`]) rather than an admission, and when that
    /// rule declines it reports what stopped it — "no interpretation — a K-like
    /// eliminator", "the major premise is not a constructor", and five more —
    /// never this bare label.
    ///
    /// The last construction site was the `Certifier` trait's *default*
    /// implementation of `iota`, which delegated to `admit` under this string
    /// so that a backend with nothing to say still reported a gap. That trait
    /// had one implementation and it overrode every method, so the default
    /// described only `NullCertifier`; both are gone. Kept, like
    /// [`Admit::Binder`], [`Admit::App`] and [`Admit::BoolTrue`], so the label
    /// stays enumerable and a reappearance in [`admit_report`] would be visible
    /// as a regression.
    Iota,
    /// Quotient computation: `Quot.lift`/`Quot.ind` applied to a `Quot.mk`.
    Quot,
    /// Native arithmetic on literals (`Nat.add`, `Nat.succ`, …).
    ///
    /// **Not a primitive `ℕ`.** This said "Milestone 4 replaces this with the
    /// kernel's primitive `ℕ` and its rule schemas", and that option is
    /// refused: `kernel::term::TermData` has three variants and function
    /// symbols enter only through conservative definitional extension, so the
    /// primitive signature stays `{∈, =}` — a primitive sort would be a change
    /// to the closed TCB. What replaces this is a **certificate built from
    /// `derived::nat`'s binary operations over von Neumann `ω`**; see
    /// `DECISIONS.md`, 2026-08-11.
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
    /// premises of real rules ([`crate::tg::TgBackend::proj_cong`],
    /// [`crate::tg::TgBackend::eta`]) and
    /// are no longer dropped. `proof_irrel`'s two typings were the same story
    /// one judgement up, and are [`crate::tg::TgBackend::proof_irrel`]'s
    /// premises now.
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
    /// …or because it still carries antecedents. Parking such a certificate is
    /// sound as a closed implication, but the parked copy crosses no binder and
    /// can never discharge them, so it is real boundary debt.
    Conditional,
    /// …or because the certificate stands under kernel hypotheses, which a
    /// memo keyed on the input `ExprPtr` alone must never import
    /// ([`hypothesis_free`]).
    Hypothetical,
    /// A `NotAMemoRoot` node that *is* the full-`whnf` memo's own root — the
    /// share of the refusals a store-back extended to that memo would convert.
    WhnfRoot,
}

impl TraceCert {
    pub const ALL: [TraceCert; 7] = [
        TraceCert::Recalled,
        TraceCert::Derived,
        TraceCert::Parked,
        TraceCert::NotAMemoRoot,
        TraceCert::Conditional,
        TraceCert::Hypothetical,
        TraceCert::WhnfRoot,
    ];
    pub fn name(self) -> &'static str {
        match self {
            TraceCert::Recalled => "recalled from the trace's own slot",
            TraceCert::Derived => "derived (slot empty)",
            TraceCert::Parked => "parked back into the memo entry",
            TraceCert::NotAMemoRoot => "not parked: not a live memo entry's root",
            TraceCert::Conditional => "not parked: still has antecedents",
            TraceCert::Hypothetical => "not parked: stands under kernel hypotheses",
            TraceCert::WhnfRoot => "  …of those, the full-whnf memo's own root",
        }
    }
}

#[cfg(feature = "stepcount")]
const N_TRACE_CERT: usize = 7;
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
