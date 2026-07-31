//! The Tarski–Grothendieck proof backend: real [`kernel::Thm`] certificates.
//!
//! # What this does and does not claim
//!
//! Every Lean expression is interpreted as a term of the kernel's first-order
//! language, and every definitional-equality certificate is a genuine kernel
//! theorem `⟦a⟧ = ⟦b⟧` — derived from the equality axioms by real inference
//! rules, not asserted.
//!
//! Most of the interpretation is still **pure signature extension**: fresh
//! symbols with *no* axioms (the dependent `pi`, `let`, `proj`, `bvar`, the
//! level formers, …). That is unconditionally conservative, so nothing here
//! enlarges the trusted base or risks consistency. Four parts of the
//! interpretation are now *definitional extensions* instead, which is what
//! makes them mean something:
//!
//! * **`Sort`**. `⟦Sort 0⟧` is a fixed constant and `⟦Sort (u+1)⟧ := U(⟦Sort u⟧)`,
//!   where `U` is the least-Grothendieck-universe operator of
//!   [`derived::universe`]. `⊢ ∀x. x ∈ U(x)` then gives
//!   `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` outright — the one typing fact this backend has.
//!   Levels that are not literal successors keep an opaque `sort` symbol.
//! * **`App`**. `⟦f a⟧ := app(⟦f⟧, ⟦a⟧)`, with `app` the set-theoretic
//!   application of [`derived::funcs`].
//! * **`Lam`**. `⟦λx:A. b⟧` is the *function graph* `{⟨x, t(x)⟩ : x ∈ ⟦A⟧}` of
//!   [`derived::funcs::lambda`]. See "Lambdas" below for how the body is turned
//!   into a function symbol, and why the version used here is `lambda_n`.
//! * **`Pi`**. `⟦A → B⟧ := fs(⟦A⟧, ⟦B⟧)`, the set-theoretic function space of
//!   [`derived::funspace`], when the body does not mention the binder; and
//!   `⟦Π x:A. B⟧ := dprod_C(s⃗, ⟦A⟧)`, the **dependent product** over the fibre
//!   `x ↦ ⟦B⟧`, when it does. The fibre is built by the same skeleton
//!   decomposition the lambdas use (see "Lambdas" below), so the binder is
//!   opened at a local and non-dependence is decided *exactly* — "the
//!   interpreted body does not mention this binder's variable" — rather than
//!   conservatively from the loose-bvar count. With every binder in a `Π` tower
//!   opened, an interpreted term contains no `bvar` symbols at all.
//!
//! With those in place [`derived::funcs::beta_conditional`] applies, and
//! [`Certifier::beta`] is a real derivation rather than an admit — modulo one
//! premise it cannot always discharge, discussed under "What beta still costs".
//!
//! # Lambdas: how the body becomes a function symbol
//!
//! `lambda` wants the body as a *unary* function symbol `t`, but a Lean lambda
//! body is an open expression. Instantiating the binder at a fresh local and
//! interpreting gives a term `bt` containing one distinguished free variable
//! `v`; the obvious move is then `t(v) := bt`. That is wrong as it stands,
//! because a nested lambda's body mentions the *enclosing* binders too, and a
//! defined symbol may not contain free variables that are not among its
//! parameters (it would not be a conservative extension).
//!
//! The fix is to abstract more: `bt` is split into a **skeleton** — the part
//! that actually mentions `v` — and the list of **maximal `v`-free subterms**,
//! which become extra parameters. So
//!
//! ```text
//! ⟦λ y:A. b⟧  :=  lam_C(s₁, …, s_k, ⟦A⟧)
//! ```
//!
//! where `C` is the skeleton, `lam_C` is the graph symbol built once per
//! skeleton, and `s⃗` are the abstracted subterms. This decomposition is
//! canonical *and* stable under substitution — substituting into an `s_i`
//! keeps it `v`-free and leaves `C` alone — which is exactly the property beta
//! needs: `⟦b[a]⟧` really is `⟦b⟧` with the abstracted positions filled in, so
//! the two sides of the beta equation line up syntactically instead of merely
//! morally. Without it, `⟦(λx.λy.x) P⟧` and `⟦λy.P⟧` would be built from
//! unrelated symbols and no chain of steps could connect them.
//!
//! A skeleton's graph is derived **once for the whole run**, not once per
//! declaration: the signature every backend builds terms in is shared per
//! thread (see [`Shared`]), so two occurrences of one body shape in two
//! declarations are the same *term* and hit the same cache. That is what makes
//! the construction affordable for every lambda, with no cut-off on how many
//! subterms a body may abstract.
//!
//! The extra parameters are why `lambda_n`, `beta_conditional_n` and
//! `lam_ext_n` exist: the derived originals take a unary body symbol, and `t`
//! here has arity `k + 1`. They are the derived derivations with the prefix
//! threaded through, and coincide with them at `k = 0`. `lam_ext_n` threads
//! *two* prefixes, of independent lengths, since the two lambdas it relates
//! have unrelated skeletons.
//!
//! # What beta still costs
//!
//! `beta_conditional` is *conditional*: a set-theoretic function has a set
//! domain, so `app(lam(A), a) = t(a)` needs `a ∈ A`. Discharging that is a
//! **typing** obligation — `⟦a⟧ ∈ ⟦A⟧` whenever Lean says `a : A` — and it is
//! Lean's typing judgement, so it is discharged by a family of clauses, one per
//! typing rule: [`TgBackend::has_type`].
//!
//! Two of them are facts about the *operators* the interpretation is built from
//! (`domain_premise`):
//!
//! * `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧`, from `⊢ ∀x. x ∈ U(x)` — which is not restricted
//!   to sorts, and settles any obligation whose target is `U(⟦a⟧)`;
//! * `⟦A → A⟧ ∈ ⟦Sort (u+1)⟧` when `⟦A⟧` is `⟦Sort u⟧`, from
//!   [`derived::funspace`]'s `⊢ ∀a. fs(a,a) ∈ U(a)`.
//!
//! The restriction to the diagonal `fs(a,a)` is not a shortcut either: the
//! two-argument form `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))` exists,
//! but its antecedent needs closure of `U(x)` under binary unions, which is
//! unproved.
//!
//! The rest are structural. A constant transfers the obligation to its *value*
//! along the defining equation; an application is the characteristic property of
//! its function's type — `fs`'s `app(f,x) ∈ b`, or the dependent product's
//! `∀x ∈ A. app(f,x) ∈ b(x)` conjunct with the fibre unfolded. A local is the
//! carried assumption. A lambda and a `Π` are *not yet reachable*: their rules
//! are [`derived::ext::lam_in_dprod`] and [`derived::ext::dprod_in_universe`],
//! which exist for a **unary** body and fibre symbol, while every lambda and `Π`
//! here carries the hole prefix the skeleton decomposition gives it — so they
//! need the same prefix-threaded treatment `beta_conditional_n`, `lam_ext_n`,
//! `dprod_ext_n` and `dprod_const_fibre_n` already have, and `lam_in_dprod`'s
//! pointwise premise needs a `has_type` that can itself rest on the binder's
//! assumption.
//!
//! **That is what the remaining obligations are waiting on, and the ledger says
//! so per shape** (see [`ht_report`]). Over the tutorial corpus, of 552
//! obligations: 278 are about a *local*, which is the assumption path by design;
//! 164 are about an opaque constant or an application of one, which is an
//! inductive type, constructor or recursor and has no axioms at all, so nothing
//! about where it lives is derivable at any point; 64 are about a lambda. On
//! `init-prelude`, of 17494: 5182 local, 3959 opaque, 5497 lambda. So the
//! typing rules cannot close this category on their own — the interpretation of
//! *inductives* is what the opaque half needs, and it is out of scope for the
//! inductive-free fragment.
//!
//! Everywhere else the premise is **carried rather than admitted**. The
//! certificate becomes `⊢ (⟦a⟧ ∈ ⟦A⟧) → ⟦redex⟧ = ⟦reduct⟧` — a complete
//! derivation of a weaker statement, not an assertion — and every rule below
//! merges its premises' assumptions and lifts its reasoning through the
//! conjunction. At a `λ` binder an assumption about *that binder's own variable*
//! is discharged into `lam_ext_n`'s pointwise premise, which is exactly the
//! shape that premise wants.
//!
//! That matters because the obligation used to poison whole subtrees: a beta
//! step that could not discharge it became an admit, and every `trans`, `symm`
//! and congruence above it became "over an admitted premise". Carrying it
//! collapses each of those cascades to a single accounted gap. Measured, over
//! the tutorial corpus: 726 gaps before, 586 after, with the 206
//! `beta: argument not shown to lie in the binder's domain` gaps gone entirely;
//! on `good/init-prelude.ndjson`, 23812 before and 18025 after. `028_peano2`
//! goes from 32 gaps to 8 and `029_peano3` from 59 to 9.
//!
//! # Honesty
//!
//! **Every rule that concludes something about two specific terms is handed
//! those terms and checks its result against them.** [`Certifier::beta`],
//! [`Certifier::delta`], [`Certifier::zeta`], [`Certifier::lam_cong`],
//! [`Certifier::pi_cong`], [`Certifier::app_cong`], [`Certifier::trans`] and
//! [`Certifier::symm`] — the rules that build a chain rather than read one off —
//! check before returning [`TgCert::Proved`] that the theorem they hold is
//! literally `⟦a⟧ = ⟦b⟧` for the `a`, `b` the checker claimed equal; `refl`,
//! `sort` and `const_eq` compare the two interpretations directly.
//!
//! The check goes through [`CondEq::proves`], so a *conditional* premise is
//! matched on the same equation as an unconditional one rather than being
//! exempted from the comparison.
//!
//! A *conditional* certificate is held in its own variant and never passes for
//! an unconditional one — [`TgCert::thm`] answers `None` for it — and the
//! assumptions it advertises are checked, on construction, to be literally the
//! antecedent of the theorem it carries ([`CondEq::new`]). And a conditional
//! certificate that reaches the checker as an *answer* is not a proof of what
//! the checker claimed, so it is counted and reported as a gap; see the escape
//! ledger next to [`escaped`]. Over the tutorial corpus 128 certificates finish
//! that way, and 2507 on `init-prelude`; those numbers are in the totals above,
//! not excluded from them.
//!
//! `app_cong`, `trans` and `symm` used to be the exception — handed
//! sub-*certificates* only, so unable to see what they were supposed to be
//! proving — and are not any more. How much they were waving through is now a
//! measured quantity rather than a guess: the number of calls whose derivation
//! **fails** the comparison, reported on its own line by [`global_report`].
//!
//! | rule | tutorial corpus (91 files) | `init-prelude` |
//! | --- | ---: | ---: |
//! | `app_cong` | 9 (in 7 files) | 2 |
//! | `trans` | 0 | 0 |
//! | `symm` | 0 | 0 |
//!
//! It is a separate line and not a gap row, because a failed guard does not
//! always mean a gap: when the two sides interpret to the *same* term,
//! reflexivity proves the claim outright and there is nothing left to report.
//! That is what happens to both `init-prelude` mismatches, which is why the
//! total there goes **down** by one — a `trans` that used to compose over an
//! admitted premise now composes over a real reflexivity. The nine tutorial
//! mismatches are genuine gaps and are reported as such, taking the corpus from
//! 535 to 545: nine `congruence: derived equation does not match the claim`,
//! plus a cascade of nine into `pi congruence over an admitted body premise`
//! (156 → 165) and one into `congruence over an admitted premise` (36 → 37),
//! less nine that were being reported as `pi congruence: the body certificate is
//! not the fibres' pointwise equation` (12 → 3). The count rose because the
//! mis-stated claim is now named where it is made instead of upstream of it. All
//! nine fall in files that already had gaps; the 65 files at zero gaps are the
//! same 65.
//!
//! That `trans` and `symm` never miss, and that `app_cong` misses twice in
//! 79,516 derivations on `init-prelude`, is worth stating plainly, because it
//! contradicts what this module used to say (see the `Π` section below): the
//! certificates arriving at a binder are about the terms the checker claimed, so
//! `app_cong` was not the reason `pi_cong` could not use them.
//!
//! [`Certifier::pi_cong`] is handed both terms and checks, and has three routes
//! to a derivation — congruence, Extensionality and the constant-fibre bridge.
//! What each buys is stated plainly next.
//!
//! # What `Π` congruence still costs
//!
//! A `Π` type interprets two ways — `fs` when the body ignores the binder and
//! `dprod_C` when it does not — and the head symbol of the second depends on the
//! *shape* of the fibre. So `pi_cong` is in the same three positions `lam_cong`
//! is, and takes the same three routes:
//!
//! * both sides `fs` — congruence, via the derived [`derived::ext::fs_cong`];
//! * both sides the same `dprod_C` — congruence over its arguments; failing
//!   that, and for two *different* `dprod`s, dependent-product Extensionality
//!   ([`dprod_ext_n`]), whose pointwise premise is read off the body certificate
//!   by the same [`TgBackend::pointwise_premise`] the lambda rule uses;
//! * one of each — the **bridge**: `dprod_const_fibre_n` says a dependent
//!   product over a *constant* fibre **is** the function space, and the fibre is
//!   constant exactly when the other side's body ignores the binder, which is
//!   what its certificate says.
//!
//! Measured on `good/init-prelude.ndjson`, against the previous encoding (a
//! dependent `Π` as an opaque `pi` symbol over the raw de Bruijn body):
//!
//! | gap | before | after |
//! | --- | ---: | ---: |
//! | `pi congruence` (all reasons) | 4538 | 4480 |
//! | … dependent/non-dependent interpret differently | 1196 | **0** |
//! | … cascade: the body premise was itself admitted | 2427 | 2868 |
//! | … the body certificate does not make the fibre constant | — | 621 |
//! | … the body certificate is not the fibres' pointwise equation | — | 283 |
//! | **TOTAL gaps** | 16009 | **15954** |
//!
//! and over the tutorial corpus 538 → 535, with 65 of 91 files at zero gaps
//! rather than 64.
//!
//! **The encoding mismatch is gone as a category, and what replaces it is
//! mostly not `pi_cong`'s to fix.** Of the 621 bridge failures, ~500 are cases
//! where the certificate handed down is *reflexive*.
//!
//! This was previously read as `app_cong` being unable to see what it was
//! supposed to be proving, and so handing up a certificate that need not be
//! about the binder's bodies at all. Guarding `app_cong` settles that question,
//! and the reading was wrong: with the guard in place `app_cong`'s derivation
//! misses its claim **twice** over the whole of `init-prelude`, and all 621
//! bridge failures and 283 pointwise failures remain, unchanged to the unit. The
//! reflexive certificates really are about the two bodies — the bodies are the
//! same term, which is why the certificate is reflexive — and what they fail to
//! establish is the thing the bridge actually needs, that the *fibre* is
//! constant in the binder. That is a property of the fibre's construction, not
//! of the certificate's provenance, and it is `pi_cong`'s to fix after all.
//!
//! The guard did move the tutorial numbers, but in the opposite direction from
//! the one that hypothesis predicts: `pi congruence: the body certificate is not
//! the fibres' pointwise equation` drops from 12 to 3 there, because nine claims
//! that used to arrive at `pi_cong` already bent are now stopped, and named, at
//! the `app_cong` that bent them.
//!
//! The largest remaining category by far is still the cascade: a beta step below
//! whose typing obligation is undischargeable, which no congruence rule can
//! repair.
//!
//! Two things this changed elsewhere, both consequences of opening the binder:
//!
//! * `def_eq_binder_aux` now instantiates `Π` frames at the locals introduced
//!   above them, exactly as it already did for `λ` frames. It deliberately did
//!   not, *because* `⟦Π⟧` was built over the raw body; that reason has gone.
//!   Without the change the bridge and the Extensionality route are unreachable
//!   below the outermost binder (measured: 16097 gaps rather than 15954).
//! * The **de Bruijn shift** category — 756 gaps where the claim had two
//!   different `bvar` symbols for one binder — has gone with the `bvar`s.

use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use crate::expr::Expr;
use crate::level::Level;
use derived::funcs::Apply;
use kernel::{Certifier, Env, FnSym, Formula, FreeVar, Term, Thm};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::rc::Rc;

/// A certificate: a real kernel theorem, a real kernel theorem that still rests
/// on assumptions, or a named gap.
///
/// Making the gap a *variant* rather than a silent success is the point. A
/// backend that could only return `Thm` would have to either refuse (breaking
/// the checker) or forge (defeating the exercise); this way an unproved step is
/// recorded, propagates through the combinators, and can be reported.
///
/// [`TgCert::Conditional`] is a *separate variant* rather than a `hyps` field on
/// `Proved`, and that is deliberate. `Proved` means "this equation is derived,
/// full stop"; every existing consumer of [`TgCert::thm`] keeps exactly that
/// reading, and a rule that has not been taught about assumptions cannot
/// silently treat a conditional derivation as an unconditional one — the
/// compiler makes it say what it does with the new variant. The cardinal rule
/// ("never return `Proved` for a theorem not matched against the claim") is
/// therefore still checkable by reading the `Proved` sites alone.
#[derive(Debug)]
pub enum TgCert {
    /// A genuine derivation of `⟦a⟧ = ⟦b⟧`.
    Proved(Thm),
    /// A genuine derivation of `⊢ (h₁ ∧ … ∧ hₙ) → ⟦a⟧ = ⟦b⟧`, `n ≥ 1`.
    ///
    /// The theorem is complete — nothing here is asserted — but the *claim* the
    /// checker made is the bare equation, so until every `hᵢ` is discharged this
    /// is a step taken on trust. See [`escape_report`]: a conditional
    /// certificate that is never handed back to a rule is counted and reported
    /// as a gap.
    Conditional {
        /// Literally `⊢ conj(hyps) → ⟦a⟧ = ⟦b⟧`; checked on construction.
        thm: Thm,
        /// The assumption atoms, in the order the left-nested conjunction
        /// `conj(R ++ [h]) = conj(R) ∧ h` puts them.
        hyps: Vec<Formula>,
    },
    /// A step that was taken on trust, tagged with why.
    Admitted(&'static str),
}

/// Cloning a conditional certificate creates a *second* obligation, and the
/// escape ledger counts copies, not derivations: a copy that is stored in one of
/// the checker's caches and a copy that is handed back as an answer are both
/// certificates that have to be accounted for. So the `Clone` impl is written
/// out rather than derived, in order to bump the counter.
impl Clone for TgCert {
    fn clone(&self) -> Self {
        match self {
            TgCert::Proved(t) => TgCert::Proved(t.clone()),
            TgCert::Conditional { thm, hyps } => {
                note_conditional();
                CONDITIONAL_COPIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                TgCert::Conditional { thm: thm.clone(), hyps: hyps.clone() }
            }
            TgCert::Admitted(r) => TgCert::Admitted(r),
        }
    }
}

impl TgCert {
    /// The underlying theorem, if this step was actually proved **outright**.
    ///
    /// A conditional derivation deliberately answers `None` here: its theorem is
    /// not the equation, it is an implication, and a caller that has not been
    /// taught to discharge the antecedent must not be handed it.
    pub fn thm(&self) -> Option<&Thm> {
        match self {
            TgCert::Proved(t) => Some(t),
            TgCert::Conditional { .. } | TgCert::Admitted(_) => None,
        }
    }
    /// Whether this certificate is a complete, unconditional derivation.
    pub fn is_proved(&self) -> bool { matches!(self, TgCert::Proved(_)) }
}

// ─────────────────────────────────────────────────────────────────────────────
// Conditional equations.
//
// The one obligation this backend cannot generally discharge is a *typing*
// one: `beta_conditional_n` needs `⟦a⟧ ∈ ⟦A⟧` for the binder's domain, and
// `domain_premise` knows only two instances of it. Rather than admit the step,
// the premise is recorded as a genuine antecedent and carried: every rule below
// merges its premises' assumption sets and lifts its equality reasoning through
// the conjunction, and at a λ binder the assumption about that binder's own
// variable is discharged into `lam_ext_n`'s pointwise premise.
//
// Nothing here is trusted. A `CondEq` is checked on construction to be exactly
// `⊢ conj(hyps) → (a = b)`, so a rule that mangles the assumption list produces
// `None` — hence a reported gap — rather than a certificate that claims more
// than it proves.
// ─────────────────────────────────────────────────────────────────────────────

/// A derivation of an equation together with the assumptions it rests on:
/// `thm` is literally `⊢ (h₁ ∧ … ∧ hₙ) → a = b`, or `⊢ a = b` when `hyps` is
/// empty.
///
/// The conjunction is **left-nested**, so `conj(R ++ [h]) = conj(R) ∧ h` and
/// [`derived::uncurry`] peels the last assumption off — which is what the
/// discharge at a binder needs.
#[derive(Debug, Clone)]
struct CondEq {
    thm: Thm,
    hyps: Vec<Formula>,
}

impl CondEq {
    /// Check `thm` really is `⊢ conj(hyps) → (a = b)` and package the two.
    ///
    /// This is the only constructor, so no `CondEq` anywhere can misdescribe its
    /// own assumptions.
    fn new(thm: Thm, hyps: Vec<Formula>) -> Option<CondEq> {
        match conj_of(&hyps) {
            None => {
                thm.concl().as_eq()?;
            }
            Some(h) => {
                let (ante, concl) = thm.concl().as_imp()?;
                if ante != h {
                    return None
                }
                concl.as_eq()?;
            }
        }
        Some(CondEq { thm, hyps })
    }

    /// An unconditional derivation.
    fn plain(thm: Thm) -> Option<CondEq> { CondEq::new(thm, Vec::new()) }

    /// `⊢ t = t`.
    fn refl(t: Term) -> CondEq { CondEq { thm: Thm::eq_refl(t), hyps: Vec::new() } }

    /// The equation derived, under the assumptions.
    fn as_eq(&self) -> Option<(Term, Term)> { u_as_eq(&self.thm, conj_of(&self.hyps).as_ref()) }

    /// Whether this derivation is of the equation `l = r`.
    fn proves(&self, l: &Term, r: &Term) -> bool { self.as_eq() == Some((l.clone(), r.clone())) }
}

/// `h₁ ∧ … ∧ hₙ`, left-nested; `None` for the empty list.
fn conj_of(hyps: &[Formula]) -> Option<Formula> {
    let mut it = hyps.iter();
    let first = it.next()?.clone();
    Some(it.fold(first, |acc, h| Formula::and(acc, h.clone())))
}

/// `⊢ conj(hyps) → hyps[i]`, by peeling conjuncts off the left-nested form.
fn conj_proj(hyps: &[Formula], i: usize) -> Option<Thm> {
    let n = hyps.len();
    if i >= n {
        return None
    }
    // `cur : ⊢ conj(hyps) → conj(hyps[..k])`, starting at `k = n` with
    // reflexivity and shedding one conjunct at a time.
    let mut cur = derived::imp_refl(conj_of(hyps)?);
    let mut k = n;
    while k > i + 1 {
        let (prefix, last) = (conj_of(&hyps[..k - 1])?, hyps[k - 1].clone());
        cur = derived::syl(&cur, &derived::and_left(prefix, last))?;
        k -= 1;
    }
    if i == 0 {
        // `conj(hyps[..1])` *is* `hyps[0]`.
        return Some(cur)
    }
    derived::syl(&cur, &derived::and_right(conj_of(&hyps[..i])?, hyps[i].clone()))
}

/// Re-state `⊢ conj(from) → φ` as `⊢ conj(to) → φ`, where every assumption of
/// `from` also occurs in `to`.
///
/// This is what lets two derivations with different assumption sets be combined:
/// both are re-stated under the merged set first. It is also how assumptions get
/// *reordered*, which the discharge at a binder needs — the one being discharged
/// has to be last.
fn reassume(thm: &Thm, from: &[Formula], to: &[Formula]) -> Option<Thm> {
    if from == to {
        return Some(thm.clone())
    }
    let Some(h) = conj_of(to) else {
        // Nothing to assume: only an already-unconditional theorem qualifies.
        return from.is_empty().then(|| thm.clone())
    };
    if from.is_empty() {
        return Some(derived::a1i(thm, h))
    }
    // `⊢ conj(to) → conj(from)`, built conjunct by conjunct in `from`'s order,
    // which reproduces `from`'s own left-nesting.
    let mut acc: Option<Thm> = None;
    for f in from {
        let p = conj_proj(to, to.iter().position(|g| g == f)?)?;
        acc = Some(match acc {
            None => p,
            Some(a) => derived::hyp_and(&a, &p)?,
        });
    }
    derived::syl(&acc?, thm)
}

/// The union of two assumption lists, `a`'s order first.
fn merge_hyps(a: &[Formula], b: &[Formula]) -> Vec<Formula> {
    let mut out = a.to_vec();
    for h in b {
        if !out.contains(h) {
            out.push(h.clone());
        }
    }
    out
}

// The `u_*` family: the equality toolkit of `derived`, repeated "under an
// assumption". `h = None` is the unconditional case and each function then
// coincides with its `derived` original; `h = Some(H)` works inside `⊢ H → …`,
// where `a1i` weakens and `hyp_mp` is modus ponens. Writing them this way means
// every rule below has exactly one code path, so the conditional case cannot
// drift from the unconditional one.

/// `⊢ φ` ↦ `⊢ H → φ`.
fn u_a1i(thm: &Thm, h: Option<&Formula>) -> Thm {
    match h {
        None => thm.clone(),
        Some(h) => derived::a1i(thm, h.clone()),
    }
}

/// From `⊢ H → (φ → ψ)` and `⊢ H → φ` infer `⊢ H → ψ`.
fn u_mp(imp: &Thm, arg: &Thm, h: Option<&Formula>) -> Option<Thm> {
    match h {
        None => Thm::mp(imp, arg),
        Some(_) => derived::hyp_mp(imp, arg),
    }
}

/// The equation `⊢ H → (a = b)` concludes — and `None` unless the antecedent is
/// literally `H`, so a theorem assuming something else cannot be mistaken for
/// one assuming this.
fn u_as_eq(thm: &Thm, h: Option<&Formula>) -> Option<(Term, Term)> {
    match h {
        None => thm.concl().as_eq(),
        Some(h) => {
            let (ante, concl) = thm.concl().as_imp()?;
            (ante == *h).then_some(())?;
            concl.as_eq()
        }
    }
}

/// Transitivity under an assumption. `derived::eq_trans`, threaded.
fn u_eq_trans(env: &mut Env, ab: &Thm, bc: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b1) = u_as_eq(ab, h)?;
    let (b2, c) = u_as_eq(bc, h)?;
    if b1 != b2 {
        return None
    }
    let x = env.fresh_var();
    // ⊢ b = c → (a = b → a = c)
    let leib = Thm::eq_leibniz(b1, c, x, Formula::eq(a, Term::var(x)));
    let step = u_mp(&u_a1i(&leib, h), bc, h)?;
    u_mp(&step, ab, h)
}

/// Symmetry under an assumption. `derived::eq_symm`, threaded.
fn u_eq_symm(env: &mut Env, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b) = u_as_eq(ab, h)?;
    let x = env.fresh_var();
    // ⊢ a = b → (a = a → b = a)
    let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(Term::var(x), a.clone()));
    let step = u_mp(&u_a1i(&leib, h), ab, h)?;
    u_mp(&step, &u_a1i(&Thm::eq_refl(a), h), h)
}

/// Congruence in one argument, under an assumption. `derived::congr_arg`.
fn u_congr_arg(env: &mut Env, f: FnSym, args: &[Term], idx: usize, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b) = u_as_eq(ab, h)?;
    if args.get(idx) != Some(&a) {
        return None
    }
    let lhs = Term::apply(f, args.to_vec());
    let x = env.fresh_var();
    let mut hole = args.to_vec();
    hole[idx] = Term::var(x);
    let leib = Thm::eq_leibniz(a, b, x, Formula::eq(lhs.clone(), Term::apply(f, hole)));
    let step = u_mp(&u_a1i(&leib, h), ab, h)?;
    u_mp(&step, &u_a1i(&Thm::eq_refl(lhs), h), h)
}

/// Congruence in every argument, under an assumption. `derived::congr`.
fn u_congr(env: &mut Env, f: FnSym, eqs: &[Thm], h: Option<&Formula>) -> Option<Thm> {
    let mut args: Vec<Term> = Vec::with_capacity(eqs.len());
    for e in eqs {
        args.push(u_as_eq(e, h)?.0);
    }
    if args.len() != f.arity() as usize {
        return None
    }
    let mut acc = u_a1i(&Thm::eq_refl(Term::apply(f, args.clone())), h);
    for (i, e) in eqs.iter().enumerate() {
        let step = u_congr_arg(env, f, &args, i, e, h)?;
        args[i] = u_as_eq(e, h)?.1;
        acc = u_eq_trans(env, &acc, &step, h)?;
    }
    Some(acc)
}

/// How many assumptions a certificate may accumulate before the derivation is
/// abandoned and a gap reported instead.
///
/// A pure cost guard. Every combination re-states both premises under the
/// merged assumption set, which costs one projection per assumption, so an
/// unbounded set would make a long transitivity chain quadratic. Nothing is unsound about a larger bound; a
/// chain that hits it reports `too many undischarged assumptions`, which is
/// visible in the coverage report.
const MAX_HYPS: usize = 12;

// ─────────────────────────────────────────────────────────────────────────────
// The shared prelude.
//
// `Apply::new` and `least_universe` are the same derivation every time — they
// take no input beyond a fresh `Env` — but together they cost ~10ms, and a
// `TgBackend` is created per declaration. Building them once per thread and
// replaying the result is therefore worth it.
//
// Replaying is sound because an `Env` is *only* a pair of counters: it records
// no signature, so a theorem proved against one `Env` is a theorem, full stop.
// All that must be arranged is that a fresh `Env` never re-issues a symbol or
// variable the prelude already used, which `fast_forward` does by burning the
// same number of ids. `FnSym::id`/`FreeVar::id` make the counts observable.
//
// The same argument is what lets [`Shared`] carry one `Env` for every backend
// on the thread, which is why `fast_forward` now runs once per thread rather
// than once per declaration.
// ─────────────────────────────────────────────────────────────────────────────

/// The once-per-thread part of the interpretation's machinery.
///
/// # One pairing operation, not two
///
/// `Apply::new` and `funspace::Development::new` each build their *own*
/// [`derived::funcs::Sets`], so the version of this that called both had two
/// unrelated ordered pairs: `app`'s and `fs`'s. That cost nothing while the two
/// halves never met — `lam`/`app` used one, `fs` the other, and no lemma
/// mentioned both. The `Π` bridge is exactly a lemma that mentions both
/// (`f ∈ fs(A,B) → app(f,x) ∈ B`), so the development is now assembled by hand
/// over `ap.sets`: the product, the function space and the universe facts are
/// built from the same pairing `app` is built from, and
/// [`derived::ext::dprod_const_fibre`]'s stack checks would refuse anything
/// else.
struct Prelude {
    /// Set-theoretic application, and everything it is built from.
    ap: Apply,
    /// The least-universe operator `U`.
    u_sym: FnSym,
    /// `⊢ ∀x. x ∈ U(x)`.
    mem_u: Thm,
    /// The function space `fs(a,b) = b^a`, over `ap.sets` and the Cartesian
    /// product carved from it.
    fs: derived::funspace::Funspace,
    /// `⊢ ∀a. fs(a,a) ∈ U(a)`.
    fs_in_u: Thm,
    /// `⊢ ∀a ∀a' ∀b ∀b'. (a = a' → (b = b' → fs(a,b) = fs(a',b')))`.
    fs_cong: Thm,
    /// `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)`.
    fs_app_mem: Thm,
    /// `⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ ∀x ∈ a. app(f,x) ∈ c) → f ∈ fs(a,c))`.
    fs_retarget: Thm,
    /// How many function symbols and free variables the above consumed.
    n_syms: u32,
    n_vars: u32,
}

impl Prelude {
    /// The function-space symbol.
    fn fs_sym(&self) -> FnSym { self.fs.fs }
}

thread_local! {
    static PRELUDE: std::cell::RefCell<Option<Rc<Prelude>>> =
        const { std::cell::RefCell::new(None) };
}

fn prelude() -> Rc<Prelude> {
    PRELUDE.with(|slot| {
        if let Some(p) = slot.borrow().as_ref() {
            return p.clone()
        }
        use derived::funspace as fsp;
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("TG prelude: the application machinery is closed");
        // `Space` supplies the power set and the least universe, neither of
        // which depends on the pairing — but it builds its own `Sets`, and the
        // three theorems that *do* depend on one (`union_sing`, `empty_ax`,
        // `pair_inj`) are therefore taken from `ap`, which has exactly the same
        // three over `ap.sets`. What is left is a `Space` whose every component
        // is about one pairing operation.
        let sp = fsp::Space::new(&mut env).expect("TG prelude: the ambient space");
        let space = fsp::Space {
            sets: derived::funcs::Sets {
                up: ap.sets.up,
                up_ax: ap.sets.up_ax.clone(),
                un: ap.sets.un,
                un_ax: ap.sets.un_ax.clone(),
            },
            union_sing: ap.union_sing.clone(),
            empty: ap.empty,
            empty_ax: ap.empty_ax.clone(),
            pair_inj: ap.pair_inj.clone(),
            ..sp
        };
        let (u_sym, mem_u) = (space.lu, space.mem_lu.clone());

        // The function space, over `ap.sets` and its own product. `U` has to be
        // the same symbol in `⊢ ∀x. x ∈ U(x)` and in `⊢ ∀a. fs(a,a) ∈ U(a)`, or
        // the two facts would be about different operators and the beta path
        // could use only one of them — which is why the universe facts are
        // taken from the same `space` the inclusion chain below runs in.
        let prod = fsp::product(&mut env, &space.sets).expect("TG prelude: the Cartesian product");
        let fs = fsp::Funspace::new(&mut env, &space.sets, space.pow, &space.pow_ax, &prod, &space.empty_ax)
            .expect("TG prelude: the function space");
        let up_sub = fsp::upair_subset(&mut env, &space.sets).expect("TG prelude: unordered pairs are small");
        let pair_pp = fsp::pair_in_pow_pow(&mut env, &space.sets, space.pow, &space.pow_ax, &up_sub)
            .expect("TG prelude: ordered pairs are small");
        let (ml, mr) = fsp::mem_bin_union(&mut env, &space.sets).expect("TG prelude: binary union");
        let prod_sub = fsp::product_subset_pow_pow(&mut env, &space.sets, space.pow, &prod, &pair_pp, &ml, &mr)
            .expect("TG prelude: the product is small");
        let in_u_of = fsp::funspace_in_universe_of(&mut env, &space, &prod, &prod_sub, &fs)
            .expect("TG prelude: the function space is small");
        let fs_in_u = fsp::funspace_in_universe(&mut env, &space, &fs, &in_u_of)
            .expect("TG prelude: the diagonal function space is in the universe");

        let fs_cong = derived::ext::fs_cong(&mut env, &fs).expect("TG prelude: function-space congruence");
        // The two `b`-independent halves of the `Π` bridge, derived once rather
        // than inside every call to [`dprod_const_fibre_n`].
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("TG prelude: application at a pair");
        let fs_app_mem = derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair)
            .expect("TG prelude: a function's values lie in its codomain");
        let fs_retarget = derived::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair)
            .expect("TG prelude: the codomain may be retargeted");
        // One extra of each, purely to read the counters back out.
        let n_syms = env.declare(0).id() + 1;
        let n_vars = env.fresh_var().id() + 1;
        let p = Rc::new(Prelude {
            ap,
            u_sym,
            mem_u,
            fs,
            fs_in_u,
            fs_cong,
            fs_app_mem,
            fs_retarget,
            n_syms,
            n_vars,
        });
        *slot.borrow_mut() = Some(p.clone());
        p
    })
}

/// Advance a fresh `Env` past every id the prelude used.
fn fast_forward(env: &mut Env, p: &Prelude) {
    for _ in 0..p.n_syms {
        env.declare(0);
    }
    for _ in 0..p.n_vars {
        env.fresh_var();
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The n-ary lambda graph.
//
// `derived::funcs::lambda`/`beta_conditional` take a *unary* body symbol. The
// skeleton decomposition described in the module docs produces a body symbol
// with `k` extra parameters, so the two constructions are repeated here in
// parameterised form. They are line-for-line the derived originals with the
// prefix `p⃗` threaded through `t`'s and `lam`'s argument lists; at `k = 0` they
// reduce to exactly the derived versions.
//
// Nothing here is trusted: like everything outside `kernel/`, these can only
// reach a `Thm` through the kernel's primitive rules, so a mistake yields a
// `None` (hence a reported gap) rather than a false theorem. The shapes are
// asserted at the end of each function all the same.
// ─────────────────────────────────────────────────────────────────────────────

/// The graph `lam(p⃗, A) = { ⟨x, t(p⃗, x)⟩ : x ∈ A }`, with
/// `⊢ ∀p⃗ ∀A ∀y. (y ∈ lam(p⃗,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(p⃗,x)⟩))`.
///
/// The `k = 0` case is [`derived::funcs::lambda`].
fn lambda_n(env: &mut Env, ap: &Apply, t: FnSym) -> Option<(FnSym, Thm)> {
    let k = (t.arity() as usize).checked_sub(1)?;
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (t_a, tx) = (Term::var(av), Term::var(x));

    let mut targs = pts.clone();
    targs.push(tx.clone());
    let pair = ap.sets.pair(tx.clone(), Term::apply(t, targs));

    let (y, phi, exu) = derived::exists_unique_eq(env, &[], &pair);
    let repl = Thm::ax_replacement(env, x, y, phi.clone())?;
    let repl_a = derived::inst_all(&repl, std::slice::from_ref(&t_a))?;
    let premise = Thm::gen(x, &derived::a1i(&exu, Formula::mem(tx.clone(), t_a.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, t_a), phi));
    let mut params = ps;
    params.push(av);
    derived::define_by_membership(env, &params, &img, y, &cond)
}

/// `⊢ ∀p⃗ ∀A ∀a. (a ∈ A → app(lam(p⃗,A), a) = t(p⃗,a))` — beta reduction.
///
/// The `k = 0` case is [`derived::funcs::beta_conditional`]; see there for the
/// argument. Only the argument lists of `t` and `lam` differ.
fn beta_conditional_n(env: &mut Env, ap: &Apply, t: FnSym, lam: FnSym, lam_ax: &Thm) -> Option<Thm> {
    use derived::funcs::hyp_syl;
    use derived::{
        a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and,
        hyp_iff_mp, hyp_iff_mpr, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, mpd_const, singleton, syl,
    };

    let k = (t.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != k + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, a, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (t_a, ta, tx, ty) = (Term::var(av), Term::var(a), Term::var(x), Term::var(y));

    // `t(p⃗, ·)` and `lam(p⃗, ·)`, the only places the extra parameters show up.
    let t_at = |arg: Term| {
        let mut v = pts.clone();
        v.push(arg);
        Term::apply(t, v)
    };
    let lam_t = {
        let mut v = pts.clone();
        v.push(t_a.clone());
        Term::apply(lam, v)
    };
    let lam_inst = |thm: &Thm, extra: &[Term]| {
        let mut v = pts.clone();
        v.extend_from_slice(extra);
        inst_all(thm, &v)
    };

    let val = t_at(ta.clone()); // t(p⃗, a)
    let tx_val = t_at(tx.clone()); // t(p⃗, x)
    let h = Formula::mem(ta.clone(), t_a.clone()); // a ∈ A

    let pair_ay = ap.sets.pair(ta.clone(), ty.clone());
    let pair_aval = ap.sets.pair(ta.clone(), val.clone());
    let pair_x = ap.sets.pair(tx.clone(), tx_val.clone());

    // ── ⟨a,t(a)⟩ ∈ lam(A), by taking x := a in the image condition ───────────
    let lam_at_val = lam_inst(lam_ax, &[t_a.clone(), pair_aval.clone()])?;
    let body_val = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_aval.clone(), pair_x.clone()));
    let h_witness = hyp_and(&imp_refl(h.clone()), &a1i(&Thm::eq_refl(pair_aval.clone()), h.clone()))?;
    let h_ex = syl(&h_witness, &exists_intro_imp(x, body_val, ta.clone())?)?;
    let h_in_lam = syl(&h_ex, &iff_mpr(&lam_at_val)?)?;

    // ── The collection is inhabited, so `coll_ax` applies ────────────────────
    let mem_pair_y = Formula::mem(pair_ay.clone(), lam_t.clone());
    let h_ne = syl(&h_in_lam, &exists_intro_imp(y, mem_pair_y.clone(), val.clone())?)?;
    let coll_here = inst_all(&ap.coll_ax, &[lam_t.clone(), ta.clone()])?;
    let h_coll = syl(&h_ne, &coll_here)?;

    // ── ⟨a,y⟩ ∈ lam(A) ↔ y = t(a) ────────────────────────────────────────────
    let eq_y_val = Formula::eq(ty.clone(), val.clone());
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        val.clone(),
        ty.clone(),
        w,
        Formula::mem(ap.sets.pair(ta.clone(), Term::var(w)), lam_t.clone()),
    );
    let bwd = syl(&h_in_lam, &com12(&syl(&eq_symm_imp(env, ty.clone(), val.clone()), &carry)?)?)?;

    let lam_at_y = lam_inst(lam_ax, &[t_a.clone(), pair_ay.clone()])?;
    let kf = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let k_eq = and_right(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let inj = inst_all(&ap.pair_inj, &[ta.clone(), ty.clone(), tx.clone(), tx_val.clone()])?;
    let k_conj = syl(&k_eq, &inj)?;
    let (e_ax, e_yt) = (Formula::eq(ta.clone(), tx.clone()), Formula::eq(ty.clone(), tx_val.clone()));
    let k_ax = syl(&k_conj, &and_left(e_ax.clone(), e_yt.clone()))?;
    let k_ytx = syl(&k_conj, &and_right(e_ax, e_yt))?;
    let w2 = env.fresh_var();
    let congr = mpd_const(
        &Thm::eq_leibniz(ta.clone(), tx.clone(), w2, Formula::eq(val.clone(), t_at(Term::var(w2)))),
        &Thm::eq_refl(val.clone()),
    )?;
    let k_txta = syl(&syl(&k_ax, &congr)?, &eq_symm_imp(env, val.clone(), tx_val.clone()))?;
    let w3 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(tx_val.clone(), val.clone(), w3, Formula::eq(ty.clone(), Term::var(w3)));
    let k_goal = hyp_mp(&hyp_mp(&a1i(&carry2, kf), &k_txta)?, &k_ytx)?;
    let fwd = syl(&iff_mp(&lam_at_y)?, &exists_elim_imp(x, &Thm::gen(x, &k_goal), &eq_y_val)?)?;

    // ── coll(lam(A), a) and {t(a)} have the same members ─────────────────────
    let sing = singleton(ap.sets.up, val.clone());
    let ms = inst_all(&ap.mem_sing, &[val.clone(), ty.clone()])?;
    let coll_term = ap.coll_of(lam_t.clone(), ta.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let coll_at_y = Formula::forall(y, Formula::iff(mem_yc.clone(), mem_pair_y));
    let h_iff_y = syl(&h_coll, &Thm::ax_inst(coll_at_y, ty.clone())?)?;
    let (h_c_lam, h_lam_c) = (hyp_iff_mp(&h_iff_y)?, hyp_iff_mpr(&h_iff_y)?);
    let h_c_sing = hyp_syl(&hyp_syl(&h_c_lam, &a1i(&fwd, h.clone()))?, &a1i(&iff_mpr(&ms)?, h.clone()))?;
    let h_sing_c = hyp_syl(&hyp_syl(&a1i(&iff_mp(&ms)?, h.clone()), &bwd)?, &h_lam_c)?;
    let mem_ys = Formula::mem(ty.clone(), sing.clone());
    let h_same = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_yc, mem_ys))?,
        &Thm::gen(y, &hyp_and(&h_c_sing, &h_sing_c)?),
    )?;
    let h_coll_eq = syl(&h_same, &inst_all(&ext, &[coll_term.clone(), sing.clone()])?)?;

    // ── app(lam(A),a) = ⋃coll = ⋃{t(a)} = t(a) ───────────────────────────────
    let ucoll = ap.sets.union_of(coll_term.clone());
    let using = ap.sets.union_of(sing.clone());
    let w4 = env.fresh_var();
    let congr_u = mpd_const(
        &Thm::eq_leibniz(coll_term, sing, w4, Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w4)))),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let app_term = ap.apply(lam_t.clone(), ta.clone());
    let app_def = inst_all(&ap.app_ax, &[lam_t, ta.clone()])?;
    let w5 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(ucoll, using.clone(), w5, Formula::eq(app_term.clone(), Term::var(w5)));
    let h_app_using = hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w6 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, val.clone(), w6, Formula::eq(app_term.clone(), Term::var(w6))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&val))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    // Not a `debug_assert`: this is the statement the caller relies on, and a
    // release build must not skip the check.
    if *out.concl() != Formula::imp(h, Formula::eq(app_term, val)) {
        return None
    }
    let mut all = ps;
    all.push(av);
    all.push(a);
    Some(gen_all(&all, &out))
}

/// `⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(p⃗,x) = t'(q⃗,x))) → lam(p⃗,A) = lam'(q⃗,A')))`
/// — lambda graph extensionality, with a parameter prefix on each side.
///
/// The `k = k' = 0` case is [`derived::ext::lam_ext`], and this is that
/// derivation with the two prefixes threaded through the argument lists of
/// `t`/`lam` and `t2`/`lam2`. Nothing else changes: the argument never takes
/// those terms apart, it only quotes them, so the extra parameters ride along
/// untouched. The prefixes need not have the same length — the two lambdas
/// being compared have independent skeletons.
///
/// As everywhere outside `kernel/`, a mistake here can only produce `None`, and
/// hence a reported gap. The final shape is checked regardless.
#[allow(clippy::too_many_arguments)]
fn lam_ext_n(
    env: &mut Env,
    ap: &Apply,
    t: FnSym,
    lam: FnSym,
    lam_ax: &Thm,
    t2: FnSym,
    lam2: FnSym,
    lam2_ax: &Thm,
) -> Option<Thm> {
    use derived::funcs::hyp_syl;
    use derived::{
        a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and, hyp_mp,
        iff_mp, iff_mpr, inst_all, syl, uncurry,
    };

    let k = (t.arity() as usize).checked_sub(1)?;
    let k2 = (t2.arity() as usize).checked_sub(1)?;
    if lam.arity() as usize != k + 1 || lam2.arity() as usize != k2 + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qs: Vec<FreeVar> = (0..k2).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, av2, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tx, ty) = (Term::var(av), Term::var(av2), Term::var(x), Term::var(y));

    /// `f(prefix⃗, arg)`.
    fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
        let mut v = prefix.to_vec();
        v.push(arg);
        Term::apply(f, v)
    }
    /// The instantiation list `prefix⃗, A, y` for a graph's characteristic axiom.
    fn inst2(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
        let mut v = prefix.to_vec();
        v.push(a.clone());
        v.push(b.clone());
        v
    }

    let lam_t = at(lam, &pts, ta.clone()); // lam(p⃗, A)
    let lam2_t = at(lam2, &qts, ta2.clone()); // lam'(q⃗, A')
    let val1 = at(t, &pts, tx.clone()); // t(p⃗, x)
    let val2 = at(t2, &qts, tx.clone()); // t'(q⃗, x)
    let pair1 = ap.sets.pair(tx.clone(), val1.clone()); // ⟨x, t(p⃗,x)⟩
    let pair2 = ap.sets.pair(tx.clone(), val2.clone()); // ⟨x, t'(q⃗,x)⟩

    // The two hypotheses, and their conjunction `H`.
    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let pointwise =
        Formula::forall(x, Formula::imp(Formula::mem(tx.clone(), ta.clone()), Formula::eq(val1.clone(), val2.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());

    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let eq_y1 = Formula::eq(ty.clone(), pair1.clone());
    let eq_y2 = Formula::eq(ty.clone(), pair2.clone());
    let body1 = Formula::and(mem_xa.clone(), eq_y1.clone());
    let body2 = Formula::and(mem_xa2.clone(), eq_y2.clone());
    let ex1 = Formula::exists(x, body1.clone());
    let ex2 = Formula::exists(x, body2.clone());

    let mem_y1 = Formula::mem(ty.clone(), lam_t.clone());
    let mem_y2 = Formula::mem(ty.clone(), lam2_t.clone());

    // Both characteristic axioms must have exactly the shape `lambda_n` gives,
    // or the derivation below would be about the wrong sets. Checked, not
    // `debug_assert`ed: this runs in release.
    let lam_at_y = inst_all(lam_ax, &inst2(&pts, &ta, &ty))?;
    if *lam_at_y.concl() != Formula::iff(mem_y1.clone(), ex1.clone()) {
        return None
    }
    let lam2_at_y = inst_all(lam2_ax, &inst2(&qts, &ta2, &ty))?;
    if *lam2_at_y.concl() != Formula::iff(mem_y2.clone(), ex2.clone()) {
        return None
    }

    // ── Forward: a member of lam(p⃗,A) is a member of lam'(q⃗,A') ─────────────
    let k_f = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_dom = syl(&k_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let k_pw = syl(&k_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let k_xa = syl(&k_body, &and_left(mem_xa.clone(), eq_y1.clone()))?;
    let k_eqy = syl(&k_body, &and_right(mem_xa.clone(), eq_y1.clone()))?;

    let k_tt = hyp_mp(&syl(&k_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &k_xa)?;
    let w1 = env.fresh_var();
    let carry_dom = Thm::eq_leibniz(ta.clone(), ta2.clone(), w1, Formula::mem(tx.clone(), Term::var(w1)));
    let k_xa2 = hyp_mp(&hyp_mp(&a1i(&carry_dom, k_f.clone()), &k_dom)?, &k_xa)?;
    let w2 = env.fresh_var();
    let carry_val = Thm::eq_leibniz(
        val1.clone(),
        val2.clone(),
        w2,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w2))),
    );
    let k_eqy2 = hyp_mp(&hyp_mp(&a1i(&carry_val, k_f), &k_tt)?, &k_eqy)?;

    let k_ex2 = syl(&hyp_and(&k_xa2, &k_eqy2)?, &exists_intro_imp(x, body2.clone(), tx.clone())?)?;
    let fwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&k_ex2)?)?), &Formula::imp(h.clone(), ex2.clone()))?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam_at_y)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(&lam2_at_y)?, h.clone()),
    )?;

    // ── Backward: the mirror image, with symmetry twice ──────────────────────
    let j = Formula::and(h.clone(), body2.clone());
    let j_h = and_left(h.clone(), body2.clone());
    let j_body = and_right(h.clone(), body2.clone());
    let j_dom = syl(&j_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let j_pw = syl(&j_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let j_xa2 = syl(&j_body, &and_left(mem_xa2.clone(), eq_y2.clone()))?;
    let j_eqy2 = syl(&j_body, &and_right(mem_xa2.clone(), eq_y2.clone()))?;

    let j_dom_symm = syl(&j_dom, &eq_symm_imp(env, ta.clone(), ta2.clone()))?;
    let w3 = env.fresh_var();
    let carry_dom2 = Thm::eq_leibniz(ta2.clone(), ta.clone(), w3, Formula::mem(tx.clone(), Term::var(w3)));
    let j_xa = hyp_mp(&hyp_mp(&a1i(&carry_dom2, j.clone()), &j_dom_symm)?, &j_xa2)?;

    let j_tt = hyp_mp(&syl(&j_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &j_xa)?;
    let j_tt_symm = syl(&j_tt, &eq_symm_imp(env, val1.clone(), val2.clone()))?;
    let w4 = env.fresh_var();
    let carry_val2 = Thm::eq_leibniz(
        val2.clone(),
        val1.clone(),
        w4,
        Formula::eq(ty.clone(), ap.sets.pair(tx.clone(), Term::var(w4))),
    );
    let j_eqy = hyp_mp(&hyp_mp(&a1i(&carry_val2, j), &j_tt_symm)?, &j_eqy2)?;

    let j_ex1 = syl(&hyp_and(&j_xa, &j_eqy)?, &exists_intro_imp(x, body1.clone(), tx.clone())?)?;
    let bwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&j_ex1)?)?), &Formula::imp(h.clone(), ex1.clone()))?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&lam2_at_y)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(&lam_at_y)?, h.clone()),
    )?;

    // ── Same members, hence equal ───────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_y = Thm::mp(&Thm::ax_dist(y, h.clone(), Formula::iff(mem_y1, mem_y2))?, &Thm::gen(y, &h_iff))?;
    let h_eq = syl(&all_y, &inst_all(&ext, &[lam_t.clone(), lam2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(lam_t, lam2_t))) {
        return None
    }
    let mut all = ps;
    all.extend(qs);
    all.push(av);
    all.push(av2);
    Some(gen_all(&all, &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// The n-ary dependent product.
//
// `derived::ext`'s `DProd` and `dprod_const_fibre` take a *unary* fibre symbol
// `b(x)`, and a Lean `Π`'s body generally interprets to a term with free
// variables besides the binder's — the enclosing binders' locals — which a
// unary symbol may not contain. That is the same problem `lambda_n` solves for
// lambdas, and it is solved the same way: the body is split into a skeleton and
// its maximal binder-free subterms, which become a parameter prefix `p⃗`, so the
// fibre symbol is `b(p⃗, x)` and everything built on it carries the prefix too.
//
// Measured, the unary case really is the rare one: over `good/init-prelude.ndjson`
// a dependent `Π` whose body mentions nothing but its own binder arises 11
// times. So this is not an optimisation of the unary path, it *is* the path.
//
// The three functions below are `derived::ext::image_symbol`, `dprod_symbol`
// and `dprod_const_fibre` with the prefix threaded through the argument lists,
// exactly as `lambda_n`/`beta_conditional_n`/`lam_ext_n` above are the threaded
// forms of their derived originals; at `k = 0` they coincide with them.
// `dprod_members` and `dprod_subset_funspace` have no counterpart here because
// nothing below uses them.
//
// Nothing here is trusted: like everything outside `kernel/`, a mistake yields
// `None` — hence a reported gap — rather than a false theorem. The shapes are
// checked at the end all the same, in release as well as debug.
// ─────────────────────────────────────────────────────────────────────────────

/// `∀x. (x ∈ A → app(f,x) ∈ b(p⃗,x))` — `f` is a section of the fibration.
///
/// The `k = 0` case is [`derived::ext::is_section`].
fn section_n(env: &mut Env, ap: &Apply, b: FnSym, pts: &[Term], a: &Term, f: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    let mut bargs = pts.to_vec();
    bargs.push(tx.clone());
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(ap.apply(f.clone(), tx), Term::apply(b, bargs)),
        ),
    )
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])` — Leibniz under a
/// hypothesis. `derived::ext`'s own copy is private.
fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    derived::hyp_mp(&derived::a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// From `⊢ H → a = b` infer `⊢ H → b = a`.
fn hyp_eq_symm(env: &mut Env, h_eq: &Thm) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    derived::syl(h_eq, &derived::eq_symm_imp(env, a, b))
}

/// From `⊢ H → a = b` and `⊢ H → b = c` infer `⊢ H → a = c`.
fn hyp_eq_trans(env: &mut Env, ab: &Thm, bc: &Thm) -> Option<Thm> {
    let (h, e1) = ab.concl().as_imp()?;
    let (_, e2) = bc.concl().as_imp()?;
    let (a, b1) = e1.as_eq()?;
    let (b2, c) = e2.as_eq()?;
    if b1 != b2 {
        return None
    }
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(b1, c, w, Formula::eq(a, Term::var(w)));
    derived::hyp_mp(&derived::hyp_mp(&derived::a1i(&leib, h), bc)?, ab)
}

/// From `⊢ H → a = b` infer `⊢ H → c[a/w] = c[b/w]` — congruence under a
/// hypothesis, for a term `c` with the hole `w`.
///
/// `lhs` must be `c[a/w]`; that is checked rather than assumed, since a term
/// cannot be substituted into from outside the kernel.
fn hyp_congr(h_eq: &Thm, w: FreeVar, lhs: &Term, c: &Term) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    let leib = Thm::eq_leibniz(a, b, w, Formula::eq(lhs.clone(), c.clone()));
    let (ante, _) = leib.concl().as_imp()?.1.as_imp()?;
    if ante != Formula::eq(lhs.clone(), lhs.clone()) {
        return None
    }
    derived::syl(h_eq, &derived::mpd_const(&leib, &Thm::eq_refl(lhs.clone()))?)
}

/// From `⊢ P → (Q → R)` infer `⊢ (P ∧ Q) → R` — the converse of
/// [`derived::uncurry`].
fn curry(t: &Thm) -> Option<Thm> {
    let (p, rest) = t.concl().as_imp()?;
    let (q, _) = rest.as_imp()?;
    let h = Formula::and(p.clone(), q.clone());
    let hp = derived::and_left(p.clone(), q.clone());
    let hq = derived::and_right(p, q);
    derived::hyp_mp(&derived::hyp_mp(&derived::a1i(t, h), &hp)?, &hq)
}

/// `⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → g(x) = g'(x))) → img(p⃗,A) = img'(q⃗,A')))`
/// — extensionality for Replacement images, with a parameter prefix on each
/// side.
///
/// The `k = k' = 0` case is [`derived::ext::image_ext`]; the prefixes are left
/// *free* here rather than generalised, so that the caller — which allocated
/// them — can quantify them along with everything else at the end.
///
/// The two axioms are checked against the shape they must have rather than
/// assumed: a mismatch would still be sound but would prove something about the
/// wrong sets, and silently, so it returns `None` instead.
#[allow(clippy::too_many_arguments)]
fn image_ext_n(
    env: &mut Env,
    x: FreeVar,
    pts: &[Term],
    g1: &Term,
    img: FnSym,
    img_ax: &Thm,
    qts: &[Term],
    g2: &Term,
    img2: FnSym,
    img2_ax: &Thm,
) -> Option<Thm> {
    use derived::funcs::hyp_syl;
    use derived::{
        a1i, and_left, and_right, com12, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all, hyp_and, hyp_mp,
        iff_mp, iff_mpr, inst_all, syl, uncurry,
    };

    if img.arity() as usize != pts.len() + 1 || img2.arity() as usize != qts.len() + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let (av, av2, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tx, ty) = (Term::var(av), Term::var(av2), Term::var(x), Term::var(y));

    // The bodies are the caller's terms, so they have to be kept clear of the
    // variables this derivation binds — otherwise the quantifiers below would
    // capture an occurrence and the conclusion would say something else.
    for v in [av, av2, y] {
        if g1.occurs_free(v) || g2.occurs_free(v) {
            return None
        }
    }

    /// `f(prefix⃗, arg)`, and the instantiation list `prefix⃗, A, y`.
    fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
        let mut v = prefix.to_vec();
        v.push(arg);
        Term::apply(f, v)
    }
    fn inst2(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
        let mut v = prefix.to_vec();
        v.push(a.clone());
        v.push(b.clone());
        v
    }

    let img_t = at(img, pts, ta.clone());
    let img2_t = at(img2, qts, ta2.clone());

    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let pointwise = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(g1.clone(), g2.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());

    let eq_y1 = Formula::eq(ty.clone(), g1.clone());
    let eq_y2 = Formula::eq(ty.clone(), g2.clone());
    let body1 = Formula::and(mem_xa.clone(), eq_y1.clone());
    let body2 = Formula::and(mem_xa2.clone(), eq_y2.clone());
    let ex1 = Formula::exists(x, body1.clone());
    let ex2 = Formula::exists(x, body2.clone());

    let mem_y1 = Formula::mem(ty.clone(), img_t.clone());
    let mem_y2 = Formula::mem(ty.clone(), img2_t.clone());

    let img_at_y = inst_all(img_ax, &inst2(pts, &ta, &ty))?;
    if *img_at_y.concl() != Formula::iff(mem_y1.clone(), ex1.clone()) {
        return None
    }
    let img2_at_y = inst_all(img2_ax, &inst2(qts, &ta2, &ty))?;
    if *img2_at_y.concl() != Formula::iff(mem_y2.clone(), ex2.clone()) {
        return None
    }

    // ── Forward: a member of img(p⃗,A) is a member of img'(q⃗,A') ─────────────
    let k = Formula::and(h.clone(), body1.clone());
    let k_h = and_left(h.clone(), body1.clone());
    let k_body = and_right(h.clone(), body1.clone());
    let k_dom = syl(&k_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let k_pw = syl(&k_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let k_xa = syl(&k_body, &and_left(mem_xa.clone(), eq_y1.clone()))?;
    let k_eqy = syl(&k_body, &and_right(mem_xa.clone(), eq_y1.clone()))?;

    let k_gg = hyp_mp(&syl(&k_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &k_xa)?;
    let w1 = env.fresh_var();
    let carry_dom = Thm::eq_leibniz(ta.clone(), ta2.clone(), w1, Formula::mem(tx.clone(), Term::var(w1)));
    let k_xa2 = hyp_mp(&hyp_mp(&a1i(&carry_dom, k.clone()), &k_dom)?, &k_xa)?;
    let w2 = env.fresh_var();
    let carry_val = Thm::eq_leibniz(g1.clone(), g2.clone(), w2, Formula::eq(ty.clone(), Term::var(w2)));
    let k_eqy2 = hyp_mp(&hyp_mp(&a1i(&carry_val, k), &k_gg)?, &k_eqy)?;

    let k_ex2 = syl(&hyp_and(&k_xa2, &k_eqy2)?, &exists_intro_imp(x, body2.clone(), tx.clone())?)?;
    let fwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&k_ex2)?)?), &Formula::imp(h.clone(), ex2.clone()))?)?;
    let h_fwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&img_at_y)?, h.clone()), &fwd_ex)?,
        &a1i(&iff_mpr(&img2_at_y)?, h.clone()),
    )?;

    // ── Backward: the mirror image, with symmetry twice ──────────────────────
    let j = Formula::and(h.clone(), body2.clone());
    let j_h = and_left(h.clone(), body2.clone());
    let j_body = and_right(h.clone(), body2.clone());
    let j_dom = syl(&j_h, &and_left(eq_dom.clone(), pointwise.clone()))?;
    let j_pw = syl(&j_h, &and_right(eq_dom.clone(), pointwise.clone()))?;
    let j_xa2 = syl(&j_body, &and_left(mem_xa2.clone(), eq_y2.clone()))?;
    let j_eqy2 = syl(&j_body, &and_right(mem_xa2.clone(), eq_y2.clone()))?;

    let j_dom_symm = syl(&j_dom, &eq_symm_imp(env, ta.clone(), ta2.clone()))?;
    let w3 = env.fresh_var();
    let carry_dom2 = Thm::eq_leibniz(ta2.clone(), ta.clone(), w3, Formula::mem(tx.clone(), Term::var(w3)));
    let j_xa = hyp_mp(&hyp_mp(&a1i(&carry_dom2, j.clone()), &j_dom_symm)?, &j_xa2)?;

    let j_gg = hyp_mp(&syl(&j_pw, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &j_xa)?;
    let j_gg_symm = syl(&j_gg, &eq_symm_imp(env, g1.clone(), g2.clone()))?;
    let w4 = env.fresh_var();
    let carry_val2 = Thm::eq_leibniz(g2.clone(), g1.clone(), w4, Formula::eq(ty.clone(), Term::var(w4)));
    let j_eqy = hyp_mp(&hyp_mp(&a1i(&carry_val2, j), &j_gg_symm)?, &j_eqy2)?;

    let j_ex1 = syl(&hyp_and(&j_xa, &j_eqy)?, &exists_intro_imp(x, body1.clone(), tx.clone())?)?;
    let bwd_ex =
        com12(&exists_elim_imp(x, &Thm::gen(x, &com12(&uncurry(&j_ex1)?)?), &Formula::imp(h.clone(), ex1.clone()))?)?;
    let h_bwd = hyp_syl(
        &hyp_syl(&a1i(&iff_mp(&img2_at_y)?, h.clone()), &bwd_ex)?,
        &a1i(&iff_mpr(&img_at_y)?, h.clone()),
    )?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_y = Thm::mp(&Thm::ax_dist(y, h.clone(), Formula::iff(mem_y1, mem_y2))?, &Thm::gen(y, &h_iff))?;
    let h_eq = syl(&all_y, &inst_all(&ext, &[img_t.clone(), img2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(img_t, img2_t))) {
        return None
    }
    Some(gen_all(&[av, av2], &out))
}

/// `⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(p⃗,x) = b'(q⃗,x))) → dprod(p⃗,A) = dprod'(q⃗,A')))`
/// — dependent product extensionality, with a parameter prefix on each side.
///
/// The `k = k' = 0` case is [`derived::ext::dprod_ext`]. This is what `pi_cong`
/// needs for two dependent `Π` types whose bodies have *different* shapes: the
/// head symbols are then different and unrelated, so congruence over sub-terms
/// relates nothing — exactly the position `lam_cong` is in, and settled the same
/// way, by Extensionality.
///
/// The two defining axioms are rebuilt from the symbols handed in and compared,
/// so a mismatched fibre or product is refused rather than silently described.
#[allow(clippy::too_many_arguments)]
fn dprod_ext_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &derived::funspace::Funspace,
    a: (FnSym, FnSym, &Thm, FnSym, &Thm),
    b: (FnSym, FnSym, &Thm, FnSym, &Thm),
) -> Option<Thm> {
    use derived::funcs::hyp_syl;
    use derived::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry};

    let (bs, img, img_ax, dprod, dprod_def) = a;
    let (bs2, img2, img2_ax, dprod2, dprod2_def) = b;
    let np = (bs.arity() as usize).checked_sub(1)?;
    let nq = (bs2.arity() as usize).checked_sub(1)?;
    if img.arity() as usize != np + 1 || dprod.arity() as usize != np + 1 {
        return None
    }
    if img2.arity() as usize != nq + 1 || dprod2.arity() as usize != nq + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
    let qs: Vec<FreeVar> = (0..nq).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();

    fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
        let mut v = prefix.to_vec();
        v.push(arg);
        Term::apply(f, v)
    }
    fn inst2(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
        let mut v = prefix.to_vec();
        v.push(a.clone());
        v.push(b.clone());
        v
    }

    let x = env.fresh_var();
    let tx = Term::var(x);
    let bx = at(bs, &pts, tx.clone());
    let b2x = at(bs2, &qts, tx.clone());

    // ⊢ ∀A ∀A'. (A = A' → (PW → img(p⃗,A) = img'(q⃗,A'))), the fibre images.
    let img_ext = image_ext_n(env, x, &pts, &bx, img, img_ax, &qts, &b2x, img2, img2_ax)?;

    let (av, av2, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, ta2, tf) = (Term::var(av), Term::var(av2), Term::var(f));

    let eq_dom = Formula::eq(ta.clone(), ta2.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let mem_xa2 = Formula::mem(tx.clone(), ta2.clone());
    let pointwise = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(bx.clone(), b2x.clone())));
    let h = Formula::and(eq_dom.clone(), pointwise.clone());
    let h_dom = and_left(eq_dom.clone(), pointwise.clone());
    let h_pw = and_right(eq_dom.clone(), pointwise.clone());

    // ── The function space the product is carved out of ──────────────────────
    let h_img = curry(&inst_all(&img_ext, &[ta.clone(), ta2.clone()])?)?;
    let u = ap.sets.union_of(at(img, &pts, ta.clone()));
    let u2 = ap.sets.union_of(at(img2, &qts, ta2.clone()));
    let w0 = env.fresh_var();
    let h_u = hyp_congr(&h_img, w0, &u, &ap.sets.union_of(Term::var(w0)))?;

    let fs_t = fsp.of(ta.clone(), u.clone());
    let fs_mid = fsp.of(ta2.clone(), u.clone());
    let fs2_t = fsp.of(ta2.clone(), u2.clone());
    let w1 = env.fresh_var();
    let h_fs1 = hyp_congr(&h_dom, w1, &fs_t, &fsp.of(Term::var(w1), u.clone()))?;
    let w2 = env.fresh_var();
    let h_fs2 = hyp_congr(&h_u, w2, &fs_mid, &fsp.of(ta2.clone(), Term::var(w2)))?;
    let h_fs = hyp_eq_trans(env, &h_fs1, &h_fs2)?;

    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let mem_fs2 = Formula::mem(tf.clone(), fs2_t.clone());
    let w3 = env.fresh_var();
    let h_mem_fwd = hyp_leibniz(&h_fs, w3, &Formula::mem(tf.clone(), Term::var(w3)))?;
    let w4 = env.fresh_var();
    let h_mem_bwd = hyp_leibniz(&hyp_eq_symm(env, &h_fs)?, w4, &Formula::mem(tf.clone(), Term::var(w4)))?;

    // ── The section condition, rebuilt at our own `x` so it can be opened ────
    let sec = section_n(env, ap, bs, &pts, &ta, &tf);
    let sec2 = section_n(env, ap, bs2, &qts, &ta2, &tf);
    let app_fx = ap.apply(tf.clone(), tx.clone());
    let sec_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), bx.clone()));
    let sec2_body = Formula::imp(mem_xa2.clone(), Formula::mem(app_fx.clone(), b2x.clone()));
    if sec != Formula::forall(x, sec_body.clone()) || sec2 != Formula::forall(x, sec2_body.clone()) {
        return None
    }

    // Forward, under `M := (H ∧ sec) ∧ x ∈ A'`. Both hypotheses are stated over
    // `A`, so the first move is to bring `x` back there.
    let k = Formula::and(h.clone(), sec.clone());
    let k_h = and_left(h.clone(), sec.clone());
    let k_sec = and_right(h.clone(), sec.clone());
    let m_k = and_left(k.clone(), mem_xa2.clone());
    let m_xa2 = and_right(k.clone(), mem_xa2.clone());
    let m_h = syl(&m_k, &k_h)?;
    let m_dom = syl(&m_h, &h_dom)?;
    let w5 = env.fresh_var();
    let m_to_a = hyp_leibniz(&hyp_eq_symm(env, &m_dom)?, w5, &Formula::mem(tx.clone(), Term::var(w5)))?;
    let m_xa = hyp_mp(&m_to_a, &m_xa2)?;
    let m_bb = hyp_mp(&syl(&syl(&m_h, &h_pw)?, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &m_xa)?;
    let m_app = hyp_mp(&syl(&syl(&m_k, &k_sec)?, &Thm::ax_inst(sec.clone(), tx.clone())?)?, &m_xa)?;
    let w6 = env.fresh_var();
    let m_goal = hyp_mp(&hyp_leibniz(&m_bb, w6, &Formula::mem(app_fx.clone(), Term::var(w6)))?, &m_app)?;
    // `x` is bound in `K`, so it generalises out from under it.
    let k_sec2 = Thm::mp(&Thm::ax_dist(x, k.clone(), sec2_body.clone())?, &Thm::gen(x, &uncurry(&m_goal)?))?;
    let h_sec_fwd = uncurry(&k_sec2)?;

    // Backward, under `N := (H ∧ sec') ∧ x ∈ A`, the mirror image.
    let j = Formula::and(h.clone(), sec2.clone());
    let j_h = and_left(h.clone(), sec2.clone());
    let j_sec2 = and_right(h.clone(), sec2.clone());
    let n_j = and_left(j.clone(), mem_xa.clone());
    let n_xa = and_right(j.clone(), mem_xa.clone());
    let n_h = syl(&n_j, &j_h)?;
    let w7 = env.fresh_var();
    let n_xa2 = hyp_mp(&hyp_leibniz(&syl(&n_h, &h_dom)?, w7, &Formula::mem(tx.clone(), Term::var(w7)))?, &n_xa)?;
    let n_bb = hyp_mp(&syl(&syl(&n_h, &h_pw)?, &Thm::ax_inst(pointwise.clone(), tx.clone())?)?, &n_xa)?;
    let n_app2 = hyp_mp(&syl(&syl(&n_j, &j_sec2)?, &Thm::ax_inst(sec2.clone(), tx.clone())?)?, &n_xa2)?;
    let w8 = env.fresh_var();
    let n_goal =
        hyp_mp(&hyp_leibniz(&hyp_eq_symm(env, &n_bb)?, w8, &Formula::mem(app_fx.clone(), Term::var(w8)))?, &n_app2)?;
    let j_sec = Thm::mp(&Thm::ax_dist(x, j.clone(), sec_body.clone())?, &Thm::gen(x, &uncurry(&n_goal)?))?;
    let h_sec_bwd = uncurry(&j_sec)?;

    // ── The two membership conditions agree ──────────────────────────────────
    let l = Formula::and(mem_fs.clone(), sec.clone());
    let l2 = Formula::and(mem_fs2.clone(), sec2.clone());

    let p_h = and_left(h.clone(), l.clone());
    let p_l = and_right(h.clone(), l.clone());
    let p_mem = hyp_mp(&syl(&p_h, &h_mem_fwd)?, &syl(&p_l, &and_left(mem_fs.clone(), sec.clone()))?)?;
    let p_sec = hyp_mp(&syl(&p_h, &h_sec_fwd)?, &syl(&p_l, &and_right(mem_fs.clone(), sec.clone()))?)?;
    let h_l_fwd = uncurry(&hyp_and(&p_mem, &p_sec)?)?;

    let q_h = and_left(h.clone(), l2.clone());
    let q_l = and_right(h.clone(), l2.clone());
    let q_mem = hyp_mp(&syl(&q_h, &h_mem_bwd)?, &syl(&q_l, &and_left(mem_fs2.clone(), sec2.clone()))?)?;
    let q_sec = hyp_mp(&syl(&q_h, &h_sec_bwd)?, &syl(&q_l, &and_right(mem_fs2.clone(), sec2.clone()))?)?;
    let h_l_bwd = uncurry(&hyp_and(&q_mem, &q_sec)?)?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let (dp_t, dp2_t) = (at(dprod, &pts, ta.clone()), at(dprod2, &qts, ta2.clone()));
    let (mem_dp, mem_dp2) = (Formula::mem(tf.clone(), dp_t.clone()), Formula::mem(tf.clone(), dp2_t.clone()));

    let dp_at = inst_all(dprod_def, &inst2(&pts, &ta, &tf))?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), l) {
        return None
    }
    let dp2_at = inst_all(dprod2_def, &inst2(&qts, &ta2, &tf))?;
    if *dp2_at.concl() != Formula::iff(mem_dp2.clone(), l2) {
        return None
    }

    let h_fwd = hyp_syl(&hyp_syl(&a1i(&iff_mp(&dp_at)?, h.clone()), &h_l_fwd)?, &a1i(&iff_mpr(&dp2_at)?, h.clone()))?;
    let h_bwd = hyp_syl(&hyp_syl(&a1i(&iff_mp(&dp2_at)?, h.clone()), &h_l_bwd)?, &a1i(&iff_mpr(&dp_at)?, h.clone()))?;
    let h_iff = hyp_and(&h_fwd, &h_bwd)?;
    let all_f = Thm::mp(&Thm::ax_dist(f, h.clone(), Formula::iff(mem_dp, mem_dp2))?, &Thm::gen(f, &h_iff))?;
    let h_eq = syl(&all_f, &inst_all(&ext, &[dp_t.clone(), dp2_t.clone()])?)?;

    let out = uncurry(&h_eq)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(eq_dom, Formula::imp(pointwise, Formula::eq(dp_t, dp2_t))) {
        return None
    }
    let mut all = ps;
    all.extend(qs);
    all.push(av);
    all.push(av2);
    Some(gen_all(&all, &out))
}

/// The Replacement image `img(p⃗,A) = { b(p⃗,x) : x ∈ A }`, with
/// `⊢ ∀p⃗ ∀A ∀w. (w ∈ img(p⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(p⃗,x)))`.
///
/// The `k = 0` case is [`derived::ext::image_symbol`].
fn image_symbol_n(env: &mut Env, b: FnSym) -> Option<(FnSym, Thm)> {
    let k = (b.arity() as usize).checked_sub(1)?;
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(av), Term::var(x));

    let mut bargs = pts;
    bargs.push(tx.clone());
    let bx = Term::apply(b, bargs);

    let (w, phi, exu) = derived::exists_unique_eq(env, &[], &bx);
    let repl = Thm::ax_replacement(env, x, w, phi.clone())?;
    let repl_a = derived::inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(x, &derived::a1i(&exu, Formula::mem(tx.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
    let mut params = ps;
    params.push(av);
    derived::define_by_membership(env, &params, &img, w, &cond)
}

/// The dependent product `dprod(p⃗,A) = Π(x:A). b(p⃗,x)`, with
/// `⊢ ∀p⃗ ∀A ∀f. (f ∈ dprod(p⃗,A) ↔ (f ∈ fs(A,⋃img(p⃗,A)) ∧ section(f)))`.
///
/// The `k = 0` case is [`derived::ext::dprod_symbol`]. One call to
/// `separation_full` and nothing else, exactly as there.
fn dprod_symbol_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &derived::funspace::Funspace,
    img: FnSym,
    b: FnSym,
) -> Option<(FnSym, Thm)> {
    let k = (b.arity() as usize).checked_sub(1)?;
    if img.arity() as usize != k + 1 {
        return None
    }
    let ps: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let mut iargs = pts.clone();
    iargs.push(ta.clone());
    let fs_t = fsp.of(ta.clone(), ap.sets.union_of(Term::apply(img, iargs)));
    let psi = section_n(env, ap, b, &pts, &ta, &tf);
    let l = Formula::and(Formula::mem(tf.clone(), fs_t.clone()), psi.clone());

    let existence = derived::funcs::separation_full(env, f, &psi, &fs_t, &ap.empty_ax)?;
    let mut params = ps;
    params.push(av);
    derived::define_by_membership(env, &params, &existence, f, &l)
}

/// `⊢ ∀p⃗ ∀A ∀B. ((∀x. (x ∈ A → b(p⃗,x) = B)) → dprod(p⃗,A) = fs(A,B))` — a
/// dependent product over a **constant fibre** is the function space.
///
/// The `k = 0` case is [`derived::ext::dprod_const_fibre`], and this is that
/// derivation with the prefix threaded through the argument lists of `b`, `img`
/// and `dprod`; nothing else changes, because the argument never takes those
/// terms apart. The two `b`-independent lemmas it consumes — `app_mem` and
/// `retarget` — are hoisted into [`Prelude`] rather than re-derived per fibre,
/// which is the only other difference.
///
/// No inhabitation antecedent, and the empty domain is included: see the
/// derived original for why the obvious route through `⋃img(A) = B` is *false*
/// at `A = ∅` and is avoided.
#[allow(clippy::too_many_arguments)]
fn dprod_const_fibre_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &derived::funspace::Funspace,
    b: FnSym,
    img: FnSym,
    img_ax: &Thm,
    dprod: FnSym,
    dprod_def: &Thm,
    app_mem: &Thm,
    retarget: &Thm,
) -> Option<Thm> {
    use derived::{
        a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
    };

    let np = (b.arity() as usize).checked_sub(1)?;
    if img.arity() as usize != np + 1 || dprod.arity() as usize != np + 1 {
        return None
    }
    let ext = Thm::ax_extensionality(env);
    let ps: Vec<FreeVar> = (0..np).map(|_| env.fresh_var()).collect();
    let pts: Vec<Term> = ps.iter().map(|p| Term::var(*p)).collect();
    /// `f(p⃗, arg)`.
    fn at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
        let mut v = prefix.to_vec();
        v.push(arg);
        Term::apply(f, v)
    }

    let (av, bigb, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tbb, tf) = (Term::var(av), Term::var(bigb), Term::var(f));
    let x = env.fresh_var();
    let tx = Term::var(x);

    // The hypothesis: the fibre is constantly `B` on `A`.
    let bx = at(b, &pts, tx.clone());
    let mem_xa = Formula::mem(tx.clone(), ta.clone());
    let h = Formula::forall(x, Formula::imp(mem_xa.clone(), Formula::eq(bx.clone(), tbb.clone())));

    // The two sets being compared, and the condition `dprod` is defined by.
    let img_t = at(img, &pts, ta.clone());
    let u = ap.sets.union_of(img_t.clone());
    let fs_b = fsp.of(ta.clone(), tbb.clone());
    let mem_fs_u = Formula::mem(tf.clone(), fsp.of(ta.clone(), u.clone()));
    let mem_fs_b = Formula::mem(tf.clone(), fs_b.clone());
    let sec = section_n(env, ap, b, &pts, &ta, &tf);
    let app_fx = ap.apply(tf.clone(), tx.clone());
    let sec_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), bx.clone()));
    if sec != Formula::forall(x, sec_body.clone()) {
        return None
    }
    let l = Formula::and(mem_fs_u.clone(), sec.clone());

    let dp_t = at(dprod, &pts, ta.clone());
    let mem_dp = Formula::mem(tf.clone(), dp_t.clone());
    let mut dargs = pts.clone();
    dargs.push(ta.clone());
    dargs.push(tf.clone());
    let dp_at = inst_all(dprod_def, &dargs)?;
    if *dp_at.concl() != Formula::iff(mem_dp.clone(), l) {
        return None
    }

    // The two "values land here" hypotheses `funspace_retarget` consumes.
    let vi_b_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), tbb.clone()));
    let vi_u_body = Formula::imp(mem_xa.clone(), Formula::mem(app_fx.clone(), u.clone()));

    // ── ←: a function into `B` is a section of the constant fibration ────────
    let kf = Formula::and(h.clone(), mem_fs_b.clone());
    let k_h = and_left(h.clone(), mem_fs_b.clone());
    let k_fs = and_right(h.clone(), mem_fs_b.clone());

    let m = Formula::and(kf.clone(), mem_xa.clone());
    let m_k = and_left(kf.clone(), mem_xa.clone());
    let m_xa = and_right(kf.clone(), mem_xa.clone());

    let am_at = inst_all(app_mem, &[ta.clone(), tbb.clone(), tf.clone(), tx.clone()])?;
    let m_app_b = hyp_mp(&a1i(&am_at, m.clone()), &hyp_and(&syl(&m_k, &k_fs)?, &m_xa)?)?;
    let m_fibre = hyp_mp(&syl(&syl(&m_k, &k_h)?, &Thm::ax_inst(h.clone(), tx.clone())?)?, &m_xa)?;
    let w1 = env.fresh_var();
    let m_sec_body = hyp_mp(
        &hyp_leibniz(&hyp_eq_symm(env, &m_fibre)?, w1, &Formula::mem(app_fx.clone(), Term::var(w1)))?,
        &m_app_b,
    )?;
    let k_sec = Thm::mp(&Thm::ax_dist(x, kf.clone(), sec_body.clone())?, &Thm::gen(x, &uncurry(&m_sec_body)?))?;

    // `b(p⃗,x) ∈ img(p⃗,A)` for `x ∈ A`, so a value in `b(p⃗,x)` is a value in `⋃img(p⃗,A)`.
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let img_body =
        Formula::and(Formula::mem(tx2.clone(), ta.clone()), Formula::eq(bx.clone(), at(b, &pts, tx2)));
    let mut gargs = pts.clone();
    gargs.push(ta.clone());
    gargs.push(bx.clone());
    let img_at = inst_all(img_ax, &gargs)?;
    if *img_at.concl() != Formula::iff(Formula::mem(bx.clone(), img_t.clone()), Formula::exists(x2, img_body.clone()))
    {
        return None
    }
    let m_witness = hyp_and(&m_xa, &a1i(&Thm::eq_refl(bx.clone()), m.clone()))?;
    let m_img = syl(&syl(&m_witness, &exists_intro_imp(x2, img_body, tx.clone())?)?, &iff_mpr(&img_at)?)?;
    let intro = derived::funcs::union_intro(env, &ap.sets, img_t, bx, app_fx.clone())?;
    let m_app_u = syl(&hyp_and(&m_img, &m_sec_body)?, &intro)?;
    let k_vi_u = Thm::mp(&Thm::ax_dist(x, kf.clone(), vi_u_body)?, &Thm::gen(x, &uncurry(&m_app_u)?))?;

    let rt_u = inst_all(retarget, &[ta.clone(), tbb.clone(), u.clone(), tf.clone()])?;
    let k_fs_u = hyp_mp(&a1i(&rt_u, kf.clone()), &hyp_and(&k_fs, &k_vi_u)?)?;
    let k_dp = hyp_mp(&a1i(&iff_mpr(&dp_at)?, kf.clone()), &hyp_and(&k_fs_u, &k_sec)?)?;
    let bwd = uncurry(&k_dp)?;

    // ── →: a section of a constant fibration is a function into `B` ─────────
    let j = Formula::and(h.clone(), mem_dp.clone());
    let j_h = and_left(h.clone(), mem_dp.clone());
    let j_dp = and_right(h.clone(), mem_dp.clone());
    let j_l = hyp_mp(&a1i(&iff_mp(&dp_at)?, j.clone()), &j_dp)?;
    let j_fs_u = syl(&j_l, &and_left(mem_fs_u.clone(), sec.clone()))?;
    let j_sec = syl(&j_l, &and_right(mem_fs_u, sec.clone()))?;

    let n = Formula::and(j.clone(), mem_xa.clone());
    let n_j = and_left(j.clone(), mem_xa.clone());
    let n_xa = and_right(j.clone(), mem_xa);
    let n_app_bx = hyp_mp(&syl(&syl(&n_j, &j_sec)?, &Thm::ax_inst(sec, tx.clone())?)?, &n_xa)?;
    let n_fibre = hyp_mp(&syl(&syl(&n_j, &j_h)?, &Thm::ax_inst(h.clone(), tx)?)?, &n_xa)?;
    let w2 = env.fresh_var();
    let n_app_b =
        hyp_mp(&hyp_leibniz(&n_fibre, w2, &Formula::mem(app_fx.clone(), Term::var(w2)))?, &n_app_bx)?;
    if *n_app_b.concl() != Formula::imp(n, Formula::mem(app_fx, tbb.clone())) {
        return None
    }
    let j_vi_b = Thm::mp(&Thm::ax_dist(x, j.clone(), vi_b_body)?, &Thm::gen(x, &uncurry(&n_app_b)?))?;

    let rt_b = inst_all(retarget, &[ta, u, tbb, tf])?;
    let fwd = uncurry(&hyp_mp(&a1i(&rt_b, j.clone()), &hyp_and(&j_fs_u, &j_vi_b)?)?)?;

    // ── Same members, hence equal ────────────────────────────────────────────
    let all_f = Thm::mp(&Thm::ax_dist(f, h.clone(), Formula::iff(mem_dp, mem_fs_b))?, &Thm::gen(f, &hyp_and(&fwd, &bwd)?))?;
    let out = syl(&all_f, &inst_all(&ext, &[dp_t.clone(), fs_b.clone()])?)?;
    // The statement the caller relies on; a release build must not skip it.
    if *out.concl() != Formula::imp(h, Formula::eq(dp_t, fs_b)) {
        return None
    }
    let mut all = ps;
    all.push(av);
    all.push(bigb);
    Some(gen_all(&all, &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// The two application-typing rules.
//
// Both are the *characteristic property* of the interpretation of a `Π` type,
// applied — which is the whole content of Lean's application typing rule once
// `Π` means what it means here. They are free functions rather than methods so
// that they can be tested against genuine inhabitants: the corpus cannot reach
// them yet (every Lean function value is a lambda or an opaque constant, and
// neither has a typing lemma yet), so the tests are the only thing exercising
// them. See `app_in_codomain_types_the_identity` and `app_in_fibre_types_a_section`.
//
// Neither can produce a false claim: a `Thm` is only obtainable from the
// kernel's rules, and every caller re-checks the conclusion against the
// membership it is supposed to be.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ app(f,x) ∈ cod` from `⊢ f ∈ fs(dom,cod)` and `⊢ x ∈ dom`.
///
/// `fs_app_mem` must be [`Prelude::fs_app_mem`],
/// `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)`.
fn app_in_codomain(
    fs_app_mem: &Thm,
    dom: &Term,
    cod: &Term,
    f: &Term,
    x: &Term,
    h_f: &Thm,
    h_x: &Thm,
) -> Option<Thm> {
    let inst = derived::inst_all(fs_app_mem, &[dom.clone(), cod.clone(), f.clone(), x.clone()])?;
    Thm::mp(&inst, &derived::and_intro(h_f, h_x))
}

/// `⊢ app(f,x) ∈ b(h⃗,x)`, unfolded, from `⊢ f ∈ dprod(h⃗,dom)` and `⊢ x ∈ dom`.
///
/// `dprod_def` is [`Fibre::dprod_def`] — `f ∈ dprod(h⃗,A)` iff `f` lies in a
/// function space *and* `∀x. (x ∈ A → app(f,x) ∈ b(h⃗,x))` — and it is the
/// second conjunct that does the work. `b_def` is [`Fibre::b_def`], which turns
/// `b(h⃗,x)` into the fibre skeleton with `x` in the binder slot; that is what
/// makes the result line up syntactically with `⟦B[x]⟧`, by exactly the argument
/// [`TgBackend::beta_step`] makes for the body.
#[allow(clippy::too_many_arguments)]
fn app_in_fibre(
    env: &mut Env,
    app: FnSym,
    dprod_def: &Thm,
    b_def: &Thm,
    holes: &[Term],
    dom: &Term,
    f: &Term,
    x: &Term,
    h_f: &Thm,
    h_x: &Thm,
) -> Option<Thm> {
    let mut inst = holes.to_vec();
    inst.push(dom.clone());
    inst.push(f.clone());
    let at_f = derived::inst_all(dprod_def, &inst)?;
    let members = Thm::mp(&derived::iff_mp(&at_f)?, h_f)?;
    let section = derived::and_elim_right(&members)?;
    let at_x = derived::inst_all(&section, std::slice::from_ref(x))?;
    let in_fibre = Thm::mp(&at_x, h_x)?;

    let mut binst = holes.to_vec();
    binst.push(x.clone());
    let unfold = derived::inst_all(b_def, &binst)?;
    let (fibre_t, body_t) = unfold.concl().as_eq()?;
    let app_t = Term::apply(app, vec![f.clone(), x.clone()]);
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(fibre_t, body_t.clone(), w, Formula::mem(app_t.clone(), Term::var(w)));
    let out = Thm::mp(&Thm::mp(&leib, &unfold)?, &in_fibre)?;
    // The statement the caller relies on; a release build must not skip it.
    (*out.concl() == Formula::mem(app_t, body_t)).then_some(out)
}

/// The function symbols the interpretation uses that carry *no* axioms.
///
/// All are introduced by signature extension; that is sound but limiting, and
/// it is why the rules over them (`zeta`, …) stay in the equational fragment.
/// `sort`, `lam`, `app` and the dependent product are *not* here: those are real
/// definitional extensions, held in [`Prelude`], [`Shared::lam_infos`] and
/// [`Shared::pi_infos`].
#[derive(Clone, Copy)]
struct Syms {
    /// Sorts whose level is not a literal successor tower.
    sort: FnSym,
    /// The fallback for a `Π` whose fibre decomposition broke down — which is
    /// unreachable in principle, and a reported gap rather than a wrong answer
    /// if it ever is not. Every other `Π` is an `fs` or a `dprod`.
    pi: FnSym,
    let_: FnSym,
    proj: FnSym,
    /// Lean's de Bruijn indices. A Lean expression is already de Bruijn and
    /// hash-consed, so alpha-equivalent Lean terms are pointer-equal and map to
    /// syntactically equal kernel terms; a per-index symbol therefore suffices
    /// and no binding structure need be reproduced on the kernel side.
    bvar: FnSym,
    /// Universe levels.
    lzero: FnSym,
    lsucc: FnSym,
    lmax: FnSym,
    limax: FnSym,
    /// Index encodings for `bvar`, `proj` and level/name parameters.
    idx: FnSym,
    /// `⟦Sort 0⟧`, the base of the universe tower.
    sort0: FnSym,
}

/// Everything known about one lambda *skeleton*. Shared by every lambda whose
/// body has that shape.
struct LamInfo {
    /// The head symbol of the interpretation, `lam_C(h⃗, A)`.
    lam: FnSym,
    /// The graph machinery, when it was built; `None` for the inert encoding,
    /// in which case `lam` is an opaque symbol and beta over this lambda
    /// reports a gap. Every skeleton gets a graph now — there is no hole-count
    /// cut-off — so the `None` case is the construction refusing, which it does
    /// not do on any corpus measured.
    graph: Option<Graph>,
}

/// Everything known about one dependent-`Π` *fibre skeleton*. Shared by every
/// `Π` whose body has that shape.
struct PiInfo {
    /// The head symbol of the interpretation, `dprod_C(h⃗, A)`.
    dprod: FnSym,
    /// The dependent-product machinery, when it was built; `None` for the inert
    /// encoding, in which case `dprod` is an opaque symbol and the `Π` bridge
    /// over it reports a gap.
    fibre: Option<Fibre>,
}

/// The definitional-extension half of a dependent-`Π` skeleton.
struct Fibre {
    /// The fibre function `b(h⃗, x)`.
    b: FnSym,
    /// `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    b_def: Thm,
    /// The Replacement image `img(h⃗, A) = { b(h⃗,x) : x ∈ A }`.
    img: FnSym,
    /// `⊢ ∀h⃗ ∀A ∀w. (w ∈ img(h⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(h⃗,x)))`.
    img_ax: Thm,
    /// `⊢ ∀h⃗ ∀A ∀f. (f ∈ dprod(h⃗,A) ↔ (f ∈ fs(A,⋃img(h⃗,A)) ∧ section(f)))`.
    dprod_def: Thm,
}

/// The definitional-extension half of a lambda skeleton.
struct Graph {
    /// The body function `t(h⃗, x)`.
    t: FnSym,
    /// `⊢ ∀h⃗ ∀x. t(h⃗,x) = skeleton`.
    t_def: Thm,
    /// `⊢ ∀h⃗ ∀A ∀y. (y ∈ lam(h⃗,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(h⃗,x)⟩))`.
    lam_ax: Thm,
}

// ─────────────────────────────────────────────────────────────────────────────
// There is no cut-off on the hole count.
//
// There used to be one — `MAX_HOLES = 8` — because a skeleton's graph cost
// ~130µs to derive and `good/init-prelude.ndjson` reached some 32k distinct
// skeletons, so building them all added ~13s to the run. Sharing the signature
// across the thread's backends (see [`Shared`]) collapsed those 32388 skeletons
// to 2651 — the same shapes, now recognised as the same — and the graph
// construction with them, from 2.3s to 0.66s.
//
// So the cap is gone, and with it the entire `beta: the lambda's graph … was
// not built` category: 1228 gaps on `init-prelude` and 24 over the tutorials
// before, zero now. Measured on `good/init-prelude.ndjson`, with the tutorial
// totals beside it — all with the shared signature, so the first row is *not*
// the old baseline, which was 5.4s for the same 18025 gaps:
//
// | cut-off | prelude gaps | prelude runtime | not built | tutorial gaps |
// |--------:|-------------:|----------------:|----------:|--------------:|
// | 8       | 18025        | 2.7 s           | 1228      | 586           |
// | 16      | 16830        | 3.2 s           | 493       | 567           |
// | 32      | 16301        | 4.0 s           | 205       | 542           |
// | 64      | 16199        | 5.1 s           | 108       | 538           |
// | 128     | 16061        | 6.8 s           | 26        | 538           |
// | none    | 16009        | 8.8 s           | 0         | 538           |
//
// The hole distribution says no finite value could ever have been principled.
// Over `init-prelude`'s 2651 skeletons: 1% need no hole at all, 34% need 1–4,
// 22% need 5–8, 21% need 9–16, 14% need 17–32, 6% need 33–64, and 3% need more
// than 64 — a tail that thins but does not stop, reaching past 128. Every cap
// is a bet on the corpus.
//
// What removing it costs — 8.8s against 2.7s — is *not* graph construction, and
// that is the reason it is no longer guarded. A beta step instantiates a lemma
// whose formula grows with the hole count, one quantifier at a time, so a redex
// over a `k`-hole lambda costs O(k²) inside the kernel's `open`/`close`; a perf
// profile of the uncapped run puts ~40% of its samples in `Term::new`,
// `Term::open` and the allocator beneath them, and `beta_step` accounts for 3.8s
// of the 8.8s against 0.7s for every graph in the run. That is the derivation
// the checker exists to produce, not a mitigation for producing it slowly.
// ─────────────────────────────────────────────────────────────────────────────

/// Where one particular lambda *occurrence* sits: which skeleton it uses, and
/// with what arguments.
struct LamSite {
    /// Key into [`Shared::lam_infos`].
    key: Term,
    /// The abstracted `v`-free subterms, in traversal order.
    holes: Vec<Term>,
    /// `⟦binder_type⟧`.
    dom: Term,
}

/// Where one particular dependent-`Π` *occurrence* sits.
struct PiSite {
    /// Key into [`Shared::pi_infos`].
    key: Term,
    /// The abstracted `v`-free subterms, in traversal order.
    holes: Vec<Term>,
    /// `⟦binder_type⟧`.
    dom: Term,
}

// ─────────────────────────────────────────────────────────────────────────────
// The shared signature.
//
// A `TgBackend` is built per declaration, but the *signature* it builds terms
// in has no reason to be per declaration. A lambda skeleton is a property of
// the body's shape, and the same shapes recur in declaration after
// declaration — but when every backend has its own `Env`, the symbols standing
// for `app`, `proj`, the bound-variable slot and the enclosing lambdas are
// different symbols each time, so two occurrences of one shape produce two
// *different* skeleton terms and the graph is derived twice. Measured on
// `good/init-prelude.ndjson`: 32388 distinct skeleton terms for 1566 distinct
// shapes, a factor of 20 of pure repetition.
//
// Sharing one `Env` across the thread's backends makes those terms literally
// equal, so a shape's graph is derived once for the whole run: 32388 skeletons
// become 2651, and the graph construction drops from 2.3s to 0.66s. Coverage is
// unchanged to the gap — the derivations are the same derivations, and nothing
// about what one declaration can prove depends on another.
//
// Only the *signature* and what is keyed on it moves. `parts`, `consts`,
// `exprs`, `locals` and the rest stay per declaration: they are keyed by Lean
// nodes whose identity is per declaration, and they are not what makes
// skeletons differ — everything in a body that does not mention the binder is
// abstracted into a hole, so a skeleton contains only `app`/`proj`/`Π`
// structure, the canonical variables, and the graph symbols of nested lambdas.
//
// Sharing is sound for the same reason the [`Prelude`] replay is: an `Env` is
// only a pair of counters, so one shared `Env` issues *fewer* colliding names
// than several independent ones, never more.
//
// It does mean those counters now run for the whole check rather than being
// reset per declaration. `init-prelude` ends at 40264 symbols and 463129
// variables for 2059 declarations — about 225 variables each — against a `u32`
// each. A development three orders of magnitude larger would approach the
// variable limit, and the kernel's counters are `checked_add`, so that is a
// panic rather than an aliased variable. The remedy, if it is ever needed, is
// to drop `SHARED` and start a fresh one: nothing outside it depends on it
// persisting, and the only cost of recycling is re-deriving the graphs.
// ─────────────────────────────────────────────────────────────────────────────

/// The per-thread signature, and the derivations keyed on it.
struct Shared {
    /// The kernel signature and variable source, shared by every backend on
    /// this thread so that equal skeletons are equal *terms*.
    env: Env,
    /// The axiom-free interpretation symbols; copied into each backend.
    syms: Syms,
    /// Canonical variables for skeletons, so that two lambdas with the same
    /// body shape produce the *same* key. Reused across skeletons: they are
    /// abstracted away by `define_abbrev` immediately and never escape.
    hole_vars: Vec<FreeVar>,
    x_canon: FreeVar,
    /// Head symbol (and, when built, graph machinery) per distinct skeleton.
    lam_infos: HashMap<Term, Rc<LamInfo>>,
    /// Beta theorems, derived lazily: most lambdas are never a redex head.
    lam_betas: HashMap<Term, Option<Thm>>,
    /// Graph-extensionality theorems, keyed by the *pair* of skeletons being
    /// related. Derived lazily and shared: `lam_ext_n` is a full Extensionality
    /// derivation, and a development compares the same two body shapes over and
    /// over (once per occurrence, and again per `def_eq` call).
    lam_exts: HashMap<(Term, Term), Option<Thm>>,
    /// Dependent-product extensionality theorems, keyed the same way.
    pi_exts: HashMap<(Term, Term), Option<Thm>>,
    /// Head symbol (and, when built, fibre machinery) per distinct dependent-`Π`
    /// body skeleton.
    pi_infos: HashMap<Term, Rc<PiInfo>>,
    /// Constant-fibre bridge theorems, derived lazily: most `Π` types are never
    /// compared against a function space.
    pi_bridges: HashMap<Term, Option<Thm>>,
}

thread_local! {
    static SHARED: std::cell::RefCell<Option<Rc<std::cell::RefCell<Shared>>>> =
        const { std::cell::RefCell::new(None) };
}

/// The thread's shared signature, created on first use.
fn shared(pre: &Prelude) -> Rc<std::cell::RefCell<Shared>> {
    SHARED.with(|slot| {
        if let Some(s) = slot.borrow().as_ref() {
            return s.clone()
        }
        let mut env = Env::new();
        fast_forward(&mut env, pre);
        let syms = Syms {
            sort: env.declare(1),
            pi: env.declare(2),
            let_: env.declare(3),
            proj: env.declare(2),
            bvar: env.declare(1),
            lzero: env.declare(0),
            lsucc: env.declare(1),
            lmax: env.declare(2),
            limax: env.declare(2),
            idx: env.declare(1),
            sort0: env.declare(0),
        };
        let x_canon = env.fresh_var();
        let sh = Rc::new(std::cell::RefCell::new(Shared {
            env,
            syms,
            hole_vars: Vec::new(),
            x_canon,
            lam_infos: HashMap::new(),
            lam_betas: HashMap::new(),
            lam_exts: HashMap::new(),
            pi_exts: HashMap::new(),
            pi_infos: HashMap::new(),
            pi_bridges: HashMap::new(),
        }));
        *slot.borrow_mut() = Some(sh.clone());
        sh
    })
}

/// The Tarski–Grothendieck backend.
pub struct TgBackend<'x, 't: 'x, 'p: 't> {
    /// The signature, and everything keyed on it, shared per thread.
    shared: Rc<std::cell::RefCell<Shared>>,
    /// The application machinery and the universe operator, shared per thread.
    pre: Rc<Prelude>,
    /// The checker's declaration environment, used to resolve a constant to its
    /// value so that `⟦c⟧` can be an *explicit definition* rather than an opaque
    /// symbol. This is what makes delta reduction justifiable at all.
    decls: &'x crate::env::Env<'x, 't>,
    /// Defining equations `⊢ ⟦c⟧ = ⟦value⟧`, keyed by the constant's expression
    /// node. Delta certificates are built from these by congruence.
    const_defs: HashMap<ExprPtr<'t>, Thm>,
    /// Defining equations `⊢ ⟦let …⟧ = ⟦body[val/x]⟧`, keyed by the `Let` node.
    /// Zeta reduction is exactly this equation.
    let_defs: HashMap<ExprPtr<'t>, Thm>,
    syms: Syms,
    /// Interpretation cache. Without it, interpreting nested expressions would
    /// be quadratic; with it, each hash-consed Lean node is translated once.
    exprs: HashMap<ExprPtr<'t>, Term>,
    levels: HashMap<LevelPtr<'t>, Term>,
    /// One representative per level-equivalence class, so that levels the
    /// checker considers equal interpret to identical terms.
    level_reps: Vec<LevelPtr<'t>>,
    /// Memoised class lookup.
    level_canon: HashMap<LevelPtr<'t>, LevelPtr<'t>>,
    /// Per-name and per-index constants, allocated on demand.
    consts: HashMap<NamePtr<'t>, FnSym>,
    /// Lean local ids to kernel free variables. Allocated through `Env` rather
    /// than derived from the Lean id: the derived rules mint fresh variables for
    /// Leibniz holes, and a collision between such a hole and a Lean local would
    /// substitute at the wrong occurrences — a genuine soundness bug, not just a
    /// wrong answer.
    locals: HashMap<u64, kernel::FreeVar>,
    params: HashMap<NamePtr<'t>, Term>,
    idxs: HashMap<u64, Term>,

    /// The applicative structure of every term this backend built. The kernel
    /// does not expose `Term`'s constructors for reading, and the skeleton
    /// decomposition has to take terms apart, so the shape is recorded on the
    /// way in.
    parts: HashMap<Term, (FnSym, Vec<Term>)>,
    /// Where each lambda occurrence sits.
    lam_sites: HashMap<ExprPtr<'t>, LamSite>,
    /// Where each dependent-`Π` occurrence sits.
    pi_sites: HashMap<ExprPtr<'t>, PiSite>,
    /// A copy of the shared canonical bound-variable slot, so that the common
    /// read-only use needs no borrow.
    x_canon: FreeVar,

    /// Typing derivations `⊢ ⟦e⟧ ∈ ty`, memoised on the pair. `None` is cached
    /// too: most of what this is asked is not derivable, and re-deriving that
    /// answer is the cost that matters.
    has_types: HashMap<(ExprPtr<'t>, Term), Option<(Thm, HtClause)>>,
    /// The `(e, ty)` pairs currently being worked on, so that a definition that
    /// somehow refers to itself returns `None` instead of looping.
    ht_active: Vec<(ExprPtr<'t>, Term)>,
    /// Memoised syntactic type synthesis.
    syn_types: HashMap<ExprPtr<'t>, Option<ExprPtr<'t>>>,
    /// Memoised "could this shape ever be typed" test.
    typeables: HashMap<ExprPtr<'t>, bool>,

    _marker: PhantomData<&'p ()>,
}

impl<'x, 't: 'x, 'p: 't> TgBackend<'x, 't, 'p> {
    /// A backend for one declaration, over the thread's shared signature.
    pub fn new(decls: &'x crate::env::Env<'x, 't>) -> Self {
        let pre = prelude();
        let shared = shared(&pre);
        let (syms, x_canon) = {
            let sh = shared.borrow();
            (sh.syms, sh.x_canon)
        };
        TgBackend {
            shared,
            pre,
            decls,
            const_defs: HashMap::new(),
            let_defs: HashMap::new(),
            syms,
            exprs: HashMap::new(),
            levels: HashMap::new(),
            level_reps: Vec::new(),
            level_canon: HashMap::new(),
            consts: HashMap::new(),
            locals: HashMap::new(),
            params: HashMap::new(),
            idxs: HashMap::new(),
            parts: HashMap::new(),
            lam_sites: HashMap::new(),
            pi_sites: HashMap::new(),
            x_canon,
            has_types: HashMap::new(),
            ht_active: Vec::new(),
            syn_types: HashMap::new(),
            typeables: HashMap::new(),
            _marker: PhantomData,
        }
    }

    /// The shared signature, for the duration of one statement.
    ///
    /// Every use is deliberately short-lived: holding this across a call that
    /// itself reaches the shared state would panic on the re-entrant borrow.
    fn env_mut(&self) -> std::cell::RefMut<'_, Env> {
        std::cell::RefMut::map(self.shared.borrow_mut(), |s| &mut s.env)
    }

    /// Build `f(args)` and remember its shape, so that [`Self::skeleton`] can
    /// take it apart again later.
    fn mk(&mut self, f: FnSym, args: Vec<Term>) -> Term {
        let t = Term::apply(f, args.clone());
        self.parts.entry(t.clone()).or_insert((f, args));
        t
    }

    /// Accept `eq` as a proof that `redex` and `reduct` are equal, but only
    /// after checking it really is that equation. Every rule that concludes
    /// something about two specific terms goes through this.
    fn check_against(
        &mut self,
        ctx: &mut <Self as Certifier>::Ctx,
        eq: Thm,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
        what: &'static str,
    ) -> TgCert {
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if *eq.concl() == kernel::Formula::eq(lhs, rhs) {
            self.proved(eq)
        } else if what == "zeta" {
            self.note_admit("zeta: derived equation does not match the reduction")
        } else {
            self.note_admit("derived equation does not match the reduction")
        }
    }

    /// Wrap a derived theorem, tallying it for the coverage report.
    fn proved(&mut self, t: Thm) -> TgCert {
        note_proved();
        TgCert::Proved(t)
    }

    /// Wrap a derivation together with whatever it still assumes.
    ///
    /// The single place a [`TgCert::Conditional`] is built. `CondEq`'s
    /// constructor has already checked that the theorem is literally
    /// `⊢ conj(hyps) → (a = b)`, so the assumptions recorded here are the
    /// theorem's real antecedents and not a label attached to it.
    fn cert(&mut self, c: CondEq) -> TgCert {
        if c.hyps.is_empty() {
            return self.proved(c.thm)
        }
        note_proved();
        note_conditional();
        MAX_ASSUMED.fetch_max(c.hyps.len() as u64, std::sync::atomic::Ordering::Relaxed);
        TgCert::Conditional { thm: c.thm, hyps: c.hyps }
    }

    /// Take a certificate handed to a rule, as a conditional equation.
    ///
    /// Every [`Certifier`] method that receives certificates calls this on each
    /// of them, whatever it then does with them — that is what keeps the escape
    /// ledger exact (see [`escape_report`]): a conditional certificate is
    /// accounted for the moment a rule takes it, so the ones left over are
    /// exactly the copies the checker consumed as an *answer*.
    fn consume(&mut self, c: &TgCert) -> Option<CondEq> {
        match c {
            TgCert::Proved(t) => CondEq::plain(t.clone()),
            TgCert::Conditional { thm, hyps } => {
                note_consumed();
                CondEq::new(thm.clone(), hyps.clone())
            }
            TgCert::Admitted(_) => None,
        }
    }

    /// Transitivity, merging the two derivations' assumptions.
    fn ceq_trans(&mut self, ab: &CondEq, bc: &CondEq) -> Option<CondEq> {
        let hyps = merge_hyps(&ab.hyps, &bc.hyps);
        if hyps.len() > MAX_HYPS {
            return None
        }
        let h = conj_of(&hyps);
        let x = reassume(&ab.thm, &ab.hyps, &hyps)?;
        let y = reassume(&bc.thm, &bc.hyps, &hyps)?;
        CondEq::new(u_eq_trans(&mut self.env_mut(), &x, &y, h.as_ref())?, hyps)
    }

    /// Symmetry, keeping the assumptions.
    fn ceq_symm(&mut self, ab: &CondEq) -> Option<CondEq> {
        let h = conj_of(&ab.hyps);
        CondEq::new(u_eq_symm(&mut self.env_mut(), &ab.thm, h.as_ref())?, ab.hyps.clone())
    }

    /// Congruence over `f`, merging every argument's assumptions.
    fn ceq_congr(&mut self, f: FnSym, cs: &[CondEq]) -> Option<CondEq> {
        let mut hyps: Vec<Formula> = Vec::new();
        for c in cs {
            hyps = merge_hyps(&hyps, &c.hyps);
        }
        if hyps.len() > MAX_HYPS {
            return None
        }
        let h = conj_of(&hyps);
        let mut lifted = Vec::with_capacity(cs.len());
        for c in cs {
            lifted.push(reassume(&c.thm, &c.hyps, &hyps)?);
        }
        CondEq::new(u_congr(&mut self.env_mut(), f, &lifted, h.as_ref())?, hyps)
    }

    fn note_admit(&mut self, reason: &'static str) -> TgCert {
        // Tallied straight into the run totals rather than buffered and merged
        // on `Drop`: a `Drop` impl on the backend would make `TypeChecker`'s
        // borrow of its context live to the end of scope, which breaks callers
        // that legitimately reuse the context afterwards.
        merge_one(reason);
        TgCert::Admitted(reason)
    }

    /// A 0-ary "numeral" term standing for an index. These are opaque tags, not
    /// the primitive `ℕ` of milestone 4.
    fn idx_term(&mut self, i: u64) -> Term {
        if let Some(t) = self.idxs.get(&i) {
            return t.clone()
        }
        // Encoded as `idx` applied to itself i times over a base would be
        // linear in i; instead each distinct index gets its own nullary symbol,
        // which keeps interpretation O(1) per node.
        let s = self.env_mut().declare(0);
        let inner = self.mk(s, vec![]);
        let t = self.mk(self.syms.idx, vec![inner]);
        self.idxs.insert(i, t.clone());
        t
    }

    /// Interpret a universe level.
    ///
    /// The level is *simplified first*. The checker decides level equality with
    /// its own algebra (`eq_antisymm`), under which e.g. `imax 1 1` and `1` are
    /// equal; interpreting them naively would give syntactically different terms
    /// and turn a settled equality into an unprovable one. Normalising to the
    /// checker's canonical form keeps the two views in step, so equal levels map
    /// to identical terms and reflexivity discharges them.
    /// The canonical representative of `l`'s level-equivalence class.
    ///
    /// `simplify` is not a normal form: it settles neither commutativity,
    /// associativity, idempotence nor absorption of `max`, so `max u v` and
    /// `max v u` remain syntactically different while the checker rightly calls
    /// them equal. Rather than reimplement level algebra — `CLAUDE.md` puts
    /// levels in the translator, not the kernel — reuse the checker's own
    /// decision procedure and keep one representative per class.
    ///
    /// The scan is linear in the number of distinct classes, which is bounded by
    /// the development's universe vocabulary (tens, in practice) rather than its
    /// size.
    fn canon_level(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> LevelPtr<'t> {
        let l = ctx.simplify(l);
        if let Some(r) = self.level_canon.get(&l) {
            return *r
        }
        for rep in self.level_reps.clone() {
            if ctx.eq_antisymm(l, rep) {
                self.level_canon.insert(l, rep);
                return rep
            }
        }
        self.level_reps.push(l);
        self.level_canon.insert(l, l);
        l
    }

    /// Interpret a level structurally.
    ///
    /// Deliberately does **not** canonicalise: canonicalising here and then
    /// decomposing the representative can hand a sub-level back the whole level
    /// (absorption maps `succ u` to `max u (succ u)`, whose own sub-level is
    /// `succ u`), and the recursion never terminates. Canonicalisation happens
    /// once, at the dispatch point in [`Self::interp_sort`], where the shape
    /// choice actually matters.
    fn interp_level(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> Term {
        let l = ctx.simplify(l);
        if let Some(t) = self.levels.get(&l) {
            return t.clone()
        }
        let t = match ctx.read_level(l) {
            Level::Zero => self.mk(self.syms.lzero, vec![]),
            Level::Succ(a, _) => {
                let a = self.interp_level(ctx, a);
                self.mk(self.syms.lsucc, vec![a])
            }
            Level::Max(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                self.mk(self.syms.lmax, vec![a, b])
            }
            Level::IMax(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                self.mk(self.syms.limax, vec![a, b])
            }
            Level::Param(n, _) => {
                if let Some(t) = self.params.get(&n) {
                    t.clone()
                } else {
                    let s = self.env_mut().declare(0);
                    let t = self.mk(s, vec![]);
                    self.params.insert(n, t.clone());
                    t
                }
            }
        };
        self.levels.insert(l, t.clone());
        t
    }

    /// `⟦Sort l⟧`, climbing the universe tower.
    ///
    /// `⟦Sort 0⟧` is a constant and `⟦Sort (l+1)⟧ := U(⟦Sort l⟧)`, so
    /// `⊢ ∀x. x ∈ U(x)` immediately gives `⟦Sort l⟧ ∈ ⟦Sort (l+1)⟧`. Levels
    /// that are neither zero nor a successor (`max`, `imax`, a parameter) fall
    /// back to the opaque `sort` symbol: nothing is known about where they sit,
    /// which is honest, and the encoding stays injective on simplified levels so
    /// the `sort` rule is unaffected.
    fn interp_sort(&mut self, ctx: &mut TcCtx<'t, 'p>, level: LevelPtr<'t>) -> Term {
        // Dispatch on the *canonical representative* of the level, not on its
        // raw shape. Otherwise `Sort (max u u)` takes the opaque branch while
        // the equal `Sort u` takes the universe-tower branch, and two equal
        // levels yield different terms — which is what made idempotence and
        // absorption unprovable.
        let l = self.canon_level(ctx, level);
        match ctx.read_level(l) {
            Level::Zero => self.mk(self.syms.sort0, vec![]),
            Level::Succ(a, _) => {
                let below = self.interp_sort(ctx, a);
                self.mk(self.pre.u_sym, vec![below])
            }
            _ => {
                let lt = self.interp_level(ctx, l);
                self.mk(self.syms.sort, vec![lt])
            }
        }
    }

    fn interp_levels(&mut self, ctx: &mut TcCtx<'t, 'p>, ls: LevelsPtr<'t>) -> Vec<Term> {
        ctx.read_levels(ls).iter().copied().collect::<Vec<_>>().into_iter().map(|l| self.interp_level(ctx, l)).collect()
    }

    /// The `i`-th canonical hole variable, allocating on demand.
    fn hole_var(&mut self, i: usize) -> FreeVar {
        let mut sh = self.shared.borrow_mut();
        while sh.hole_vars.len() <= i {
            let v = sh.env.fresh_var();
            sh.hole_vars.push(v);
        }
        sh.hole_vars[i]
    }

    /// The graph machinery for a skeleton, if that skeleton has been seen.
    fn lam_info(&self, key: &Term) -> Option<Rc<LamInfo>> { self.shared.borrow().lam_infos.get(key).cloned() }

    /// Split `t` into the part that mentions `v` and the maximal `v`-free
    /// subterms, which are pushed onto `holes` and replaced by canonical hole
    /// variables. `v` itself becomes the canonical bound-variable slot.
    ///
    /// Returns `None` if a term mentioning `v` was not built by [`Self::mk`],
    /// which would mean the interpretation had leaked a variable — a bug, and
    /// one that should surface as a gap rather than be papered over.
    fn skeleton(&mut self, t: &Term, v: FreeVar, holes: &mut Vec<Term>) -> Option<Term> {
        if !t.occurs_free(v) {
            let h = self.hole_var(holes.len());
            holes.push(t.clone());
            return Some(Term::var(h))
        }
        if *t == Term::var(v) {
            return Some(Term::var(self.x_canon))
        }
        let (f, args) = self.parts.get(t)?.clone();
        let mut out = Vec::with_capacity(args.len());
        for a in &args {
            out.push(self.skeleton(a, v, holes)?);
        }
        Some(Term::apply(f, out))
    }

    /// The definitional extension behind one skeleton: the body symbol
    /// `t(h⃗,x) := skeleton` and its graph `lam(h⃗,A) = {⟨x,t(h⃗,x)⟩ : x ∈ A}`.
    ///
    /// Derived once per skeleton and then shared by every occurrence of that
    /// shape, in every declaration this thread checks.
    fn build_graph(&mut self, sk: &Term, holes: usize) -> Option<(FnSym, Graph)> {
        let mut ps: Vec<FreeVar> = Vec::with_capacity(holes + 1);
        for i in 0..holes {
            ps.push(self.hole_var(i));
        }
        ps.push(self.x_canon);
        let (t, t_def) = derived::define_abbrev(&mut self.env_mut(), &ps, sk)?;
        let (lam, lam_ax) = lambda_n(&mut self.env_mut(), &self.pre.clone().ap, t)?;
        Some((lam, Graph { t, t_def, lam_ax }))
    }

    /// Interpret `λ binder:dom. body` as a set-theoretic function graph.
    ///
    /// Returns `None` only if the decomposition itself broke down, which would
    /// be a bug in this module; the caller then falls back to an opaque symbol
    /// so that a bug degrades into a reported gap rather than a wrong answer.
    fn interp_lambda(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        binder_name: NamePtr<'t>,
        binder_style: crate::expr::BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> Option<Term> {
        let dom = self.interp(ctx, binder_type);

        // Open the binder at a fresh local, with a kernel variable reserved for
        // it up front so the interpretation of the body puts that variable in
        // exactly the bound occurrences.
        let local = ctx.mk_unique(binder_name, binder_style, binder_type);
        let key = local_key(ctx, local)?;
        let v = self.env_mut().fresh_var();
        self.locals.insert(key, v);
        let body_open = ctx.inst(body, &[local]);
        let bt = self.interp(ctx, body_open);

        let mut holes = Vec::new();
        let sk = self.skeleton(&bt, v, &mut holes)?;

        let info = match self.lam_info(&sk) {
            Some(i) => i,
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let info = match self.build_graph(&sk, holes.len()) {
                    Some((lam, g)) => Rc::new(LamInfo { lam, graph: Some(g) }),
                    // Inert: the right *shape*, so that the interpretation stays
                    // compositional, but with no defining axioms and hence no
                    // beta. The construction is closed for every skeleton this
                    // module builds, so this is unreachable in practice — and a
                    // reported gap rather than a wrong answer if it ever is not.
                    None => Rc::new(LamInfo { lam: self.env_mut().declare(arity), graph: None }),
                };
                self.shared.borrow_mut().lam_infos.insert(sk.clone(), info.clone());
                info
            }
        };

        let mut args = holes.clone();
        args.push(dom.clone());
        let term = self.mk(info.lam, args);
        self.lam_sites.insert(e, LamSite { key: sk, holes, dom });
        Some(term)
    }

    /// The fibre machinery for a `Π` skeleton, if that skeleton has been seen.
    fn pi_info(&self, key: &Term) -> Option<Rc<PiInfo>> { self.shared.borrow().pi_infos.get(key).cloned() }

    /// The definitional extension behind one `Π` skeleton: the fibre symbol
    /// `b(h⃗,x) := skeleton`, its Replacement image, and the dependent product
    /// `dprod(h⃗,A) = Π(x:A). b(h⃗,x)`.
    ///
    /// Derived once per skeleton and shared by every occurrence of that shape.
    fn build_fibre(&mut self, sk: &Term, holes: usize) -> Option<(FnSym, Fibre)> {
        let mut ps: Vec<FreeVar> = Vec::with_capacity(holes + 1);
        for i in 0..holes {
            ps.push(self.hole_var(i));
        }
        ps.push(self.x_canon);
        let (b, b_def) = derived::define_abbrev(&mut self.env_mut(), &ps, sk)?;
        let (img, img_ax) = image_symbol_n(&mut self.env_mut(), b)?;
        let pre = self.pre.clone();
        let (dprod, dprod_def) = dprod_symbol_n(&mut self.env_mut(), &pre.ap, &pre.fs, img, b)?;
        Some((dprod, Fibre { b, b_def, img, img_ax, dprod_def }))
    }

    /// Interpret `Π binder:dom. body`.
    ///
    /// A `Π` whose body does not mention the binder is the arrow `A → B`, and
    /// the arrow is a set: the function space `fs(A,B)` of
    /// [`derived::funspace`]. One that does is the **dependent product**
    /// `dprod_C(h⃗, A)` over the fibre `b_C(h⃗, ·)`, built by exactly the
    /// skeleton decomposition the lambda machinery uses — see [`build_fibre`].
    ///
    /// [`build_fibre`]: Self::build_fibre
    ///
    /// # Why the binder is opened
    ///
    /// This used to interpret the body in its *raw* de Bruijn form, with the
    /// binder's occurrences left as the opaque `bvar` symbol. That is enough
    /// for an opaque `pi(A,B)`, and not enough for a dependent product: the
    /// fibre `b(h⃗,x)` has to be a function *of* the binder, so the binder has
    /// to be a variable the definition can abstract. So the binder is opened at
    /// a fresh local, exactly as in [`Self::interp_lambda`].
    ///
    /// Two things fall out of that, both good. Non-dependence is now decided
    /// **exactly** — "the interpreted body does not mention this binder's
    /// variable" — rather than conservatively from the loose-bvar count, so a
    /// body that mentions an *enclosing* binder but not this one is now the
    /// arrow it really is. And with every binder in the tower opened, an
    /// interpreted term contains no `bvar` symbols at all, which is what makes
    /// the certificates the checker hands down (stated at *its* locals) line up
    /// with the terms the claim is about.
    ///
    /// Returns `None` only if the decomposition itself broke down; the caller
    /// then falls back to the opaque `pi` symbol, so a bug degrades into a
    /// reported gap rather than a wrong answer.
    fn interp_pi(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        binder_name: NamePtr<'t>,
        binder_style: crate::expr::BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> Option<Term> {
        let dom = self.interp(ctx, binder_type);

        // A body with no loose de Bruijn index cannot mention the binder, and
        // instantiating it would be the identity — so skip the local entirely.
        if ctx.num_loose_bvars(body) == 0 {
            let b = self.interp(ctx, body);
            return Some(self.mk(self.pre.fs_sym(), vec![dom, b]))
        }

        let local = ctx.mk_unique(binder_name, binder_style, binder_type);
        let key = local_key(ctx, local)?;
        let v = self.env_mut().fresh_var();
        self.locals.insert(key, v);
        let body_open = ctx.inst(body, &[local]);
        let bt = self.interp(ctx, body_open);

        // The exact test: a body whose interpretation does not mention the
        // binder's variable is a constant fibre, i.e. an arrow.
        if !bt.occurs_free(v) {
            return Some(self.mk(self.pre.fs_sym(), vec![dom, bt]))
        }

        let mut holes = Vec::new();
        let sk = self.skeleton(&bt, v, &mut holes)?;

        let info = match self.pi_info(&sk) {
            Some(i) => i,
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let info = match self.build_fibre(&sk, holes.len()) {
                    Some((dprod, fb)) => Rc::new(PiInfo { dprod, fibre: Some(fb) }),
                    // Inert: the right *shape*, so that the interpretation stays
                    // compositional, but with no defining axioms and hence no
                    // bridge. A reported gap rather than a wrong answer.
                    None => Rc::new(PiInfo { dprod: self.env_mut().declare(arity), fibre: None }),
                };
                self.shared.borrow_mut().pi_infos.insert(sk.clone(), info.clone());
                info
            }
        };

        let mut args = holes.clone();
        args.push(dom.clone());
        let term = self.mk(info.dprod, args);
        self.pi_sites.insert(e, PiSite { key: sk, holes, dom });
        Some(term)
    }

    /// Interpret a Lean expression as a kernel term.
    pub fn interp(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Term {
        if let Some(t) = self.exprs.get(&e) {
            return t.clone()
        }
        let t = match ctx.read_expr(e) {
            Expr::Sort { level, .. } => self.interp_sort(ctx, level),
            Expr::Var { dbj_idx, .. } => {
                let i = self.idx_term(dbj_idx as u64);
                self.mk(self.syms.bvar, vec![i])
            }
            Expr::Const { name, levels, .. } => {
                // A constant with a value becomes an **explicit definition**
                // `⟦c⟧ := ⟦value⟧`, monomorphised at these levels. That is
                // conservative for free (`∃!y. y = t` holds for any term), and
                // it is what makes delta reduction justifiable: without a
                // defining equation there is nothing relating the constant to
                // what it unfolds to.
                //
                // Constants without values — axioms, constructors, recursors —
                // stay opaque, which is correct: they do not delta-reduce.
                let decls = self.decls;
                let value = decls.get_declar_val(&name).and_then(|(uparams, val)| {
                    (ctx.read_levels(levels).len() == ctx.read_levels(uparams).len())
                        .then(|| ctx.subst_expr_levels(val, uparams, levels))
                });
                if let Some(val_subst) = value {
                    let body = self.interp(ctx, val_subst);
                    // A definition body with free variables outside the parameter list
                    // cannot be introduced soundly; fall back to an opaque symbol.
                    let Some((sym, axiom)) = derived::define_abbrev(&mut self.env_mut(), &[], &body) else {
                        let s = self.env_mut().declare(0);
                        return Term::apply(s, vec![])
                    };
                    self.const_defs.insert(e, axiom);
                    self.mk(sym, vec![])
                } else {
                    let args = self.interp_levels(ctx, levels);
                    let arity = u32::try_from(args.len()).expect("universe parameter count overflow");
                    let sym = match self.consts.get(&name) {
                        Some(s) if s.arity() == arity => *s,
                        _ => {
                            let s = self.env_mut().declare(arity);
                            self.consts.insert(name, s);
                            s
                        }
                    };
                    self.mk(sym, args)
                }
            }
            Expr::App { fun, arg, .. } => {
                let (f, a) = (self.interp(ctx, fun), self.interp(ctx, arg));
                self.mk(self.pre.ap.app, vec![f, a])
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                match self.interp_lambda(ctx, e, binder_name, binder_style, binder_type, body) {
                    Some(t) => t,
                    None => {
                        // Unreachable in principle; see `interp_lambda`. One
                        // opaque symbol per occurrence, which says nothing about
                        // the lambda but is cheap, closed, and makes beta over
                        // it report a gap instead of misbehaving.
                        let d = self.interp(ctx, binder_type);
                        let s = self.env_mut().declare(1);
                        self.mk(s, vec![d])
                    }
                }
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                // A *non-dependent* `Π x:A. B` is the arrow `A → B` — the
                // function space `fs(A,B)` of [`derived::funspace`] — and a
                // dependent one the **dependent product** `dprod_C(h⃗,A)` of
                // [`dprod_symbol_n`]. Both have real axioms behind them, and
                // `dprod_const_fibre_n` relates them when the fibre turns out to
                // be constant. See [`Self::interp_pi`].
                match self.interp_pi(ctx, e, binder_name, binder_style, binder_type, body) {
                    Some(t) => t,
                    None => {
                        // Unreachable in principle; see `interp_pi`. The opaque
                        // symbol says nothing about the `Π` but is cheap and
                        // closed, and makes the bridge over it report a gap
                        // instead of misbehaving.
                        let (d, b) = (self.interp(ctx, binder_type), self.interp(ctx, body));
                        self.mk(self.syms.pi, vec![d, b])
                    }
                }
            }
            Expr::Let { val, body, .. } => {
                // A `let` denotes its expansion, so introduce it as an
                // **explicit definition** of that expansion — exactly as a
                // constant is introduced as a definition of its value. Zeta is
                // then the defining equation, a real theorem, rather than the
                // interpretation quietly doing the substitution itself (which
                // would leave the kernel certifying nothing about the step).
                //
                // The expansion may mention Lean locals, i.e. kernel free
                // variables, so those become parameters of the symbol; `define`
                // refuses a body with a free variable it does not abstract.
                let expanded = ctx.inst(body, &[val]);
                let t = self.interp(ctx, expanded);
                let mut fvs = Vec::new();
                t.free_vars(&mut fvs);
                let defined = derived::define_abbrev(&mut self.env_mut(), &fvs, &t);
                match defined {
                    Some((sym, axiom)) => {
                        let args: Vec<Term> = fvs.iter().map(|v| Term::var(*v)).collect();
                        // Specialise `⊢ ∀fvs. sym(fvs) = t` down to this instance.
                        if let Some(inst) = derived::inst_all(&axiom, &args) {
                            self.let_defs.insert(e, inst);
                        }
                        self.mk(sym, args)
                    }
                    None => {
                        let s = self.env_mut().declare(0);
                        self.mk(s, vec![])
                    }
                }
            }
            Expr::Local { id, .. } => {
                // Lean locals become kernel *free* variables. This is what makes
                // the eventual certificate a closed statement: generalising over
                // them is `lam_cong`/`pi_cong`'s job, and free variables are
                // exactly what the kernel's `gen` rule can abstract.
                // `FVarId` is either a de Bruijn *level* (used while descending
                // under binders) or a globally unique id; keep the two in
                // separate halves of the key space so they cannot alias.
                let key = match id {
                    crate::expr::FVarId::DbjLevel(n) => n as u64,
                    crate::expr::FVarId::Unique(n) => (n as u64) | (1 << 32),
                };
                let v = match self.locals.get(&key) {
                    Some(v) => *v,
                    None => {
                        let v = self.env_mut().fresh_var();
                        self.locals.insert(key, v);
                        v
                    }
                };
                Term::var(v)
            }
            Expr::Proj { idx, structure, .. } => {
                let i = self.idx_term(idx as u64);
                let s = self.interp(ctx, structure);
                self.mk(self.syms.proj, vec![i, s])
            }
            // Literals get one opaque nullary symbol each. Distinct literals get
            // distinct symbols because the whole match is memoised on the
            // hash-consed `ExprPtr`, so equal literals are the same node.
            // Milestone 4 replaces these with the kernel's primitive `ℕ` and its
            // native bignum rule schemas.
            Expr::NatLit { .. } | Expr::StringLit { .. } => {
                let s = self.env_mut().declare(0);
                self.mk(s, vec![])
            }
        };
        self.exprs.insert(e, t.clone());
        t
    }

    /// `⊢ ⟦a⟧ ∈ dom`, the typing premise `beta_conditional_n` is conditional on,
    /// or `None` when this interpretation does not know that membership.
    ///
    /// Two facts are available, both genuine theorems about the two operators
    /// the interpretation is built from:
    ///
    /// * `⊢ ∀x. x ∈ U(x)` — a sort sits in the next universe up, since
    ///   `⟦Sort (u+1)⟧` *is* `U(⟦Sort u⟧)`;
    /// * `⊢ ∀a. fs(a,a) ∈ U(a)` — the function space `t → t` sits in the least
    ///   universe over `t`, which is what makes `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧`
    ///   available now that a non-dependent `Pi` is interpreted as `fs`.
    ///
    /// Whichever applies, the result is checked to be literally `⟦a⟧ ∈ dom`
    /// before it is returned, so a mistake here yields a gap and not a theorem
    /// about the wrong terms.
    fn domain_premise(&mut self, ta: &Term, dom: &Term) -> Option<Thm> {
        let want = Formula::mem(ta.clone(), dom.clone());
        let out = if *dom == Term::apply(self.pre.u_sym, vec![ta.clone()]) {
            let mem_u = self.pre.mem_u.clone();
            derived::inst_all(&mem_u, std::slice::from_ref(ta))?
        } else {
            // `⟦a⟧` has to be a *diagonal* function space `fs(t,t)`: the
            // two-argument form `(a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c)` carries an
            // antecedent about binary unions that is not dischargeable here.
            let (f, args) = self.parts.get(ta)?.clone();
            if f != self.pre.fs_sym() || args.len() != 2 || args[0] != args[1] {
                return None
            }
            let t = args[0].clone();
            if *dom != Term::apply(self.pre.u_sym, vec![t.clone()]) {
                return None
            }
            let fs_in_u = self.pre.fs_in_u.clone();
            derived::inst_all(&fs_in_u, std::slice::from_ref(&t))?
        };
        (*out.concl() == want).then_some(out)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The type-directed interpretation.
    //
    // `domain_premise` above knows two facts about the *operators* the
    // interpretation is built from, and nothing about Lean's typing judgement.
    // `has_type` is the judgement: `⊢ ⟦e⟧ ∈ ⟦A⟧` derived by recursion on the
    // structure of `e`, one clause per Lean typing rule. Every clause ends at
    // the same guard — the theorem handed back must literally conclude
    // `Formula::mem(⟦e⟧, ty)` — so a clause that builds the wrong thing yields
    // `None`, i.e. a carried assumption and a reported gap, never a claim.
    //
    // `None` means "not proved". It never means "assume it": the assumption
    // path is `beta_step`'s, and it is visible in the escape ledger.
    //
    // What each clause needs:
    //
    // * `Sort u` — `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` *is* `x ∈ U(x)`, so it is already
    //   settled by `domain_premise`'s first branch, which is not restricted to
    //   sorts. There is no separate clause and nothing to add.
    // * `Const c` — `⟦c⟧` is introduced as a *definition* of `⟦value⟧`, so the
    //   membership transfers along the defining equation and the obligation
    //   becomes the value's own. Constants with no value (axioms, inductive
    //   types, constructors, recursors) are opaque symbols with no axioms
    //   whatever, so nothing about where they live is derivable — honestly
    //   `None`.
    // * `App f a` — the characteristic property of the interpretation of `f`'s
    //   type. For `fs(A,B)` that is `Prelude::fs_app_mem`; for a dependent
    //   product it is the `∀x ∈ A. app(f,x) ∈ b(x)` conjunct of `dprod_def`,
    //   after which `b(h⃗,⟦a⟧)` is unfolded to the fibre skeleton — the same
    //   unfolding `beta_step` does, which is why the result lines up with
    //   `⟦B[a]⟧` syntactically.
    // * `Local w` — the carried assumption; `None` here on purpose.
    // * `Lam` and `Pi` — need `lam_in_dprod` and `dprod_in_universe`
    //   respectively, neither of which exists in `derived` yet. `None`, and
    //   counted, so the cost of their absence is a measured number rather than
    //   a guess (see [`ht_report`]).
    // * `Let`, `Proj`, literals — `None`.
    // ─────────────────────────────────────────────────────────────────────────

    /// How deep the recursion may go before giving up.
    ///
    /// A pure cost and termination guard. A Lean definition cannot refer to
    /// itself, so unfolding constants terminates, but a chain of aliases can be
    /// long and each link re-interprets a type; `Self::ht_active` catches an
    /// actual cycle and this catches everything else. Nothing is unsound about
    /// a larger bound: hitting it returns `None`, hence a carried assumption.
    const MAX_TYPE_DEPTH: u32 = 16;

    /// `⊢ ⟦e⟧ ∈ ty`, or `None` when this interpretation cannot derive it.
    ///
    /// Memoised on `(e, ty)`. The memo caches negative results too, including
    /// ones the depth bound or the cycle guard caused; that can only lose
    /// completeness — a `Some` is checked against its claim on every path out,
    /// so nothing false can be cached.
    fn has_type(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: &Term, depth: u32) -> Option<Thm> {
        let key = (e, ty.clone());
        let out = match self.has_types.get(&key) {
            Some(r) => r.clone(),
            None => {
                if depth > Self::MAX_TYPE_DEPTH || self.ht_active.contains(&key) {
                    return None
                }
                self.ht_active.push(key.clone());
                let out = self.has_type_uncached(ctx, e, ty, depth);
                self.ht_active.pop();

                // The guard. A theorem that does not literally conclude the
                // membership being claimed is not a proof of it, whatever it
                // proves. Every clause passes through here, once.
                let want = Formula::mem(self.interp(ctx, e), ty.clone());
                let out = out.filter(|(t, _)| *t.concl() == want);
                self.has_types.insert(key, out.clone());
                out
            }
        };
        // Counted per *use*, memo replays included, so the split says which
        // typing rule is carrying the work rather than which was derived first.
        let (thm, clause) = out?;
        note_ht(clause);
        Some(thm)
    }

    /// [`Self::has_type`] without the memo, the guard or the cycle check;
    /// reports which clause answered.
    fn has_type_uncached(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        depth: u32,
    ) -> Option<(Thm, HtClause)> {
        // The two facts about the operators themselves — `x ∈ U(x)`, which is
        // what makes `Sort` work, and `fs(a,a) ∈ U(a)`. Both are term-level and
        // cheap, so they are tried before anything is taken apart.
        let te = self.interp(ctx, e);
        if let Some(t) = self.domain_premise(&te, ty) {
            let by = if *ty == Term::apply(self.pre.u_sym, vec![te]) { HtClause::MemU } else { HtClause::FsDiag };
            return Some((t, by))
        }
        match ctx.read_expr(e) {
            Expr::Const { .. } => self.has_type_const(ctx, e, ty, depth),
            Expr::App { fun, arg, .. } => self.has_type_app(ctx, fun, arg, depth),
            _ => None,
        }
    }

    /// `⟦c⟧ ∈ ty` from `⟦value⟧ ∈ ty`, along the defining equation
    /// `⊢ ⟦c⟧ = ⟦value⟧` that [`Self::interp`] introduced for the constant.
    fn has_type_const(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        depth: u32,
    ) -> Option<(Thm, HtClause)> {
        let Expr::Const { name, levels, .. } = ctx.read_expr(e) else { return None };
        // Interpreting the constant is what registers its defining equation.
        let _ = self.interp(ctx, e);
        let def = self.const_defs.get(&e).cloned()?;
        let (c_t, val_t) = def.concl().as_eq()?;

        let decls = self.decls;
        let (uparams, val) = decls.get_declar_val(&name)?;
        if ctx.read_levels(levels).len() != ctx.read_levels(uparams).len() {
            return None
        }
        let val = ctx.subst_expr_levels(val, uparams, levels);
        // The value's interpretation is what the defining equation is about; if
        // the two have drifted apart the rewrite below simply will not apply.
        let h = self.has_type(ctx, val, ty, depth + 1)?;

        // ⊢ ⟦value⟧ = ⟦c⟧, then Leibniz at the hole `x ∈ ty`.
        let back = derived::eq_symm(&mut self.env_mut(), &def)?;
        let x = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(val_t, c_t, x, Formula::mem(Term::var(x), ty.clone()));
        let out = Thm::mp(&Thm::mp(&leib, &back)?, &h)?;
        Some((out, HtClause::Const))
    }

    /// `app(⟦f⟧,⟦a⟧) ∈ ty` from `⟦f⟧ ∈ ⟦Π A B⟧` and `⟦a⟧ ∈ ⟦A⟧`.
    ///
    /// The `Π` is read off `f`'s *syntactic* type ([`Self::syn_type`]): no
    /// reduction and no definitional equality, so this cannot call back into the
    /// checker while the checker is inside the backend.
    ///
    /// The target `ty` is not an input: what this derives is whatever the
    /// characteristic property yields, and [`Self::has_type`]'s guard decides
    /// whether that is the membership being claimed.
    fn has_type_app(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        fun: ExprPtr<'t>,
        arg: ExprPtr<'t>,
        depth: u32,
    ) -> Option<(Thm, HtClause)> {
        // Interpreting a `Π` builds a fibre — a Replacement derivation — so the
        // shape check that says the head could conceivably be typed at all comes
        // first, and the type is interpreted only if it passes.
        if !self.typeable_shape(ctx, fun, 0) {
            return None
        }
        let fty = self.syn_type(ctx, fun)?;
        let Expr::Pi { binder_type, .. } = ctx.read_expr(fty) else { return None };

        let fty_t = self.interp(ctx, fty);
        let dom_t = self.interp(ctx, binder_type);
        let (tf, ta) = (self.interp(ctx, fun), self.interp(ctx, arg));
        let hf = self.has_type(ctx, fun, &fty_t, depth + 1)?;
        let ha = self.has_type(ctx, arg, &dom_t, depth + 1)?;

        // Non-dependent: `⟦Π A B⟧` is the function space, and a function's
        // values lie in its codomain.
        if let Some((f, args)) = self.parts.get(&fty_t).cloned() {
            if f == self.pre.fs_sym() && args.len() == 2 && args[0] == dom_t {
                let lem = self.pre.fs_app_mem.clone();
                let out = app_in_codomain(&lem, &dom_t, &args[1], &tf, &ta, &hf, &ha)?;
                return Some((out, HtClause::AppFs))
            }
        }

        // Dependent: the `∀x ∈ A. app(f,x) ∈ b(x)` conjunct of the dependent
        // product's defining axiom, then the fibre symbol unfolded.
        let site = self.pi_sites.get(&fty)?;
        let (skel, holes, pdom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        if pdom != dom_t {
            return None
        }
        let info = self.pi_info(&skel)?;
        let fb = info.fibre.as_ref()?;
        let (dprod_def, b_def) = (fb.dprod_def.clone(), fb.b_def.clone());
        let app = self.pre.ap.app;
        let out = app_in_fibre(
            &mut self.env_mut(),
            app,
            &dprod_def,
            &b_def,
            &holes,
            &pdom,
            &tf,
            &ta,
            &hf,
            &ha,
        )?;
        Some((out, HtClause::AppDProd))
    }

    /// Lean's type for `e`, read off the declaration environment and the
    /// binders — no `whnf`, no `infer`, no definitional equality.
    ///
    /// This is deliberately *not* the checker's `infer`. `infer` lives on
    /// `TypeChecker`, which owns this backend and is in the middle of a call
    /// into it, and it decides definitional equalities on the way — so calling
    /// it here would be re-entrant. Every case below is a projection out of data
    /// already to hand, and anything else is `None`.
    fn syn_type(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let Some(r) = self.syn_types.get(&e) {
            return *r
        }
        let out = match ctx.read_expr(e) {
            Expr::Local { binder_type, .. } => Some(binder_type),
            Expr::Sort { level, .. } => {
                let l = ctx.succ(level);
                Some(ctx.mk_sort(l))
            }
            Expr::Const { name, levels, .. } => {
                let decls = self.decls;
                let info = *decls.get_declar(&name)?.info();
                (ctx.read_levels(levels).len() == ctx.read_levels(info.uparams).len()).then_some(())?;
                Some(ctx.subst_expr_levels(info.ty, info.uparams, levels))
            }
            Expr::App { fun, arg, .. } => {
                let fty = self.syn_type(ctx, fun)?;
                // Only a `Π` in the head position is usable, and exposing one
                // would need `whnf`. A type that is not syntactically a `Π` is
                // simply not read here.
                match ctx.read_expr(fty) {
                    Expr::Pi { body, .. } => Some(ctx.inst(body, &[arg])),
                    _ => None,
                }
            }
            _ => None,
        };
        self.syn_types.insert(e, out);
        out
    }

    /// Classify an argument whose typing obligation `has_type` could not
    /// discharge, so that the remaining work is a table rather than a guess.
    fn ht_shape(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> HtMiss {
        let head = |b: &mut Self, ctx: &mut TcCtx<'t, 'p>, h: ExprPtr<'t>| match ctx.read_expr(h) {
            Expr::Const { name, .. } => {
                if b.decls.get_declar_val(&name).is_some() {
                    HtMiss::AppDefHead
                } else {
                    HtMiss::AppOpaqueHead
                }
            }
            Expr::Lambda { .. } => HtMiss::AppLamHead,
            Expr::Local { .. } => HtMiss::AppLocalHead,
            _ => HtMiss::AppOther,
        };
        match ctx.read_expr(e) {
            Expr::Local { .. } => HtMiss::Local,
            Expr::Lambda { .. } => HtMiss::Lam,
            Expr::Pi { .. } => HtMiss::Pi,
            Expr::Const { name, .. } =>
                if self.decls.get_declar_val(&name).is_some() {
                    HtMiss::ConstDef
                } else {
                    HtMiss::ConstOpaque
                },
            Expr::App { .. } => {
                let (h, _) = ctx.unfold_apps(e);
                head(self, ctx, h)
            }
            _ => HtMiss::Other,
        }
    }

    /// Whether `e` is of a shape [`Self::has_type`] could conceivably discharge.
    ///
    /// A cost guard, not a soundness one: `has_type` would answer `None` for all
    /// of these anyway, but only after interpreting a type, and interpreting a
    /// `Π` builds a fibre. The shapes that are never typeable — a local, a
    /// lambda, an opaque constant — are much the commonest arguments, so
    /// checking first is what keeps this off the hot path.
    fn typeable_shape(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, depth: u32) -> bool {
        if let Some(b) = self.typeables.get(&e) {
            return *b
        }
        if depth > Self::MAX_TYPE_DEPTH {
            return false
        }
        let out = match ctx.read_expr(e) {
            Expr::Sort { .. } => true,
            Expr::Const { name, levels, .. } => {
                let decls = self.decls;
                match decls.get_declar_val(&name) {
                    Some((uparams, val)) if ctx.read_levels(levels).len() == ctx.read_levels(uparams).len() => {
                        let val = ctx.subst_expr_levels(val, uparams, levels);
                        self.typeable_shape(ctx, val, depth + 1)
                    }
                    _ => false,
                }
            }
            Expr::App { fun, .. } => self.typeable_shape(ctx, fun, depth + 1),
            _ => false,
        };
        self.typeables.insert(e, out);
        out
    }

    /// The beta theorem for one lambda skeleton, derived on first use.
    fn beta_thm(&mut self, key: &Term) -> Option<Thm> {
        if let Some(t) = self.shared.borrow().lam_betas.get(key) {
            return t.clone()
        }
        let info = self.lam_info(key)?;
        let g = info.graph.as_ref()?;
        let (t, lam, lam_ax) = (g.t, info.lam, g.lam_ax.clone());
        let ap = self.pre.clone();
        let thm = beta_conditional_n(&mut self.env_mut(), &ap.ap, t, lam, &lam_ax);
        self.shared.borrow_mut().lam_betas.insert(key.clone(), thm.clone());
        thm
    }

    /// One beta contraction: `⊢ app(⟦λ⟧, ⟦a⟧) = ⟦body[a]⟧`, possibly under the
    /// assumption `⟦a⟧ ∈ dom` when the typing obligation cannot be discharged.
    fn beta_step(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        lam_expr: ExprPtr<'t>,
        body: ExprPtr<'t>,
        arg: ExprPtr<'t>,
    ) -> Result<(CondEq, ExprPtr<'t>), &'static str> {
        // Interpreting the lambda is what registers its graph symbol.
        let _ = self.interp(ctx, lam_expr);
        let Some(site) = self.lam_sites.get(&lam_expr) else {
            return Err("beta: the lambda has no function-graph interpretation")
        };
        let (key, holes, dom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        let ta = self.interp(ctx, arg);

        // The domain premise is settled *first*: it is a term comparison plus
        // one instantiation, while the beta lemma below is a derivation, and
        // most redexes fail here.
        //
        // The obligation is Lean's typing judgement, and `has_type` is that
        // judgement — one clause per typing rule, over the two facts
        // `domain_premise` knows about the operators themselves. When no clause
        // applies the step is **not** admitted: the premise is kept as a genuine assumption and
        // the certificate says so, `⊢ (⟦a⟧ ∈ dom) → …`. It then has to be
        // discharged before the certificate reaches a boundary, or it is
        // reported as a gap (see `escape_report`).
        let mem_inst = self.has_type(ctx, arg, &dom, 0);
        note_ht_call(mem_inst.is_some());
        if mem_inst.is_none() {
            note_ht_miss(self.ht_shape(ctx, arg));
        }
        let hyps = match mem_inst {
            Some(_) => Vec::new(),
            None => vec![Formula::mem(ta.clone(), dom.clone())],
        };
        let Some(beta) = self.beta_thm(&key) else {
            return Err("beta: the lambda's graph, and so its beta lemma, was not built")
        };

        // ⊢ ⟦a⟧ ∈ dom → app(lam(h⃗,dom), ⟦a⟧) = t(h⃗, ⟦a⟧)
        let mut inst = holes.clone();
        inst.push(dom.clone());
        inst.push(ta.clone());
        let Some(conditional) = derived::inst_all(&beta, &inst) else {
            return Err("beta: instantiating the beta lemma failed")
        };

        // With the membership in hand the premise comes off; without it the
        // implication *is* the certificate, its antecedent being the single
        // assumption recorded above.
        let eq_t = match &mem_inst {
            Some(m) => {
                let Some(t) = Thm::mp(&conditional, m) else {
                    return Err("beta: discharging the domain premise failed")
                };
                t
            }
            None => conditional,
        };
        let Some(eq_t) = CondEq::new(eq_t, hyps) else {
            return Err("beta: the beta lemma does not have the assumed shape")
        };

        // Unfold `t(h⃗, ⟦a⟧)` to the skeleton with the argument plugged in, and
        // check that is literally the interpretation of the contracted body.
        let info = self.lam_info(&key).expect("skeleton registered");
        let Some(g) = info.graph.as_ref() else {
            return Err("beta: the lambda's graph was not built")
        };
        let mut inst_t = holes;
        inst_t.push(ta);
        let Some(unfold) = derived::inst_all(&g.t_def, &inst_t) else {
            return Err("beta: instantiating the body definition failed")
        };
        let Some(unfold) = CondEq::plain(unfold) else {
            return Err("beta: the body definition is not an equation")
        };
        let Some(step) = self.ceq_trans(&eq_t, &unfold) else {
            return Err("beta: chaining the body definition failed")
        };

        let next = ctx.inst(body, &[arg]);
        let tnext = self.interp(ctx, next);
        let Some((_, rhs)) = step.as_eq() else {
            return Err("beta: the derived step is not an equation")
        };
        if rhs != tnext {
            return Err("beta: the contracted body does not match its interpretation")
        }
        Ok((step, next))
    }

    /// The whole (possibly multi-argument) beta contraction the checker asked
    /// for, as `⊢ ⟦redex⟧ = ⟦reduct⟧` — or, where a contraction's typing
    /// obligation could not be discharged, under the assumptions it needed.
    fn derive_beta(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
    ) -> Result<CondEq, &'static str> {
        let (fun, args) = ctx.unfold_apps(redex);
        if args.is_empty() {
            return Err("beta: the redex is not an application")
        }
        let mut cur = fun;
        let mut acc = CondEq::refl(self.interp(ctx, fun));
        let app = self.pre.ap.app;

        for arg in args {
            let ta = self.interp(ctx, arg);
            let Some(lifted) = self.ceq_congr(app, &[acc.clone(), CondEq::refl(ta)]) else {
                return Err("beta: congruence over the spine refused")
            };
            acc = lifted;
            // The checker contracts every leading lambda it can and re-applies
            // whatever is left over, so stop peeling at the first non-lambda and
            // let congruence carry the rest.
            if let Expr::Lambda { body, .. } = ctx.read_expr(cur) {
                let (step, next) = self.beta_step(ctx, cur, body, arg)?;
                let Some(chained) = self.ceq_trans(&acc, &step) else {
                    return Err("beta: chaining a contraction failed")
                };
                acc = chained;
                cur = next;
            }
        }

        // Guard. The derivation is worth nothing unless it is a derivation of
        // the equation the checker actually claimed.
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if !acc.proves(&lhs, &rhs) {
            return Err("beta: derived equation does not match the reduction")
        }
        Ok(acc)
    }

    /// Graph extensionality relating the two lambda *skeletons*, derived on
    /// first use and shared thereafter.
    fn lam_ext_thm(&mut self, ka: &Term, kb: &Term) -> Option<Thm> {
        let key = (ka.clone(), kb.clone());
        if let Some(t) = self.shared.borrow().lam_exts.get(&key) {
            return t.clone()
        }
        let ia = self.lam_info(ka)?;
        let ib = self.lam_info(kb)?;
        let thm = match (ia.graph.as_ref(), ib.graph.as_ref()) {
            (Some(ga), Some(gb)) => {
                let ap = self.pre.clone();
                lam_ext_n(&mut self.env_mut(), &ap.ap, ga.t, ia.lam, &ga.lam_ax, gb.t, ib.lam, &gb.lam_ax)
            }
            _ => None,
        };
        self.shared.borrow_mut().lam_exts.insert(key, thm.clone());
        thm
    }

    /// The pointwise premise of [`lam_ext_n`], read off the body certificate.
    ///
    /// The certificate says `⊢ ⟦b⟧ = ⟦b'⟧` with both bodies opened at the
    /// checker's local for this binder — a kernel *free* variable `w`. What the
    /// extensionality lemma wants is `⊢ ∀x. (x ∈ A → t(h⃗,x) = t'(h⃗',x))`.
    ///
    /// The bridge is the two body-symbol definitions: `t(h⃗,w)` unfolds to the
    /// skeleton with `w` in the binder slot, which is exactly the certificate's
    /// left-hand side — *if* `w` is the right variable, which is checked by
    /// comparing the unfolded terms rather than assumed. `w` itself is not
    /// handed to this rule, so it is searched for among the free variables of
    /// the certificate; a body that ignores its binder pins nothing, and then a
    /// fresh variable does (the resulting `∀` is vacuous, which is correct).
    ///
    /// Weakening to the guarded form is `a1i`, and the generalisation is the
    /// kernel's `gen` — which needs no side condition, since a `Thm` carries no
    /// hypotheses. It does need `w` to be absent from `h⃗`, `h⃗'` and `A`, or the
    /// `∀` would capture them; the candidates are filtered on exactly that, and
    /// a slip could only make the `mp` below fail, never produce a false claim.
    ///
    /// # Discharging an assumption
    ///
    /// This is also the one place where a carried assumption goes away. If the
    /// body certificate is conditional and one of its assumptions is literally
    /// `w ∈ A` — the guard of the very `∀` being built — then that assumption is
    /// *not* weakened in, it is **used**: re-stated last, peeled off with
    /// [`derived::uncurry`], generalised, and pushed back through the ∀ with
    /// `Thm::ax_dist`. The kernel checks `ax_dist`'s side condition (`w` not
    /// free in the remaining assumptions), so a mistake is a rejection.
    ///
    /// Returns the premise together with the assumptions that survive it.
    fn pointwise_premise(
        &mut self,
        t_def_a: &Thm,
        t_def_b: &Thm,
        holes_a: &[Term],
        holes_b: &[Term],
        dom_a: &Term,
        body: &CondEq,
    ) -> Option<(Thm, Vec<Formula>)> {
        let (u1, u2) = body.as_eq()?;

        // Variables `w` may be: those the two body interpretations mention, but
        // not any that the parameters or the domain do.
        let mut excluded: Vec<FreeVar> = Vec::new();
        for h in holes_a.iter().chain(holes_b.iter()) {
            h.free_vars(&mut excluded);
        }
        dom_a.free_vars(&mut excluded);
        let mut seen: Vec<FreeVar> = Vec::new();
        u1.free_vars(&mut seen);
        u2.free_vars(&mut seen);
        let mut cands: Vec<FreeVar> = Vec::new();
        for v in seen {
            if !excluded.contains(&v) && !cands.contains(&v) {
                cands.push(v);
            }
        }
        // A body that does not mention its binder leaves `w` free; any variable
        // not already in play will do, and a fresh one certainly is not.
        cands.push(self.env_mut().fresh_var());

        for w in cands {
            let tw = Term::var(w);
            let inst = |holes: &[Term]| {
                let mut v = holes.to_vec();
                v.push(tw.clone());
                v
            };
            let Some(ea) = derived::inst_all(t_def_a, &inst(holes_a)) else { continue };
            let Some(eb) = derived::inst_all(t_def_b, &inst(holes_b)) else { continue };
            // `t(h⃗,w) = ⟦b⟧` and `t'(h⃗',w) = ⟦b'⟧` — the halves that make the
            // certificate applicable at all.
            match (ea.concl().as_eq(), eb.concl().as_eq()) {
                (Some((_, ra)), Some((_, rb))) if ra == u1 && rb == u2 => {}
                _ => continue,
            }
            let Some(eb_symm) = derived::eq_symm(&mut self.env_mut(), &eb) else { continue };
            let (Some(ea), Some(eb_symm)) = (CondEq::plain(ea), CondEq::plain(eb_symm)) else { continue };
            let Some(half) = self.ceq_trans(&ea, body) else { continue };
            let Some(at_w) = self.ceq_trans(&half, &eb_symm) else { continue };
            let Some(out) = self.guard_and_generalise(&at_w, w, dom_a) else { continue };
            return Some(out)
        }
        None
    }

    /// Turn `⊢ conj(hyps) → (l = r)`, stated at the free variable `w`, into
    /// `⊢ conj(rest) → ∀x. (x ∈ A → l[x] = r[x])`.
    ///
    /// The guarded, generalised form is what both extensionality lemmas want as
    /// a premise: [`lam_ext_n`]'s pointwise equation and
    /// [`dprod_const_fibre_n`]'s constant-fibre condition are the same shape.
    ///
    /// Weakening to the guarded form is `a1i`, and the generalisation is the
    /// kernel's `gen` — which needs no side condition, since a `Thm` carries no
    /// hypotheses. It does need `w` to be absent from `A` and from anything the
    /// two sides are supposed to be uniform in; the callers filter their
    /// candidates on exactly that, and a slip could only make the `mp` in the
    /// caller fail, never produce a false claim.
    ///
    /// # Discharging an assumption
    ///
    /// This is the one place where a carried assumption goes away. If the
    /// certificate is conditional and one of its assumptions is literally
    /// `w ∈ A` — the guard of the very `∀` being built — then that assumption is
    /// *not* weakened in, it is **used**: re-stated last, peeled off with
    /// [`derived::uncurry`], generalised, and pushed back through the ∀ with
    /// `Thm::ax_dist`. The kernel checks `ax_dist`'s side condition (`w` not
    /// free in the remaining assumptions), so a mistake is a rejection.
    ///
    /// Returns the premise together with the assumptions that survive it.
    fn guard_and_generalise(&mut self, at_w: &CondEq, w: FreeVar, dom: &Term) -> Option<(Thm, Vec<Formula>)> {
        let (l, r) = at_w.as_eq()?;
        let (eqf, guard) = (Formula::eq(l, r), Formula::mem(Term::var(w), dom.clone()));

        // The guarded body `w ∈ A → l = r`, under whatever assumptions are left
        // over. Either the guard is one of the certificate's own assumptions —
        // then it is discharged into the implication rather than assumed twice —
        // or it is pure weakening.
        let (rest, guarded) = match at_w.hyps.iter().position(|f| *f == guard) {
            Some(i) => {
                let mut rest = at_w.hyps.clone();
                rest.remove(i);
                let mut last = rest.clone();
                last.push(guard.clone());
                let re = reassume(&at_w.thm, &at_w.hyps, &last)?;
                if rest.is_empty() {
                    // `conj([guard])` *is* `guard`: already the wanted form.
                    (rest, re)
                } else {
                    let peeled = derived::uncurry(&re)?;
                    (rest, peeled)
                }
            }
            None => {
                let rest = at_w.hyps.clone();
                if rest.is_empty() {
                    (rest, derived::a1i(&at_w.thm, guard.clone()))
                } else {
                    (rest, derived::syl(&at_w.thm, &Thm::ax_k(eqf.clone(), guard.clone()))?)
                }
            }
        };

        let all = Thm::gen(w, &guarded);
        if rest.is_empty() {
            return Some((all, rest))
        }
        // `⊢ ∀w. (conj(rest) → (w ∈ A → …))` becomes
        // `⊢ conj(rest) → ∀w. (w ∈ A → …)`. The kernel refuses if `w` is free in
        // `conj(rest)`, which is exactly the condition under which the move
        // would be wrong.
        let rc = conj_of(&rest)?;
        let dist = Thm::ax_dist(w, rc, Formula::imp(guard, eqf))?;
        let out = Thm::mp(&dist, &all)?;
        Some((out, rest))
    }

    /// Dependent-product extensionality relating the two fibre *skeletons*,
    /// derived on first use and shared thereafter.
    fn pi_ext_thm(&mut self, ka: &Term, kb: &Term) -> Option<Thm> {
        let key = (ka.clone(), kb.clone());
        if let Some(t) = self.shared.borrow().pi_exts.get(&key) {
            return t.clone()
        }
        let ia = self.pi_info(ka)?;
        let ib = self.pi_info(kb)?;
        let thm = match (ia.fibre.as_ref(), ib.fibre.as_ref()) {
            (Some(fa), Some(fb)) => {
                let pre = self.pre.clone();
                dprod_ext_n(
                    &mut self.env_mut(),
                    &pre.ap,
                    &pre.fs,
                    (fa.b, fa.img, &fa.img_ax, ia.dprod, &fa.dprod_def),
                    (fb.b, fb.img, &fb.img_ax, ib.dprod, &fb.dprod_def),
                )
            }
            _ => None,
        };
        self.shared.borrow_mut().pi_exts.insert(key, thm.clone());
        thm
    }

    /// The constant-fibre bridge for one `Π` skeleton, derived on first use and
    /// shared thereafter: `dprod_const_fibre_n` is a full Extensionality
    /// argument in both directions, and the same body shape recurs.
    fn pi_bridge_thm(&mut self, key: &Term) -> Option<Thm> {
        if let Some(t) = self.shared.borrow().pi_bridges.get(key) {
            return t.clone()
        }
        let info = self.pi_info(key)?;
        let thm = match info.fibre.as_ref() {
            Some(fb) => {
                let pre = self.pre.clone();
                dprod_const_fibre_n(
                    &mut self.env_mut(),
                    &pre.ap,
                    &pre.fs,
                    fb.b,
                    fb.img,
                    &fb.img_ax,
                    info.dprod,
                    &fb.dprod_def,
                    &pre.fs_app_mem,
                    &pre.fs_retarget,
                )
            }
            None => None,
        };
        self.shared.borrow_mut().pi_bridges.insert(key.clone(), thm.clone());
        thm
    }

    /// The constant-fibre premise of [`dprod_const_fibre_n`], read off the body
    /// certificate: `⊢ ∀x. (x ∈ A → b(h⃗,x) = B)`.
    ///
    /// The certificate relates the two `Π` bodies opened at the checker's local
    /// `w`. One of them is the dependent side, and `b(h⃗,w)` unfolds — by the
    /// fibre's defining equation — to exactly that; the other does not mention
    /// the binder at all, so it *is* the constant `B` the function space names.
    /// Chaining the two gives `b(h⃗,w) = B` at that one `w`, and
    /// [`Self::guard_and_generalise`] turns it into the pointwise condition.
    ///
    /// Which variable `w` is, is not handed to this rule; it is searched for
    /// among the free variables the certificate mentions, and the unfolding is
    /// *compared* rather than assumed, so a wrong guess yields `None`.
    fn fibre_premise(
        &mut self,
        b_def: &Thm,
        holes: &[Term],
        dom: &Term,
        target: &Term,
        body: &CondEq,
    ) -> Option<(Thm, Vec<Formula>)> {
        let (u1, u2) = body.as_eq()?;

        // Variables `w` may be: those the certificate mentions, but not any that
        // the parameters, the domain or the constant fibre do — generalising
        // over one of those would capture it.
        let mut excluded: Vec<FreeVar> = Vec::new();
        for h in holes {
            h.free_vars(&mut excluded);
        }
        dom.free_vars(&mut excluded);
        target.free_vars(&mut excluded);
        let mut seen: Vec<FreeVar> = Vec::new();
        u1.free_vars(&mut seen);
        u2.free_vars(&mut seen);
        let mut cands: Vec<FreeVar> = Vec::new();
        for v in seen {
            if !excluded.contains(&v) && !cands.contains(&v) {
                cands.push(v);
            }
        }
        cands.push(self.env_mut().fresh_var());

        for w in cands {
            let mut args = holes.to_vec();
            args.push(Term::var(w));
            let Some(unfold) = derived::inst_all(b_def, &args) else { continue };
            let Some((_, sk)) = unfold.concl().as_eq() else { continue };
            // Orient the body certificate so that it proves `skeleton = B`.
            let oriented = if u1 == sk && u2 == *target {
                body.clone()
            } else if u2 == sk && u1 == *target {
                match self.ceq_symm(body) {
                    Some(c) => c,
                    None => continue,
                }
            } else {
                continue
            };
            let Some(unfold) = CondEq::plain(unfold) else { continue };
            let Some(at_w) = self.ceq_trans(&unfold, &oriented) else { continue };
            let Some(out) = self.guard_and_generalise(&at_w, w, dom) else { continue };
            return Some(out)
        }
        None
    }

    /// [`retarget`] against this backend's record of term structure.
    fn retarget(&self, cert: &CondEq, want_l: &Term, want_r: &Term) -> Option<CondEq> {
        retarget_cond(&self.parts, cert, want_l, want_r)
    }

    /// One premise of `Π` congruence, as `⊢ l = r` under its assumptions.
    ///
    /// Three ways to get there, in order: the certificate already *is* that
    /// equation; it becomes that equation after [`Self::retarget`]; or the two
    /// sides interpret identically and reflexivity proves it outright. The last
    /// is the only one that survives an admitted certificate, and it is a
    /// complete proof rather than a shortcut.
    fn pi_premise(&mut self, c: Option<&CondEq>, l: &Term, r: &Term) -> Option<CondEq> {
        if let Some(t) = c {
            if t.proves(l, r) {
                return Some(t.clone())
            }
            if let Some(rt) = self.retarget(t, l, r) {
                return Some(rt)
            }
        }
        (l == r).then(|| CondEq::refl(l.clone()))
    }

    /// Discharge a lemma's premises with derivations that may carry assumptions.
    ///
    /// `lemma` is `⊢ p₁ → (p₂ → … → concl)` and each `prem` derives one `pᵢ`
    /// under its own assumptions; the result is the conclusion under the union.
    /// This is `Thm::mp`, once per premise, re-stated under the merged
    /// assumption set — the shape both congruences need.
    fn discharge(&mut self, lemma: &Thm, prems: &[CondEq]) -> Option<CondEq> {
        let mut hyps: Vec<Formula> = Vec::new();
        for p in prems {
            hyps = merge_hyps(&hyps, &p.hyps);
        }
        if hyps.len() > MAX_HYPS {
            return None
        }
        let h = conj_of(&hyps);
        let mut acc = u_a1i(lemma, h.as_ref());
        for p in prems {
            let lifted = reassume(&p.thm, &p.hyps, &hyps)?;
            acc = u_mp(&acc, &lifted, h.as_ref())?;
        }
        CondEq::new(acc, hyps)
    }

    /// `⊢ ⟦Π x:A. b⟧ = ⟦Π x:A'. b'⟧`.
    ///
    /// Three cases, by the head symbols of the two interpretations:
    ///
    /// * both `fs` — congruence, via the derived [`derived::ext::fs_cong`];
    /// * both the *same* `dprod` — congruence over its arguments, which are the
    ///   fibre's abstracted subterms followed by the domain;
    /// * one of each — the **bridge**: the dependent side's fibre is shown
    ///   constant on the domain and [`dprod_const_fibre_n`] identifies it with
    ///   the function space. See [`Self::derive_pi_bridge`].
    fn derive_pi_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        if !matches!((ctx.read_expr(a), ctx.read_expr(b)), (Expr::Pi { .. }, Expr::Pi { .. })) {
            return Err("pi congruence: not applied to two Π types")
        }
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        // Read the two premises' targets straight off the *claim* rather than
        // re-interpreting the two sub-expressions. Those agree today, but this
        // way the premises are by construction about the terms the conclusion
        // will be compared against, so the rule cannot drift from its guard.
        let (Some((fa, aargs)), Some((fb, bargs))) = (self.parts.get(&ta).cloned(), self.parts.get(&tb).cloned())
        else {
            return Err("pi congruence: a Π has no applicative interpretation")
        };
        // Two dependent products: congruence over the shared head symbol when
        // the two bodies have the same shape, and Extensionality otherwise —
        // exactly the split `lam_cong` makes, and for the same reason.
        if self.pi_sites.contains_key(&a) && self.pi_sites.contains_key(&b) {
            if fa == fb {
                if let Ok(t) = self.derive_pi_argwise(fa, &aargs, &bargs, dom, body) {
                    return Ok(t)
                }
            }
            return self.derive_pi_dprod_ext(a, b, dom, body)
        }
        if fa != fb {
            return self.derive_pi_bridge(a, b, fa, &aargs, fb, &bargs, dom, body)
        }
        let fs = self.pre.fs_sym();
        if fa == fs || fa == self.syms.pi {
            // Both binary, and in the same order: domain then codomain (or, for
            // the opaque fallback symbol, the raw body).
            if aargs.len() != 2 || bargs.len() != 2 {
                return Err("pi congruence: a Π interprets to an unexpected arity")
            }
            let (ia, ja) = (aargs[0].clone(), aargs[1].clone());
            let (ib, jb) = (bargs[0].clone(), bargs[1].clone());
            let dom_thm = self.pi_premise(dom, &ia, &ib).ok_or(pi_dom_gap(dom))?;
            let body_thm = self.pi_premise(body, &ja, &jb).ok_or(pi_body_gap(body))?;
            if fa == fs {
                // `fs_cong` is the lemma derived for exactly this case; the
                // opaque fallback symbol has none, and plain congruence over it
                // is all the signature supports.
                let lemma = self.pre.fs_cong.clone();
                let inst = derived::inst_all(&lemma, &[ia, ib, ja, jb])
                    .ok_or("pi congruence: instantiating function-space congruence failed")?;
                return self.discharge(&inst, &[dom_thm, body_thm]).ok_or("pi congruence: discharging a premise failed")
            }
            return self.ceq_congr(fa, &[dom_thm, body_thm]).ok_or("pi congruence: congruence rule refused")
        }
        Err("pi congruence: a Π interprets to an unexpected head symbol")
    }

    /// Congruence over a dependent product's arguments — the abstracted,
    /// binder-free subterms of the body followed by the binder's domain.
    ///
    /// The cheap route when the two `Π` types differ only in those positions: no
    /// Extensionality derivation is needed, and on this corpus the arguments are
    /// usually literally equal, so most positions are reflexivity.
    fn derive_pi_argwise(
        &mut self,
        f: FnSym,
        aargs: &[Term],
        bargs: &[Term],
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        if aargs.len() != bargs.len() || aargs.is_empty() {
            return Err("pi congruence: a Π interprets to an unexpected arity")
        }
        let last = aargs.len() - 1;
        let mut prems = Vec::with_capacity(aargs.len());
        for i in 0..aargs.len() {
            let c = if i == last { dom } else { body };
            let Some(p) = self.pi_premise(c, &aargs[i], &bargs[i]) else {
                return Err(if i == last { pi_dom_gap(dom) } else { pi_body_gap(body) })
            };
            prems.push(p);
        }
        self.ceq_congr(f, &prems).ok_or("pi congruence: congruence rule refused")
    }

    /// `⊢ dprod_C(h⃗,A) = dprod_C'(h⃗',A')`, by dependent-product extensionality.
    ///
    /// The mirror of [`Self::derive_lam_cong`], and for the same reason: the
    /// head symbol of `⟦Π⟧` depends on the *shape* of the fibre, so two `Π`
    /// types with differently-shaped bodies are built by unrelated symbols and
    /// no amount of `congr_arg` relates them. What does is that the two products
    /// have the same members — [`dprod_ext_n`] — whose pointwise premise is read
    /// off the body certificate by the very same [`Self::pointwise_premise`] the
    /// lambda rule uses, the fibre's defining equation playing the part of the
    /// graph body's.
    fn derive_pi_dprod_ext(
        &mut self,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        let (Some(sa), Some(sb)) = (self.pi_sites.get(&a), self.pi_sites.get(&b)) else {
            return Err("pi congruence: a Π has no dependent-product interpretation")
        };
        let (key_a, holes_a, dom_a) = (sa.key.clone(), sa.holes.clone(), sa.dom.clone());
        let (key_b, holes_b, dom_b) = (sb.key.clone(), sb.holes.clone(), sb.dom.clone());
        let (Some(info_a), Some(info_b)) = (self.pi_info(&key_a), self.pi_info(&key_b)) else {
            return Err("pi congruence: the Π's fibre skeleton was not registered")
        };
        let (Some(fa), Some(fb)) = (info_a.fibre.as_ref(), info_b.fibre.as_ref()) else {
            return Err("pi congruence: the Π's fibre was not built")
        };
        let (b_def_a, b_def_b) = (fa.b_def.clone(), fb.b_def.clone());

        let dom_thm = match dom {
            Some(d) if d.proves(&dom_a, &dom_b) => d.clone(),
            _ if dom_a == dom_b => CondEq::refl(dom_a.clone()),
            _ => return Err(pi_dom_gap(dom)),
        };
        let Some(body_thm) = body else { return Err("pi congruence over an admitted body premise") };
        let Some((pointwise, rest)) =
            self.pointwise_premise(&b_def_a, &b_def_b, &holes_a, &holes_b, &dom_a, body_thm)
        else {
            return Err("pi congruence: the body certificate is not the fibres' pointwise equation")
        };

        let Some(ext) = self.pi_ext_thm(&key_a, &key_b) else {
            return Err("pi congruence: dependent-product extensionality could not be derived")
        };
        let mut args = holes_a;
        args.extend(holes_b);
        args.push(dom_a);
        args.push(dom_b);
        let Some(inst) = derived::inst_all(&ext, &args) else {
            return Err("pi congruence: instantiating dependent-product extensionality failed")
        };

        // Both premises under the union of their assumptions; `pointwise` is not
        // an equation, so `Self::discharge` does not apply and the two `mp`s are
        // done by hand, exactly as in `derive_lam_cong`.
        let hyps = merge_hyps(&dom_thm.hyps, &rest);
        if hyps.len() > MAX_HYPS {
            return Err("pi congruence: too many undischarged assumptions")
        }
        let h = conj_of(&hyps);
        let lemma = u_a1i(&inst, h.as_ref());
        let Some(dom_lifted) = reassume(&dom_thm.thm, &dom_thm.hyps, &hyps) else {
            return Err("pi congruence: re-stating the domain premise failed")
        };
        let Some(after_dom) = u_mp(&lemma, &dom_lifted, h.as_ref()) else {
            return Err("pi congruence: discharging the domain premise failed")
        };
        let Some(pw_lifted) = reassume(&pointwise, &rest, &hyps) else {
            return Err("pi congruence: re-stating the pointwise premise failed")
        };
        let Some(out) = u_mp(&after_dom, &pw_lifted, h.as_ref()) else {
            return Err("pi congruence: discharging the pointwise premise failed")
        };
        CondEq::new(out, hyps).ok_or("pi congruence: the result is not the assumed equation")
    }

    /// `⊢ fs(A,B) = dprod_C(h⃗,A')`, or its mirror — the two encodings of `Π`
    /// bridged.
    ///
    /// `⟦Π x:A. B⟧` is the function space when the body does not mention the
    /// binder and the dependent product when it does, so two `Π` types the
    /// checker calls equal can interpret with unrelated head symbols. Congruence
    /// relates nothing here; what does is
    /// `⊢ ∀A ∀B. ((∀x. (x ∈ A → b(h⃗,x) = B)) → dprod(h⃗,A) = fs(A,B))`, whose
    /// hypothesis says the fibre is *constant* on the domain — which is exactly
    /// what the body certificate says, since the other side's body does not
    /// mention the binder at all.
    ///
    /// Three steps: the fibre premise ([`Self::fibre_premise`]) discharges the
    /// bridge at the dependent side's own domain, giving
    /// `dprod(h⃗,A') = fs(A',B)`; `fs_cong` and the domain premise move `fs(A',B)`
    /// to `fs(A,B)`; and the two are chained. Nothing is assumed about which
    /// side is which — the result is compared against the claim by the caller.
    #[allow(clippy::too_many_arguments)]
    fn derive_pi_bridge(
        &mut self,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        fa: FnSym,
        aargs: &[Term],
        fb: FnSym,
        bargs: &[Term],
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        let fs = self.pre.fs_sym();
        // Which side is the function space, and which the dependent product?
        // `flip` records that the *claim* is `dprod … = fs …`, so the derivation
        // below — which always builds `fs … = dprod …` — has to be turned round.
        let (dep_e, fs_args, flip) = if fa == fs && self.pi_sites.contains_key(&b) {
            (b, aargs, false)
        } else if fb == fs && self.pi_sites.contains_key(&a) {
            (a, bargs, true)
        } else if self.pi_sites.contains_key(&a) && self.pi_sites.contains_key(&b) {
            // Two dependent products over *different* fibre skeletons. Relating
            // them is dependent-product extensionality — `derived::ext::dprod_ext`
            // in the parameter-threading form, which is not built here.
            return Err("pi congruence: two Π bodies have unrelated fibre skeletons")
        } else {
            return Err("pi congruence: dependent and non-dependent Π interpret differently")
        };
        if fs_args.len() != 2 {
            return Err("pi congruence: a Π interprets to an unexpected arity")
        }
        let (fs_dom, fs_cod) = (fs_args[0].clone(), fs_args[1].clone());

        let site = self.pi_sites.get(&dep_e).expect("checked just above");
        let (key, holes, dep_dom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        let Some(info) = self.pi_info(&key) else {
            return Err("pi congruence: the Π's fibre skeleton was not registered")
        };
        let Some(b_def) = info.fibre.as_ref().map(|f| f.b_def.clone()) else {
            return Err("pi congruence: the Π's fibre was not built")
        };

        // The domain premise, always oriented as `fs`'s domain = the dependent
        // product's domain.
        let (dl, dr) = if flip { (dep_dom.clone(), fs_dom.clone()) } else { (fs_dom.clone(), dep_dom.clone()) };
        let Some(dom_thm) = self.pi_premise(dom, &dl, &dr) else { return Err(pi_dom_gap(dom)) };
        let dom_thm = if flip {
            self.ceq_symm(&dom_thm).ok_or("pi congruence: re-orienting the domain premise failed")?
        } else {
            dom_thm
        };

        // The constant-fibre premise, and the bridge it discharges.
        let Some(body) = body else { return Err("pi congruence over an admitted body premise") };
        let Some((fibre, rest)) = self.fibre_premise(&b_def, &holes, &dep_dom, &fs_cod, body) else {
            return Err("pi congruence: the body certificate does not make the fibre constant")
        };
        let Some(bridge) = self.pi_bridge_thm(&key) else {
            return Err("pi congruence: the constant-fibre bridge could not be derived")
        };
        let mut args = holes;
        args.push(dep_dom.clone());
        args.push(fs_cod.clone());
        let Some(inst) = derived::inst_all(&bridge, &args) else {
            return Err("pi congruence: instantiating the constant-fibre bridge failed")
        };
        // `⊢ conj(rest) → dprod(h⃗,A') = fs(A',B)`, then turned round.
        let h = conj_of(&rest);
        let lemma = u_a1i(&inst, h.as_ref());
        let Some(bridged) = u_mp(&lemma, &fibre, h.as_ref()) else {
            return Err("pi congruence: discharging the fibre premise failed")
        };
        let Some(bridged) = CondEq::new(bridged, rest) else {
            return Err("pi congruence: the bridge is not the assumed equation")
        };
        let Some(bridged) = self.ceq_symm(&bridged) else {
            return Err("pi congruence: re-orienting the bridge failed")
        };

        // `fs(A,B) = fs(A',B)` from the domain premise, then chained on.
        let lemma = self.pre.fs_cong.clone();
        let inst = derived::inst_all(&lemma, &[fs_dom, dep_dom, fs_cod.clone(), fs_cod.clone()])
            .ok_or("pi congruence: instantiating function-space congruence failed")?;
        let cod_refl = CondEq::refl(fs_cod);
        let Some(retarget) = self.discharge(&inst, &[dom_thm, cod_refl]) else {
            return Err("pi congruence: discharging the domain premise failed")
        };
        let Some(out) = self.ceq_trans(&retarget, &bridged) else {
            return Err("pi congruence: chaining the bridge failed")
        };
        if flip {
            return self.ceq_symm(&out).ok_or("pi congruence: re-orienting the result failed")
        }
        Ok(out)
    }

    /// `⊢ ⟦λx:A. b⟧ = ⟦λx:A'. b'⟧`, by graph extensionality.
    fn derive_lam_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        // Interpreting the two lambdas is what registers their graph symbols.
        let _ = self.interp(ctx, a);
        let _ = self.interp(ctx, b);
        let (Some(sa), Some(sb)) = (self.lam_sites.get(&a), self.lam_sites.get(&b)) else {
            return Err("lam congruence: a lambda has no function-graph interpretation")
        };
        let (key_a, holes_a, dom_a) = (sa.key.clone(), sa.holes.clone(), sa.dom.clone());
        let (key_b, holes_b, dom_b) = (sb.key.clone(), sb.holes.clone(), sb.dom.clone());

        let Some(info_a) = self.lam_info(&key_a) else {
            return Err("lam congruence: the lambda's skeleton was not registered")
        };
        let Some(info_b) = self.lam_info(&key_b) else {
            return Err("lam congruence: the lambda's skeleton was not registered")
        };
        let (Some(ga), Some(gb)) = (info_a.graph.as_ref(), info_b.graph.as_ref()) else {
            return Err("lam congruence: the lambda's graph was not built")
        };
        let (t_def_a, t_def_b) = (ga.t_def.clone(), gb.t_def.clone());

        // The domain premise. The certificate the checker handed down is the
        // right one when it proves the two binder types equal; when the types
        // interpret identically, reflexivity does the job instead — which is
        // the only way a gapped domain certificate can still be rescued.
        let dom_thm = match dom {
            Some(d) if d.proves(&dom_a, &dom_b) => d.clone(),
            _ if dom_a == dom_b => CondEq::refl(dom_a.clone()),
            _ => return Err("lam congruence: the domain certificate does not match the binder types"),
        };

        let Some(body_thm) = body else {
            return Err("lam congruence over an admitted premise")
        };
        let Some((pointwise, rest)) =
            self.pointwise_premise(&t_def_a, &t_def_b, &holes_a, &holes_b, &dom_a, body_thm)
        else {
            return Err("lam congruence: the body certificate is not the graphs' pointwise equation")
        };
        // `pointwise` is `⊢ conj(rest) → ∀x. …`, whose consequent is not an
        // equation — so it cannot be a `CondEq`, and `Self::discharge` (which
        // returns one) does not apply. The two premises are discharged by hand
        // below with the same `reassume`/`u_mp` moves.

        let Some(ext) = self.lam_ext_thm(&key_a, &key_b) else {
            return Err("lam congruence: graph extensionality could not be derived")
        };
        let mut args = holes_a;
        args.extend(holes_b);
        args.push(dom_a);
        args.push(dom_b);
        let Some(inst) = derived::inst_all(&ext, &args) else {
            return Err("lam congruence: instantiating graph extensionality failed")
        };

        // Both premises are discharged under the union of their assumptions:
        // the domain equation's, and whatever the pointwise premise could not
        // shed at the binder.
        let hyps = merge_hyps(&dom_thm.hyps, &rest);
        if hyps.len() > MAX_HYPS {
            return Err("lam congruence: too many undischarged assumptions")
        }
        let h = conj_of(&hyps);
        let lemma = u_a1i(&inst, h.as_ref());
        let Some(dom_lifted) = reassume(&dom_thm.thm, &dom_thm.hyps, &hyps) else {
            return Err("lam congruence: re-stating the domain premise failed")
        };
        let Some(after_dom) = u_mp(&lemma, &dom_lifted, h.as_ref()) else {
            return Err("lam congruence: discharging the domain premise failed")
        };
        let Some(pw_lifted) = reassume(&pointwise, &rest, &hyps) else {
            return Err("lam congruence: re-stating the pointwise premise failed")
        };
        // This is the step that would fail if the generalisation above had
        // captured a parameter: the premise would not be the lemma's.
        let Some(out) = u_mp(&after_dom, &pw_lifted, h.as_ref()) else {
            return Err("lam congruence: discharging the pointwise premise failed")
        };
        CondEq::new(out, hyps).ok_or("lam congruence: the result is not the assumed equation")
    }
}

/// Why a `Π` congruence could not use its domain premise: the certificate below
/// was itself a gap, or it was about the wrong terms. Naming the two apart is
/// what makes the coverage report say which is missing.
fn pi_dom_gap(c: Option<&CondEq>) -> &'static str {
    if c.is_none() {
        "pi congruence over an admitted domain premise"
    } else {
        "pi congruence: the domain certificate is not about the binder types"
    }
}

/// [`pi_dom_gap`] for the body premise.
fn pi_body_gap(c: Option<&CondEq>) -> &'static str {
    if c.is_none() {
        "pi congruence over an admitted body premise"
    } else {
        "pi congruence: the body certificate is not about the binder bodies"
    }
}

/// The applicative structure of the terms a match may take apart: the shape
/// [`TgBackend::parts`] records on the way in.
type Parts = HashMap<Term, (FnSym, Vec<Term>)>;

/// Match `have` against `want`, reading off which free variables of `have` have
/// to become which subterms of `want`.
///
/// A pure syntactic first-order match, one-sided: only `have`'s free variables
/// are treated as holes, and a variable bound twice to different terms fails.
/// Interior nodes are compared through `parts`, so a term the backend did not
/// build stops the match rather than being taken apart by guesswork.
fn match_term(parts: &Parts, have: &Term, want: &Term, subst: &mut Vec<(FreeVar, Term)>) -> Option<()> {
    if have == want {
        return Some(())
    }
    if let Some((f, hargs)) = parts.get(have) {
        let (g, wargs) = parts.get(want)?;
        if f != g || hargs.len() != wargs.len() {
            return None
        }
        for (h, w) in hargs.iter().zip(wargs.iter()) {
            match_term(parts, h, w, subst)?;
        }
        return Some(())
    }
    // Not an application the backend built, so the only thing it can be and
    // still match is a free variable standing for a whole subterm.
    let mut fvs = Vec::new();
    have.free_vars(&mut fvs);
    if fvs.len() != 1 || *have != Term::var(fvs[0]) {
        return None
    }
    let v = fvs[0];
    match subst.iter().find(|(u, _)| *u == v) {
        Some((_, t)) => (t == want).then_some(()),
        None => {
            subst.push((v, want.clone()));
            Some(())
        }
    }
}

/// Re-aim a certificate from the *opened* form of a binder body at the raw
/// de Bruijn form that `⟦Π⟧` is built over.
///
/// The checker compares binder bodies after instantiating them at locals, so
/// the certificate it hands `pi_cong` is about `⟦B[l⃗]⟧`, with `l⃗` kernel free
/// variables — whereas `⟦Π x:A. B⟧` is `sym(⟦A⟧, ⟦B⟧)` over the *raw* body, in
/// which those positions are `bvar` symbols instead. The two are related by
/// exactly the rule a free variable admits: generalise it, then instantiate at
/// the term wanted in its place. `Thm::gen` needs no side condition here — a
/// `Thm` carries no hypotheses — and `ax_inst` is the kernel's own
/// instantiation, so the result is a genuine theorem about the wanted terms.
///
/// Which term goes in which variable's place is *read off* by matching the
/// certificate against the wanted equation rather than guessed, and the outcome
/// is compared against that equation before it is returned. So the worst a
/// mismatch can do — a shifted de Bruijn index under a nested `Π`, a body the
/// backend did not build, one local that would have to become two different
/// terms — is produce `None`, hence a reported gap.
///
/// A certificate that carries assumptions is re-aimed the same way, except that
/// generalising and re-instantiating rewrites the *assumptions* too — so they
/// are substituted alongside, and `CondEq::new` re-checks that the rewritten
/// list really is the rewritten theorem's antecedent.
fn retarget_cond(parts: &Parts, cert: &CondEq, want_l: &Term, want_r: &Term) -> Option<CondEq> {
    let (have_l, have_r) = cert.as_eq()?;
    let mut subst: Vec<(FreeVar, Term)> = Vec::new();
    match_term(parts, &have_l, want_l, &mut subst)?;
    match_term(parts, &have_r, want_r, &mut subst)?;
    if subst.is_empty() {
        // Nothing to re-aim, and the caller has already compared the
        // certificate verbatim; going on would only re-derive what it has.
        return None
    }
    let mut cur = cert.thm.clone();
    let mut hyps = cert.hyps.clone();
    for (v, t) in subst {
        cur = derived::inst_all(&Thm::gen(v, &cur), std::slice::from_ref(&t))?;
        hyps = hyps.iter().map(|f| f.subst(v, &t)).collect();
    }
    // The guard. Nothing above is trusted to have produced the right equation,
    // and `CondEq::new` re-checks that the assumptions really are the theorem's
    // antecedent after the rewrite.
    let out = CondEq::new(cur, hyps)?;
    out.proves(want_l, want_r).then_some(out)
}

/// [`retarget_cond`] for a certificate that assumes nothing.
#[cfg(test)]
fn retarget(parts: &Parts, cert: &Thm, want_l: &Term, want_r: &Term) -> Option<Thm> {
    let c = CondEq::plain(cert.clone())?;
    Some(retarget_cond(parts, &c, want_l, want_r)?.thm)
}

/// The `locals` key for a Lean free variable expression.
fn local_key<'t, 'p>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Option<u64> {
    match ctx.read_expr(e) {
        Expr::Local { id: crate::expr::FVarId::DbjLevel(n), .. } => Some(n as u64),
        Expr::Local { id: crate::expr::FVarId::Unique(n), .. } => Some((n as u64) | (1 << 32)),
        _ => None,
    }
}

impl<'x, 't: 'x, 'p: 't> Certifier for TgBackend<'x, 't, 'p> {
    type Term = ExprPtr<'t>;
    type Cert = TgCert;
    type Ctx = TcCtx<'t, 'p>;

    fn refl(&mut self, ctx: &mut Self::Ctx, a: Self::Term) -> TgCert {
        let t = self.interp(ctx, a);
        self.proved(Thm::eq_refl(t))
    }

    /// Symmetry, **guarded**.
    ///
    /// Turning an equation around is the least a rule can do, and it was still
    /// unchecked: the certificate handed in need not be about `b ≡ a` at all,
    /// and reversing whatever it *is* about produced a `Proved` for a claim the
    /// rule had never looked at. Now the reversed equation is matched against
    /// `⟦a⟧ = ⟦b⟧` — through [`CondEq::proves`], which reads the equation out
    /// from under the assumption list, so a conditional premise is checked on
    /// the same terms as an unconditional one — and anything else is a gap.
    fn symm(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, c: TgCert) -> TgCert {
        let cc = self.consume(&c);
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match cc {
            Some(t) => match self.ceq_symm(&t) {
                Some(t) if t.proves(&ta, &tb) => return self.cert(t),
                Some(_) => {
                    note_unmatched(Rule::Symm);
                    "symm: derived equation does not match the claim"
                }
                None => "symm refused",
            },
            None => "symm over an admitted premise",
        };
        // Both sides interpret identically: reflexivity proves the claim
        // outright, needing no premise. Same fallback, and same justification,
        // as in `lam_cong`/`pi_cong`.
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Transitivity, **guarded**.
    ///
    /// `ceq_trans` already refuses two premises that do not meet in the middle,
    /// but agreeing on a midpoint says nothing about the *endpoints*: two
    /// certificates about an unrelated pair compose perfectly well, and the
    /// composite was then returned as a proof of whatever the checker happened
    /// to be claiming. `a` and `b` are that claim, and the composite is matched
    /// against `⟦a⟧ = ⟦b⟧` before it counts.
    fn trans(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, ab: TgCert, bc: TgCert) -> TgCert {
        // Both are taken before either is inspected: a premise the rule cannot
        // use is still a premise the rule has *received*, and the escape ledger
        // counts receipt.
        let (x, y) = (self.consume(&ab), self.consume(&bc));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match (x, y) {
            (Some(x), Some(y)) => match self.ceq_trans(&x, &y) {
                Some(t) if t.proves(&ta, &tb) => return self.cert(t),
                Some(_) => {
                    note_unmatched(Rule::Trans);
                    "trans: derived equation does not match the claim"
                }
                None => "trans refused",
            },
            _ => "trans over an admitted premise",
        };
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Congruence for application, **guarded**.
    ///
    /// `⟦f x⟧` is `app(⟦f⟧, ⟦x⟧)`, so this is ordinary congruence over the
    /// interpretation's application symbol — and precisely because it is so
    /// ordinary it was the one place a wrong certificate could travel furthest.
    /// Handed only two sub-certificates, the rule could not tell whether they
    /// were about the function and argument of the application it was supposed
    /// to be proving something about; it built `app(l₁,l₂) = app(r₁,r₂)` from
    /// whatever it was given and returned that as a proof of the claim. A
    /// certificate assembled that way is about a term the checker never asked
    /// about, and it then arrived at a binder where `pi_cong` — which does check
    /// — could only report a gap several levels away from the rule that made it.
    ///
    /// Now `a` and `b` are the two applications, so the congruence is matched
    /// against `⟦a⟧ = ⟦b⟧` and a mismatch is named where it happens. That
    /// happens 9 times over the tutorial corpus (in 7 files) and twice on
    /// `init-prelude`, and the nine are the same nine `pi_cong` was previously
    /// reporting as `the body certificate is not the fibres' pointwise
    /// equation`, which drops from 12 to 3. It was *not* the cause of the 621
    /// bridge failures, as the module docs used to claim; those are unchanged.
    fn app_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, f: TgCert, arg: TgCert) -> TgCert {
        let s = self.pre.ap.app;
        let (cf, cx) = (self.consume(&f), self.consume(&arg));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match (cf, cx) {
            (Some(x), Some(y)) => match self.ceq_congr(s, &[x, y]) {
                Some(t) if t.proves(&ta, &tb) => return self.cert(t),
                Some(_) => {
                    note_unmatched(Rule::AppCong);
                    "congruence: derived equation does not match the claim"
                }
                None => "congruence rule refused",
            },
            // A gap anywhere below means the whole congruence is a gap; there is
            // nothing to prove congruence *from*.
            _ => "congruence over an admitted premise",
        };
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Congruence for `λ`, by **graph extensionality**, and guarded.
    ///
    /// `⟦λx:A. b⟧` is a function *graph* `lam_C(s⃗, ⟦A⟧)` whose head symbol
    /// depends on the shape of the body, so this is not congruence over
    /// sub-terms: from `⊢ ⟦A⟧ = ⟦A'⟧` and `⊢ ⟦b⟧ = ⟦b'⟧` one has to conclude
    /// `⊢ lam_C(s⃗,⟦A⟧) = lam_C'(s⃗',⟦A'⟧)` for two *different* symbols. Two
    /// graphs are equal because they have the same members, which is
    /// Extensionality — [`derived::ext::lam_ext`], here in the
    /// parameter-threading form [`lam_ext_n`] the skeleton decomposition needs.
    ///
    /// Its second premise is *pointwise*, `∀x. (x ∈ A → t(x) = t'(x))`, whereas
    /// the certificate this rule is handed compares the bodies at one fixed
    /// local. [`Self::pointwise_premise`] closes that gap: the local is a kernel
    /// free variable, `Thm::gen` abstracts it with no side condition (a `Thm`
    /// carries no hypotheses), and the `x ∈ A` guard is pure weakening. What it
    /// must establish — and does, by unfolding both body definitions and
    /// comparing terms — is that the certificate really is about the graphs'
    /// body symbols at that variable.
    ///
    /// Whatever comes out is checked against `⟦a⟧ = ⟦b⟧` before it counts as a
    /// proof, so every way this can go wrong is a gap rather than a false
    /// theorem.
    ///
    /// # Binder chains
    ///
    /// A binder *chain* is folded up innermost-first, and this used to be where
    /// the rule stopped: `def_eq_binder_aux` handed each frame its lambda in
    /// **un-instantiated** form, so an inner frame's lambda still carried loose
    /// de Bruijn indices for the enclosing binders — interpreted as opaque
    /// `bvar` symbols — while the certificate beneath it was about bodies opened
    /// at real locals. `pointwise_premise` could then never match, and the outer
    /// frame was in turn handed an equation between those un-instantiated inner
    /// lambdas. On a chain of length two or more, nothing derivable here bridged
    /// that.
    ///
    /// `def_eq_binder_aux` now instantiates each `λ` frame at the locals
    /// introduced above it, so the frame's terms *are* the ones its premises
    /// talk about, and the derivation applies at every depth. (`Π` frames are
    /// deliberately left alone: `⟦Π⟧` is built over the raw de Bruijn body, so
    /// `pi_cong` wants the opposite form. See the comment there.)
    ///
    /// The degenerate case remains as a fallback: if the two lambdas interpret
    /// to the *same* graph, reflexivity proves the claim outright, with no
    /// premise needed. That is a complete proof, not a shortcut — and it is
    /// still what closes the chains the derivation cannot reach.
    fn lam_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, dom: TgCert, body: TgCert) -> TgCert {
        let (cd, cb) = (self.consume(&dom), self.consume(&body));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match self.derive_lam_cong(ctx, a, b, cd.as_ref(), cb.as_ref()) {
            Ok(t) if t.proves(&ta, &tb) => return self.cert(t),
            Ok(_) => "lam congruence: derived equation does not match the claim",
            Err(reason) => reason,
        };
        // Both lambdas interpret to the same graph: reflexivity is the claim.
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Congruence for `Π`, **guarded**.
    ///
    /// `⟦Π x:A. B⟧` is `fs(⟦A⟧,⟦B⟧)` when the body ignores the binder and the
    /// dependent product `dprod_C(s⃗,⟦A⟧)` when it does not, so the two sides of
    /// a claim can be built by unrelated symbols. [`Self::derive_pi_cong`] picks
    /// among the three routes — congruence, dependent-product Extensionality,
    /// and the constant-fibre bridge — and the module docs record what each one
    /// buys.
    ///
    /// Getting the premises into the form the claim needs is
    /// [`TgBackend::retarget`]'s job wherever the certificate is stated at a
    /// different local from the one the claim is about; the substitution is read
    /// off by matching rather than assumed.
    ///
    /// Everything is checked against `⟦a⟧ = ⟦b⟧` before it counts as a proof, so
    /// every way this can go wrong is a gap rather than a false theorem.
    ///
    /// The reflexivity fallback covers the case where both sides interpret
    /// identically — a complete proof of the claim, needing no premise at all,
    /// and on this corpus by far the commonest way a `Π` congruence is settled.
    fn pi_cong(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term, dom: TgCert, body: TgCert) -> TgCert {
        let (cd, cb) = (self.consume(&dom), self.consume(&body));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match self.derive_pi_cong(ctx, a, b, cd.as_ref(), cb.as_ref()) {
            Ok(t) if t.proves(&ta, &tb) => return self.cert(t),
            Ok(_) => "pi congruence: derived equation does not match the claim",
            Err(reason) => reason,
        };
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    fn beta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> TgCert {
        match self.derive_beta(ctx, redex, reduct) {
            Ok(t) => self.cert(t),
            Err(reason) => self.note_admit(reason),
        }
    }

    /// Zeta: `let x := v; b ≡ b[v/x]`.
    ///
    /// Discharged by the `Let`'s defining equation, guarded against the claim in
    /// the same way as `delta` and `beta`.
    fn zeta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> TgCert {
        let Some(eq) = self.let_defs.get(&redex).cloned() else {
            let _ = self.interp(ctx, redex);
            match self.let_defs.get(&redex).cloned() {
                Some(eq) => return self.check_against(ctx, eq, redex, reduct, "zeta"),
                None => return self.note_admit("zeta: the let has no defining equation"),
            }
        };
        self.check_against(ctx, eq, redex, reduct, "zeta")
    }

    fn delta(&mut self, ctx: &mut Self::Ctx, redex: Self::Term, reduct: Self::Term) -> TgCert {
        // `redex` is `c a₁ … aₙ` and `reduct` is `value a₁ … aₙ`. Interpreting
        // the head constant registers its defining equation `⊢ ⟦c⟧ = ⟦value⟧`;
        // folding `app_cong` over the argument spine lifts that to the whole
        // application.
        let (fun, args) = ctx.unfold_apps(redex);
        let _ = self.interp(ctx, fun);
        let Some(head) = self.const_defs.get(&fun).cloned() else {
            return self.note_admit("delta: head constant has no defining equation")
        };
        let mut acc = head;
        for a in args {
            let ta = self.interp(ctx, a);
            let refl = Thm::eq_refl(ta);
            let app = self.pre.ap.app;
            let stepped = derived::congr(&mut self.env_mut(), app, &[acc, refl]);
            match stepped {
                Some(t) => acc = t,
                None => return self.note_admit("delta: congruence over the spine refused"),
            }
        }
        // Guard: the derived equation must really be about the two terms the
        // checker claims are equal. If the interpretation and the reduction have
        // drifted apart, that is a bug — report it rather than pass it off.
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if *acc.concl() != kernel::Formula::eq(lhs, rhs) {
            return self.note_admit("delta: derived equation does not match the reduction")
        }
        self.proved(acc)
    }

    fn eta(&mut self, _ctx: &mut Self::Ctx, _a: Self::Term, _b: Self::Term) -> TgCert {
        self.note_admit("eta (needs a function-extensionality lemma)")
    }

    fn sort(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term) -> TgCert {
        // The checker only calls this when the two levels are equal under its
        // own level algebra. When that makes the interpretations syntactically
        // identical, reflexivity settles it outright. When it does not — say
        // `max u v` versus `max v u` — proving it needs level axioms the
        // signature does not have, so it is recorded as a gap rather than waved
        // through.
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            self.proved(Thm::eq_refl(ta))
        } else {
            self.note_admit("sort equality modulo level algebra")
        }
    }

    fn const_eq(&mut self, ctx: &mut Self::Ctx, a: Self::Term, b: Self::Term) -> TgCert {
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            self.proved(Thm::eq_refl(ta))
        } else {
            self.note_admit("constant equality modulo level algebra")
        }
    }

    fn admit(&mut self, _ctx: &mut Self::Ctx, _a: Self::Term, _b: Self::Term, reason: &'static str) -> TgCert {
        self.note_admit(reason)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Reporting.
//
// A `TgBackend` is created per `TypeChecker`, i.e. per declaration, and dropped
// with it, so the per-run totals have to be accumulated somewhere shared. This
// is a report on the checker's own completeness, not part of any derivation.
// ─────────────────────────────────────────────────────────────────────────────

use std::sync::Mutex;

static TOTALS: Mutex<Option<Vec<(&'static str, u64)>>> = Mutex::new(None);
static PROVED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

// ── The guard ledger ─────────────────────────────────────────────────────────
//
// `app_cong`, `trans` and `symm` used to return whatever their premises composed
// to, without ever comparing it against the equation the checker claimed. They
// now do compare, and this counts how often that comparison *fails* — which is
// the number that says how much used to be waved through.
//
// It is deliberately not a gap row. A rule whose derivation misses the claim
// usually still reports a gap and is counted there, but not always: when both
// sides interpret to the same term, reflexivity proves the claim outright and
// there is nothing to report. So the totals below and the gap rows measure two
// different things, and folding them together would misstate both.

/// The three rules this ledger covers.
#[derive(Clone, Copy)]
enum Rule {
    AppCong,
    Trans,
    Symm,
}

static UNMATCHED: [std::sync::atomic::AtomicU64; 3] =
    [const { std::sync::atomic::AtomicU64::new(0) }; 3];

/// Record one derivation that did not match the claim it was built for.
fn note_unmatched(r: Rule) { UNMATCHED[r as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

// ── The escape ledger ────────────────────────────────────────────────────────
//
// A conditional certificate is a complete derivation of an *implication*, while
// the checker's claim is the bare equation. So carrying one is only honest for
// as long as it stays inside the derivation: the moment a copy is used as an
// answer, an assumption has been taken on trust, and it has to be reported.
//
// The backend cannot see where the checker stops recursing, so the accounting is
// done the other way round, by copies:
//
//   * every conditional certificate *created* — by a rule, or by `Clone`, since
//     a copy is a second certificate that must also be accounted for —
//     increments `CONDITIONAL`;
//   * every conditional certificate *handed back to a rule* increments
//     `CONSUMED`, because the rule has then either folded the assumption into
//     its own result (which is counted in turn), proved the claim without it, or
//     reported a gap instead.
//
// The difference is exactly the number of copies that no rule ever received —
// the ones the checker consumed as a verdict, plus any left in its caches. Those
// are the escapes, and they are reported as gaps. `TgBackend::consume` is the
// single funnel for the second counter, and every `Certifier` method that takes
// a certificate calls it on every argument, whatever it then does.
//
// The direction of the residual error matters and is stated plainly: a copy
// abandoned in a cache is counted as an escape although nothing was concluded
// from it, so this **over**-reports. It cannot under-report, because a copy that
// was never handed to a rule cannot have had its assumption discharged.

/// Conditional certificates brought into existence, copies included.
static CONDITIONAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// How many of those were copies. A copy the checker parked in a cache and never
/// used again is the one thing this ledger over-reports, so the number is kept
/// visible: it bounds the over-report.
static CONDITIONAL_COPIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Conditional certificates handed back to a rule, which accounts for them.
static CONSUMED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// The largest assumption set any one certificate carried.
static MAX_ASSUMED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The gap reported for a certificate that reached a boundary still assuming
/// something. There is exactly one place an assumption is introduced —
/// [`TgBackend::beta_step`], when `domain_premise` cannot show the argument
/// lies in the binder's domain — so this names the assumption it names.
const ESCAPED: &str = "undischarged assumption ⟦arg⟧ ∈ ⟦binder domain⟧ survived to the boundary";

/// Record one conditional certificate coming into existence.
pub fn note_conditional() { CONDITIONAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record one conditional certificate being handed back to a rule.
fn note_consumed() { CONSUMED.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// How many certificates finished conditional. Zero is the only value that lets
/// a file be called fully derived.
pub fn escaped() -> u64 {
    use std::sync::atomic::Ordering::Relaxed;
    CONDITIONAL.load(Relaxed).saturating_sub(CONSUMED.load(Relaxed))
}

/// Record one fully-derived certificate.
pub fn note_proved() { PROVED.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record one step taken on trust.
pub fn merge_one(reason: &'static str) {
    let mut g = TOTALS.lock().expect("tg totals poisoned");
    let v = g.get_or_insert_with(Vec::new);
    match v.iter_mut().find(|(r, _)| *r == reason) {
        Some((_, m)) => *m += 1,
        None => v.push((reason, 1)),
    }
}

// ── The typing ledger ────────────────────────────────────────────────────────
//
// `has_type` is a family of clauses, one per Lean typing rule, and the useful
// question about it is not "how often does it work" but *which rule carries the
// work* — and, for the obligations it cannot discharge, what shape of argument
// they are about. Both halves are counted, because the second is the list of
// what the interpretation still lacks, in the order it would pay to fix.

/// The clause that discharged a typing obligation.
#[derive(Clone, Copy)]
enum HtClause {
    /// `⊢ ∀x. x ∈ U(x)`, which is also the `Sort` rule.
    MemU,
    /// `⊢ ∀a. fs(a,a) ∈ U(a)`.
    FsDiag,
    /// Along a constant's defining equation, from its value's typing.
    Const,
    /// A function's values lie in its codomain (`fs`).
    AppFs,
    /// The dependent product's characteristic property.
    AppDProd,
}

const N_HT_CLAUSES: usize = 5;

impl HtClause {
    const fn name(self) -> &'static str {
        match self {
            HtClause::MemU => "x ∈ U(x)  (Sort, and any U-shaped domain)",
            HtClause::FsDiag => "fs(a,a) ∈ U(a)",
            HtClause::Const => "Const: along the defining equation",
            HtClause::AppFs => "App: a function's values lie in its codomain",
            HtClause::AppDProd => "App: the dependent product's sections",
        }
    }
    const ALL: [HtClause; N_HT_CLAUSES] =
        [HtClause::MemU, HtClause::FsDiag, HtClause::Const, HtClause::AppFs, HtClause::AppDProd];
}

/// The shape of an argument whose typing obligation could not be discharged.
#[derive(Clone, Copy)]
enum HtMiss {
    Local,
    ConstOpaque,
    ConstDef,
    Lam,
    Pi,
    AppOpaqueHead,
    AppDefHead,
    AppLamHead,
    AppLocalHead,
    AppOther,
    Other,
}

const N_HT_MISSES: usize = 11;

impl HtMiss {
    const fn name(self) -> &'static str {
        match self {
            HtMiss::Local => "a local — carried as an assumption, by design",
            HtMiss::ConstOpaque => "an opaque constant — no axioms, so nothing is derivable",
            HtMiss::ConstDef => "a defined constant whose value is not typeable",
            HtMiss::Lam => "a lambda — needs lam_in_dprod",
            HtMiss::Pi => "a Π — needs dprod_in_universe",
            HtMiss::AppOpaqueHead => "an application of an opaque constant",
            HtMiss::AppDefHead => "an application of a defined constant",
            HtMiss::AppLamHead => "an application of a lambda — needs lam_in_dprod",
            HtMiss::AppLocalHead => "an application of a local",
            HtMiss::AppOther => "an application of something else",
            HtMiss::Other => "a let, projection or literal",
        }
    }
    const ALL: [HtMiss; N_HT_MISSES] = [
        HtMiss::Local,
        HtMiss::ConstOpaque,
        HtMiss::ConstDef,
        HtMiss::Lam,
        HtMiss::Pi,
        HtMiss::AppOpaqueHead,
        HtMiss::AppDefHead,
        HtMiss::AppLamHead,
        HtMiss::AppLocalHead,
        HtMiss::AppOther,
        HtMiss::Other,
    ];
}

static HT_CLAUSES: [std::sync::atomic::AtomicU64; N_HT_CLAUSES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_CLAUSES];
static HT_MISSES: [std::sync::atomic::AtomicU64; N_HT_MISSES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_MISSES];
/// Obligations asked of `has_type` by `beta_step`, and how many it settled.
static HT_ASKED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static HT_SETTLED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Record one clause discharging an obligation. Counts *every* use, memo
/// replays and the recursive ones inside a larger derivation included, which is
/// what says which typing rule is carrying the work.
fn note_ht(c: HtClause) { HT_CLAUSES[c as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record one top-level obligation and whether it was settled.
fn note_ht_call(ok: bool) {
    use std::sync::atomic::Ordering::Relaxed;
    HT_ASKED.fetch_add(1, Relaxed);
    if ok {
        HT_SETTLED.fetch_add(1, Relaxed);
    }
}

/// Record the shape of one obligation that was not settled.
fn note_ht_miss(m: HtMiss) { HT_MISSES[m as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// The typing ledger, or the empty string if `has_type` was never asked.
fn ht_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let (asked, settled) = (HT_ASKED.load(Relaxed), HT_SETTLED.load(Relaxed));
    if asked == 0 {
        return String::new()
    }
    let width = HtClause::ALL
        .iter()
        .map(|c| c.name().len())
        .chain(HtMiss::ALL.iter().map(|m| m.name().len()))
        .max()
        .unwrap_or(24)
        + 6;
    let mut s = format!(
        "  typing obligations (⟦a⟧ ∈ ⟦A⟧): {asked} asked, {settled} discharged, {} carried as assumptions\n",
        asked - settled
    );
    for c in HtClause::ALL {
        let n = HT_CLAUSES[c as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("by {}", c.name())));
        }
    }
    for m in HtMiss::ALL {
        let n = HT_MISSES[m as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("not shown: {}", m.name())));
        }
    }
    s
}

/// Render what the TG kernel actually derived over this run.
pub fn global_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let g = TOTALS.lock().expect("tg totals poisoned");
    let proved = PROVED.load(Relaxed);
    let mut rows: Vec<(&'static str, u64)> = g.clone().unwrap_or_default();
    // An escaped assumption is a gap in exactly the sense the rest of this table
    // measures: a conclusion the checker took that was not derived outright.
    // It is added here rather than tallied through `merge_one` because it is
    // only knowable once the whole run is over.
    let escapes = escaped();
    if escapes > 0 {
        rows.push((ESCAPED, escapes));
    }
    rows.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    let width = rows.iter().map(|(r, _)| r.len() + 5).chain([24]).max().unwrap_or(24);
    let mut s = String::from("Tarski-Grothendieck kernel: derivation coverage\n");
    s.push_str(&format!("  {:<width$}  {proved:>12}\n", "derived (real kernel Thm)"));
    let total: u64 = rows.iter().map(|(_, n)| *n).sum();
    for (r, n) in &rows {
        s.push_str(&format!("  {:<width$}  {n:>12}\n", format!("gap: {r}")));
    }
    s.push_str(&format!("  {:<width$}  {total:>12}\n", "TOTAL gaps"));
    let made = CONDITIONAL.load(Relaxed);
    if made > 0 {
        s.push_str(&format!(
            "  conditional derivations: {} made ({} of them copies), {} accounted for by a rule, {} escaped (max {} assumptions)\n",
            made,
            CONDITIONAL_COPIES.load(Relaxed),
            CONSUMED.load(Relaxed),
            escapes,
            MAX_ASSUMED.load(Relaxed),
        ));
    }
    let unmatched: Vec<(&str, u64)> = [("app_cong", Rule::AppCong), ("trans", Rule::Trans), ("symm", Rule::Symm)]
        .into_iter()
        .map(|(n, r)| (n, UNMATCHED[r as usize].load(Relaxed)))
        .collect();
    if unmatched.iter().any(|(_, n)| *n > 0) {
        s.push_str("  derivations that failed their guard (did not match the claim):");
        for (n, c) in &unmatched {
            s.push_str(&format!(" {n}={c}"));
        }
        s.push('\n');
    }
    s.push_str(&ht_report());
    if total == 0 && proved > 0 {
        s.push_str("  >> every definitional-equality step was fully derived\n");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh constant, usable to instantiate a quantifier at.
    fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

    /// [`lam_ext_n`] pinned to its *exact* conclusion, at a prefix on one side
    /// only — the asymmetric case, which is what `lam_cong` normally meets and
    /// which `derived::ext::lam_ext` cannot express.
    ///
    /// The shape has to be pinned rather than merely checked for provability:
    /// `lam_cong` matches its result against the claim syntactically, so a
    /// lemma that is only *equivalent* to the intended one is useless.
    #[test]
    fn lam_ext_n_has_the_stated_shape() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2); // t(p, x)
        let t2 = env.declare(1); // t'(x)
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");

        let thm = lam_ext_n(&mut env, &ap, t, lam, &lam_ax, t2, lam2, &lam2_ax).expect("lam_ext_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_a2) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_a2.clone()]).expect("instantiate");

        let x = env.fresh_var();
        let tx = Term::var(x);
        let pointwise = Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), big_a.clone()),
                Formula::eq(Term::apply(t, vec![p.clone(), tx.clone()]), Term::apply(t2, vec![tx])),
            ),
        );
        let expected = Formula::imp(
            Formula::eq(big_a.clone(), big_a2.clone()),
            Formula::imp(
                pointwise,
                Formula::eq(Term::apply(lam, vec![p, big_a]), Term::apply(lam2, vec![big_a2])),
            ),
        );
        assert_eq!(*inst.concl(), expected, "lam_ext_n has the wrong shape");
    }

    /// A graph symbol whose arity does not match its body symbol's is refused,
    /// rather than yielding a theorem about a malformed term.
    #[test]
    fn lam_ext_n_rejects_mismatched_arities() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2);
        let t2 = env.declare(1);
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");

        let wrong = env.declare(3);
        assert!(lam_ext_n(&mut env, &ap, t, wrong, &lam_ax, t2, lam2, &lam2_ax).is_none());
        assert!(lam_ext_n(&mut env, &ap, t, lam, &lam_ax, t2, wrong, &lam2_ax).is_none());
        // A nullary body symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(lam_ext_n(&mut env, &ap, nullary, lam, &lam_ax, t2, lam2, &lam2_ax).is_none());
    }

    /// A `parts` map for the terms built here, mirroring [`TgBackend::mk`].
    fn mk_in(parts: &mut Parts, f: FnSym, args: Vec<Term>) -> Term {
        let t = Term::apply(f, args.clone());
        parts.insert(t.clone(), (f, args));
        t
    }

    /// [`retarget`] does what `pi_cong` needs: a certificate stated at a local
    /// becomes one stated at the bound-variable encoding, with *exactly* the
    /// wanted conclusion.
    #[test]
    fn retarget_reaims_a_certificate_at_the_de_bruijn_form() {
        let mut env = Env::new();
        let mut parts = Parts::new();
        let (f, bvar) = (env.declare(1), env.declare(1));
        // `bvar(idx₀)`, the interpretation of a loose de Bruijn index, and a
        // second constant to stand for a different one.
        let b0 = mk_in(&mut parts, bvar, vec![constant(&mut env)]);
        let b1 = mk_in(&mut parts, bvar, vec![constant(&mut env)]);

        // A genuinely non-reflexive certificate stated at a local: `⊢ d(v) = f(v)`.
        let v = env.fresh_var();
        let fv = mk_in(&mut parts, f, vec![Term::var(v)]);
        let (d, d_def) = derived::define_abbrev(&mut env, &[v], &fv).expect("define");
        let dv = mk_in(&mut parts, d, vec![Term::var(v)]);
        let cert = derived::inst_all(&d_def, &[Term::var(v)]).expect("instantiate");
        assert_eq!(*cert.concl(), Formula::eq(dv, fv), "the certificate is stated at the local");

        // Re-aimed at the raw form the claim uses, and *exactly* that.
        let (db, fb) = (mk_in(&mut parts, d, vec![b0.clone()]), mk_in(&mut parts, f, vec![b0.clone()]));
        let out = retarget(&parts, &cert, &db, &fb).expect("retarget should re-aim");
        assert_eq!(*out.concl(), Formula::eq(db.clone(), fb));

        // One local cannot become two different terms: the certificate says
        // nothing about `d(bvar₀) = f(bvar₁)` and must not be bent into it.
        let fb1 = mk_in(&mut parts, f, vec![b1.clone()]);
        assert!(retarget(&parts, &cert, &db, &fb1).is_none(), "inconsistent binding must be refused");

        // A head symbol the certificate does not have is refused outright.
        let db1 = mk_in(&mut parts, d, vec![b1]);
        assert!(retarget(&parts, &cert, &db1, &db).is_none(), "mismatched head symbol must be refused");

        // A term the backend never built cannot be taken apart.
        let stranger = Term::apply(f, vec![b0]);
        let mut bare = Parts::new();
        bare.insert(stranger.clone(), (f, vec![]));
        assert!(retarget(&bare, &cert, &stranger, &stranger).is_none(), "unknown structure must be refused");
    }

    /// The prelude's stack, rebuilt: `app`, the Cartesian product and the
    /// function space over *one* `Sets`, which is what the `Π` lemmas need.
    fn pi_stack(env: &mut Env) -> (Apply, derived::funspace::Product, derived::funspace::Funspace) {
        let ap = Apply::new(env).expect("Apply::new");
        let (pow, pow_ax) = derived::power(env);
        let prod = derived::funspace::product(env, &ap.sets).expect("product");
        let fs = derived::funspace::Funspace::new(env, &ap.sets, pow, &pow_ax, &prod, &ap.empty_ax)
            .expect("Funspace::new");
        (ap, prod, fs)
    }

    /// `id(a)`, together with `⊢ id(a) ∈ fs(a,a)` — the one concrete function
    /// this development builds, and so the only genuine inhabitant of a function
    /// space a test of the application-typing rules can use.
    fn identity_in_funspace(
        env: &mut Env,
        ap: &Apply,
        prod: &derived::funspace::Product,
        fs: &derived::funspace::Funspace,
        a: &Term,
    ) -> (Term, Thm) {
        use derived::funspace::{identity_graph, identity_is_function};
        let (id, id_ax) = identity_graph(env, &ap.sets).expect("identity_graph");
        let id_fun =
            identity_is_function(env, &ap.sets, prod, id, &id_ax, &ap.pair_inj).expect("identity_is_function");
        let is_fun = derived::inst_all(&id_fun, std::slice::from_ref(a)).expect("isfun at a");
        let id_a = Term::apply(id, vec![a.clone()]);
        let members =
            derived::inst_all(&fs.fs_ax, &[a.clone(), a.clone(), id_a.clone()]).expect("fs_ax at a, a, id(a)");
        let thm = Thm::mp(&derived::iff_mpr(&members).expect("iff_mpr"), &is_fun).expect("mp");
        assert_eq!(*thm.concl(), Formula::mem(id_a.clone(), fs.of(a.clone(), a.clone())));
        (id_a, thm)
    }

    /// [`app_in_codomain`] against a genuine inhabitant: the identity function
    /// on `{c}`, applied to `c`, lands back in `{c}`.
    ///
    /// The corpus cannot reach this clause — every Lean function value is a
    /// lambda or an opaque constant, and neither has a typing lemma yet — so
    /// this is what says the rule composes at all.
    #[test]
    fn app_in_codomain_types_the_identity() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem =
            derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("funspace_app_mem");

        let c = constant(&mut env);
        let a0 = derived::singleton(ap.sets.up, c.clone());
        let (mem_c, _) = derived::upair_members(&ap.sets.up_ax, &c, &c).expect("upair_members");
        let (id_a, id_in_fs) = identity_in_funspace(&mut env, &ap, &prod, &fs, &a0);

        let out = app_in_codomain(&app_mem, &a0, &a0, &id_a, &c, &id_in_fs, &mem_c).expect("app_in_codomain");
        assert_eq!(
            *out.concl(),
            Formula::mem(ap.apply(id_a, c), a0),
            "app_in_codomain did not type the application"
        );
    }

    /// [`app_in_fibre`] against a genuine inhabitant.
    ///
    /// A dependent product needs a *section* to be inhabited, and the only
    /// function available is the identity — so the fibre is taken constant,
    /// `b(p,x) := p`, which by [`dprod_const_fibre_n`] makes the product a
    /// function space and the identity a member of it. The fibre symbol is
    /// still a fibre: the route goes through `dprod_def`'s section conjunct and
    /// unfolds `b(A,c)`, which is the step that has to line up with `⟦B[a]⟧`.
    #[test]
    fn app_in_fibre_types_a_section() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem =
            derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("funspace_app_mem");
        let retarget =
            derived::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair).expect("funspace_retarget");

        // `b(p,x) := p`, a one-parameter fibre that ignores the binder.
        let (p, x) = (env.fresh_var(), env.fresh_var());
        let (b, b_def) = derived::define_abbrev(&mut env, &[p, x], &Term::var(p)).expect("define_abbrev");
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let bridge =
            dprod_const_fibre_n(&mut env, &ap, &fs, b, img, &img_ax, dprod, &dprod_def, &app_mem, &retarget)
                .expect("dprod_const_fibre_n");

        let c = constant(&mut env);
        let a0 = derived::singleton(ap.sets.up, c.clone());
        let (mem_c, _) = derived::upair_members(&ap.sets.up_ax, &c, &c).expect("upair_members");

        // `∀x. (x ∈ A → b(A,x) = A)`, the bridge's premise, straight from `b`'s
        // definition; then `⊢ dprod(A,A) = fs(A,A)`.
        let w = env.fresh_var();
        let at_w = derived::inst_all(&b_def, &[a0.clone(), Term::var(w)]).expect("b_def at A, w");
        let cond = Thm::gen(w, &derived::a1i(&at_w, Formula::mem(Term::var(w), a0.clone())));
        let inst = derived::inst_all(&bridge, &[a0.clone(), a0.clone(), a0.clone()]).expect("bridge at A");
        let eq = Thm::mp(&inst, &cond).expect("the constant-fibre premise");

        // The identity, moved across that equation into the dependent product.
        let (id_a, id_in_fs) = identity_in_funspace(&mut env, &ap, &prod, &fs, &a0);
        let back = derived::eq_symm(&mut env, &eq).expect("eq_symm");
        let dp = Term::apply(dprod, vec![a0.clone(), a0.clone()]);
        let v = env.fresh_var();
        let leib = Thm::eq_leibniz(
            fs.of(a0.clone(), a0.clone()),
            dp.clone(),
            v,
            Formula::mem(id_a.clone(), Term::var(v)),
        );
        let id_in_dp = Thm::mp(&Thm::mp(&leib, &back).expect("mp"), &id_in_fs).expect("mp");
        assert_eq!(*id_in_dp.concl(), Formula::mem(id_a.clone(), dp));

        let out = app_in_fibre(
            &mut env,
            ap.app,
            &dprod_def,
            &b_def,
            std::slice::from_ref(&a0),
            &a0,
            &id_a,
            &c,
            &id_in_dp,
            &mem_c,
        )
        .expect("app_in_fibre");
        assert_eq!(
            *out.concl(),
            Formula::mem(ap.apply(id_a, c), a0),
            "app_in_fibre did not type the application at the unfolded fibre"
        );
    }

    /// The dependent product over a fibre symbol with a `k`-parameter prefix.
    fn dprod_over(
        env: &mut Env,
        ap: &Apply,
        fs: &derived::funspace::Funspace,
        b: FnSym,
    ) -> (FnSym, Thm, FnSym, Thm) {
        let (img, img_ax) = image_symbol_n(env, b).expect("image_symbol_n");
        let (dprod, dprod_def) = dprod_symbol_n(env, ap, fs, img, b).expect("dprod_symbol_n");
        (img, img_ax, dprod, dprod_def)
    }

    /// [`dprod_const_fibre_n`] pinned to its *exact* conclusion, at a genuine
    /// parameter prefix — the case the unary `derived::ext::dprod_const_fibre`
    /// cannot express, and the only one the checker ever meets.
    ///
    /// The shape has to be pinned rather than merely checked for provability:
    /// `pi_cong` matches its result against the claim syntactically, so a lemma
    /// that is only *equivalent* to the intended one is useless.
    #[test]
    fn dprod_const_fibre_n_has_the_stated_shape() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let b = env.declare(2); // b(p, x)
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem = derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("app_mem");
        let retarget = derived::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair).expect("retarget");

        let thm = dprod_const_fibre_n(&mut env, &ap, &fs, b, img, &img_ax, dprod, &dprod_def, &app_mem, &retarget)
            .expect("dprod_const_fibre_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_b) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_b.clone()]).expect("instantiate");
        let x = env.fresh_var();
        let expected = Formula::imp(
            Formula::forall(
                x,
                Formula::imp(
                    Formula::mem(Term::var(x), big_a.clone()),
                    Formula::eq(Term::apply(b, vec![p.clone(), Term::var(x)]), big_b.clone()),
                ),
            ),
            Formula::eq(Term::apply(dprod, vec![p, big_a.clone()]), fs.of(big_a, big_b)),
        );
        assert_eq!(*inst.concl(), expected, "dprod_const_fibre_n has the wrong shape");

        // Non-vacuity twice over: the two sides of the equation are built by
        // different symbols, and the hypothesis is not the conclusion.
        let (ante, concl) = inst.concl().as_imp().expect("an implication");
        let (l, r) = concl.as_eq().expect("an equation");
        assert_ne!(l, r, "the lemma would equate a term with itself");
        assert_ne!(ante, concl);
    }

    /// The stack is *checked*, not assumed: a fibre, image or product the
    /// dependent product was not built over is refused, rather than yielding a
    /// theorem about the wrong sets.
    #[test]
    fn dprod_const_fibre_n_rejects_a_mismatch() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let (b, b2) = (env.declare(2), env.declare(2));
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let (img2, img2_ax, dprod2, dprod2_def) = dprod_over(&mut env, &ap, &fs, b2);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem = derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("app_mem");
        let rt = derived::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair).expect("retarget");

        let ok = |e: &mut Env, b, i, ia: &Thm, d, dd: &Thm| dprod_const_fibre_n(e, &ap, &fs, b, i, ia, d, dd, &app_mem, &rt);
        assert!(ok(&mut env, b, img, &img_ax, dprod, &dprod_def).is_some(), "the matched stack goes through");
        // The other fibre's product, image or defining axiom: each refused.
        assert!(ok(&mut env, b, img, &img_ax, dprod2, &dprod2_def).is_none(), "a foreign dependent product");
        assert!(ok(&mut env, b, img2, &img2_ax, dprod, &dprod_def).is_none(), "a foreign fibre image");
        assert!(ok(&mut env, b2, img, &img_ax, dprod, &dprod_def).is_none(), "a foreign fibre");
        assert!(ok(&mut env, b, img2, &img_ax, dprod, &dprod_def).is_none(), "an image axiom for another image");
        // A nullary fibre symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(ok(&mut env, nullary, img, &img_ax, dprod, &dprod_def).is_none(), "a fibre with no binder slot");
    }

    /// [`dprod_ext_n`] pinned to its *exact* conclusion, at a prefix on one side
    /// only — the asymmetric case, which is what `pi_cong` normally meets and
    /// which `derived::ext::dprod_ext` cannot express.
    #[test]
    fn dprod_ext_n_has_the_stated_shape() {
        let mut env = Env::new();
        let (ap, _prod, fs) = pi_stack(&mut env);
        let (b, b2) = (env.declare(2), env.declare(1)); // b(p,x) and b'(x)
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let (img2, img2_ax, dprod2, dprod2_def) = dprod_over(&mut env, &ap, &fs, b2);

        let thm = dprod_ext_n(
            &mut env,
            &ap,
            &fs,
            (b, img, &img_ax, dprod, &dprod_def),
            (b2, img2, &img2_ax, dprod2, &dprod2_def),
        )
        .expect("dprod_ext_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_a2) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_a2.clone()]).expect("instantiate");
        let x = env.fresh_var();
        let tx = Term::var(x);
        let pointwise = Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), big_a.clone()),
                Formula::eq(Term::apply(b, vec![p.clone(), tx.clone()]), Term::apply(b2, vec![tx])),
            ),
        );
        let expected = Formula::imp(
            Formula::eq(big_a.clone(), big_a2.clone()),
            Formula::imp(
                pointwise,
                Formula::eq(Term::apply(dprod, vec![p, big_a]), Term::apply(dprod2, vec![big_a2])),
            ),
        );
        assert_eq!(*inst.concl(), expected, "dprod_ext_n has the wrong shape");
    }

    /// A defining axiom that is not the one [`dprod_symbol_n`] produces for the
    /// symbol at hand is rejected: the derivation would otherwise be sound but
    /// about the wrong sets, and silently so.
    #[test]
    fn dprod_ext_n_rejects_a_foreign_axiom() {
        let mut env = Env::new();
        let (ap, _prod, fs) = pi_stack(&mut env);
        let (b, b2) = (env.declare(2), env.declare(1));
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let (img2, img2_ax, dprod2, dprod2_def) = dprod_over(&mut env, &ap, &fs, b2);

        // The two products swapped over: right shape, wrong symbols.
        assert!(dprod_ext_n(
            &mut env,
            &ap,
            &fs,
            (b, img, &img_ax, dprod2, &dprod2_def),
            (b2, img2, &img2_ax, dprod, &dprod_def),
        )
        .is_none());
        // An arity that does not match the fibre's.
        let wrong = env.declare(3);
        assert!(dprod_ext_n(
            &mut env,
            &ap,
            &fs,
            (b, wrong, &img_ax, dprod, &dprod_def),
            (b2, img2, &img2_ax, dprod2, &dprod2_def),
        )
        .is_none());
    }

    /// A membership atom over fresh constants, to stand for an assumption.
    fn atom(env: &mut Env) -> Formula { Formula::mem(constant(env), constant(env)) }

    /// The left-nested conjunction is the one the discharge relies on:
    /// `conj(R ++ [h])` has to be `conj(R) ∧ h`, or `uncurry` peels the wrong
    /// assumption off and the binder discharges something it was not given.
    #[test]
    fn conj_is_left_nested_and_projects() {
        let mut env = Env::new();
        let hs: Vec<Formula> = (0..4).map(|_| atom(&mut env)).collect();
        let whole = conj_of(&hs).expect("non-empty");
        assert_eq!(whole, Formula::and(conj_of(&hs[..3]).expect("non-empty"), hs[3].clone()));
        assert_eq!(conj_of(&hs[..1]), Some(hs[0].clone()), "a single assumption is itself");
        assert_eq!(conj_of(&[]), None);

        for (i, h) in hs.iter().enumerate() {
            let p = conj_proj(&hs, i).expect("projection");
            assert_eq!(*p.concl(), Formula::imp(whole.clone(), h.clone()), "projection {i}");
        }
        assert!(conj_proj(&hs, 4).is_none(), "out of range");
    }

    /// `reassume` really re-states a derivation, and only under a *superset*:
    /// re-stating under assumptions that do not include the ones actually used
    /// would be exactly the way to lose an obligation silently.
    #[test]
    fn reassume_restates_and_reorders() {
        let mut env = Env::new();
        let (h1, h2, h3) = (atom(&mut env), atom(&mut env), atom(&mut env));
        let c = constant(&mut env);
        let eq = Formula::eq(c.clone(), c.clone());

        // ⊢ (h1 ∧ h2) → c = c
        let from = vec![h1.clone(), h2.clone()];
        let base = derived::a1i(&Thm::eq_refl(c.clone()), conj_of(&from).expect("non-empty"));

        // Reordered and extended.
        let to = vec![h3.clone(), h2.clone(), h1.clone()];
        let out = reassume(&base, &from, &to).expect("re-statement");
        assert_eq!(*out.concl(), Formula::imp(conj_of(&to).expect("non-empty"), eq.clone()));

        // Dropping an assumption that is genuinely used is refused.
        assert!(reassume(&base, &from, &[h1.clone()]).is_none(), "must not shed an assumption");
        assert!(reassume(&base, &from, &[]).is_none(), "must not shed every assumption");
        // An unconditional theorem may of course be weakened.
        let plain = Thm::eq_refl(c);
        let weak = reassume(&plain, &[], std::slice::from_ref(&h1)).expect("weakening");
        assert_eq!(*weak.concl(), Formula::imp(h1, eq));
    }

    /// `CondEq` refuses to describe a theorem it does not have: an assumption
    /// list that is not the theorem's antecedent is rejected outright, which is
    /// what stops a rule from advertising a discharged obligation it never
    /// discharged.
    #[test]
    fn cond_eq_checks_its_own_assumptions() {
        let mut env = Env::new();
        let (h1, h2) = (atom(&mut env), atom(&mut env));
        let c = constant(&mut env);
        let refl = Thm::eq_refl(c.clone());

        assert!(CondEq::new(refl.clone(), vec![]).is_some(), "a bare equation assumes nothing");
        assert!(CondEq::new(refl.clone(), vec![h1.clone()]).is_none(), "an equation is not an implication");

        let under_h1 = derived::a1i(&refl, h1.clone());
        assert!(CondEq::new(under_h1.clone(), vec![h1.clone()]).is_some());
        assert!(CondEq::new(under_h1.clone(), vec![h2.clone()]).is_none(), "the wrong assumption");
        assert!(CondEq::new(under_h1.clone(), vec![]).is_none(), "assumption cannot be dropped");
        assert!(CondEq::new(under_h1, vec![h1, h2]).is_none(), "assumption cannot be invented");

        // The conclusion has to be an equation, whatever the antecedent is.
        let not_eq = derived::imp_refl(Formula::false_());
        assert!(CondEq::new(not_eq, vec![Formula::false_()]).is_none());
    }

    /// Transitivity across two derivations with different assumptions produces
    /// the union, as a real antecedent.
    #[test]
    fn conditional_transitivity_merges_assumptions() {
        let mut env = Env::new();
        let (h1, h2) = (atom(&mut env), atom(&mut env));
        let b = constant(&mut env);
        // ⊢ h1 → d = b and ⊢ h2 → b = b, from a genuine equation and reflexivity.
        let (d, d_def) = derived::define_abbrev(&mut env, &[], &b).expect("define");
        let ab = derived::inst_all(&d_def, &[]).expect("instantiate"); // ⊢ d = b
        let da = Term::apply(d, vec![]);

        let c1 = CondEq::new(derived::a1i(&ab, h1.clone()), vec![h1.clone()]).expect("conditional");
        let c2 = CondEq::new(derived::a1i(&Thm::eq_refl(b.clone()), h2.clone()), vec![h2.clone()]).expect("cond");

        let hyps = merge_hyps(&c1.hyps, &c2.hyps);
        let h = conj_of(&hyps).expect("non-empty");
        let x = reassume(&c1.thm, &c1.hyps, &hyps).expect("restate");
        let y = reassume(&c2.thm, &c2.hyps, &hyps).expect("restate");
        let out = u_eq_trans(&mut env, &x, &y, Some(&h)).expect("transitivity");
        assert_eq!(*out.concl(), Formula::imp(Formula::and(h1, h2), Formula::eq(da, b)));
    }

    /// A characteristic axiom that is not the one `lambda_n` produces for the
    /// symbol at hand is rejected: the derivation would otherwise be sound but
    /// about the wrong sets, and silently so.
    #[test]
    fn lam_ext_n_rejects_a_foreign_axiom() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2);
        let t2 = env.declare(1);
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");
        // The two axioms swapped over: right shape, wrong symbols.
        assert!(lam_ext_n(&mut env, &ap, t, lam, &lam2_ax, t2, lam2, &lam_ax).is_none());
    }
}
