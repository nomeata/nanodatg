//! Theorems, inference rules, and the axioms of Tarski–Grothendieck set theory.
//!
//! # Hilbert axioms, Isabelle judgement
//!
//! The judgement is `Γ ⊢ φ`: [`Thm`] carries a **finite set of hypotheses beside
//! the formula**, exactly as Isabelle/Pure's `thm` carries its `hyps`. The
//! *axioms* are still the Hilbert ones (Łukasiewicz A1–A3, instantiation,
//! distribution) — only the judgement changed.
//!
//! This reverses the design recorded in `DECISIONS.md`, 2026-07-30, and the
//! `CLAUDE.md` requirement it was following, both of which demanded that a `Thm`
//! be a bare formula with no context. The reversal was decided by the project
//! owner on the ground that decides it:
//!
//! > "The alternative will be too slow at run time. We try to keep the cost of
//! > each kernel operation as performed by the checker **constant**."
//!
//! ## Why the alternative is not merely inelegant
//!
//! With no `Γ`, an assumption has to be encoded as an *antecedent inside* the
//! formula — the Metamath discipline, which `derived/` practised by hand across
//! ~38 000 lines and then automated in `derived::hyp`. Under that encoding a
//! theorem proved under `Γ` is really `⊢ ⋀Γ → φ`, so combining two theorems
//! means first re-proving **both** against `⋀(Γ ∪ Δ)`: rebuilding the
//! conjunction, projecting each old hypothesis out of the new one, and chaining.
//! Every one of those steps is a kernel call.
//!
//! The above-kernel layer measured the cost exactly. One binary operation on
//! hypothesis sets with `u = |Γ ∪ Δ|` costs **`13u² + 73u − 134` kernel calls** —
//! an exact integer fit at every measured point, depending only on `u` and not on
//! how the hypotheses split between the premises. The inference it enables costs
//! **53** once the sets already agree. So the bookkeeping is between 1× and 82×
//! the inference, it is *quadratic* rather than linear, it compounds to `Θ(k³)`
//! over a chain of `k` steps, and memoisation buys nothing because each merge
//! targets a set never seen before. Hypothesis sets do not stay small either:
//! the main argument in `derived/src/universe/union.rs` accumulates nine.
//!
//! Beside the formula, the same merge is a union of two sorted lists of pointers
//! and the two premise theorems are used **unchanged**. That is the entire
//! argument, and it is Isabelle's.
//!
//! ## What it costs, honestly
//!
//! Three things, each priced below and none free.
//!
//! * `gen` acquires a real side condition, `x ∉ FV(Γ)` — the classic
//!   natural-deduction one. It was previously argued to be *vacuous*; that
//!   argument is now false. See [`Thm::gen`].
//! * `define` must refuse a hypothetical witness, or a symbol gets minted from
//!   something proved only under an assumption. See [`define`].
//! * **A `Thm` establishes its conclusion only when its hypothesis set is
//!   empty**, so code outside the kernel that reads a conclusion without reading
//!   the hypotheses is no longer sound — the definitional-equality cache being
//!   the instance that prompted the point. This one is not local to the kernel
//!   and is stated in full below.
//!
//! # What a `Thm` asserts
//!
//! **A `Thm` is not a closed formula.** `Thm::eq_refl(Term::var(x))` is `⊢ x = x`
//! with `x` free, `Thm::ax_replacement` hands back a formula with the caller's
//! `x` and `y` free inside it, and nothing in this crate ever closes either. The
//! convention that makes such a theorem *mean* something — and which every rule
//! below silently assumes — is:
//!
//! > **`Γ ⊢ φ` asserts `∀x⃗. (⋀Γ → φ)`, where `x⃗ = FV(Γ ∪ {φ})`.** Equivalently:
//! > under **every** assignment to the free variables of the whole sequent that
//! > satisfies every member of `Γ`, `φ` holds. A free variable is *schematic* —
//! > it stands for an arbitrary object, not for a particular one the theorem
//! > knows about — and the *same* assignment is read on both sides of the
//! > turnstile.
//!
//! Two things about that statement are load-bearing and neither is implied by
//! the types.
//!
//! **The quantifier sits outside both sides.** `∀x⃗. (⋀Γ → φ)`, not
//! `(⋀Γ) → ∀x⃗. φ` and not `(∀x⃗. ⋀Γ) → (∀x⃗. φ)`. Free variables are *shared*
//! across the turnstile: `{x ∈ y} ⊢ x ∈ y` is `∀x ∀y. (x ∈ y → x ∈ y)`, one
//! quantifier prefix over both. Under the inside-φ reading the same sequent would
//! assert `(x ∈ y) → ∀x ∀y. (x ∈ y)`, which is false, and which [`Thm::gen`]
//! would then be entitled to produce. This is why the reading has to be written
//! down: the previous section here was written for a hypothesis-free judgement
//! and simply did not say which side the quantifier was on, because there was
//! only one side.
//!
//! **It is conservative over the old reading.** With `Γ` empty, `⋀Γ` is `⊤` and
//! the statement collapses to "`⊢ φ` asserts `∀FV(φ). φ`" — word for word what
//! this section said before hypotheses existed. Every theorem `derived/` and
//! `checker/` build lands in that case, so nothing they rely on has changed
//! meaning. This is the standard reading for a Hilbert system with schematic
//! variables; Metamath's `$p` statements work the same way.
//!
//! ## Why `gen` must now check `x ∉ FV(Γ)`
//!
//! **The previous version of this section argued that the side condition was
//! vacuous, and that argument is retracted.** It read: "Here there is no `Γ` — a
//! `Thm` is one formula and nothing else — so there is no hypothesis for `x` to
//! be free in, and the side condition is not merely unchecked, it is *vacuous*."
//! Its premise was true when it was written and is false now. It is quoted here
//! once, as a retraction, and appears nowhere else: a retired soundness argument
//! left standing beside the code it no longer justifies is an invitation to
//! delete the check, and this crate has a documented history of doc comments
//! asserting properties the code did not have.
//!
//! The condition is the classic one. From `{x ∈ y} ⊢ x ∈ y` one must **not**
//! conclude `{x ∈ y} ⊢ ∀x. x ∈ y`. Under the reading above the premise is
//! `∀x ∀y. (x ∈ y → x ∈ y)`, a tautology, while the conclusion is
//! `∀x ∀y. (x ∈ y → ∀x. x ∈ y)`, which fails in any model with a two-element
//! set. What licenses generalisation is that the assignments satisfying `Γ` are
//! closed under changing `x`, and that is exactly `x ∉ FV(Γ)`.
//!
//! The condition is *still* vacuous on a hypothesis-free theorem, so the rule
//! behaves identically on every derivation written against the old kernel. That
//! is a fact about those callers, not a property of the rule, and it is the only
//! reason [`Thm::gen`] could keep an infallible signature.
//!
//! Since a fact about today's callers is the kind of guarantee this project has
//! watched evaporate before, it is now **a property of the repository**:
//! `ci/check-boundary.sh` rejects any occurrence of `Thm::assume` or
//! `Thm::implies_intr` in shipped code outside `kernel/`, so no caller can reach
//! [`Thm::gen`] with a hypothetical theorem without first changing a CI rule that
//! says why the panic is unreachable. Test code is exempt and deliberately so —
//! pinning the guard requires building a hypothetical theorem on purpose.
//!
//! **This does not generalise to the other side conditions.** [`Thm::ax_dist`]'s
//! `x ∉ FV(φ)` is a **separate** condition about a different `φ` — the antecedent
//! of the implication under the quantifier, not a hypothesis — and it remains
//! real, checked, and untouched by any of this. Conflating the two would be a way
//! of "simplifying" one of them away. Concluding "free variables are universal,
//! so the variable side conditions are all vacuous here" is how a genuine check
//! gets deleted, and it is how one nearly was.
//!
//! ## What hypotheses do *not* buy: naming an object
//!
//! There is still no existential-elimination rule and there still cannot be one.
//! From `⊢ ∃x. φ(x)` you may **not** conclude `{φ(c)} ⊢ φ(c)` and then treat `c`
//! as *the* witness: [`Thm::assume`] makes no claim about its formula, the free
//! `c` is schematic like every other, and the moment the hypothesis is discharged
//! the result is `⊢ φ(c) → ψ` with `c` still universal. Eliminating an
//! existential still means proving `⊢ φ(x) → ψ` with `x ∉ FV(ψ)` and going
//! through [`Thm::ax_dist`] and the `¬∀¬` encoding. `gen`'s side condition is
//! precisely what stops the shortcut.
//!
//! # THE `hyps()` OBLIGATION — for whoever owns `checker/`
//!
//! **This is a live unsoundness if ignored, not a slowdown.** It cannot be fixed
//! in this crate.
//!
//! ## The obligation in general
//!
//! > **A `Thm` no longer establishes its conclusion.** It establishes it *only
//! > when [`Thm::hyps`] is empty.* Any code outside the kernel that reads
//! > [`Thm::concl`] without reading [`Thm::hyps`] — whether it **stores** the
//! > theorem for reuse somewhere else, or merely **compares** its conclusion
//! > against an expected formula and reports success — silently imports `Γ`.
//!
//! The storing case is the obvious one and the comparing case is the one that
//! reads as harmless: a function that checks `thm.concl() == expected` and
//! answers `true` has accepted `Γ ⊢ expected` as a proof of `expected`, with no
//! store and no key anywhere in sight. Nothing in this crate can detect either,
//! because from the kernel's side the theorem in hand is a perfectly good
//! theorem; the error is entirely in what the checker concluded from it. Inside
//! the kernel the same discipline is [`define`]'s `witness.hyps().is_empty()`.
//!
//! ## The instance that prompted it: the definitional-equality cache
//!
//! The definitional-equality cache in `checker/` memoises "these two `Expr`s are
//! equal" together with the [`Thm`] certifying it, and reuses the entry anywhere
//! the same pair comes up. That was sound for a specific reason, stated in this
//! header until today: a `Thm` was valid **absolutely**, so an equality proved
//! once was usable in every Lean local context, and the pair of `Expr`s was a
//! complete key.
//!
//! With hypotheses beside the formula that argument fails. `Γ ⊢ a = b` is valid
//! only where `Γ` holds. Storing it under the key `(a, b)` and retrieving it
//! elsewhere **silently imports `Γ`** — the retrieved certificate looks like a
//! proof of `a = b` and is not one.
//!
//! Two acceptable fixes, in order of preference:
//!
//! 1. **Cache only hypothesis-free theorems.** Refuse to insert an entry whose
//!    `Thm::hyps()` is non-empty. Trivially correct, keeps the existing key, and
//!    loses nothing today because the checker's backend never calls
//!    [`Thm::assume`] outside its own tests — every certificate it builds has
//!    `hyps() == []`.
//! 2. **Key the cache on the hypothesis set as well**, i.e. on
//!    `(a, b, thm.hyps())`. Necessary if the backend ever starts proving
//!    conversions under assumptions. It puts hypothesis-set equality on the hot
//!    path, which is a second reason the set is canonically ordered: comparing
//!    two sets is `==` on two sorted vectors, not a subset test.
//!
//!    **Option 2 does not discharge the obligation on its own**, and reading it
//!    as if it did is the trap. A key match says the entry was *stored* under
//!    `Γ`; it is not a proof that `Γ` holds at the *use* site. The retrieving
//!    code must additionally either use the value only where every member of `Γ`
//!    is in force, or re-check that `Γ` is empty — and that second option is
//!    option 1 with a wider key.
//!
//!    Option 2 also **changes what `impl Ord for Formula` is trusted for.**
//!    Today the canonical order is a completeness concern only (see "The trusted
//!    surface" below). Under a key that mentions the set, two representations of
//!    one set have to collide in the key or the lookup answers about the wrong
//!    entry, so canonicality moves into the *external* soundness story. Whoever
//!    takes option 2 is re-trusting that order for a property the kernel does not
//!    currently rely on, and owes the argument.
//!
//! ## What the checker has done about it
//!
//! **Option 1, already.** `checker/src/certify.rs`'s `is_unconditional` now reads
//! `c.thm().is_some_and(|t| t.hyps().is_empty())` where it used to read
//! `c.is_proved()` — the variant `Proved` no longer implies the theorem is
//! unconditional, so the predicate asks the theorem — and it gates the equality
//! cache's insertion in `checker/src/tc.rs`. A second and deliberately weaker
//! predicate in the same file, `hypothesis_free`, gates the reduct memo's one
//! write site, because a certificate carrying its assumptions as *antecedents
//! inside* a closed formula imports nothing while a kernel `Γ` does.
//!
//! **The previous version of this section is retracted**, not amended. It said
//! doing neither fix "is the current state by default: the cache is unchanged and
//! its key is unchanged". That described a hole which is closed. A comment in the
//! trusted crate that reports a live unsoundness where there is none is the same
//! defect as one that reports a check where there is none — it spends the next
//! reader's attention on the wrong line, and it teaches them that this file's
//! warnings are stale, which is the expensive part. Two doc comments here have
//! already asserted properties the code did not have.
//!
//! What is *not* discharged is the general statement above, for the stores and
//! comparisons not yet written. `is_unconditional` fails closed as
//! certificate-producing rules are added; any new code that reads `concl()` owes
//! the same check.
//!
//! # Where getting the free-variable reading wrong produced `⊢ ⊥`
//!
//! [`define`]'s free-variable check is the place this convention has teeth, and
//! it was **absent**, and it was exploited — `DECISIONS.md`, "SECOND SOUNDNESS
//! BUG", 2026-07-30. With `xs = []` and `φ(y) := (y = v)` for a stray `v`, the
//! obligation `∃!y. y = v` is provable and the defining axiom came back as
//! `⊢ f = v` with `v` free. Under the universal reading that says `∀v. f = v`,
//! and `gen` makes it explicit; two instantiations give `c₁ = c₂` for arbitrary
//! constants, and `⊢ ⊥` follows. The witness had proved "for each `v` there is a
//! unique `y`" — so `y` depends on `v` — while `f(x⃗)` takes no `v` argument.
//!
//! The lesson worth keeping is not "add a check to `define`" but the reason the
//! check belongs there: `define` is the one rule that turns a *proved* formula
//! into a *new symbol*, and a free variable of that formula is universally
//! quantified on the premise side while the symbol it produces is not
//! parameterised by it. Any future rule that mints a symbol, a constant, or an
//! axiom out of a proved formula has to answer the same question. See the
//! comment on the check in [`define`] for the argument in full.
//!
//! **Hypotheses put a second instance of that same shape in front of `define`**,
//! and it is guarded by the same reasoning: a witness proved under `Γ` justifies
//! a symbol only where `Γ` holds, while the defining axiom `define` returns holds
//! everywhere. The check is `witness.hyps().is_empty()`.
//!
//! # The trusted surface
//!
//! Everything marked "primitive rule" below is trusted: if one of them is
//! unsound, the system proves nothing. Everything marked "derived" is *not*
//! trusted in the same way — it is ordinary code that can only reach a `Thm` by
//! calling primitives, so a bug there yields a rejection or a wrong-but-derivable
//! theorem, never an underivable one.
//!
//! The hypothesis machinery adds **two** trusted things and no more: the
//! `occurs_free` scan in [`Thm::gen_checked`] and the emptiness check in
//! [`define`]. If either is wrong, this kernel proves things that are false.
//!
//! The `sort_unstable`/`dedup` in `Thm::mk_hyps` was listed here as a third, and
//! that overstated it. **Kernel soundness does not depend on `impl Ord for
//! Formula` at all.** `dedup` compares with the structural `PartialEq`, not with
//! `cmp`, so a broken order can only leave genuine duplicates non-adjacent —
//! which keeps a formula that is genuinely assumed, a strictly weaker theorem —
//! and can never delete an element that is not a duplicate of its neighbour. No
//! rule reads the *order*: [`Thm::gen_checked`] scans every element,
//! [`Thm::implies_intr`]'s filter compares against every element, [`Thm::mp`]
//! concatenates both sets, and [`define`] asks only whether the set is empty. A
//! broken order therefore yields **incompleteness, not unsoundness** — two equal
//! sets listed differently stop comparing equal, so a later `mp` returns `None`
//! far from the cause.
//!
//! So the order is trusted for *canonicality, and hence for completeness*: it
//! must be total and must agree with `==` (which is what makes `dedup` remove
//! exactly the duplicates), and it is not trusted to mean anything. The one way
//! it would become soundness-relevant is option 2 of the cache obligation above
//! — keying an external store on the hypothesis set — because then two
//! representations of one set must collide in the key. That is a change to what
//! `impl Ord for Formula` is trusted for, and it belongs to whoever makes it.

use crate::term::{FnSym, Formula, FormulaData, FreeVar, Term, VarGen};

/// A sequent `Γ ⊢ φ`: a formula proved under a finite set of hypotheses.
///
/// The only way to obtain one is through the inference rules in this module.
/// The fields are private and there is no public constructor, so a client cannot
/// forge a theorem — that is the whole LCF argument.
///
/// **The conclusion need not be closed**, and the free variables of the whole
/// sequent are read *universally*: `Γ ⊢ φ` asserts that under **every**
/// assignment to `FV(Γ ∪ {φ})` satisfying every member of `Γ`, `φ` holds. When
/// `Γ` is empty that is the old reading, `⊢ φ` asserts `∀FV(φ). φ`, unchanged.
/// The convention is stated in full in the module documentation, it is what
/// [`Thm::gen`]'s side condition and [`define`]'s free-variable check exist to
/// respect, and reading a free variable any other way is how this crate once
/// proved `⊥`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Thm {
    /// The hypotheses, **sorted by `Formula`'s total order and duplicate-free**.
    ///
    /// That invariant is what makes `hyps` a *set*: two theorems proved under
    /// the same assumptions have `==` vectors whatever order the assumptions
    /// arrived in.
    ///
    /// **An earlier version of this comment said the invariant "is established in
    /// exactly two places — `mk` … and `mk_hyps` … — and every rule below goes
    /// through one of them", and both halves were false.** Two rules build the
    /// struct literally, bypassing both constructors, and they are precisely the
    /// two an editor of the hypothesis machinery would touch first. Neither was
    /// buggy; the sentence was. A false claim of the form "everything goes
    /// through here" is worse than no claim — it is the sentence a reader uses to
    /// enumerate where the invariant must be re-verified, so it sends the audit
    /// to the wrong lines. Same defect as the retracted compartmentalisation
    /// claim on `mk_defining_axiom` below, and the same reason it is written out
    /// rather than quietly amended.
    ///
    /// There are **four** construction sites in this file, and each preserves the
    /// invariant for its own reason:
    ///
    /// * `mk` — the vector is empty, which is sorted and duplicate-free
    ///   vacuously. Every axiom and every rule whose premises carry no
    ///   hypotheses goes through it.
    /// * `mk_hyps` — sorts and dedups, so it *establishes* the invariant from an
    ///   arbitrary caller-supplied vector. This is the only site that has to do
    ///   any work. [`Thm::implies_intr`] and [`Thm::mp`] go through it.
    /// * [`Thm::assume`] — builds `Thm { hyps: vec![phi], .. }` directly. A
    ///   one-element vector is sorted and duplicate-free whatever `φ` is, so
    ///   there is nothing to establish.
    /// * [`Thm::gen_checked`] — builds `Thm { hyps: thm.hyps.clone(), .. }`
    ///   directly. A clone of a canonical vector is canonical, and the rule
    ///   alters only the conclusion. ([`Thm::gen`] is a wrapper over it and adds
    ///   no fifth site.)
    ///
    /// Adding a fifth site, or changing what any of these four does to the
    /// vector, means re-checking that list. Nothing in the type enforces it, and
    /// no rule outside this file can construct a `Thm` at all.
    hyps: Vec<Formula>,
    concl: Formula,
}

impl Thm {
    /// The formula this theorem asserts.
    pub fn concl(&self) -> &Formula { &self.concl }

    /// The hypotheses it asserts it under, in canonical order and without
    /// duplicates. Empty for every theorem built from the axioms alone.
    pub fn hyps(&self) -> &[Formula] { &self.hyps }

    /// Internal: a theorem with **no** hypotheses. The axioms and every rule
    /// whose premises are axioms use this, so the hypothesis-free fragment of
    /// the kernel is byte-for-byte the code it was before hypotheses existed.
    /// Every use is a trusted step and should sit under a rule that documents
    /// why the conclusion is valid.
    fn mk(concl: Formula) -> Thm { Thm { hyps: Vec::new(), concl } }

    /// Internal: a theorem under hypotheses, canonicalised here so that no
    /// caller has to be trusted to produce a sorted, duplicate-free set.
    ///
    /// `sort_unstable` is sound despite the name: the order is total and agrees
    /// with `==` (see `impl Ord for Formula`), so equal elements are
    /// interchangeable and there is no stability to lose. The cost is zero on an
    /// empty vector, which is the case every pre-existing caller of this kernel
    /// hits.
    fn mk_hyps(mut hyps: Vec<Formula>, concl: Formula) -> Thm {
        hyps.sort_unstable();
        hyps.dedup();
        Thm { hyps, concl }
    }
}

/// Whether a formula is locally closed. Exposed for the substitution tests.
pub fn debug_locally_closed(f: &Formula) -> bool { f.locally_closed(0) }

/// The signature: which function symbols exist, and a source of fresh variables.
///
/// Function symbols are introduced by **pure signature extension** — a new
/// symbol with *no* axioms constraining it. That is unconditionally
/// conservative: any model of the base theory expands to a model of the
/// extension by interpreting the new symbol arbitrarily, so nothing new becomes
/// provable in the base language, and in particular consistency is preserved.
/// No proof obligation, and no growth of the trusted base.
///
/// This is enough for the equational fragment of the Lean interpretation:
/// reflexivity, symmetry, transitivity and congruence hold for *any* function
/// symbols whatever, because they are consequences of the equality axioms
/// rather than of anything specific to sets. Rules that need the symbols to
/// actually *mean* something — beta reduction, above all — require defining
/// axioms and hence a conservativity obligation; see `kernel/README.md`.
#[derive(Debug)]
pub struct Env {
    brand: u32,
    next_sym: u32,
    vars: VarGen,
}

/// Hands each `Env` a distinct brand, so that symbols and variables from
/// different environments can never be confused for one another.
static NEXT_BRAND: core::sync::atomic::AtomicU32 = core::sync::atomic::AtomicU32::new(0);

/// Allocate the next environment brand from `counter`, or panic if exhausted.
///
/// Uses `fetch_update`, **not** `fetch_add`, and the difference is a soundness
/// one. `fetch_add` on an atomic *wraps* — `overflow-checks` does not apply to
/// atomics — so guarding it with `checked_add` on the value it *returns* is a
/// one-shot: it panics on the call that wraps, by which point the counter has
/// already been reset to zero, and the next caller is handed a brand colliding
/// with the very first `Env`. That reinstates the cross-environment symbol
/// collision in full, and was a demonstrated route to `⊢ ⊥`.
///
/// `fetch_update` leaves the counter untouched when its closure returns `None`,
/// so exhaustion becomes a permanent latch rather than a gate that opens once.
/// A panic is not a fence — it is catchable safe Rust — so the guard has to
/// make the bad state unreachable, not merely announce it.
fn next_brand(counter: &core::sync::atomic::AtomicU32) -> u32 {
    use core::sync::atomic::Ordering::Relaxed;
    counter
        .fetch_update(Relaxed, Relaxed, |n| n.checked_add(1))
        .expect("environment brand counter exhausted")
        + 1
}

impl Default for Env {
    fn default() -> Self { Self::new() }
}

impl Env {
    /// An empty signature, with a brand distinct from every other `Env`.
    pub fn new() -> Self {
        let brand = next_brand(&NEXT_BRAND);
        Env { brand, next_sym: 0, vars: VarGen::new(brand) }
    }

    /// Introduce a fresh function symbol of the given arity, constrained by no
    /// axioms. Conservative by construction; see the type-level docs.
    pub fn declare(&mut self, arity: u32) -> FnSym {
        let id = self.next_sym;
        self.next_sym = self.next_sym.checked_add(1).expect("function symbol counter overflow");
        FnSym { brand: self.brand, id, arity }
    }

    /// A variable distinct from all others produced by this environment.
    pub fn fresh_var(&mut self) -> FreeVar { self.vars.fresh() }
}

// ─────────────────────────────────────────────────────────────────────────────
// Primitive rules — the trusted core.
//
// The propositional fragment is the standard Łukasiewicz axiomatisation, which
// is complete for classical propositional logic; the quantifier fragment adds
// instantiation and the distribution axiom; equality adds reflexivity and
// Leibniz. All are valid under the usual Tarskian semantics.
// ─────────────────────────────────────────────────────────────────────────────

impl Thm {
    /// Primitive rule (A1): `φ → (ψ → φ)`.
    pub fn ax_k(phi: Formula, psi: Formula) -> Thm {
        Thm::mk(Formula::imp(phi.clone(), Formula::imp(psi, phi)))
    }

    /// Primitive rule (A2): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`.
    pub fn ax_s(phi: Formula, psi: Formula, chi: Formula) -> Thm {
        let left = Formula::imp(phi.clone(), Formula::imp(psi.clone(), chi.clone()));
        let right = Formula::imp(Formula::imp(phi.clone(), psi), Formula::imp(phi, chi));
        Thm::mk(Formula::imp(left, right))
    }

    /// Primitive rule (A3), classical: `(¬φ → ¬ψ) → (ψ → φ)`.
    ///
    /// This is what makes the logic classical, which the target theory requires.
    pub fn ax_contra(phi: Formula, psi: Formula) -> Thm {
        let left = Formula::imp(Formula::not(phi.clone()), Formula::not(psi.clone()));
        Thm::mk(Formula::imp(left, Formula::imp(psi, phi)))
    }

    /// Primitive rule (A4), universal instantiation: `(∀x. φ) → φ[t/x]`.
    ///
    /// No "substitutable for" side condition is needed here, unlike in a named
    /// representation: `t` is locally closed by construction and the bound
    /// occurrences it replaces are de Bruijn indices, so capture is impossible.
    /// That side condition is exactly the one that classically goes wrong, and
    /// the representation has removed it rather than checked it.
    ///
    /// Returns `None` if `phi` is not universally quantified.
    pub fn ax_inst(phi: Formula, t: Term) -> Option<Thm> {
        let body = phi.instantiate(&t)?;
        Some(Thm::mk(Formula::imp(phi, body)))
    }

    /// Primitive rule (A5), distribution: `(∀x. (φ → ψ)) → (φ → ∀x. ψ)`,
    /// **provided `x` does not occur free in `φ`**.
    ///
    /// This is the other classic side condition, and here it is real and must be
    /// checked: without it one could derive `(∀x. x=x → P(x)) → (x=x → ∀x. P(x))`
    /// and generalise a variable that is still constrained. Returns `None` when
    /// the condition fails.
    pub fn ax_dist(x: FreeVar, phi: Formula, psi: Formula) -> Option<Thm> {
        if phi.occurs_free(x) {
            return None
        }
        let left = Formula::forall(x, Formula::imp(phi.clone(), psi.clone()));
        let right = Formula::imp(phi, Formula::forall(x, psi));
        Some(Thm::mk(Formula::imp(left, right)))
    }

    /// Primitive rule, assumption: `{φ} ⊢ φ`.
    ///
    /// Valid by inspection: under any assignment satisfying `{φ}`, `φ` holds.
    /// It is the only rule that *introduces* a hypothesis, and it asserts
    /// nothing about `φ` — the hypothesis and the conclusion are the same
    /// formula, so no assignment can make the sequent false.
    ///
    /// `φ` may mention free variables, and they are read universally like every
    /// other free variable in the kernel: `{φ(x)} ⊢ φ(x)` asserts `∀x. (φ(x) →
    /// φ(x))`. It does **not** fix `x` to some particular object satisfying
    /// `φ`, which is why this rule is not an existential elimination and why
    /// [`Thm::gen`] must still refuse to quantify `x` while `φ(x)` is assumed.
    ///
    /// Builds the struct directly rather than going through `mk_hyps`: a
    /// one-element vector is sorted and duplicate-free whatever `φ` is, so the
    /// canonicality invariant holds with nothing to do.
    pub fn assume(phi: Formula) -> Thm { Thm { hyps: vec![phi.clone()], concl: phi } }

    /// Primitive rule, discharge: from `Γ ⊢ φ` infer `Γ ∖ {h} ⊢ h → φ`.
    ///
    /// The deduction theorem as a rule rather than as a metatheorem. Valid under
    /// the reading in the module docs: take any assignment satisfying `Γ ∖ {h}`.
    /// If it also satisfies `h` then it satisfies all of `Γ`, so `φ` holds and
    /// hence `h → φ`; if it does not satisfy `h`, then `h → φ` holds vacuously.
    /// Either way `h → φ` holds, which is the conclusion.
    ///
    /// **`h` need not be among the hypotheses**, and this is total rather than
    /// fallible for that reason. If `h ∉ Γ` the set is unchanged and the
    /// argument above still goes through — the second branch does not use
    /// `h ∈ Γ` and the first does not need it. So the rule silently *weakens*
    /// instead of rejecting. That is Isabelle's `implies_intr` and it is sound;
    /// a caller who wanted the hypothesis gone should check [`Thm::hyps`],
    /// because this rule will not tell them it was never there.
    pub fn implies_intr(h: &Formula, thm: &Thm) -> Thm {
        let rest = thm.hyps.iter().filter(|g| *g != h).cloned().collect();
        Thm::mk_hyps(rest, Formula::imp(h.clone(), thm.concl.clone()))
    }

    /// Primitive rule, modus ponens: from `Γ ⊢ φ → ψ` and `Δ ⊢ φ` infer
    /// `Γ ∪ Δ ⊢ ψ`.
    ///
    /// The union is the whole reason hypotheses are carried *beside* the
    /// formula rather than encoded as antecedents inside it: it is one merge of
    /// two sorted lists, and the two premises are used unchanged. Encoding the
    /// same thing as `⋀Γ → φ → ψ` would require re-proving both premises
    /// against `⋀(Γ ∪ Δ)` first, which is `O(|Γ ∪ Δ|)` kernel calls per step.
    ///
    /// Soundness: at any assignment satisfying `Γ ∪ Δ` both premises apply,
    /// giving `φ → ψ` and `φ`, hence `ψ`. Note this needs both premises to be
    /// read at the *same* assignment, which is exactly what the universal
    /// reading of free variables provides.
    ///
    /// Returns `None` if the premises do not line up — a mismatch is a bug in
    /// the untrusted caller, and rejecting is the correct response.
    pub fn mp(imp: &Thm, arg: &Thm) -> Option<Thm> {
        match imp.concl.data() {
            FormulaData::Imp(a, b) if *a == arg.concl =>
                Some(Thm::mk_hyps(imp.hyps.iter().chain(&arg.hyps).cloned().collect(), b.clone())),
            _ => None,
        }
    }

    /// Primitive rule, generalisation: from `Γ ⊢ φ` infer `Γ ⊢ ∀x. φ`,
    /// **provided `x` is free in no member of `Γ`**.
    ///
    /// # The side condition is real, and it is the classic one
    ///
    /// From `{x ∈ y} ⊢ x ∈ y` one must **not** conclude `{x ∈ y} ⊢ ∀x. x ∈ y`.
    /// The premise says every assignment making `x ∈ y` true makes `x ∈ y`
    /// true; the conclusion would say every such assignment makes *everything* a
    /// member of `y`, which is false in any model with a two-element set. The
    /// condition `x ∉ FV(Γ)` is what separates the two: with `x` absent from
    /// every hypothesis, the assignments satisfying `Γ` are closed under
    /// changing `x`, so `φ` holding at all of them is `∀x. φ` holding at all of
    /// them.
    ///
    /// Until hypotheses existed this rule was unconditional, and the module
    /// header argued at length that the condition was not merely unchecked but
    /// *vacuous*, there being no `Γ` for `x` to be free in. That argument was
    /// correct then and is **false now**. It survives in exactly one place — the
    /// module header, quoted once and marked as retracted — because a retired
    /// soundness argument left standing beside the code it no longer justifies
    /// is how the next reader deletes the check.
    ///
    /// The condition remains vacuous on hypothesis-free theorems, so this rule
    /// behaves exactly as before on every derivation written against the old
    /// kernel — the check simply never fires. That is the sense in which the
    /// change is backward compatible, and it is also why this rule can keep its
    /// infallible signature: see [`Thm::gen_checked`].
    ///
    /// # Panics
    ///
    /// If `x` is free in a hypothesis. There is no sound `Thm` to return, so
    /// the alternatives were a panic or an `Option`, and an `Option` would have
    /// changed the signature that ~500 existing call sites use. Callers holding
    /// a theorem with hypotheses should use [`Thm::gen_checked`]; callers whose
    /// theorem has none — every caller written before this rule gained a side
    /// condition — cannot reach the panic.
    pub fn gen(x: FreeVar, thm: &Thm) -> Thm {
        Thm::gen_checked(x, thm).expect("gen: the generalised variable is free in a hypothesis")
    }

    /// [`Thm::gen`] with the side condition reported rather than raised:
    /// `None` when `x` is free in a hypothesis.
    ///
    /// This is the primitive; `gen` is the panicking wrapper. Two entry points
    /// to one rule is not a compartment — both are trusted, and an audit must
    /// read this one, which is where the check lives.
    ///
    /// # Why the check is a scan, and not a cached `FV(Γ)`
    ///
    /// It was proposed to store `FV(Γ)` alongside `Γ` and union it in every
    /// rule, so that this becomes a set-membership test rather than a walk over
    /// every hypothesis. That was **rejected**, on three grounds:
    ///
    /// * **It is not on the hot path.** `Γ` is empty for every theorem the
    ///   checker and `derived/` build, and `[].iter().any(..)` is already free.
    ///   The scan only runs on genuinely hypothetical theorems, where the sets
    ///   observed in practice hold single digits of small formulas.
    /// * **It is not asymptotically worse than what this rule already does.**
    ///   `Formula::forall` *closes over the conclusion*, walking and
    ///   reallocating the entire conclusion tree. A walk of `Γ` alongside it is
    ///   a constant factor on a rule that is already linear in the syntax it
    ///   touches. The cost the whole hypothesis change was made to remove was
    ///   `O(|Γ ∪ Δ|)` **kernel calls** per operation, which is a different
    ///   quantity by orders of magnitude — a scan is not a kernel call.
    /// * **A cached set is a denormalised invariant in the trusted base**, and
    ///   getting the benefit requires unioning the parents' sets in every rule
    ///   rather than recomputing (which would be strictly worse than scanning).
    ///   If such a cache ever *under*-approximated `FV(Γ)`, this rule would
    ///   accept an unsound generalisation and nothing would notice. Recomputing
    ///   from `Γ` cannot drift from `Γ`.
    ///
    /// If a measurement ever shows the scan mattering, cache it — and pin the
    /// cache against a recomputation, because that is the property at risk.
    ///
    /// The result reuses `thm`'s hypothesis vector unchanged, which is already
    /// canonical; the rule alters only the conclusion.
    pub fn gen_checked(x: FreeVar, thm: &Thm) -> Option<Thm> {
        if thm.hyps.iter().any(|h| h.occurs_free(x)) {
            return None
        }
        Some(Thm { hyps: thm.hyps.clone(), concl: Formula::forall(x, thm.concl.clone()) })
    }

    /// Primitive rule, reflexivity of equality: `⊢ t = t`.
    pub fn eq_refl(t: Term) -> Thm { Thm::mk(Formula::eq(t.clone(), t)) }

    /// Primitive rule, Leibniz / substitution of equals:
    /// `⊢ a = b → (φ[a/x] → φ[b/x])`.
    ///
    /// Together with reflexivity this generates the whole equality theory —
    /// symmetry, transitivity and congruence are *derived* rather than trusted.
    ///
    /// They are not derived **below**, as this comment used to say, and nothing
    /// below this line derives anything: they live in `derived/src/lib.rs`,
    /// outside this crate and outside the trusted base. What follows in this file
    /// is the TG axioms and `define`, all of them primitive. Pointing at derived
    /// rules that are not here inflates the apparent size of the TCB, which is
    /// the wrong direction to be wrong in for a file whose whole claim is that it
    /// is small enough to read.
    ///
    /// `subst_pair` is `(phi.subst(x, &a), phi.subst(x, &b))` with the shared
    /// `close(x, 0)` computed once instead of twice — the same two formulas and
    /// the same two `locally_closed` checks, one fewer full-tree walk. See
    /// [`Formula::subst_pair`]; `PERF-REVIEW.md` F3.
    pub fn eq_leibniz(a: Term, b: Term, x: FreeVar, phi: Formula) -> Thm {
        let (phi_a, phi_b) = phi.subst_pair(x, &a, &b);
        Thm::mk(Formula::imp(Formula::eq(a, b), Formula::imp(phi_a, phi_b)))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The axioms of Tarski–Grothendieck set theory.
//
// Each is a primitive: it is asserted, not derived, and is part of the trusted
// base. Tarski's Axiom A is what supplies arbitrarily large inaccessible
// cardinals, which is what covers Lean's universe hierarchy.
// ─────────────────────────────────────────────────────────────────────────────

/// `q = {a}`, said without introducing a singleton symbol: `∀r. (r ∈ q ↔ r = a)`.
pub fn is_singleton(env: &mut Env, q: Term, a: Term) -> Formula {
    let r = env.fresh_var();
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q), Formula::eq(Term::var(r), a)))
}

/// `q = {a, b}`: `∀r. (r ∈ q ↔ (r = a ∨ r = b))`.
pub fn is_upair(env: &mut Env, q: Term, a: Term, b: Term) -> Formula {
    let r = env.fresh_var();
    let rhs = Formula::or(Formula::eq(Term::var(r), a), Formula::eq(Term::var(r), b));
    Formula::forall(r, Formula::iff(Formula::mem(Term::var(r), q), rhs))
}

/// `p = ⟨a, b⟩` in the Kuratowski sense, i.e. `p = {{a}, {a,b}}`, written as a
/// formula: `∀q. (q ∈ p ↔ (q = {a} ∨ q = {a,b}))`.
///
/// Describing pairs rather than introducing a pairing *symbol* is what lets
/// Tarski's axiom mention functions while the primitive signature stays `{∈,=}`.
pub fn is_opair(env: &mut Env, p: Term, a: Term, b: Term) -> Formula {
    let q = env.fresh_var();
    let tq = Term::var(q);
    let left = is_singleton(env, tq.clone(), a.clone());
    let right = is_upair(env, tq.clone(), a, b);
    Formula::forall(q, Formula::iff(Formula::mem(tq, p), Formula::or(left, right)))
}

/// `⟨a, b⟩ ∈ f`: `∃p. (p ∈ f ∧ p = ⟨a,b⟩)`.
pub fn pair_in(env: &mut Env, f: Term, a: Term, b: Term) -> Formula {
    let p = env.fresh_var();
    let tp = Term::var(p);
    let is_pair = is_opair(env, tp.clone(), a, b);
    Formula::exists(p, Formula::and(Formula::mem(tp, f), is_pair))
}

/// `x ≈ m` — there is a bijection from `x` onto `m`.
///
/// Spelled out as: some `f` whose pairs all run from `x` to `m`, is total on
/// `x`, is onto `m`, is single-valued, and is injective. This is the disjunct
/// whose omission made the earlier Tarski axiom inconsistent, so it is written
/// out in full rather than approximated.
pub fn equinumerous(env: &mut Env, x: Term, m: Term) -> Formula {
    let f = env.fresh_var();
    let tf = Term::var(f);

    let (a1, b1) = (env.fresh_var(), env.fresh_var());
    let in_xm = {
        let p = pair_in(env, tf.clone(), Term::var(a1), Term::var(b1));
        let concl = Formula::and(Formula::mem(Term::var(a1), x.clone()), Formula::mem(Term::var(b1), m.clone()));
        Formula::forall(a1, Formula::forall(b1, Formula::imp(p, concl)))
    };

    let (a2, b2) = (env.fresh_var(), env.fresh_var());
    let total = {
        let p = pair_in(env, tf.clone(), Term::var(a2), Term::var(b2));
        Formula::forall(a2, Formula::imp(Formula::mem(Term::var(a2), x.clone()), Formula::exists(b2, p)))
    };

    let (a3, b3) = (env.fresh_var(), env.fresh_var());
    let onto = {
        let p = pair_in(env, tf.clone(), Term::var(a3), Term::var(b3));
        Formula::forall(b3, Formula::imp(Formula::mem(Term::var(b3), m.clone()), Formula::exists(a3, p)))
    };

    let (a4, b4, c4) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let single_valued = {
        let p1 = pair_in(env, tf.clone(), Term::var(a4), Term::var(b4));
        let p2 = pair_in(env, tf.clone(), Term::var(a4), Term::var(c4));
        let concl = Formula::eq(Term::var(b4), Term::var(c4));
        Formula::forall(a4, Formula::forall(b4, Formula::forall(c4, Formula::imp(Formula::and(p1, p2), concl))))
    };

    let (a5, b5, c5) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let injective = {
        let p1 = pair_in(env, tf.clone(), Term::var(a5), Term::var(c5));
        let p2 = pair_in(env, tf.clone(), Term::var(b5), Term::var(c5));
        let concl = Formula::eq(Term::var(a5), Term::var(b5));
        Formula::forall(a5, Formula::forall(b5, Formula::forall(c5, Formula::imp(Formula::and(p1, p2), concl))))
    };

    let body = Formula::and(in_xm, Formula::and(total, Formula::and(onto, Formula::and(single_valued, injective))));
    Formula::exists(f, body)
}

/// `a` is non-empty: `∃w. w ∈ a`.
///
/// The guard on the last clause of [`Thm::ax_choice`]. Nothing can pick a
/// member of the empty set, so the choice clause has to be restricted, and this
/// is the restriction — stated positively rather than as `a ≠ ∅`, because there
/// is no `∅` in the kernel's signature to compare against.
pub fn nonempty(env: &mut Env, a: Term) -> Formula {
    let w = env.fresh_var();
    Formula::exists(w, Formula::mem(Term::var(w), a))
}

/// `f` is a choice function on `x` — the body of [`Thm::ax_choice`], at terms.
///
/// ```text
///   (∀p. p ∈ f → ∃a ∃b. (a ∈ x ∧ p = ⟨a,b⟩))              — a graph over x
/// ∧ (∀a ∀b ∀c. ((⟨a,b⟩ ∈ f ∧ ⟨a,c⟩ ∈ f) → b = c))         — single-valued
/// ∧ (∀a. a ∈ x → ∃b. ⟨a,b⟩ ∈ f)                           — total on x
/// ∧ (∀a ∀b. (((a ∈ x ∧ ∃w. w ∈ a) ∧ ⟨a,b⟩ ∈ f) → b ∈ a))  — picks a member
/// ```
///
/// The first three clauses are exactly "`f` is a function with domain `x`" —
/// the first bounds the domain, the third fills it, the second makes it
/// single-valued — and the fourth is the choice property, guarded by
/// [`nonempty`]. Ordered pairs are *described*, via [`is_opair`] and
/// [`pair_in`], exactly as in [`equinumerous`]; nothing is added to the
/// signature `{∈,=}`.
///
/// Exposed so that a caller carrying the hypothesis `IsChoiceFn(f,u)` can build
/// **the same formula** the axiom's existential is about. Rebuilding it
/// independently would risk an antecedent that no instance of the axiom
/// discharges.
pub fn is_choice_fn(env: &mut Env, f: Term, x: Term) -> Formula {
    // ∀p. (p ∈ f → ∃a ∃b. (a ∈ x ∧ p = ⟨a,b⟩))
    let (p1, a1, b1) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let graph = {
        let is_pair = is_opair(env, Term::var(p1), Term::var(a1), Term::var(b1));
        let body = Formula::and(Formula::mem(Term::var(a1), x.clone()), is_pair);
        let witness = Formula::exists(a1, Formula::exists(b1, body));
        Formula::forall(p1, Formula::imp(Formula::mem(Term::var(p1), f.clone()), witness))
    };

    // ∀a ∀b ∀c. ((⟨a,b⟩ ∈ f ∧ ⟨a,c⟩ ∈ f) → b = c)
    let (a2, b2, c2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let single_valued = {
        let ab = pair_in(env, f.clone(), Term::var(a2), Term::var(b2));
        let ac = pair_in(env, f.clone(), Term::var(a2), Term::var(c2));
        let concl = Formula::eq(Term::var(b2), Term::var(c2));
        Formula::forall(a2, Formula::forall(b2, Formula::forall(c2, Formula::imp(Formula::and(ab, ac), concl))))
    };

    // ∀a. (a ∈ x → ∃b. ⟨a,b⟩ ∈ f)
    let (a3, b3) = (env.fresh_var(), env.fresh_var());
    let total = {
        let ab = pair_in(env, f.clone(), Term::var(a3), Term::var(b3));
        Formula::forall(a3, Formula::imp(Formula::mem(Term::var(a3), x.clone()), Formula::exists(b3, ab)))
    };

    // ∀a ∀b. (((a ∈ x ∧ ∃w. w ∈ a) ∧ ⟨a,b⟩ ∈ f) → b ∈ a)
    let (a4, b4) = (env.fresh_var(), env.fresh_var());
    let chooses = {
        let ne = nonempty(env, Term::var(a4));
        let ab = pair_in(env, f.clone(), Term::var(a4), Term::var(b4));
        let hyp = Formula::and(Formula::and(Formula::mem(Term::var(a4), x), ne), ab);
        let concl = Formula::mem(Term::var(b4), Term::var(a4));
        Formula::forall(a4, Formula::forall(b4, Formula::imp(hyp, concl)))
    };

    Formula::and(graph, Formula::and(single_valued, Formula::and(total, chooses)))
}

/// `x ⊆ y`, i.e. `∀z. z ∈ x → z ∈ y`.
pub fn subset(env: &mut Env, x: Term, y: Term) -> Formula {
    let z = env.fresh_var();
    Formula::forall(z, Formula::imp(Formula::mem(Term::var(z), x), Formula::mem(Term::var(z), y)))
}

impl Thm {
    /// Extensionality: `∀x ∀y. (∀z. z ∈ x ↔ z ∈ y) → x = y`.
    pub fn ax_extensionality(env: &mut Env) -> Thm {
        let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
        let same = Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), tx.clone()), Formula::mem(tz, ty.clone())));
        Thm::mk(Formula::forall(x, Formula::forall(y, Formula::imp(same, Formula::eq(tx, ty)))))
    }

    // ── The empty set is *not* an axiom ──────────────────────────────────────
    //
    // `ax_empty` asserted `∃e ∀z. ¬(z ∈ e)` and was **deleted on 2026-07-31**,
    // taking the set axioms from eight to seven. Do not reinstate it.
    //
    // Its justification was: "deriving `∅` needs the recursion theorem and a
    // transitive closure, because Tarski's universes are not transitive — from
    // `w ∈ y ∈ u` its clauses give only `{w} ∈ u`, never `w`." The transitivity
    // clause `C₁` added to `ax_tarski` the same day is *precisely*
    // `w ∈ y ∈ u → w ∈ u`, so that premise no longer holds and `∅` falls out in
    // a few steps:
    //
    //   1. `ax_tarski` at any `x` gives a `u` with `x ∈ u`, so `u` is non-empty.
    //   2. `ax_regularity` at `u` gives `y ∈ u` with no member in common with
    //      `u`.
    //   3. `C₁` gives `∀z. (z ∈ y → z ∈ u)`.
    //   4. So `∀z. ¬(z ∈ y)`, and `y` witnesses `∃e ∀z. ¬(z ∈ e)`.
    //
    // That is `derived::empty::empty_existence`, whose conclusion was checked
    // equal to this axiom's before the axiom was removed;
    // `derived::empty::empty` is built on it and `derived/tests/empty.rs` pins
    // the resulting `⊢ ∀z. ¬(z ∈ ∅)`. Uniqueness never needed asserting either:
    // it follows from Extensionality, which is what lets `define` introduce the
    // symbol.

    /// Pairing: `∀x ∀y ∃p ∀z. z ∈ p ↔ (z = x ∨ z = y)`.
    pub fn ax_pairing(env: &mut Env) -> Thm {
        let (x, y, p, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, ty, tp, tz) = (Term::var(x), Term::var(y), Term::var(p), Term::var(z));
        let rhs = Formula::or(Formula::eq(tz.clone(), tx), Formula::eq(tz.clone(), ty));
        let inner = Formula::forall(z, Formula::iff(Formula::mem(tz, tp), rhs));
        Thm::mk(Formula::forall(x, Formula::forall(y, Formula::exists(p, inner))))
    }

    /// Union: `∀x ∃u ∀z. z ∈ u ↔ ∃y. (y ∈ x ∧ z ∈ y)`.
    pub fn ax_union(env: &mut Env) -> Thm {
        let (x, u, z, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, tu, tz, ty) = (Term::var(x), Term::var(u), Term::var(z), Term::var(y));
        let witness = Formula::exists(y, Formula::and(Formula::mem(ty.clone(), tx), Formula::mem(tz.clone(), ty)));
        let inner = Formula::forall(z, Formula::iff(Formula::mem(tz, tu), witness));
        Thm::mk(Formula::forall(x, Formula::exists(u, inner)))
    }

    /// Power set: `∀x ∃p ∀z. z ∈ p ↔ z ⊆ x`.
    pub fn ax_power(env: &mut Env) -> Thm {
        let (x, p, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, tp, tz) = (Term::var(x), Term::var(p), Term::var(z));
        let sub = subset(env, tz.clone(), tx);
        let inner = Formula::forall(z, Formula::iff(Formula::mem(tz, tp), sub));
        Thm::mk(Formula::forall(x, Formula::exists(p, inner)))
    }

    /// Regularity: every non-empty set has an `∈`-minimal element.
    /// `∀x. (∃y. y ∈ x) → ∃y. (y ∈ x ∧ ¬∃z. (z ∈ y ∧ z ∈ x))`.
    pub fn ax_regularity(env: &mut Env) -> Thm {
        let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tx, ty, tz) = (Term::var(x), Term::var(y), Term::var(z));
        let nonempty = Formula::exists(y, Formula::mem(ty.clone(), tx.clone()));
        let clash = Formula::exists(z, Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz, tx.clone())));
        let minimal = Formula::exists(y, Formula::and(Formula::mem(ty, tx), Formula::not(clash)));
        Thm::mk(Formula::forall(x, Formula::imp(nonempty, minimal)))
    }

    /// Replacement, as a scheme. For a relation `φ(x, y)` supplied by the caller
    /// as a formula with two designated free variables:
    ///
    /// `∀a. (∀x. x ∈ a → ∃!y. φ) → ∃b ∀y. (y ∈ b ↔ ∃x. (x ∈ a ∧ φ))`
    ///
    /// Being a scheme, this is instantiated per-formula rather than quantified
    /// over relations, which first-order logic cannot do.
    pub fn ax_replacement(env: &mut Env, x: FreeVar, y: FreeVar, phi: Formula) -> Option<Thm> {
        // `x` and `y` must be distinct, and neither may collide with the
        // variables this scheme generates for itself.
        //
        // Without the `x ≠ y` check the scheme is **unsound**. With `x == y`,
        // the image `∃x. (x ∈ a ∧ φ)` closes over `y` as well, so the right-hand
        // side of the `↔` no longer mentions the quantified variable and the
        // conclusion degenerates to `∃b ∀y. (y ∈ b ↔ <y-free>)` — a universal
        // set whenever that formula holds, which Regularity refutes.
        //
        // The generated-variable checks defend against a caller supplying `x` or
        // `y` from a *different* generator, where freshness relative to this
        // `Env` is not guaranteed; a collision there lets `a`, `b` or `y2` be
        // captured, with the same effect.
        if x == y {
            return None
        }
        let (a, b, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        for v in [a, b, y2] {
            if v == x || v == y || phi.occurs_free(v) {
                return None
            }
        }
        let (ta, tb) = (Term::var(a), Term::var(b));
        let (tx, ty) = (Term::var(x), Term::var(y));

        // ∃!y. φ, spelled by the one function that spells it — see
        // [`exists_unique_at`]. `y2` is passed in rather than drawn there
        // because it is the variable checked against `x`, `y` and `φ` above.
        let uniq = exists_unique_at(y, y2, &phi);
        let hyp = Formula::forall(x, Formula::imp(Formula::mem(tx.clone(), ta.clone()), uniq));

        let image = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
        let concl = Formula::exists(b, Formula::forall(y, Formula::iff(Formula::mem(ty, tb), image)));

        Some(Thm::mk(Formula::forall(a, Formula::imp(hyp, concl))))
    }

    // ── Tarski's Axiom A ─────────────────────────────────────────────────────
    //
    // An earlier version of this stated the inaccessibility clause as
    // `∀y. (y ⊆ u → y ∈ u)`, dropping the `y ≈ u` disjunct. That was
    // **inconsistent**: at `y := u` the derivable `u ⊆ u` forces `u ∈ u`, which
    // Regularity refutes. Weakening a disjunction by dropping a disjunct
    // *strengthens* the axiom. See `kernel/tests/tarski_regression.rs`.
    //
    // What follows is the standard Tarski–Grothendieck statement, with the
    // disjunct restored. Equinumerosity is spelled out as a first-order formula
    // over `∈` and `=` — ordered pairs are *described*, not introduced as
    // symbols — so this adds no primitives.

    /// Tarski's Axiom A **strengthened with transitivity**: every set belongs to
    /// a Grothendieck universe.
    ///
    /// `∀x ∃u.  x ∈ u`
    /// ` ∧ (∀y ∈ u. ∀z ∈ y. z ∈ u)`            — transitive
    /// ` ∧ (∀y ∈ u. ∀z ⊆ y. z ∈ u)`            — closed under subsets of members
    /// ` ∧ (∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p)`    — power sets stay inside
    /// ` ∧ (∀y ⊆ u. (y ≈ u ∨ y ∈ u))`          — inaccessibility
    ///
    /// # Why the transitivity clause is here
    ///
    /// Tarski's Axiom A alone does **not** entail transitivity, and a Tarski
    /// universe that lacks it is not a Grothendieck universe. This is not a
    /// technicality: it is the single missing step behind every closure property
    /// the interpretation needs. `f ∈ fs(B(a), u) ∈ u` gives `f ∈ u` only by
    /// transitivity, and without that step `U(x)` is closed under neither `⋃`,
    /// binary union, products, nor function spaces — all four are *refutable*,
    /// by the countermodels recorded at the end of `derived/src/universe.rs`.
    /// Three separate constructions were blocked by its absence before it was
    /// added.
    ///
    /// It is also what the model we are implementing actually assumes. Carneiro
    /// (*The Type Theory of Lean*, §6.2) sets `U₀ = {∅,{•}}` and `U_{n+1} = V_{κₙ}`
    /// — levels of the cumulative hierarchy, transitive by construction — and its
    /// closure proofs are rank arguments that do not survive in a non-transitive
    /// set.
    ///
    /// **This costs no consistency strength.** For `κ` inaccessible, `V_κ`
    /// satisfies all five clauses, so the strengthened axiom is equiconsistent
    /// with the original — which is in turn equivalent to "there are arbitrarily
    /// large inaccessibles", exactly what the thesis assumes.
    ///
    /// # Why a fifth conjunct rather than a rewrite
    ///
    /// Because the other four clauses all stay. In particular the inaccessibility
    /// clause `C₄` is **not** optional: the thesis requires each `κₙ` to be
    /// inaccessible — "the cofinality of `κₖ` is `κₖ`" (§6.2) — and its closure
    /// proofs use that cofinality directly, `cf(λ) > sup_{x∈A}|B(x)|` for
    /// W-types and the rank-bounding argument for `Π`. Since nothing is being
    /// removed, a rewrite would only restate the same content in a shape further
    /// from the reference statement, in the one file where distance from a
    /// reference statement has already caused an inconsistency.
    ///
    /// # A note on choice, to forestall a wrong inference
    ///
    /// Tarski's Axiom A is known to imply AC, but **that fact is not used here
    /// and is not available to this development**: it is a theorem about the
    /// intended model, not something derived in this kernel. Choice is therefore
    /// asserted separately, as [`Thm::ax_choice`] — see the note there for why
    /// that costs no consistency strength, and why it is *set*-sized choice
    /// rather than global choice on `V`.
    ///
    /// This is what supplies arbitrarily large inaccessible cardinals, and
    /// hence what covers Lean's universe hierarchy. It is also the intended
    /// source of the empty set: a Grothendieck universe contains one, and
    /// without it Separation is not derivable from the other axioms.
    ///
    /// **Trusted.** Read it against a reference statement rather than against
    /// intuition; the previous version looked plausible and was contradictory.
    pub fn ax_tarski(env: &mut Env) -> Thm {
        let (x, u) = (env.fresh_var(), env.fresh_var());
        let (tx, tu) = (Term::var(x), Term::var(u));

        // ∀y ∈ u. ∀z ⊆ y. z ∈ u
        let (y1, z1) = (env.fresh_var(), env.fresh_var());
        let (ty1, tz1) = (Term::var(y1), Term::var(z1));
        let sub_z1y1 = subset(env, tz1.clone(), ty1.clone());
        let closed_sub = Formula::forall(
            y1,
            Formula::imp(
                Formula::mem(ty1, tu.clone()),
                Formula::forall(z1, Formula::imp(sub_z1y1, Formula::mem(tz1, tu.clone()))),
            ),
        );

        // ∀y ∈ u. ∃p ∈ u. ∀z ⊆ y. z ∈ p
        let (y2, z2, p2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (ty2, tz2, tp2) = (Term::var(y2), Term::var(z2), Term::var(p2));
        let sub_z2y2 = subset(env, tz2.clone(), ty2.clone());
        let closed_pow = Formula::forall(
            y2,
            Formula::imp(
                Formula::mem(ty2, tu.clone()),
                Formula::exists(
                    p2,
                    Formula::and(
                        Formula::mem(tp2.clone(), tu.clone()),
                        Formula::forall(z2, Formula::imp(sub_z2y2, Formula::mem(tz2, tp2))),
                    ),
                ),
            ),
        );

        // ∀y ⊆ u. (y ≈ u ∨ y ∈ u)
        let y3 = env.fresh_var();
        let ty3 = Term::var(y3);
        let sub_y3u = subset(env, ty3.clone(), tu.clone());
        let equi = equinumerous(env, ty3.clone(), tu.clone());
        let inacc = Formula::forall(
            y3,
            Formula::imp(sub_y3u, Formula::or(equi, Formula::mem(ty3, tu.clone()))),
        );

        // ∀y ∈ u. ∀z ∈ y. z ∈ u   — transitivity.
        //
        // Read this against a reference statement, not against intuition: it is
        // the clause that distinguishes a Grothendieck universe from a Tarski
        // one, and its absence was invisible for a long time because the doc
        // comment above claimed it. Note it is `z ∈ y`, *not* `z ⊆ y` — the
        // subset form is the separate `closed_sub` clause below, and confusing
        // the two would leave the axiom exactly as weak as it was.
        let (y0, z0) = (env.fresh_var(), env.fresh_var());
        let (ty0, tz0) = (Term::var(y0), Term::var(z0));
        let transitive = Formula::forall(
            y0,
            Formula::imp(
                Formula::mem(ty0.clone(), tu.clone()),
                Formula::forall(z0, Formula::imp(Formula::mem(tz0.clone(), ty0), Formula::mem(tz0, tu.clone()))),
            ),
        );

        let body = Formula::and(
            Formula::mem(tx, tu),
            Formula::and(transitive, Formula::and(closed_sub, Formula::and(closed_pow, inacc))),
        );
        Thm::mk(Formula::forall(x, Formula::exists(u, body)))
    }

    // ── The axiom of choice ──────────────────────────────────────────────────
    //
    // Read against Jech, *Set Theory* (3rd millennium ed.), §1 "The Axiom of
    // Choice": *"Every family of nonempty sets has a choice function"*, and its
    // first-order form `∀X ∃f. (f is a function ∧ dom f = X ∧ ∀A ∈ X. (A ≠ ∅ →
    // f(A) ∈ A))`. Kunen, *Set Theory* (2011), I.12.1 states the same shape.
    // The `A ≠ ∅` guard is not decoration: `f(∅) ∈ ∅` is refutable, so a version
    // without it is **inconsistent** — the same failure mode as the `ax_tarski`
    // bug, a clause that looks plausible and is not satisfiable.
    //
    // Functions are *described*, not introduced as symbols, exactly as in
    // `equinumerous`; the signature stays `{∈,=}` and no primitive is added.

    /// The axiom of choice: `∀X ∃f. IsChoiceFn(f, X)`.
    ///
    /// `IsChoiceFn` is [`is_choice_fn`], spelled out there in full: `f` is a
    /// function with domain `X` such that `f(x) ∈ x` for every **non-empty**
    /// `x ∈ X`.
    ///
    /// # Why this axiom, in this form
    ///
    /// Carneiro's model interprets Lean's `Classical.choice` by fixing "a choice
    /// function `ε` on `U_ω`, that is, a function such that `ε(x) ∈ x` for all
    /// `x ∈ U_ω`" (*The Type Theory of Lean*, §6.2), and applies it only at
    /// **non-empty** members: the soundness case for `choice` (§6.3) reads "`h̄ ∈
    /// [ᾱ ≠ ∅]`, so `ᾱ ≠ ∅` … `ε(ᾱ) ∈ ᾱ`". Taken literally the §6.2 sentence is
    /// unsatisfiable — `∅ ∈ U_ω` and nothing is a member of `∅` — so the guard
    /// below is what the model actually needs, not a weakening of it.
    ///
    /// `U_ω` is a *set*, so this is ordinary set-sized choice. **Global** choice
    /// (a proper-class choice function on `V`) is explicitly *not* taken: the
    /// thesis needs it only for a sharper Werner-style consistency bound (§1.2,
    /// "we would have to assume an axiom of global choice in ZFC … to interpret
    /// Lean's choice axiom" — for `ZFC_n ⊢ Con(CIC_{n+1})`, which is not the
    /// result being implemented), and it would raise the consistency strength.
    ///
    /// # Consistency strength
    ///
    /// None added. `V_κ` for `κ` inaccessible models ZFC, so every model
    /// witnessing the existing axioms models this one too. Indeed Tarski's Axiom
    /// A already *implies* AC, so this axiom is in principle redundant — but
    /// only in principle: that implication is a substantial theorem (well-ordering
    /// via the universe hierarchy) that this development has not derived and has
    /// no near-term route to. It is asserted here rather than proved, and the
    /// honest accounting is that the trusted base grows by one item while the
    /// theory grows by nothing.
    ///
    /// **Trusted.** Read it against the reference statement quoted above rather
    /// than against intuition.
    pub fn ax_choice(env: &mut Env) -> Thm {
        let (x, f) = (env.fresh_var(), env.fresh_var());
        let body = is_choice_fn(env, Term::var(f), Term::var(x));
        Thm::mk(Formula::forall(x, Formula::exists(f, body)))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Conservative definitional extension.
// ─────────────────────────────────────────────────────────────────────────────

/// **The** spelling of `∃!y. φ`: `∃y. (φ ∧ ∀y'. (φ[y'/y] → y' = y))`, at an
/// explicitly supplied `y'`.
///
/// There is exactly one of these on purpose. `∃!` appears in two trusted places
/// — the antecedent of [`Thm::ax_replacement`] and the obligation [`define`]
/// requires — and two independent spellings of one notion in a file where every
/// line is trusted is a divergence waiting to happen: the day they drift, a
/// witness that discharges one stops discharging the other, or worse, the
/// replacement scheme's antecedent quietly weakens.
///
/// `y'` is a parameter rather than drawn from an `Env` here because
/// `ax_replacement` must use the variable it has itself checked against `x`,
/// `y` and `φ`; [`exists_unique`] draws a fresh one and delegates.
///
/// The choice of `y'` is invisible in the result, provided it is fresh: the
/// locally nameless representation makes alpha-equivalent formulas
/// *syntactically* equal, so two calls with different fresh variables produce
/// the same formula. That is what lets [`define`] compare a caller's witness
/// against the statement it expects without any alpha-comparison.
fn exists_unique_at(y: FreeVar, y2: FreeVar, phi: &Formula) -> Formula {
    let uniq = Formula::forall(y2, Formula::imp(phi.subst(y, &Term::var(y2)), Formula::eq(Term::var(y2), Term::var(y))));
    Formula::exists(y, Formula::and(phi.clone(), uniq))
}

/// The statement `∃!y. φ`, at a variable freshly drawn from `env`.
///
/// A thin wrapper over [`exists_unique_at`], which is where the notion is
/// actually spelled.
pub fn exists_unique(env: &mut Env, y: FreeVar, phi: &Formula) -> Formula {
    exists_unique_at(y, env.fresh_var(), phi)
}

/// Universally quantify `body` over `xs`, outermost first.
fn close_all(xs: &[FreeVar], body: Formula) -> Formula {
    xs.iter().rev().fold(body, |acc, x| Formula::forall(*x, acc))
}

/// **Primitive: definitional extension.**
///
/// Given a proof of `⊢ ∀x⃗. ∃!y. φ(x⃗, y)`, introduce a fresh function symbol
/// `f` of arity `|x⃗|` and return its defining axiom `⊢ ∀x⃗. φ(x⃗, f(x⃗))`.
///
/// # Why this is conservative
///
/// This is the standard theorem on extension by definitions. Any model of the
/// base theory satisfies `∀x⃗ ∃!y. φ`, so it can be expanded — uniquely — to
/// interpret `f` as the function picking that `y`. Hence every model expands,
/// nothing new is provable in the base language, and consistency is preserved.
///
/// # Why uniqueness is required — and what would *not* go wrong without it
///
/// An earlier version of this comment said that "without uniqueness the symbol
/// would be a choice function and the extension would no longer be
/// conservative". **That is false**, and it matters, because it makes a policy
/// choice look like a theorem. Skolemising a proved `⊢ ∀x⃗ ∃y. φ` *is*
/// conservative: every model of the base theory expands by choosing some witness
/// per tuple, so every base-language consequence of the extension holds in all
/// models of the base theory and is therefore provable in it. That is the
/// standard Skolem-expansion lemma (Shoenfield §4.6; Hodges §3.1).
///
/// **But that lemma does not transfer to this kernel at arity ≥ 1, and the
/// paragraph that used to sit here invited a soundness bug.** It said adding a
/// Skolemising `define_choice` "would be a real option". It would not.
///
/// The reason is [`Thm::ax_replacement`], which accepts an **arbitrary
/// `Formula`** — including one mentioning a symbol introduced by `define`. That
/// is sound today *precisely because* `∃!`-defined symbols are **eliminable**:
/// every extended-scheme instance paraphrases back into the base language and is
/// therefore already derivable. A Skolem symbol is conservative for the base
/// schemes but is **not** eliminable, and a model expanded by an arbitrary
/// Skolem function need not satisfy Replacement for formulas mentioning it — the
/// function need not be amenable. So `define_choice` at arity ≥ 1 would be a
/// genuine unsoundness, not a trade.
///
/// So the `∃!` requirement is load-bearing for **soundness of the interaction
/// with the schemes**, which is stronger than the two reasons previously given
/// here. Those remain true and remain secondary:
///
/// * **Eliminability**, which is what makes the scheme interaction sound above.
/// * **No metatheoretic choice**: the Skolem argument picks a witness per tuple,
///   i.e. uses AC in the metatheory; the `∃!` version does not.
///
/// A choice function is never unique, so `Classical.choice` cannot come through
/// this primitive — see [`Thm::ax_choice`]. The safe replacement is **not**
/// Skolemisation but a **0-ary Henkin constant**: from `⊢ ∃y. φ` with
/// `FV(φ) ⊆ {y}`, mint a fresh constant `c` and conclude `⊢ φ(c)`. That *is*
/// conservative including the schemes, because a constant is a parameter — an
/// `ax_replacement` instance mentioning `c` is derivable by proving it at a fresh
/// free variable, generalising, and instantiating at `c`. No metatheoretic choice
/// is needed to expand a model by one witness. It is not implemented here.
///
/// Returns `None` if the witness does not prove precisely the expected
/// statement. Rejecting is right: a mismatch means the caller has not
/// discharged the obligation.
pub fn define(
    env: &mut Env,
    xs: &[FreeVar],
    y: FreeVar,
    phi: Formula,
    witness: &Thm,
) -> Option<(FnSym, Thm)> {
    // The witness must be **unconditional**.
    //
    // Without this the extension is unsound, and it is unsound in exactly the
    // shape of this project's SECOND SOUNDNESS BUG. `define` mints a symbol and
    // returns an axiom carrying *no* hypotheses; a witness proving only
    // `Γ ⊢ ∀x⃗. ∃!y. φ` would have its `Γ` silently dropped, so a symbol whose
    // defining property was established only under an assumption would be
    // asserted to have it outright. Concretely, `{∀x. x = c} ⊢ ∃!y. y = c` is
    // provable, and dropping the hypothesis gives `⊢ f = c` unconditionally.
    //
    // The conservativity argument below says the same thing model-theoretically:
    // it expands *every* model of the base theory using `∀x⃗ ∃!y. φ`, and a model
    // that fails `Γ` supplies no such `y` to interpret `f` by.
    //
    // Rejecting rather than absorbing `Γ` into the conclusion is deliberate. The
    // absorbing version — return `Γ ⊢ ∀x⃗. φ(x⃗, f(x⃗))` — is *not* obviously
    // sound: `f` is a fresh symbol in an environment that outlives this theorem,
    // and nothing stops a caller from discharging `Γ` later and thereby claiming
    // an unconditional defining axiom for a symbol whose existence was never
    // unconditionally justified. A caller who wants that should discharge first,
    // with [`Thm::implies_intr`], and prove the `∃!` outright.
    if !witness.hyps.is_empty() {
        return None
    }
    // `y` must not be one of the parameters, or `f(x⃗)` would capture it.
    if xs.contains(&y) {
        return None
    }
    // Every free variable of `phi` must be a parameter or the defined variable.
    //
    // Without this the extension is **unsound**, not merely sloppy. Take
    // `xs = []` and `φ(y) := (y = v)` for a stray `v`. Then `∃!y. y = v` is
    // provable, and the defining axiom is `⊢ f = v` with `v` free. A free
    // variable in a context-free system is implicitly universally quantified,
    // and `gen` makes that explicit: `⊢ ∀v. f = v`. Instantiating twice gives
    // `f = c₁` and `f = c₂`, hence `c₁ = c₂` for arbitrary constants.
    //
    // The underlying error is that the witness proves "for each `v` there is a
    // unique `y`", so the `y` depends on `v` — but `f(x⃗)` has no `v` argument,
    // so the axiom claims a single `f` works for every `v`. That is strictly
    // stronger than what was proved.
    let mut fvs = Vec::new();
    phi.free_vars(&mut fvs);
    if fvs.iter().any(|v| *v != y && !xs.contains(v)) {
        return None
    }
    let expected = close_all(xs, exists_unique(env, y, &phi));
    if *witness.concl() != expected {
        return None
    }
    let arity = u32::try_from(xs.len()).ok()?;
    let f = env.declare(arity);
    let applied = Term::apply(f, xs.iter().map(|x| Term::var(*x)).collect());
    let axiom = close_all(xs, phi.subst(y, &applied));
    Some((f, Thm::mk_defining_axiom(axiom)))
}

impl Thm {
    /// Trusted: the defining axiom produced by [`define`].
    ///
    /// **This is a naming device, not a capability restriction.** An earlier
    /// version of this comment claimed it was "private to this module's
    /// definitional-extension path so it cannot be used to assert anything
    /// else". That is false. It is module-private exactly like `mk`, and any
    /// code anywhere in `thm.rs` — every rule, every axiom, any future addition
    /// — can call either one. The compartment the sentence described does not
    /// exist, and a reader who believed it would audit the wrong line: nothing
    /// here narrows what can be asserted, so the thing that actually keeps `Thm`
    /// honest is unchanged, namely that *both* constructors are private to this
    /// module and every call to either sits under a rule that says why its
    /// conclusion is valid. Adding a wrapper does not add a wall.
    ///
    /// A false claim of compartmentalisation is worse than no claim, because it
    /// invites exactly the reasoning that produced this project's worst bug: a
    /// doc comment asserting a property the code did not have.
    ///
    /// What the separate name does buy is greppability. `define`'s conclusion is
    /// not an inference-rule application but a conservative *assertion*, whose
    /// justification is the extension-by-definitions theorem rather than a
    /// semantic validity check; giving it its own spelling lets an audit
    /// enumerate every such assertion without reading each `Thm::mk` call to see
    /// which kind it is.
    fn mk_defining_axiom(f: Formula) -> Thm { Thm::mk(f) }
}

#[cfg(test)]
mod brand_tests {
    use super::next_brand;
    use core::sync::atomic::AtomicU32;

    /// Exhaustion must **latch**. The real exploit needed 2^32 `Env::new()`
    /// calls (~23s); testing the allocator against a pre-loaded counter gets
    /// the same property in microseconds.
    #[test]
    fn brand_exhaustion_is_permanent() {
        let c = AtomicU32::new(u32::MAX - 1);
        assert_eq!(next_brand(&c), u32::MAX, "last brand should still be issued");

        // Every subsequent call must panic, and must leave the counter alone —
        // a one-shot guard would wrap here and start reissuing brand 1.
        for _ in 0..3 {
            let r = std::panic::catch_unwind(|| next_brand(&c));
            assert!(r.is_err(), "brand allocation continued past exhaustion");
        }
        assert_eq!(c.load(core::sync::atomic::Ordering::Relaxed), u32::MAX, "counter wrapped");
    }

    /// Brands are distinct and never zero.
    #[test]
    fn brands_are_distinct() {
        let c = AtomicU32::new(0);
        let (a, b) = (next_brand(&c), next_brand(&c));
        assert_ne!(a, b);
        assert!(a > 0 && b > 0);
    }
}
