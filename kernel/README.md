# `kernel` — the trusted computing base

Everything in this crate must be correct. Nothing outside it does.

## Threat model

The single threat is: **a bug in Lean's kernel lets someone derive `False`.**

We are not trying to show that a translated theorem *means* what the Lean
original means. The claim is narrower and cheaper: if a whole development
translates and this kernel accepts every step, then the development proves no
contradiction. That holds as long as the translation of `False` is genuinely
refutable in the target.

So a translation bug is **not** a soundness bug — it produces a rejection, never
a false theorem. The translator may be liberal, ugly and clever. This crate may
not.

## The trusted base, itemised

Everything below has to be right. Nothing else does.

1. The axioms of Tarski–Grothendieck set theory: **extensionality, pairing,
   union, power set, regularity, the replacement scheme, Tarski's Axiom A, and
   choice** — eight in all.

   That is two fewer than the ten the brief lists, because *singleton*,
   *ordered pair* and *the empty set* are **derived** rather than assumed —
   the first two as `upair(a,a)` and `upair(upair(a,a), upair(a,b))`, the third
   as `derived::empty::empty` — while *choice*, which the brief does not list,
   is assumed.

   ### The selection rule: assert what we have not yet derived

   An earlier version of this section justified that by "the rule that anything
   constructible conservatively should be constructed". **That rule is not the
   one in force, and it does not survive scrutiny**: it invites the reader to
   conclude that the eight above are the axioms that *cannot* be constructed,
   and at least four of them can be.

   The rule actually applied is the weaker and honest one: **assert what we have
   not yet derived.** By that rule the eight split three ways.

   * **Genuinely needed.** *Extensionality*, *regularity*, the *replacement
     scheme* and *Tarski's Axiom A*. None is a consequence of the others —
     extensionality is what fixes the notion of set, regularity and replacement
     are each independent of ZF without them, and Tarski's Axiom A is the entire
     source of consistency strength.
   * **Redundant in principle, asserted anyway: pairing, union, power set.**
     Tarski's Axiom A together with Replacement yields all three — a universe is
     transitive and closed under subsets of members and under power sets, and
     Replacement carves the pair, the union and the power set out of it. This is
     TG folklore, not something proved here; Mizar's own TG axiomatics assumes
     union and *derives* power. No such derivation exists in `derived/`, so all
     three are asserted.
   * **Redundant in principle, asserted anyway: choice.** Tarski's Axiom A
     implies AC, via well-ordering through the universe hierarchy — again a
     theorem about the intended model, not one this development has.

   So the flag "redundant in principle" applies to four of the eight, not to
   choice alone, and the previous text's singling-out of choice was inconsistent
   rather than principled.

   **Why asserting them is nonetheless defensible.** The property this TCB needs
   is not minimality but *truth in the intended model*: for `κ` inaccessible,
   `V_κ` satisfies every one of the eight, so each asserted axiom leaves the
   theory and the consistency strength exactly where they were. What an asserted
   redundancy costs is one more item that must be **read against a reference
   statement** — and `ax_tarski`'s history is the whole argument for taking that
   cost seriously rather than dismissing it: a plausible-looking clause there was
   inconsistent, and a later clause was added with no test noticing. Both are now
   pinned by independent rebuilds (`kernel/tests/tarski.rs`,
   `kernel/tests/replacement.rs`, `kernel/tests/choice.rs`), which is the price
   of the trade.

   ### Choice

   `ax_choice` was added on 2026-07-31, taking the count from seven to eight. It
   is the **only** new axiom the three non-primitive Lean axioms need:
   propositional extensionality follows from Extensionality (a `Prop` denotes a
   subset of `{•}`, and two equi-inhabited such subsets are equal — Carneiro
   §6.3), and quotients are Separation and Replacement applied to `ᾱ/∼` (§6.2).
   Only `Classical.choice` needed something that is not there, and what it needs
   is *set*-sized choice on a bounded universe — the thesis fixes "a choice
   function `ε` on `U_ω`" (§6.2) — **not** global choice on `V`, which §1.2
   needs only for a sharper Werner-style bound and which would raise the
   consistency strength.

   One caveat specific to this axiom, on top of the redundancy noted above: it
   **cannot** be Skolemised into a symbol by `define`, which requires `∃!` — a
   choice function is never unique. That much is unchanged.

   **What has changed is the consequence.** This paragraph used to end "so
   callers carry `IsChoiceFn(f,u)` as an antecedent with `f` free", full stop,
   and that is now only half the story — corrected here rather than appended to,
   because a reader asking whether this kernel can name `ε` would otherwise get
   the wrong answer. `thm::henkin` (added 2026-08-10, and item 4 of the trusted
   base below) mints a **0-ary constant** from `⊢ ∃y. φ` with `FV(φ) ⊆ {y}`, so
   at a *closed* `u` — every rung of `derived::tower` is one — `ε` is a symbol
   and `⊢ IsChoiceFn(ε,u)` is a hypothesis-free sentence. At a `u` carrying a
   parameter the rule refuses, and the free-variable route is still the only one.
   See `derived::choice::epsilon`, which is its single caller.

   ### Infinity: a theorem, not an axiom — question closed

   This used to be recorded here as an open question, with the note that the
   derivation "does not exist in `derived/`" and that asserting an `ax_infinity`
   was the cheaper option by the project's own rule. **It has been derived, so
   the question is closed and the axiom count stays at eight.**

   `derived::infinity` proves

       ⊢ ∃I. (0 ∈ I ∧ ∀n. (n ∈ I → succ(n) ∈ I))

   matched against Jech §1 and Kunen I.2 Axiom 7, **and** a primitive form with
   `0` and `succ` expanded so that it mentions no function symbol at all. The
   second form is the one that matters for this file: without it, "Infinity needs
   no axiom" would rest silently on the conservativity of the definitional
   extensions that introduced `∅` and `succ`, which is a different claim from the
   one being made.

   One thing to keep straight, since it is easy to misstate in the direction of
   this file: `ω` had to be separated at `Trans(q) ∧ …` because **a Tarski
   universe is not closed under `n ↦ n ∪ {n}`**. The universe supplies the
   material, not the closure. And `derived::empty::induction`'s
   `inductive_set_exists` is *not* Infinity — it is inductive in the power-set
   sense, at an arbitrary base point, not under the von Neumann successor.

   ### The empty set

   The empty set was the one that used to go the other way, asserted as
   `ax_empty` because Separation at a refutable condition *is* the empty-set
   axiom, and deriving it from Tarski appeared to need the recursion theorem and
   a transitive closure. Adding the transitivity clause to Tarski's Axiom A on
   2026-07-31 removed that need: a universe is now transitive, Regularity's
   minimal element of a transitive set is empty, and `ax_empty` was deleted the
   same day. See `derived::empty::empty_existence` for the derivation and the
   note where the axiom used to sit in `thm.rs` for the argument;
   `kernel/tests/rules.rs` asserts it stays gone.
2. The first-order proof system, including — especially — the free-variable and
   distinct-variable side conditions on substitution and generalisation.
3. *(from milestone 4)* The claim that the host's bignum operations correctly
   implement the intended interpretation of the primitive arithmetic symbols.
4. The two **conservative-extension** rules and their guards: `define`
   (`∃!` ⇒ a function symbol) and `thm::henkin` (`∃` with `FV(φ) ⊆ {y}` ⇒ a
   0-ary constant). Neither is an inference; each is an *assertion* justified by
   a model-expansion argument written on it, and each returns `None` rather than
   adapting when its guards fail.

   `henkin`'s free-variable check is the whole of what separates it from
   Skolemisation at arity ≥ 1, which would be a **genuine unsoundness** here
   because `ax_replacement` accepts formulas mentioning the new symbol and an
   arbitrary Skolem function need not be amenable. A constant is a parameter, so
   the schemes survive. `kernel/tests/henkin.rs` pins all three guards, each
   with a real derivation as the witness so that the refusal cannot be the shape
   check firing instead, and each was watched going red with its guard removed.

Item 3 is a deliberate, eyes-open addition to the TCB. See below.

## Current contents

* `term.rs` — terms and formulas of first-order logic with `∈`. Locally
  nameless, and `Bound` is **unconstructible from outside**: the only way to make
  one is `Formula::forall`, which closes over a named variable. So dangling
  indices cannot be built, every `Term` handed out is locally closed, and the
  classic "substitutable for" side condition on instantiation is *removed*
  rather than checked. Adversarially tested in `tests/substitution.rs`, and
  those tests are mutation-verified to actually catch depth bugs.
* `thm.rs` — the opaque `Thm` (a sequent `Γ ⊢ φ`), Hilbert-style primitive rules
  (Łukasiewicz propositional axioms, instantiation, distribution, modus ponens,
  generalisation, reflexivity, Leibniz) plus the two structural rules `assume`
  and `implies_intr`, the TG set axioms plus choice,
  and the two conservative extensions, `define` and `henkin`. Ordered pairs,
  equinumerosity, non-emptiness and "is a choice function" are *described* as
  first-order formulas over `{∈,=}` rather than introduced as symbols, so the
  axioms that mention them add no primitives.

  **Everything in `thm.rs` is primitive.** This entry used to list "derived rules
  built on top of them (symmetry, transitivity, congruence, and the propositional
  combinators)" as contents of the file, and `eq_leibniz`'s doc comment used to
  say those rules were derived "below". They are not in this crate at all — they
  are in `derived/src/lib.rs`, outside the trusted base. Claiming derived rules
  that are not here overstates the surface an audit has to read, which is the
  wrong direction to be wrong in for the file this README exists to bound.
* `lib.rs` — six lines: the crate attributes and the re-exports. The interface
  is the type theory, `Thm`/`Formula`/`Term` plus the rules and the axioms, and
  nothing else.

## Hypotheses beside the formula, not inside it

**Hilbert axioms, Isabelle judgement.** `Thm` is `Γ ⊢ φ`: a canonically ordered,
duplicate-free set of hypothesis formulas alongside the conclusion. The axioms
are still the Hilbert ones; only the judgement changed.

This reverses the earlier decision (`DECISIONS.md`, 2026-07-30) that a `Thm` be a
bare formula. The reversal was made by the project owner on a performance ground
— "we try to keep the cost of each kernel operation as performed by the checker
**constant**" — and the numbers back it. Without a `Γ`, an assumption has to be
encoded as an antecedent *inside* the formula, so combining two theorems means
re-proving both against `⋀(Γ ∪ Δ)` first. The above-kernel layer that did this
measured one binary operation at **`13u² + 73u − 134` kernel calls** for
`u = |Γ ∪ Δ|`, against **53** for the inference itself — quadratic, compounding
cubically over a chain, and immune to memoisation because every merge targets a
set never seen before. Beside the formula, the same merge is a list union and
both premises are used unchanged.

Three things it costs, all of them in `thm.rs` and all of them checked:

* **`gen` acquires the classic side condition `x ∉ FV(Γ)`.** It was previously
  argued to be *vacuous* — no `Γ`, nothing to be free in — and that argument is
  now false and has been retracted rather than amended. Without the check,
  `{x ∈ y} ⊢ x ∈ y` would yield `{x ∈ y} ⊢ ∀x. x ∈ y`.
* **`define` refuses a witness with hypotheses.** Minting a symbol from something
  proved only under an assumption has the same shape as the recorded second
  soundness bug.
* **A `Thm` establishes its conclusion only when `hyps()` is empty**, so code
  outside the kernel that reads a conclusion without reading the hypotheses is no
  longer sound — the definitional-equality cache above all. See below; this one
  is not local to the kernel.

`ax_dist`'s `x ∉ FV(φ)` is a **separate** condition about a different formula and
is untouched. Conflating the two is how a real check gets deleted.

Backward compatibility holds, and it is worth being precise about what kind of
fact that is. The mechanism is exact: `assume` is the only rule that introduces a
hypothesis, every other rule unions its premises' sets, and unioning empty sets
is the identity. `gen` kept its infallible signature — the check is reached
through `gen_checked`, and `gen` is the wrapper that panics — so no call site had
to change.

But "every theorem `derived/` and `checker/` build has `hyps() == []`" is a fact
about *those callers*, not a property of the rules, and on its own it would be
the kind of guarantee this project has twice watched evaporate.

**Retracted 2026-08-01.** This used to say the guarantee was made a property of
the repository by `ci/check-boundary.sh` rejecting `Thm::assume` and
`Thm::implies_intr` outside `kernel/`. That rule is gone. It was never a
soundness rule — `assume` giving `P ⊢ P` with the hypothesis *tracked* is exactly
what the sequent design is for — and it had already stopped meaning what everyone
cited it for, because it never scanned `mini/`, a crate that legitimately holds
hypothetical theorems and passes them into `derived/`. It constrained *producers*
while the hazard was in *consumers*.

What replaces it is stronger on every axis but that one: `Thm::gen(` is
grep-forbidden outside this crate, so callers use `gen_checked` and a
hypothetical theorem becomes a counted gap rather than a panic; `assume` is
confined to one named module per crate; hypothesis-free theorems reach stores
only through a `Sealed` newtype; and the boundary script enumerates the workspace
members and fails if any crate is scanned by nothing — the check that would have
caught the old rule going stale within hours. `derived/` keeps the ban, since it
derives rather than assumes and its ~700 `gen` calls rest on it.

## What a `Thm` asserts

A `Thm` is **not a closed formula**. `Thm::eq_refl(Term::var(x))` is `⊢ x = x`
with `x` free, and nothing in the crate ever closes it. The convention that
makes such a theorem mean something is:

> **`Γ ⊢ φ` asserts `∀x⃗. (⋀Γ → φ)` for `x⃗ = FV(Γ ∪ {φ})`** — under every
> assignment to the free variables of the whole sequent that satisfies every
> member of `Γ`, `φ` holds. A free variable is *schematic*: it stands for an
> arbitrary object, never for a particular one.

**The quantifier is outside both sides**, and free variables are shared across
the turnstile. Not `(⋀Γ) → ∀x⃗. φ`: under that reading `{x ∈ y} ⊢ x ∈ y` would
assert `(x ∈ y) → ∀x ∀y. (x ∈ y)`, which is false and which `gen` would then be
entitled to produce. The previous version of this section did not say which side
the quantifier was on, because there was only one side; that gap is exactly what
a new reader would have had to guess.

With `Γ` empty this collapses to the old statement — `⊢ φ` asserts `∀FV(φ). φ` —
so the reading is conservative and no existing theorem changed meaning. It is the
standard reading for a Hilbert system with schematic variables (Metamath's `$p`
statements work the same way). It is nonetheless a *choice*, nothing in the types
enforces it, and it is stated here and at the top of `thm.rs`.

Three consequences, in decreasing order of how easy they are to get wrong.

**`gen` needs its side condition.** `Thm::gen` may universally quantify a
variable only if it is free in no hypothesis. What licenses generalisation is
that the assignments satisfying `Γ` are closed under changing `x`, and that is
precisely `x ∉ FV(Γ)`. The condition is still vacuous on hypothesis-free
theorems, which is a fact about those callers and not a property of the rule.

**A `Thm` still cannot name a particular object.** There is no
existential-elimination rule and there cannot be one: from `⊢ ∃x. φ(x)` you may
not conclude `⊢ φ(c)` for a free `c`, since that asserts `∀c. φ(c)`. Assuming
`φ(c)` does not help — `assume` claims nothing about its formula, `c` stays
schematic, and discharging gives `⊢ φ(c) → ψ` with `c` still universal. That is
`gen`'s side condition doing its job, and it is why `ax_choice`'s callers carry
`IsChoiceFn(f,u)` as an antecedent with `f` free.

**Reading a conclusion without reading the hypotheses is no longer sound.** A
`Thm` used to establish its conclusion, full stop; see the next section.

### The `hyps()` obligation — for whoever owns `checker/`

**A live unsoundness if ignored, and it cannot be fixed in this crate.**

> **A `Thm` no longer establishes its conclusion. It establishes it only when
> `hyps()` is empty.** Any code outside the kernel that reads `concl()` without
> reading `hyps()` — whether it **stores** the theorem for reuse elsewhere or
> merely **compares** its conclusion against an expected formula and reports
> success — silently imports `Γ`.

The comparing case is the one that reads as harmless: a function that checks
`thm.concl() == expected` and answers `true` has accepted `Γ ⊢ expected` as a
proof of `expected`, with no store and no key in sight. The kernel cannot detect
either case — the theorem in hand is a perfectly good theorem, and the error is
in what the checker concluded from it.

**The instance that prompted this** is the definitional-equality cache, which
memoises "these two `Expr`s are equal" with the `Thm` certifying it, keyed on the
pair of `Expr`s, and reuses the entry anywhere. That was sound because a `Thm`
was valid absolutely. Two acceptable fixes:

1. **Cache only hypothesis-free theorems** — refuse to insert when
   `thm.hyps()` is non-empty. Three lines, trivially correct, loses nothing
   today because the backend never calls `assume` outside its own tests.
2. **Key the cache on the hypothesis set too**, i.e. on `(a, b, thm.hyps())`.
   Necessary if the backend ever proves conversions under assumptions. It puts
   hypothesis-set equality on the hot path, which is a second reason the set is
   canonically ordered: comparing two sets is `==` on two sorted vectors.

   **Option 2 does not discharge the obligation by itself.** A key match says the
   entry was *stored* under `Γ`; it is not a proof that `Γ` holds at the use
   site. The retrieving code must additionally use the value only where `Γ` is in
   force, or re-check that `Γ` is empty — which is option 1 with a wider key. And
   option 2 moves the canonical order from a completeness concern into the
   *external soundness* story, because two representations of one set must then
   collide in the key; see "How the hypothesis set is canonicalised" below for
   what that changes about what `impl Ord for Formula` is trusted for.

**The checker has taken option 1.** `checker/src/certify.rs`'s `is_unconditional`
now reads `c.thm().is_some_and(|t| t.hyps().is_empty())` where it used to read
`c.is_proved()`, gating the equality cache's insertion in `checker/src/tc.rs`; a
weaker predicate `hypothesis_free` gates the reduct memo's one write site, since
a certificate carrying its assumptions as antecedents inside a closed formula
imports nothing while a kernel `Γ` does.

This paragraph previously read "doing neither is the unsound option and is the
state today by default", and that is **retracted**: it advertised a hole that is
closed. Prose in or about the trusted base that reports a live unsoundness where
there is none costs the next reader the same attention as prose reporting a check
that does not exist, and it teaches them that these warnings are stale. What is
*not* discharged is the general statement above, for stores and comparisons not
yet written.

### How the hypothesis set is canonicalised

`impl Ord for Formula` in `term.rs`: **cached structural hash first, full
structural comparison as the tie-break**, and `Thm::mk_hyps` sorts and dedups.
Both halves of the order are pure functions of the syntax — the hash is computed
once from the constructor and the children's hashes by a fixed mixer with fixed
seeds, and the tie-break is the derived lexicographic order on `FormulaData` down
to `FreeVar` and `FnSym` identifiers. So the order is the same in every thread
and every process, with no registry to keep and nothing to clear.

That is what `derived::hyp::order::rank` could not do from outside the kernel:
unable to look inside a `Forall` or take a `Term` apart, it had to order by hash
and break ties with a thread-local first-registration registry, stable only
within one thread's lifetime. The hash goes first purely for speed — it settles
almost every comparison in one `u64` compare — and a collision costs one
structural comparison, never a wrong answer.

**What the order is trusted for: canonicality, and hence completeness — not
soundness.** `cmp` must be total and must return `Equal` exactly when `==` holds,
which is what makes `sort_unstable` + `dedup` produce a canonical listing. The
order is not meant to mean anything, and *kernel soundness does not depend on it
at all*: `dedup` compares with the structural `PartialEq`, so a broken order can
only leave genuine duplicates non-adjacent — keeping a formula that really was
assumed, i.e. a weaker theorem — and can never delete a non-duplicate. No rule
reads the order: `gen_checked` scans every element, `implies_intr`'s filter
compares against every element, `mp` concatenates, `define` asks only whether the
set is empty. So the failure mode is silent incompleteness — two equal sets
listed differently stop composing, and later rules return `None` far from the
cause.

`thm.rs` used to list the `sort_unstable`/`dedup` among the *trusted* additions
the hypothesis machinery made, alongside `gen_checked`'s scan and `define`'s
emptiness check, which read as a contradiction of the paragraph above. It is
resolved in favour of this one: there are two trusted additions, not three. The
single way the order would become soundness-relevant is option 2 of the
obligation above — keying an external store on the hypothesis set — because then
two representations of one set must collide in the key.

### Where getting this wrong produced `⊢ ⊥`

`define`'s free-variable check — every free variable of `φ` must be a parameter
or the defined variable — is where this convention has teeth, and it was
**missing, and exploited**: `DECISIONS.md`, "SECOND SOUNDNESS BUG", 2026-07-30.
With `xs = []` and `φ(y) := (y = v)` for a stray `v`, the obligation `∃!y. y = v`
is provable and the defining axiom came back as `⊢ f = v` with `v` free. Read
universally that is `∀v. f = v`; `gen` makes it explicit, two instantiations give
`c₁ = c₂` for arbitrary constants, and `⊥` follows. The witness had proved "for
each `v` there is a unique `y`", so `y` depends on `v`, while `f(x⃗)` takes no
`v` argument.

The reusable part is not "`define` needs a check" but *why it needs one there*:
`define` is the rule that turns a proved formula into a new **symbol**, and a
free variable of that formula is universally quantified on the premise side while
the symbol it produces is not parameterised by it. Any future rule that mints a
symbol, a constant or an axiom out of a proved formula owes the same argument —
including the Henkin constant discussed in `define`'s docs, which is safe only
because it requires `FV(φ) ⊆ {y}`.

### What is *not* here: the `Certifier` boundary

The trait every definitional-equality conclusion must go through, and the
`NullCertifier` that implements it trivially, live in `checker/src/certify.rs`
— outside the TCB. Neither constructs a `Thm`, no method of either mentions a
kernel type, and adding a method to the trait adds **no proving power**: it is
an interface, and a backend can still only reach a `Thm` through the primitive
rules. That is why `iota` became a method rather than being smuggled in as an
`admit` whose `reason` string a backend recognises, and its default
implementation still delegates to `admit`, so a backend with nothing to say
about it reports a gap.

They sat here originally so the declaration could avoid naming the checker's
`Expr`, at the price of two associated types that had exactly one inhabitant
each. Moving them the other way costs the kernel nothing — the dependency still
points untrusted → trusted — and buys 58 lines off the trusted surface plus a
trait stated in the terms it is actually about.

The milestone-3 obligation that **`NullCertifier` be unreachable in a release
build once the real backend exists** is now enforced rather than intended: it is
compiled under `cfg(not(feature = "tg"))`, so a `--features tg` build does not
contain it. (The kernel's old `null-certifier` feature was on by default and
nothing ever switched it off.)

## Boundary rules

Enforced by `ci/check-boundary.sh`, which is itself tested by
`ci/test-boundary.sh`:

| Rule | Also enforced by |
| --- | --- |
| No `unsafe` | `#![forbid(unsafe_code)]` |
| No external crate dependencies | empty `[dependencies]` in `Cargo.toml` |
| `Thm` has no public fields and no public constructor | — |
| No I/O, no serialization, no printing of derivations | — |
| ≤ 700 non-comment lines (697 today) | — |
| No `Thm::gen(` outside `kernel/`; `assume` confined to one module per crate; stores take `Sealed`; every workspace member scanned by something | — |
| `thm::henkin` has **exactly one** caller in the workspace, and it is `derived/src/choice/epsilon.rs` (rule 7) | — |

The last rule is about a *panic* and a *reading*, not about the kernel's own
contents: `Thm::gen` panics on a hypothetical premise and kept its infallible
signature only because no caller can hand it one, and every `concl()` read in
`checker/` is sound only because `hyps()` is empty. Both were facts about today's
callers; the rule makes them facts about the repository. Test code is exempt —
`#[cfg(test)]` items and anything under a `tests/` directory — because pinning
either guard means building a hypothetical theorem deliberately, and both
`kernel/tests/hypotheses.rs` and `checker`'s `tg.rs` tests do exactly that.

The grep duplicates the compiler- and Cargo-level enforcements on purpose: those
can be removed in the very commit that violates them, and the duplication makes
that show up as a CI failure rather than as nothing at all.

The line budget was 1000 while the crate also carried `Certifier` and
`NullCertifier`. With those gone it is 700, because a ceiling with 388 lines of
slack under it is not a boundary — it is a number nobody has to think about.
Raising it again is allowed; doing so silently is what the check exists to
prevent.

**The hypothesis change did not need it raised.** 625 → 662, so 37 non-comment
lines bought the `hyps` field, `mk_hyps`, `assume`, `implies_intr`, `gen`'s side
condition and its `gen_checked` entry point, `define`'s emptiness guard, and the
total order on `Formula` and `Term`. That leaves 38 lines of slack, which is
tight enough that the next addition to the trusted surface has to argue for
itself — which is the point of the number.

**Nor did `henkin`.** 682 → 697: fifteen non-comment lines for the rule and its
three guards, against sixty of doc comment carrying the conservativity argument,
which is the ratio this budget is designed to encourage. Three lines of slack
left. The *next* addition does have to raise this number and say why here — and
whoever does should first read rule 7 above, because the cheapest way back under
700 is to notice that a primitive with no callers should be deleted rather than
budgeted for.

**Rule 7 is not a size rule and does not belong to this section**; it is listed
here because it is the mechanism by which the trusted base is expected to
*shrink* again. The project owner's condition on `henkin` was that we might
"regret that choice later and build it differently"; `derived/src/choice/
epsilon.rs`'s header records what a replacement must provide, and rule 7 turns
"the primitive is now unused" from something a reader might notice into a red
build.

### Why no derivation printing

`Thm` carries its **conclusion and its hypotheses, and nothing else** — no proof
term, no rule name, no premise pointers. Derivations exist transiently, as the
history of API calls, and are dropped immediately. Memory is O(live theorems)
plus O(hypotheses in flight), not O(proof size), and no proof file is ever
written. This is what makes the approach affordable, and a kernel that could
serialize a derivation would invite a workflow that gives it up.

The hypothesis set does not weaken this. It is a set of *statements assumed*,
not a record of how the theorem was reached, it is bounded by what the caller
assumed rather than by the length of the derivation, and `implies_intr` shrinks
it again. A theorem with no hypotheses is exactly the object it was before.

## Why beta is conditional, and what discharging it took

**Status: done.** Beta is derived and wired. This section is kept because the
*reason* beta is a conditional statement — and why discharging that condition
needed the `Certifier` boundary widened — is the load-bearing part, and it is
still true. What is no longer true is that any of it is outstanding; the closing
subsection records what it took.

The set-theoretic function corresponding to a Lean lambda *can* be constructed —
this is Carneiro's interpretation, and it is not in doubt:

    ⟦λx:A. b⟧ = { ⟨x, ⟦b⟧⟩ : x ∈ ⟦A⟧ }        (by Replacement)
    ⟦f a⟧     = ⋃ { y : ⟨a, y⟩ ∈ ⟦f⟧ }

Two things stood between that and a derivable beta rule.

**1. Definitional extension.** `lam` and `app` have to *mean* something, which
means defining axioms rather than a bare signature extension. `thm::define`
provides this: given `⊢ ∀x⃗. ∃!y. φ(x⃗, y)` it introduces a fresh symbol and
returns `⊢ ∀x⃗. φ(x⃗, f(x⃗))`. The `∃!` premise is required as a *theorem*,
because uniqueness is exactly what makes a model's expansion unique and hence
the extension conservative. Demonstrated end to end in `derived/tests/define.rs`
(in the untrusted crate — the kernel supplies the rule, not the demonstration),
which derives `⊢ ∀x. ∃!y. y = x` from the primitives and uses it to obtain
`⊢ ∀x. f(x) = x`.

Note also that `lam` is not one symbol but a *family*: the body of a lambda is a
term with a free variable, i.e. a scheme, so each Lean lambda induces its own
definitional extension parameterised by the lambda's free variables. That is
routine, just not free.

**2. A typing premise — the real obstruction.** A set-theoretic function has a
*set* domain, so beta is not unconditional. If `a ∉ A` then

    app(lam_b(A), a) = ⋃∅ = ∅

while `⟦b[a/x]⟧` is generally something else. The derivable statement is

    ⊢ a ∈ A → app(lam_b(A), a) = b[a/x]

and discharging that antecedent requires `⊢ ⟦a⟧ ∈ ⟦A⟧` — a *typing* fact. This
is why Carneiro's interpretation is type-directed: its soundness theorem is
"if `Γ ⊢ a : A` then `⟦a⟧ ∈ ⟦A⟧`", and the interpretation is only defined
relative to a typing derivation.

So closing beta meant extending the `Certifier` boundary beyond equality to
carry typing judgements, and threading those through the checker's `infer`
alongside the existing equality certificates. That was a larger job than "add
some axioms" — which is what an earlier version of this note implied.

**What discharging it took.** All of the above has landed:

* the two derivations are `derived/src/funcs/beta.rs` — `lambda` introduces
  `lam` by Replacement (`⊢ ∀A ∀y. y ∈ lam(A) ↔ ∃x. x ∈ A ∧ y = ⟨x, t(x)⟩`) and
  `beta_conditional` gives `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = t(a))`. The
  membership antecedent is not removable, and `funcs::app_off_domain` is the
  complementary half that says why;
* `Certifier::beta` is a trait method the tg backend answers with that
  derivation rather than an admit;
* the typing judgement crossed the boundary: `Certifier` carries a
  `declar_checked` hook and a family of typing rules — one per Lean typing rule,
  each handed premises inference has already computed — and `TcCtx::infer`
  returns `Inferred { ty, cert }` instead of a bare type. `TgBackend`'s
  `has_type_*` family in `checker/src/tg.rs` is the answering side.

The one thing worth carrying forward is the shape of the fix, not its size: the
antecedent was discharged by making inference *keep* the evidence it was already
producing, not by searching for it again. `Certifier::declar_checked`'s doc
comment records what the search used to cost.

## Dependency policy

The crate is dependency-free. There is exactly one sanctioned future exception:

> **`num-bigint` (or a hand-rolled equivalent) for native numeral arithmetic,
> arriving in milestone 4.**

This is not yet a dependency — the line above exists so `ci/check-boundary.sh`
can distinguish "the sanctioned exception, documented" from "someone added a
crate". When it is actually added it must be pinned and vetted, and this section
must record the version and the vetting.

Anything else is a boundary violation.

## Milestone 4 note: built-in arithmetic

`ℕ` will be a **primitive sort** with primitive numeral syntax and native
bignum-backed rule schemas (`+`, `-` truncated, `*`, `/`, `%`, `^`, `=`, `≤`,
`<`, `gcd`, and the bitwise/shift operations), mirroring what Lean's kernel
accelerates.

These are not derived from the Peano axioms, and must not be. Lean's kernel
short-circuits `Nat.mul` to GMP rather than unfolding its recursion, so there is
no feasible-length derivation corresponding to `2^64 * 3`; deriving arithmetic
would make `decide`-heavy developments uncheckable regardless of constant
factors. Numerals are stored as bignums, never as `S(S(...))` towers.

Why this is safe to trust: every such rule is valid in the standard model
(`ℕ ↦ ω`, symbols to the usual ordinal operations), so consistency is preserved
*provided the computation is correct*. Correctness of the computation is the
whole risk, and it is a testable one — which is precisely why `ℕ` is primitive
rather than defined as von Neumann ordinals. A primitive sort with a canonical
intended meaning has no defined encoding for the rules to disagree with, which
removes the only failure mode that would be invisible to differential testing.

Differential-test against an independent implementation, including: zero,
truncated subtraction below zero, division and modulo by zero (Lean returns
`0`), and values straddling word boundaries.
