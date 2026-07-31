# Design decisions

Append-only log. When a design choice is made that `CLAUDE.md` does not already
cover: what was chosen, what was rejected, why. Entries touching `Prop`, large
elimination, universes, or inductive semantics are flagged `RISK:` — those want a
second pair of eyes eventually, because a rule there can look entirely plausible
and still be inconsistent.

---

## 2026-07-30 — Fork nanoda by importing it, rather than reimplementing

**Chosen.** Import `nanoda_lib` wholesale as the `checker/` crate (via
`git subtree`, preserving upstream history) and instrument it.

**Rejected.** Writing a fresh export parser, `Expr` representation, and type
inference from scratch, following the Kernel Arena tutorial progression.

**Why.** The goal is a checker whose *definitional-equality reasoning* emits
derivations. Nanoda already has a working, tested implementation of everything
around that — parser, hash-consed `Expr` arena, inference, reduction, inductives.
Reimplementing it would spend the entire budget rebuilding the untrusted part,
which is explicitly the part that does *not* have to be right. Instrumenting the
existing checker gets to the actual research question far sooner, and keeps a
working, testable artifact at every commit.

Importing with full history (rather than copying files) means the instrumentation
diff stays legible: `git diff nanoda-upstream/master -- checker/` is exactly the
set of changes we are responsible for.

---

## 2026-07-30 — Cargo workspace, with `kernel` as a separate crate

**Chosen.** A two-crate workspace: `kernel/` (trusted) and `checker/` (untrusted,
the nanoda fork). `CLAUDE.md` sketches `src/kernel`, `src/export`, `src/check`,
`src/interp` as directories within one crate.

**Why.** The hard requirement "no external crate dependencies under `kernel/`"
is enforceable by Cargo when the kernel is its own crate with an empty
`[dependencies]` table — the checker's `serde`/`indexmap`/`num-bigint` stack
simply cannot leak in, even accidentally. As sibling directories inside a single
crate, that rule would be enforceable only by a grep that is easy to defeat by
accident. `export`/`check`/`interp` remain as modules within `checker/`.

The `ci/check-boundary.sh` grep is retained as belt-and-suspenders for the rules
Cargo cannot express (no `unsafe`, no public `Thm` constructor, no I/O, size
budget), and because the Cargo-level and compiler-level enforcements could
otherwise be removed silently in the same commit that violates them.

---

## 2026-07-30 — The boundary check has its own self-test

**Chosen.** `ci/test-boundary.sh` builds synthetic kernels that each violate
exactly one rule and asserts `ci/check-boundary.sh` rejects them.

**Why.** A CI check that cannot fail provides no assurance, and greps are
notoriously prone to silently matching nothing. This was not hypothetical: the
self-test immediately found four real bugs in the first version of the check —
`\bprintln!\b` can never match (a word boundary cannot occur between `!` and
`(`), `awk` does not support `\b` in patterns, the `pub struct Thm {` header line
was itself being flagged as a public field, and comment stripping did not account
for `grep -rIn`'s `path:line:` prefix. Each of those would have left a boundary
rule silently unenforced.

---

## 2026-07-30 — `Certifier` is generic over the term type

**Chosen.** `trait Certifier { type Term; type Cert; ... }`, with the kernel
knowing nothing about the checker's `Expr`.

**Rejected.** Having the kernel depend on the checker's expression type.

**Why.** The dependency has to point from untrusted to trusted, never the
reverse; the TCB cannot include Lean's syntax. The checker instantiates `Term`
with its interned `ExprPtr`. The real set-theoretic backend will hold the
interner and interpretation tables inside the implementing struct.

Certificates are *values* threaded through the checker, never phantom types —
otherwise the milestone-3 backend would not be implementable, and the design
error would only surface once it was expensive to fix.

---

## 2026-07-30 — Arena corpus is the regression net; two files are "declined"

**Chosen.** `scripts/arena.sh` runs the Lean Kernel Arena corpus (102 `good`,
55 `bad`) and requires every `good` file to be accepted and every `bad` file
rejected. Baseline before any instrumentation: 152 matched, 0 mismatched.

Two `good` files — `sparse-name-index` and `level-index-out-of-order` — are
counted in a separate `declined` bucket rather than as failures. Upstream nanoda
deliberately refuses export files whose name/level back-references are not
densely numbered ("Back-refs must be continuous"), which is a parser policy, not
a judgement that the file is ill-typed.

**Why report them separately** rather than filtering them out: a silent skip
list is how a corpus quietly stops testing anything. The count stays on screen.

The corpus is vendored under `vendor/` and gitignored (17 MB, 12 MB of which is
performance data). `scripts/arena.sh` requires `nat_extension` and
`string_extension`, without which much of the corpus — including the 2059-
declaration `init-prelude` — is refused outright for containing literals.

---

## 2026-07-30 — Step counting is a feature-gated global counter

**Chosen.** `checker/src/stepcount.rs`: global relaxed atomics, bucketed by step
kind, behind an off-by-default `stepcount` cargo feature. One-line `bump(...)`
call at each reduction site.

**Rejected.** Per-`TypeChecker` counter fields threaded through the call graph.

**Why.** `check_all_declars_par` checks declarations on several threads, so a
per-checker counter would have to be plumbed and merged — exactly the
restructuring the brief warns against ("the number is only trustworthy if the
code producing it is still recognizably nanoda"). Relaxed atomics are correct
here because the counters are a monotone tally read only after all threads join.

The feature gate keeps ordinary builds unaffected: with it off, `bump` compiles
to nothing, so no `cfg` noise is needed at the call sites. Verified
behaviour-neutral — the arena corpus gives identical results with the feature on
and off.

Results and their interpretation are in `MEASUREMENTS.md`.

---

## 2026-07-30 — `def_eq` returns `Option<Cert>`, and the holes are named

**Chosen.** Every definitional-equality path in `tc.rs` returns
`certify::DefEq<'t,'p> = Option<Cert>` instead of `bool`. `Some(cert)` carries
the reason; `None` means "not shown equal", which for a checker is the same as
reject.

Where the checker cannot yet produce a real justification it calls
`Certifier::admit`, naming the site via the `certify::Admit` enum. Admits are an
enum rather than scattered strings so the remaining work is enumerable, a new
hole cannot be added without naming it, and each site is counted.

**Why an explicit `admit` rather than finishing every rule first.** The
alternative is a flag day: convert all 1300 lines of `tc.rs` before anything
compiles. `admit` makes the incomplete parts *visible in the type system and in
a report* rather than hidden behind a `bool`, and it keeps every commit green.
The count of surviving admits is the honest measure of how far milestone 3 has
to go, and it must reach zero before the TG backend can be trusted.

Current provenance on `init-prelude` (2059 declarations): **58,694 certified by
a real backend rule, 7,287 admitted (11%)**. Reflexivity (pointer equality on
the hash-consed representation, which *is* alpha equality), sort equality,
constant equality and eta are already real.

A notable finding: `eq_cache` accounts for only **687** admits, not the 57,800
suggested by the cache-hit count, because the overwhelming majority of cache
hits are settled by pointer equality and so discharge as reflexivity. The
proof-producing union-find is therefore a much smaller job than the raw hit rate
implied.

**Rejected.** Making `TypeChecker` generic over the backend. Exactly one backend
is active per build (the brief requires `NullCertifier` to be *unreachable* in
release once the real one exists, so they never coexist), and a type parameter
would have churned every `impl` block and every closure signature in `util.rs`
for no gain. The backend is a `TypeChecker` field, selected by the
`certify::Backend` alias; keeping it beside `ctx` also lets the borrow checker
see the two as disjoint fields, which is what makes
`self.certifier.beta(self.ctx, ..)` compile without contortions.

**RISK:** the `Certifier` trait gained a `Ctx` associated type. Certificates
cannot be built lazily — a `Term` is only an interner index, so a real backend
must interpret it *at the point of use*, which means it needs the arena. The
alternative, recording a lazy derivation tree and interpreting later, is exactly
the "store the derivation" design the project forbids. Flagged because it
constrains what milestone 3 can do: any rule the backend cannot discharge
eagerly, in one pass, with only the arena in hand, will need this design
revisited.

---

## 2026-07-30 — Corpus tests run the checker in a subprocess

**Chosen.** `checker/tests/corpus.rs` shells out to the built binary once per
export file.

**Why.** The checker signals rejection by panicking (`assert!`). Catching that
in-process with `catch_unwind` is fragile — it cannot distinguish a rejection
from a genuine harness crash, and nanoda checks declarations on multiple
threads. A subprocess gives an unambiguous verdict from the exit status.

Committed fixtures live in `checker/tests/fixtures/{good,bad}` so `cargo test`
always has negative coverage without the 17 MB vendored corpus. They were
verified to fail for the *right* reasons rather than incidentally: the
type-mismatch fixture trips the `def_eq` assertion, and the
apply-non-function fixture trips `ensure_pi`. The full arena corpus runs when
`vendor/arena-tests` is present and reports a skip when it is not.

---

## 2026-07-30 — Real congruence certificates; and a mis-attribution bug found

**Chosen.** `def_eq_binder_aux` and `def_eq_app` now build genuine certificates
by folding `lam_cong`/`pi_cong` and `app_cong` over the structure, instead of
admitting. This closed the two largest holes outright: binder 4,978 → 0 and app
470 → 0, taking total admits on `init-prelude` from 7,287 to 1,839.

The binder fold is where the context-freeness discipline is actually discharged:
`lam_cong`/`pi_cong` generalise over the local introduced when descending under
the binder, turning a judgement made under a binder into a closed one. That is
what keeps the certificate valid absolutely rather than relative to a local
context, and hence what keeps the equality cache globally sound.

**A real bug this surfaced.** `def_eq` weak-head-normalises its arguments and
then compares the *reduced* terms — so the certificate it returned justified
`x_n ≡ y_n`, not the `x ≡ y` it claimed. With `Cert = ()` this is invisible;
with a real backend it is a silent lie in the certificate chain, i.e. precisely
the failure mode the whole design exists to prevent. Fixed by recording both
reduction legs and composing:

    x ≡ x_n   ∘   x_n ≡ y_n   ∘   (y ≡ y_n)⁻¹

using real `trans`/`symm`. The legs themselves are admitted as `Admit::Whnf`
because `whnf` performs beta, zeta, delta, iota, quotient and projection steps
internally and returns only the reduct, with no record of which rules applied.

This *raised* the admit count from 1,839 to 4,520 (2,681 `whnf` legs). That is
honesty increasing, not a regression: those steps were always happening, they
were simply being mis-attributed. Finding this is the clearest evidence so far
that the "certificates must be values, threaded through" discipline earns its
keep — a `bool` return type cannot express the distinction that was wrong here.

**Next.** Make `whnf` return evidence alongside the reduct. Its internal step
sites are already identified and counted (see `stepcount.rs`), so the work is
threading a certificate out of `whnf_no_unfolding_aux` rather than discovering
where the steps are. After that, `lazy_delta` (1,126) composes from `delta`
plus `trans`, and `eq_cache` (687) needs the proof-producing union-find.

---

## 2026-07-30 — A real TG kernel: Hilbert-style FOL, locally nameless

**Chosen.** `kernel/` now contains an actual first-order kernel for
Tarski–Grothendieck set theory: `Term`/`Formula`, an opaque `Thm`, primitive
inference rules, and the set axioms. 511 non-comment lines, within the budget.

**Hilbert style, not natural deduction.** `CLAUDE.md` requires `Thm` to be a
formula with no context. Natural deduction's judgement is `Γ ⊢ φ`, so every step
would carry and compare a context — the thing the design forbids, and the thing
that would cost an alpha-comparison on each of billions of conversion steps. A
Hilbert system's judgement is exactly `⊢ φ`.

This pays off concretely in the trusted surface: **generalisation needs no side
condition.** In a system with contexts, `Gen` requires `x ∉ FV(Γ)`; with no `Γ`
there is nothing to check. One fewer place to get wrong.

**Locally nameless, with `Bound` unconstructible.** Bound occurrences are de
Bruijn indices, free occurrences are named, and they are *different
constructors* — so substituting for a free variable cannot capture, because free
variables are not what binders bind. Crucially there is **no public way to build
a `Bound`**: the only route is `Formula::forall`, which closes over a named
variable. A dangling index is therefore unconstructible from outside, and every
`Term` handed out is locally closed.

That removes, rather than checks, the "substitutable for" side condition on
universal instantiation — the classic hole. The side condition that remains real
is the one on the distribution axiom (`x ∉ FV(φ)`), and it is checked.

**Tested by mutation, not just by passing.** The nine adversarial substitution
tests were verified to actually catch bugs: breaking the depth increment in
`close` fails 5 of them (including the central capture test), and breaking it in
`open` fails 4. A test suite that has never been shown to fail is not evidence.

**RISK:** Tarski's Axiom A is stated incompletely — the "no surjection from `y`
onto `u`" clause needs ordered pairs, and is currently represented by the weaker
`y ∈ u` disjunct alone. It is marked `ax_tarski_incomplete` and nothing in the
checker path uses it. It must be completed before any claim depending on
inaccessibles (i.e. anything about Lean's universe hierarchy).

---

## 2026-07-30 — The interpretation takes no axioms, and says so

**Chosen.** `checker/src/tg.rs` interprets Lean expressions into kernel terms
using function symbols introduced by **pure signature extension** — fresh
symbols with *no* defining axioms.

**Why.** Signature extension is unconditionally conservative: any model of the
base theory expands to a model of the extension, so nothing new becomes provable
and consistency is preserved. No proof obligation, and the trusted base does not
grow by a single line.

**What it costs, stated plainly.** Symbols with no axioms mean nothing, so only
the *equational* fragment can be discharged — reflexivity, symmetry,
transitivity and congruence, which hold for any function symbols whatever.
Anything depending on what the symbols denote cannot be proved from nothing.
Beta is the important case: it needs `lam` and `app` to actually be a function
and its application. Those steps are returned as `TgCert::Admitted` with a
reason and are counted, never waved through.

`TgCert` is deliberately an enum (`Proved(Thm) | Admitted(&str)`) rather than a
bare `Thm`. A backend that could only return `Thm` would have to either refuse —
breaking the checker — or forge, defeating the exercise. As an enum the gap
propagates through the combinators and gets reported.

**A soundness trap avoided.** Lean locals map to kernel free variables allocated
through `Env::fresh_var`, *not* derived from the Lean id. The derived equality
rules mint fresh variables for their Leibniz holes; if such a hole collided with
a Lean local, Leibniz would substitute at the wrong occurrences. That is a real
unsoundness, not merely a wrong answer, and the allocation discipline prevents
it by construction.

**Levels are simplified before interpretation.** The checker settles level
equality with its own algebra, under which `imax 1 1` and `1` are equal;
interpreting them naively gave syntactically different terms and turned settled
equalities into unprovable ones (tutorial 003 and 004 failed exactly this way
before the fix). Normalising to the checker's canonical form keeps the two views
in step.

**Result.** With `--features tg`, tutorial exports 001, 003, 004, 005 and 008
are checked with **every definitional-equality step fully derived, zero gaps**.
006 and 007 are accepted with the beta gap reported. Acceptance across the whole
arena corpus is unchanged: 152 matched, 0 mismatched.

---

## 2026-07-30 — Definitional extension, and an honest account of beta

**Correcting an earlier entry.** The previous note said beta "needs defining
axioms for lam/app". That is true but incomplete, and the incompleteness
mattered: it made the remaining work sound like a small addition when it is not.

The set-theoretic function for a lambda is perfectly constructible —
`⟦λx:A. b⟧ = {⟨x, ⟦b⟧⟩ : x ∈ ⟦A⟧}` by Replacement, with
`⟦f a⟧ = ⋃{y : ⟨a,y⟩ ∈ ⟦f⟧}`. Two things are required, not one.

**1. Definitional extension** — now implemented as `thm::define`. Given
`⊢ ∀x⃗. ∃!y. φ(x⃗, y)` it introduces a fresh symbol and returns
`⊢ ∀x⃗. φ(x⃗, f(x⃗))`. The `∃!` is demanded as a theorem rather than assumed
because uniqueness is precisely what makes a model's expansion unique, and hence
the extension conservative; with existence alone the symbol would be a choice
function and conservativity would fail. `tests/define.rs` derives
`⊢ ∀x. ∃!y. y = x` from the primitives and uses it to obtain `⊢ ∀x. f(x) = x`,
so the whole chain is exercised rather than asserted.

Supporting this needed a small combinator library (`imp_refl`, `a1i`,
`mp_const`, `and_intro`, `exists_intro`). A Hilbert system has no deduction
theorem available as a meta-rule — that would require inducting over a stored
derivation, and derivations are deliberately not stored — so implications must
be *built* from S and K rather than discharged from assumptions. These are
derived rules, not trusted ones.

**2. A typing premise — the actual obstruction.** A set-theoretic function has a
set domain, so beta is conditional: if `a ∉ A` then `app(lam_b(A), a) = ⋃∅ = ∅`
while `⟦b[a/x]⟧` is generally not. What is derivable is

    ⊢ a ∈ A → app(lam_b(A), a) = b[a/x]

and discharging the antecedent needs `⊢ ⟦a⟧ ∈ ⟦A⟧`. This is exactly why
Carneiro's interpretation is type-directed — its soundness theorem is
"if `Γ ⊢ a : A` then `⟦a⟧ ∈ ⟦A⟧`".

**Consequence for the design.** The `Certifier` boundary currently carries only
*equality* judgements. Beta requires it to carry *typing* judgements too, with
the checker's `infer` threading membership certificates alongside the equality
ones. That is a genuine extension of the trait and of the plumbing, not an
addition of axioms.

**Not done here, deliberately.** Also outstanding before beta: ordered pairs
(Kuratowski, needing `∃!` derived from Pairing plus Extensionality) and the
Replacement instance that builds the graph. Both are routine but neither is
free, and `CLAUDE.md` is explicit that inventing semantic clauses is out of
bounds — this follows Carneiro rather than improvising an interpretation in
which beta would be unconditional.

---

## 2026-07-30 — Derived rules move out of the kernel; they are not "tactics"

**Chosen.** A third workspace crate, `derived/`, holding the derived inference
rules and (shortly) the conservative constructions. `kernel/` keeps only the
primitives: terms and formulas, `Thm`, the primitive rules, definitional
extension, and the set axioms.

**Why.** Derived rules are untrusted — they can only reach a `Thm` through the
kernel's public primitives, since `Thm`'s field is private — so they were
untrusted code sitting inside the trusted crate and consuming its size budget.
Moving them out took the kernel from 583 to 492 non-comment lines, and means the
budget now measures what actually has to be correct. The proof-engineering
library can grow without inflating the trusted base, which matters because
Hilbert-style derivations need a lot of small change.

This required adding read-only accessors (`Formula::as_eq`, `as_imp`, `as_mem`)
so untrusted code can inspect formulas. Reading is not a trusted operation: no
amount of inspection lets a client build a `Thm`.

**Not "tactics".** The crate was briefly called that, which is wrong. A tactic in
the LCF sense is goal-directed — it takes a goal to subgoals plus a validation,
and runs backwards. Everything here runs forwards, theorems to theorems, and the
crate also holds conservative *constructions* (defined symbols with their
characteristic theorems), which are not inference rules at all. `derived` is the
honest name: everything derivable from the primitives, as opposed to the
primitives themselves.

---

## 2026-07-30 — Explicit definitions are free; the ∃! only bites for implicit ones

**Chosen.** `derived::define_abbrev` introduces `f(x⃗) := t(x⃗)` and returns
`⊢ ∀x⃗. f(x⃗) = t(x⃗)`, discharging `kernel::thm::define`'s `∃!` obligation via
`derived::exists_unique_eq`.

**Why this matters more than it looks.** A *term* denotes a unique object by
construction, so `∃!y. y = t` is provable for any term whatever — the proof is
uniform and cheap (reflexivity, `imp_refl` under a `gen`, `and_intro`,
`exists_intro`). So an explicit definition is always available at no real cost.
The conservativity obligation only becomes real work when defining a set by a
*property* rather than by a term, which is where Pairing-plus-Extensionality
style derivations are needed.

This splits the remaining work cleanly. Lean's `def c := v` is an explicit
definition — `⟦c⟧ := ⟦v⟧` — so **delta needs no hard derivation at all**, only
plumbing. Lambdas are the implicit case, since a graph is specified by a
membership property.

**Blocked on plumbing, not mathematics: delta.** To define `⟦c⟧` as an
abbreviation the backend must see the constant's *value* at the moment it first
interprets the constant. It currently cannot: `Certifier::Ctx` is `TcCtx`, which
carries the expression arena but not the declaration environment
(`Env::get_declar_val` lives on `TypeChecker::env`). Fixing this means bundling
both into the context the trait passes — a mechanical change across the
certifier call sites, not a proof problem. Recorded here so the next session
does not rediscover it.

---

## 2026-07-30 — RISK: beta needs a universe hierarchy, which is a milestone of its own

Tracing what tutorial 006/007 actually require turned up a prerequisite I had
not accounted for, and it is the thing that makes "just add beta" not a small
task.

**Beta needs `⟦a⟧ ∈ ⟦A⟧`.** For 006 that is concretely `⟦Prop⟧ ∈ ⟦Sort 1⟧` —
a *universe membership* fact. So the interpretation needs a canonical hierarchy
`U₀ ∈ U₁ ∈ …` with `⟦Sort (n+1)⟧ = Uₙ`, and facts about it must be derivable.

**Tarski's Axiom A cannot simply be Skolemised.** It states `∀x ∃u. (x ∈ u ∧
universe(u))` — existence, not uniqueness. `kernel::thm::define` requires `∃!`,
precisely because uniqueness is what makes the extension conservative. So there
is no one-step route from the axiom to a universe operator.

**It is still constructible conservatively**, which is what the guideline asks
for: take `U(x)` to be the *least* universe containing `x`, i.e. the
intersection of all universes containing `x`. That is a set (it is a subset of
any one of them, which Tarski supplies), and it is unique, so `∃!` is available.
The obligation is to derive that an arbitrary intersection of universes is
itself a universe — each closure condition is preserved, but each needs
proving.

**Consequence.** The universe hierarchy is a prerequisite milestone, not a step
inside the beta work. Ordering the remaining path honestly:

1. Quantifier toolkit: `∀`-elimination under hypotheses, `∃`-elimination
   (awkward in Hilbert style — needs the distribution axiom and its side
   condition), `∃`-monotonicity.
2. `upair` by `∃!` from Pairing plus Extensionality. Kuratowski pairs then come
   free as a composition — no new extension, per the guideline.
3. The universe hierarchy, as above.
4. Lambda graphs by Replacement; `app` by union. The `∃!` for a lambda's graph
   is cheap *because* the body interprets to a term, so single-valuedness is
   `∃!y. y = t(x)` — the trivial case.
5. Typing certificates threaded through `Certifier`, to discharge `⟦a⟧ ∈ ⟦A⟧`.
6. Plumbing: `whnf` returning evidence, the lazy-delta loop composing
   certificates, and the backend seeing declaration values so `⟦c⟧ := ⟦v⟧` is an
   explicit definition.

Flagged `RISK:` because it touches universes, where a plausible-looking rule can
be inconsistent — in particular, asserting a universe hierarchy axiomatically
instead of constructing it would be an easy and tempting shortcut, and would put
real weight on an unexamined axiom.

---

## 2026-07-30 — `upair` derived; ordered pairs are a composition, not an extension

**Done.** `derived::upair` introduces `{x, y}` by conservative definitional
extension and returns its characteristic property
`⊢ ∀x ∀y ∀z. (z ∈ upair(x,y) ↔ (z = x ∨ z = y))`.

The whole chain is real: Pairing supplies existence, Extensionality supplies
uniqueness (two sets with the same members are equal, so the pair is
determined), the `∃!` is assembled in a Hilbert system with no deduction
theorem, and `kernel::thm::define` accepts it. Nothing is assumed.

Making that writable needed a "reasoning under a fixed hypothesis" layer —
`syl_imp`, `com12_imp`, `and_intro_imp` internalised as formulas, plus `hyp_mp`
which behaves like modus ponens inside a fixed hypothesis context. It is the
closest a Hilbert system gets to a deduction theorem, and without it the
derivation is unreadable.

**Ordered pairs add nothing.** Following the guideline that anything
constructible conservatively should be constructed rather than added:
`singleton(a) = upair(a,a)` and `⟨a,b⟩ = upair(upair(a,a), upair(a,b))` are pure
*term compositions*. No new symbol, no proof obligation, no signature growth —
there is a test asserting the signature does not grow when a pair is built.

The *characteristic* property of ordered pairs (`⟨a,b⟩ = ⟨c,d⟩` iff `a = c` and
`b = d`) is a separate lemma and is genuine work; it is what the function-graph
construction needs next.

---

## 2026-07-30 — One abstraction covers Pairing, Union and Power Set

**Chosen.** `derived::define_by_membership`: from `⊢ ∃s. ∀z. (z ∈ s ↔ φ(z))`,
derive the `∃!` (uniqueness from Extensionality) and introduce the symbol.

**Why it generalises.** Every basic set construction has the same shape — an
axiom asserting that a set with a prescribed membership condition exists, plus
Extensionality to pin it down. Factoring that out means each construction costs
only its existence axiom: `upair`, `union` and `power` are now four lines each,
and the fifty-line uniqueness derivation is written once.

This is the guideline paying off directly. Nothing was added to the target
logic; three constructions came out of machinery that already existed.

---

## 2026-07-30 — Constants become explicit definitions; delta is derived but not yet reachable

**Done.** The TG backend now resolves a Lean constant to its *value* and
introduces `⟦c⟧` as an **explicit definition** `⟦c⟧ := ⟦value⟧`, monomorphised
at the occurrence's universe levels — which is what `CLAUDE.md` prescribes for
levels. This is conservative for free (`∃!y. y = t` for any term), and it is
what makes delta justifiable: with an opaque symbol there is nothing relating a
constant to what it unfolds to. Constants *without* values — axioms,
constructors, recursors, and Lean's `opaque` — stay opaque, which is correct,
since they do not delta-reduce.

`Certifier::delta` now builds a real derivation: the head constant's defining
equation, lifted over the argument spine by `app_cong`, with a guard that the
derived equation really is about the two terms the checker claims are equal.

**But it is unreachable, and that is the finding.** `unfold_def` never calls
`Certifier::delta` — delta happens *inside* `whnf`, which returns only a reduct.
This is the same structural issue already noted for beta: the checker never asks
the backend about either rule. So the machinery is correct and tested but no
test changes, and no gap closes.

The consequence for ordering: **`whnf` must return evidence before any reduction
rule can be certified**, no matter how much of the mathematics is derived. That
is a refactor of `whnf`/`whnf_no_unfolding_aux` and their callers to thread
`(term, cert)` pairs.

**A trap worth recording.** Giving the backend a reference to the declaration
environment initially broke unrelated callers with borrow errors. The cause was
the `Drop` impl on the backend (which merged admit tallies): a `Drop` on a field
makes the enclosing `TypeChecker`'s borrow of its context live to the end of
scope. Fixed by tallying directly into the run totals instead. Worth remembering
before adding `Drop` to anything the checker holds.

---

## 2026-07-30 — RISK MATERIALISED: Tarski's Axiom A as stated was inconsistent

**Found and fixed.** The kernel's `ax_tarski_incomplete` stated the
inaccessibility clause as `∀y. (y ⊆ u → y ∈ u)`, dropping the `y ≺ u` ("no
surjection from `y` onto `u`") disjunct because stating it needs ordered pairs.
I had flagged that as *incomplete* and written "must not be relied on".

It was not incomplete. It was **inconsistent**. Instantiate at `y := u`: `u ⊆ u`
is trivially derivable, so `u ∈ u` follows, which Regularity refutes. An
inconsistent axiom in the trusted base lets the kernel prove anything, which is
the one failure this entire project exists to prevent.

**The axiom is removed**, not merely re-flagged. `kernel/tests/tarski_regression.rs`
derives the fatal step from the clause's shape and includes a source-level guard
so it cannot be reintroduced unnoticed. It may only return once `≺` can be
stated — which the ordered pairs now in `derived/` make possible.

**Why this matters beyond the bug.** `CLAUDE.md` says entries touching universes
"can look entirely plausible and still be inconsistent", which is exactly what
happened, and my own `RISK:` note on it a few hours earlier judged the danger to
be under-specification rather than contradiction. Two lessons:

1. A "weakened" axiom is not a safe placeholder. Weakening a *disjunction* by
   dropping a disjunct **strengthens** the axiom. That is the specific error, and
   it is easy to make again.
2. It was found by an independent reviewer looking at the axiom fresh, not by
   the tests, and not by me. The trusted base needs adversarial reading, not
   just adversarial testing.

---

## 2026-07-30 — Beta reduction derived; Tarski's axiom restated correctly

**Beta is derived.** `derived::funcs::beta_conditional` gives

    ⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = t(a))

built on a ladder that is entirely derived, nothing assumed: `⟨a,y⟩ ∈ f → y ∈
⋃⋃f`, the value collection `{y : ⟨a,y⟩ ∈ f}` as a set, `app(f,a) = ⋃coll(f,a)`,
and the lambda graph `{⟨x,t(x)⟩ : x ∈ A}` by Replacement. Verified
independently (`derived/tests/verify_beta.rs`) against a from-scratch
reconstruction of the statement, including checks that the antecedent is a real
membership claim and the conclusion is not reflexivity in disguise.

One neat observation from that work: what must be inhabited for `app(lam(A),a)`
is the *collection* `{y : ⟨a,y⟩ ∈ lam(A)}`, not the value `t(a)`. On the domain
the collection contains `t(a)` whatever `t(a)` is — including empty — so the
inhabitation antecedent discharges for free from `⟨a,t(a)⟩ ∈ lam(A)`. That is
why beta did not get blocked behind the missing empty set.

Still missing, and it *is* the empty-set axiom in disguise: the off-domain
behaviour `app(f,a) = ∅`.

**Tarski's axiom is back, stated correctly.** `Thm::ax_tarski` now carries the
`y ≈ u` disjunct, with equinumerosity spelled out as a first-order formula —
ordered pairs are *described* (`is_opair`, `pair_in`), not introduced as
symbols, so the primitive signature stays `{∈, =}` and no new primitives enter
the trusted base.

The regression test was updated rather than deleted: a Tarski axiom is permitted
again, but the source guard now asserts that any function named `ax_tarski`
mentions `equinumerous`. Absence of that disjunct is precisely what was fatal.

**Three independent findings of the same bug.** The inconsistency was reported
by two subagents working on unrelated tasks and confirmed by me on inspection.
That is worth noting as evidence for the practice: the trusted base benefits
from being read by people who did not write it.

---

## 2026-07-30 — `whnf` emits evidence; a silent gap in `lazy_delta` closed

**Done.** `whnf`, `whnf_no_unfolding` and `whnf_no_unfolding_cheap_proj` keep
their `ExprPtr`-returning signatures — none of their 28 callers changed — and
are now thin wrappers over `*_with_cert` variants that thread a certificate and
memoise it in a new `reduction_certs` cache alongside the existing reduct
caches. Each reduction site calls the corresponding backend rule.

This is the change that makes the backend *get asked*. Previously
`Certifier::beta` and `Certifier::delta` were never invoked at all, because both
happen inside `whnf`, which returned only a reduct.

**Result on 006/007:** the `whnf` and `lazy_delta` gaps are gone, replaced by a
single named root cause, `beta`, with the remainder being cascades over that one
admitted premise. They all close together when the derived beta lemma is wired
in. Gap *counts* rose (3→5 and 2→5) because one opaque terminal admit became a
decomposed chain — that is the accounting becoming honest again, the same
pattern as when `Admit::Whnf` was first introduced. Corpus-wide on
`init-prelude`, `whnf` fell 2681 → 145 and `lazy_delta` 1126 → 0.

**A silent gap this uncovered.** `lazy_delta_step`'s `Exhausted` branch handed
back the *unfolded* pair while the caller's certificate justified that pair
rather than the one it had been asked about. Like the earlier `def_eq`
mis-attribution, this was invisible under `NullCertifier` and would have been a
lie in the chain under a real backend. `Exhausted` now carries its two unfolding
legs.

**Left open** (recorded so it is not forgotten): 145 residual `whnf` admits where
a reduct was memoised by a non-certifying call and re-deriving could return a
*different* reduct (cheap-projection reduces less far), so recovering the
certificate needs per-mode memoisation or a replayable trace rather than a built
certificate. Also `iota`, `quot`, `proj_reduce`, `nat_reduce`, `nat_eq` are new
`Admit` sites rather than backend rules — the `Certifier` trait has no methods
for them yet.

---

## 2026-07-30 — The empty set: not derived, but the independence argument is overturned

**Not delivered:** an unconditional empty set. **Delivered:** both ends of the
bridge, an exact identification of the missing middle, and — importantly — a
correction to an earlier conclusion.

Derived (`derived/src/empty.rs`):

* `no_self_mem` : `⊢ ∀x. ¬(x ∈ x)`, from Regularity at `{x}`. Verified
  independently.
* `empty_from_transitive` : any *non-empty transitive* set yields the empty set.
* `separation_from_transitive` : full Separation, with the emptiness antecedent
  traded for transitivity.
* `universe_power_closed`, and then `inductive_set_exists` :
  `⊢ ∀x ∃u. (x ∈ u ∧ ∀y ∈ u. 𝒫y ∈ u)` — **Tarski gives Infinity.**
* `least_inductive_set_exists` — an `ω` contained in every inductive set, i.e.
  **induction**, carved out by `separation_nonvacuous` with `x` as witness, so
  no empty set is used and the construction is not circular.

**The earlier independence argument does not survive `ax_tarski`.** That
counter-model was generated from a ℤ-chain by pairing, union, relative power set
and replacement, all of which preserve finiteness — but Tarski's `u` has no
∈-maximal member. So the empty set is very likely *derivable* now; what is
missing is length, not principle. Worth recording as a correction: the earlier
entry stated non-derivability as settled, and it was settled only relative to
the axiom set at that moment.

**The exact blocker is transitivity, and it is real.** Tarski's `u` is not
transitive and need not be: from `w ∈ y ∈ u`, clause C₂ gives only `{w} ⊆ y`
hence `{w} ∈ u`, never `w`. Regularity on `u`, `⋃u`, `𝒫m` and `u ∪ ⋃u` all stall
at the same point — everything Tarski adds points upwards.

**The missing middle is the recursion theorem.** With induction in hand,
recursion along `ω` gives the iterates `⋃ⁿx`; their union is the transitive
closure of `x`, and `empty_from_transitive` finishes. Recursion needs only
non-vacuous Separation, so this is non-circular — but it needs finite
approximating functions over `derived/src/funcs.rs`, which is a substantial
piece of work rather than a subtlety.

---

## 2026-07-30 — The universe operator, and the shape the interpretation needs

**Delivered** (`derived/src/universe.rs`): `U(x)`, the least universe containing
`x`, by conservative definitional extension —

    ⊢ ∀x ∀z. (z ∈ U(x) ↔ ∀u. ((is_universe(u) ∧ x ∈ u) → z ∈ u))

Separation is run inside a Tarski universe `u₀` via `separation_nonvacuous`
(witness `x`, so no empty set is needed — which matters, since the empty set is
still not derivable). The `z ∈ u₀` conjunct is then eliminated because the body
at `u₀` implies it, so `u₀` does not appear in the conclusion. That elimination
*is* the well-definedness obligation, and independence of `u₀` is additionally
stated as its own theorem rather than left as an absence.

`is_universe` is checked equal to `ax_tarski`'s own body, so the predicate
cannot drift from the axiom it is supposed to mirror.

**The load-bearing consequence:** `⊢ ∀x. x ∈ U(x)`. Taking
`⟦Sort (n+1)⟧ := U(⟦Sort n⟧)` makes `⟦Sort n⟧ ∈ ⟦Sort (n+1)⟧` immediate — which
is exactly the typing premise beta needs. Verified independently, along with the
tower step `U(x) ∈ U(U(x))`.

**Incomplete: inaccessibility of `U(x)`.** Subset- and power-closure are proved;
clause C₄ is not. `inaccessibility_reduction` isolates precisely what remains: a
non-member subset is equinumerous with *some* universe `u ⊇ U(x)`, and
concluding `y ≈ U(x)` from injections both ways is Cantor–Schröder–Bernstein —
which over spelled-out bijection graphs needs the recursion theorem and `ω`.
That is mathematics, not plumbing, and the agent correctly stopped rather than
half-attempt it. So `is_universe(U(x))` is unavailable, and the "tower" is for
now a membership chain rather than a chain of universes.

---

## 2026-07-30 — SECOND SOUNDNESS BUG: `define` had no free-variable side condition

**Found, exploited, fixed.** `kernel::thm::define` did not check that `phi`'s
free variables are among the parameters. Take `xs = []` and `φ(y) := (y = v)`
for a stray `v`. Then `∃!y. y = v` is provable, the defining axiom is `⊢ f = v`
with `v` free, `gen` makes the implicit quantification explicit as `⊢ ∀v. f = v`,
and two instantiations give `c₁ = c₂` for arbitrary constants.

**I confirmed this by actually deriving `c₁ = c₂`** before fixing it — the hole
was exploitable, not merely theoretical.

The underlying error: the witness proves "for each `v` there is a unique `y`",
so `y` depends on `v` — but `f(x⃗)` takes no `v`, so the axiom claims one `f`
works for every `v`. Strictly stronger than what was proved, and exactly the
condition under which extension by definitions stops being conservative.

Fixed by requiring every free variable of `phi` to be a parameter or the defined
variable. `derived/tests/define_soundness.rs` reconstructs the exploit and
asserts refusal, and checks the property *is* accepted once `v` is a parameter,
so the condition is a side condition and not a blanket ban.

Fallout: `define_abbrev` now returns `Option`, since a caller building terms
dynamically can legitimately hit the condition. One existing test was itself
exercising the unsound case (`f() := g(a,b)` with `a,b` free, which yields
`g(a₁,b) = g(a₂,b)`) and was corrected.

**Both TCB bugs this session were found by readers who did not write the code**
— the first (Tarski) by two subagents on unrelated tasks, this one by an agent
that noticed it in passing while doing something else and chose to avoid rather
than exploit it. That is now a strong enough pattern to act on: the trusted base
should be reviewed by an agent whose only job is to attack it.

---

## 2026-07-30 — Beta wired end to end; it derives

`Certifier::beta` now discharges the real derived lemma. `⟦Sort 0⟧` is a fresh
constant and `⟦Sort (u+1)⟧ := U(⟦Sort u⟧)`, so the typing premise `a ∈ A` is an
instance of `x ∈ U(x)`. `⟦App f a⟧` is `app(⟦f⟧,⟦a⟧)` and `⟦λx:A. b⟧` is a real
function graph.

**Result:** `checker/tests/fixtures/good/beta-sort-argument.ndjson` — a
two-argument contraction under a constant that must be delta-unfolded first —
reports **15 derived, 0 gaps, "every definitional-equality step was fully
derived"**. Verified independently. Across `init-prelude`, 291 beta steps close.

The lambda body abstraction is **faithful, not opaque**: `⟦b[v]⟧` is split into
a skeleton plus its maximal `v`-free subterms, which become extra parameters.
That decomposition is stable under substitution, which is what makes `⟦b[a]⟧`
come out syntactically equal to the skeleton with arguments plugged in. An
opaque body would have been useless — the guard would reject every
instantiation.

**006/007 still do not close**, and the reason is precise: the checker contracts
both leading lambdas in a *single* `Certifier::beta` call, and while the first
contraction derives (`⟦Prop⟧ ∈ ⟦Sort 1⟧` is `x ∈ U(x)`), the second needs
`⟦Prop→Prop⟧ ∈ ⟦Sort 1⟧` — function-space closure in a universe, which is not
derived. One certificate covers the composite, so the whole call admits.

**A regression accepted deliberately:** `lam_cong` now reports a gap (979 on
`init-prelude`), because `⟦λ⟧` is a graph whose head symbol depends on the
body's shape, so congruence in the sub-positions no longer yields the claim.
Producing the old conclusion would have been a `Proved` without a matching
guard. Net effect is still positive: derived +277, gaps −277.

---

## 2026-07-30 — THIRD AND FOURTH SOUNDNESS BUGS, from a dedicated adversarial review

Both TCB bugs so far had been found by readers who did not write the code, and
neither by the test suite. Acting on that, I put an agent on `kernel/` with one
instruction — break it — given both prior exploits as worked examples, told to
*demonstrate* rather than suspect, and forbidden from fixing anything. It found
two more, each with a working derivation of `⊥`.

### 3. `ax_replacement` had no `x ≠ y` side condition

With `x == y`, the image `∃x. (x ∈ a ∧ φ)` closes over `y` as well, so the
right-hand side of the `↔` no longer mentions the quantified variable and the
conclusion degenerates to `∃b ∀y. (y ∈ b ↔ <y-free>)` — a **universal set**
whenever that formula holds, which Regularity refutes. Confirmed by inspection.

The shape of this bug is instructive: `define` *does* check the analogous
condition (`y ∉ xs`, with a comment explaining the capture), and
`ax_replacement` is the sibling that never got it — and, unlike `define`,
returned a bare `Thm`, so there was nowhere for a rejection to surface. Now
returns `Option`, refusing `x == y` and also refusing any collision between the
caller's variables and the three the scheme generates for itself.

### 4. Freshness was per-generator, but identity was global

`Env::new()` and `VarGen::new()` were both public and both started their
counters at zero, and `Thm` carries no environment tag — so theorems minted
against different generators were freely combinable. Two exploits:

* Two `Env`s produce the *same* `FnSym`, hence two contradictory defining axioms
  for one symbol: `f(t) = t` and `f(t) = {t}` give `t = {t}`, so `t ∈ t`.
* Within a single `Env`, a `VarGen::new()`-minted variable can alias one that
  `ax_replacement` is about to generate, capturing its `∃b` and again yielding
  a universal set.

Every freshness argument in the kernel — "`a`, `b`, `y2` are fresh, therefore
cannot occur in `φ`" — was an assumption about the *client*, enforced nowhere.

Fixed by **branding**: each `Env` takes a unique brand from a global counter, and
`FreeVar` and `FnSym` carry it, so symbols and variables from different
environments can never compare equal. `VarGen` is now crate-private, so the only
source of a variable is `Env::fresh_var`. Regression tests in
`derived/tests/kernel_attacks.rs`.

### The pattern is now the finding

Four soundness bugs, all in the trusted base, none found by tests. Every one was
found by reading with intent to break. Testing checks the cases you thought of;
the TCB's failures have all been cases nobody thought of. **An adversarial review
pass should be a standing part of this project's process, not a one-off** — and
it should run after every substantive change to `kernel/`.

---

## 2026-07-30 — Function space in a universe: the last set-theoretic rung

**Delivered** (`derived/src/funspace.rs`): **`⊢ ∀a. fs(a,a) ∈ U(a)`** — verified
independently. This is what makes `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` available, the one
fact tutorial 006/007 still lacked.

Two places the obvious route did not work, both instructive:

**The product needs Replacement, not Separation.** `a × b` can be empty
(`∅ × b = ∅`), so `separation_nonvacuous` is unusable and there is no
inhabitation witness to invent. Built instead as three total steps:
`row(x,b) = {⟨x,y⟩ : y ∈ b}` and `fam(a,b) = {row(x,b) : x ∈ a}` by Replacement,
then `prod(a,b) := ⋃fam(a,b)`. Unconditional, no antecedent anywhere.

**The function space needs the empty set, so it is total by default.**
`a → b` is empty when `a` is inhabited and `b` is not, so `fs` uses the same
total-by-default trick as `funcs::collection`. That leaves membership
conditional in general — and the agent then *discharged the antecedent on the
diagonal* by constructing the identity graph and proving it is a function, which
matters: without it `fs(a,a)` could for all one knew *be* `𝒫(prod(a,a))`, and
the payoff would have been a true statement about the wrong set. That is exactly
the kind of check that separates a real result from a plausible one.

**Blocked, honestly:** the two-argument case needs `a ∪ b ∈ U(c)`, i.e. closure
of `U(x)` under binary union. That does not follow from `C₂ ∧ C₃` — the only
clauses proved for `U(x)` — and would follow from inaccessibility, which is open
(Cantor–Schröder–Bernstein). It is carried as an explicit antecedent in
`funspace_in_universe_of` rather than assumed.

---

## 2026-07-30 — GOAL MET: the lambda/app/def tutorial tests derive completely

With `--features tg`, tutorial exports **001, 003, 004, 005, 006, 007, 008 and
015** all report *"every definitional-equality step was fully derived"*, zero
gaps. 006 and 007 are the beta-reduction tests; 015 came along for free.

The chain underneath is derived, not assumed: Kuratowski pairs and their
injectivity, the Cartesian product by Replacement, the function space, the least
universe `U(x)` with `x ∈ U(x)`, `fs(a,a) ∈ U(a)`, the lambda graph, `app`, and
`beta_conditional`. `⟦Sort (n+1)⟧ := U(⟦Sort n⟧)` makes the typing premise an
instance of `x ∈ U(x)`; non-dependent `Π` interprets as `fs`, which makes
`⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` an instance of `fs(a,a) ∈ U(a)`.

### A near miss worth recording

The wiring agent reported 006/007 at zero gaps and, in the same report, noted in
passing that `pi_cong` "still returns `Proved` for a theorem it does not match
against the claim", calling it a pre-existing documented exception.

It was not incidental: **the zero-gap result depended on it.** Forcing `pi_cong`
to admit dropped 006 from 15/0 to 13/2. So the headline claim was, at that
moment, resting on exactly the unguarded `Proved` I had told the agent was worse
than a gap.

The root cause was a *trait design* flaw, not an implementation slip:
`lam_cong`/`pi_cong` received only sub-certificates, so a backend **could not
check what it was being asked to prove** even if it wanted to. Fixed by passing
the two terms, so the rule compares its result against `⟦a⟧ = ⟦b⟧` and reports an
honest gap on mismatch. The tests then still come out at zero gaps — but now
because the steps are checked, not because nobody looked.

**The lesson generalises:** every rule that concludes something about two
specific terms must be handed those terms. A rule that cannot compare its output
against the claim can only guess, and a guess returned as a proof is the exact
failure this project exists to prevent. That principle is now stated in the
`Certifier` trait docs.

---

## 2026-07-30 — Pre-inductive tutorial tests: 20 → 25 of 27

The goal is every tutorial test *before inductives are introduced* (001–032;
`033_empty` is the first file with an `inductive` declaration) to derive with no
gaps. Two interpretation fixes, both in the translator rather than the kernel:

**Zeta.** `let` now gets an **explicit definition** of its expansion — exactly
as a constant gets one of its value — so zeta reduction *is* the defining
equation. The alternative, interpreting `⟦let x:=v; b⟧` directly as `⟦b[v/x]⟧`,
would have made zeta reflexivity and left the kernel certifying nothing about
the step; that is the same trap as interpreting via a normaliser. Because the
expansion can mention Lean locals, its free variables become parameters of the
symbol — `define` refuses a body with a free variable it does not abstract.
Closes `032_letRed`.

**Level algebra.** `simplify` is not a normal form: it settles neither
commutativity, associativity, idempotence nor absorption of `max`, so `max u v`
and `max v u` stayed syntactically distinct while the checker rightly called
them equal. Rather than reimplement level algebra — `CLAUDE.md` puts levels in
the translator — the interpretation now keeps one representative per
equivalence class, decided by the checker's own `eq_antisymm`. Closes 021, 022,
023, 024, 027.

**A self-inflicted crash worth recording.** The first version canonicalised
inside `interp_level`, which then decomposed the representative — and a
sub-level can canonicalise *back to the whole*: absorption maps `succ u` to
`max u (succ u)`, whose own sub-level is `succ u`. Infinite recursion, and the
arena aborted. Fixed by canonicalising once, at the dispatch point in
`interp_sort`, where the shape choice actually matters; `interp_level` recurses
structurally and does not canonicalise. The lesson: canonicalisation and
structural recursion do not compose naively, because a canonical form need not
be structurally smaller than its input.

Remaining: `028_peano2` and `029_peano3`, blocked by the congruence family.

---

## 2026-07-30 — Lambda graph extensionality derived

`derived::ext::lam_ext`:
`⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → t(x) = t'(x))) → lam(A) = lam'(A')))`,
plus a same-domain corollary. This is what `lam_cong` needs: `⟦λ⟧` is a *graph*,
so congruence over sub-terms does not give the claim — two graphs are equal
because they have the same members, which is Extensionality.

Also `ext::DProd`, the dependent product, replacing the opaque `Π` symbol with
one that has a real membership property. It carries an inhabitation antecedent
and that is genuine, not an artefact: a dependent product really can be empty
(any `x ∈ A` with `b(x)` empty), and naming the empty product needs `∅`, which
these axioms still do not supply.

**`pi_cong` is not closed by this**, and the agent said so rather than implying
otherwise: it additionally needs `dprod` extensionality. The useful observation
it left is that the first step of that argument has exactly the shape of
`lam_ext` with `b(x)` in place of `⟨x,t(x)⟩`, so generalising `lam_ext` to
arbitrary Replacement-image symbols is the right next increment.

---

## 2026-07-30 — Zeta with a free-variable expansion: it works, but was untested

Asked whether "let as definition" handles a right-hand side with free
variables. It does — the expansion's free variables become parameters of the
defined symbol, which is required because `kernel::thm::define` refuses a body
with a free variable it does not abstract.

But the honest answer at the time was **"unverified"**, and checking that was
more informative than the answer:

* Forcing `zeta` to admit and re-running the corpus shows it fires **exactly
  once** in the whole tutorial suite — `032_letRed` — and that case's expansion
  is *closed*. On `init-prelude`'s 2059 declarations it never fires at all.
* My first attempted test (`let` under a lambda) reported zero gaps *whether or
  not zeta was forced to admit*, i.e. it never reached zeta. It would have been
  a test that could not fail.

The case is now genuinely covered by `tests/fixtures/good/let-free-variable.ndjson`:
`∀ x : Type, (let y := x; y) → x` proved by `λ x p. p`, which forces
`(let y := x; y) ≡ x` through definitional equality with the expansion being the
local `x`. Confirmed to reach zeta by the same forced-admit method.

**The technique generalises and is worth reusing:** to check whether a rule is
actually exercised by a test, force it to admit and see whether the gap count
moves. A rule that never fires makes its tests vacuous, and nothing in the
normal output distinguishes "derived it" from "never asked".

---

## 2026-07-30 — The empty set arrives; the total-by-default hacks come out

`Thm::ax_empty` is now a kernel axiom (see its doc comment for why this one is
asserted rather than constructed). Downstream, three constructions had been
carrying a *default disjunct* purely because the empty case had no name:
`funcs::collection`, `funspace::fs` and `ext::DProd` were each defined as
"the intended condition, **or** an arbitrary fallback if nothing satisfies it".

All three defaults are now **gone from the definitions**, not merely hidden
behind a wrapper. Their characteristic theorems are unconditional:

* `⊢ ∀f ∀a ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f)`
* `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ isfun(f))`
* `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))`

Separation is now callable and unconditional —
`⊢ ∀a ∀z. (z ∈ sep_φ(a) ↔ (z ∈ a ∧ φ(z)))` — verified independently. And
`app_off_domain` finally states what was previously unstatable:
`⊢ ∀f ∀a. ((¬∃y. ⟨a,y⟩ ∈ f) → app(f,a) = ∅)`, which together with
`beta_conditional` makes application total: one theorem on the domain, one off
it.

Two details worth keeping:

**`separation_full` consumes the empty set** — `e` is discharged as the
existential's witness, so `∅` appears in no downstream theorem. That is why
`Apply` and `Space` can each derive their own `∅` without the results failing to
compose.

**The Tarski bridge in `empty.rs` was kept, not deleted.** `empty()` is based on
the axiom, but `empty_from_transitive` and the induction results still stand, so
if the recursion theorem is ever built, `empty()` can be re-based on them and the
axiom retired. Recorded in that module's docs.

Still conditional, and correctly so: `beta_conditional`'s domain premise (a set
function has a set domain — now complemented by `app_off_domain`), and
`funspace_in_universe_of`'s `(a ∪ b) ∈ U(c)`, which is unrelated to `∅` and needs
inaccessibility for `U(x)`.

---

## 2026-07-30 — FIFTH SOUNDNESS BUG: the brand counter wrapped

Found by the second adversarial kernel audit, **demonstrated to `⊢ ⊥`**, and it
was mine — introduced by the fix for bug #4.

```rust
NEXT_BRAND.fetch_add(1, Relaxed).checked_add(1).expect("…overflow")
```

`fetch_add` on an atomic **wraps**: `overflow-checks` does not apply to atomics.
The `checked_add` guard inspects the value `fetch_add` *returns* — the previous
one — so it fires exactly on the call where the counter has *already* reset to
zero. It is a one-shot gate, not a latch: swallow the single panic (it is
catchable safe Rust) and the next `Env` is handed brand 1 again, colliding with
the first `Env` ever created. Cross-environment symbol collision restored in
full, and from there two contradictory defining axioms for one symbol give `⊥`.
The auditor ran it: ~23 s, and it reached `⊥`.

Fixed with `fetch_update`, whose closure returning `None` leaves the counter
untouched, so exhaustion latches permanently. Unit-tested against a pre-loaded
counter, which gets the property in microseconds rather than 2³² allocations.

**Three lessons, and the third is the important one.**

1. *A panic is not a fence.* It is catchable safe Rust. A guard must make the
   bad state unreachable, not merely announce it after arriving.
2. *Atomics do not honour `overflow-checks`.* The identical `checked_add` idiom
   used for `Env::declare` and `VarGen::fresh` is correct, because those are
   plain fields written only after the check succeeds. Only the atomic wraps —
   the same-looking code was right in two places and wrong in the third.
3. **The fix for a soundness bug is itself a soundness-critical change, and
   deserves the same adversarial reading as the original.** Bug #5 exists only
   because of the fix for #4, and it survived my own review of that fix.

This also refines the earlier judgement that "the kernel is essentially frozen,
so adversarial review can be trigger-only". That still holds — but the trigger
must include *fixes to the kernel*, not just features, and the existing
regression test for #4 did not catch #5 because it only created two `Env`s.

The audit was otherwise a reasoned clean bill: all eight axioms re-derived by
hand from the de Bruijn output rather than read off doc comments, `ax_empty`
confirmed genuinely existential, `ax_replacement`'s side conditions confirmed
sufficient (they compare by value, so they survive a brand collision), `define`'s
edge cases (duplicate parameters, arity overflow, cross-`Env` inputs) argued
sound, the locally-nameless invariant confirmed unbreakable from outside, and the
hash short-circuit confirmed a fast *reject* only.

---

## 2026-07-30 — `lam_cong` wired; and a negative result on the typing bridge

**`lam_cong` now derives.** `lam_ext_n` threads a parameter prefix through each
side of `derived::ext::lam_ext`, mirroring `lambda_n`/`beta_conditional_n`;
`pointwise_premise` recovers the binder's free variable by candidate search and
*verifies* each candidate by instantiating the body definitions and comparing;
`lam_cong` then checks its result against `⟦a⟧ = ⟦b⟧` before `Proved`.
Corpus-wide `lam congruence` gaps: **572 → 2**. Tutorial files fully derived:
**27 → 64 of 91**.

**But the agent was straight about what earned that**, and it is worth recording
against the "no shortcuts" standard: of 566 newly-closed cases, 72 came from the
real extensionality derivation and 494 from a reflexivity fallback — and every
one of the 72 *also* had `⟦a⟧ == ⟦b⟧`, so reflexivity alone would have closed
all 566. On this corpus the extensionality machinery buys nothing over
`eq_refl`. It is the general rule that will matter once upstream gaps stop
starving the body certificates, but it has not yet earned the number.

Why it misses: `def_eq_binder_aux` folds binder chains innermost-first and
pushes the lambdas **un-instantiated**, so an inner frame's lambda carries loose
de Bruijn indices while the certificate under it concerns bodies opened at real
locals. Chains of length ≥ 2 are unreachable at every frame.

## The typing-bridge attempt: implemented, measured, reverted

A separate agent implemented certificate-carried typing hypotheses in full —
`TgCert::Proved { thm, hyps }` with the theorem literally
`⊢ (h₁ ∧ … ∧ hₙ) → ⟦a⟧ = ⟦b⟧`, weakening and merging, implication-form
`eq_trans`/`congr_arg`, discharge via `uncurry` + `gen` + `ax_dist`, and an
escape tracker — then **measured it firing zero times** and reverted.

My brief's premise was wrong. I said 028/029's beta arguments have types that
are locals; the *types* do, but the **arguments** are constants and
applications, never variables. Classifying every `beta: argument not shown to
lie in the binder's domain` across the corpus:

| argument is | count |
| --- | ---: |
| an application | 2151 |
| a lambda | 1503 |
| a constant | 1183 |
| other | 105 |
| a `Pi` | 64 |
| a local, binder type ≠ domain | 27 |
| **a local, binder type = domain** | **0** |

So the rule I specified has no call site anywhere. A follow-up experiment with
the most generous version — record `⟦a⟧ ∈ dom` for *any* argument — got 028 from
32 to 8 gaps and 029 from 59 to 9, discharging nearly everything, but the
residue is exactly the binder-chain limitation above.

**Closing 028/029 therefore needs both**, and neither is reachable from
`tg.rs` alone:

1. A real typing bridge `Γ ⊢ a : A ⟹ ⊢ ⟦a⟧ ∈ ⟦A⟧` for constants and
   applications at *dependent* Π types — which needs `⟦Π⟧` to be
   `ext::DProd`'s `dprod` rather than the axiom-free `pi` symbol (membership in
   `pi` is not merely underived, it is unstatable), plus a `has_type` family on
   `Certifier` so `infer` can hand typing evidence down.
2. `def_eq_binder_aux` in `tc.rs` passing down *instantiated* binders.

Recording the measurement matters as much as the conclusion: a design that
looks obviously right can have zero call sites, and only counting finds that.

---

## 2026-07-30 — Image extensionality generalises `lam_ext`; dependent products too

The parting observation from the `lam_ext` work — that its argument never
depended on the body being `⟨x, t(x)⟩` — turned out to be right, and acting on
it removed a near-duplicate derivation rather than adding one.

`ext::image_ext` :
`⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → g₁ = g₂)) → img(A) = img'(A')))`
for any two Replacement-image symbols. `lam_ext` is now a ~40-line instance of
it with `g(x) := ⟨x, t(x)⟩`, and its **public statement is unchanged** — the
four pre-existing tests that pin its exact conclusion pass unmodified, and the
test file's diff removes exactly one line (an import).

`ext::dprod_ext` :
`⊢ ∀A ∀A'. (A = A' → ((∀x. (x ∈ A → b(x) = b'(x))) → dprod(A) = dprod'(A')))`,
plus a same-domain corollary. Verified independently, including that the
conclusion equates two *different* products rather than being reflexivity in
disguise. This is what `pi_cong` needs: `⟦Π⟧`'s head symbol depends on the
fibre's shape, so congruence over sub-terms cannot give the claim — exactly the
situation `lam_ext` fixed for lambdas.

**A good instance of checking rather than assuming:** I had guessed `fs_cong`
(congruence for the function space) might be immediate from `derived::congr`.
The agent checked first and found it is not — `congr` consumes two *proved*
equations and yields a *proved* equation, whereas the required form is a
universally quantified implication, which a Hilbert system has to assemble.
Trivial in substance, not free in form.

Also added the missing equality machinery for the `⊢ H → φ` idiom (`curry`,
`hyp_leibniz`, `hyp_congr`, `hyp_eq_trans`, `hyp_eq_symm`); `hyp_congr` *checks*
that the caller's substituted left-hand side really is `c[a/w]`, since terms
cannot be substituted from outside the kernel.

---

## 2026-07-30 — Binder frames instantiated: the real extensionality path now fires

`def_eq_binder_aux` now records how many locals were introduced above each
frame and instantiates λ frames at that prefix before handing them to
`lam_cong`. Deferred to the fold rather than done during the descent, so a chain
that fails midway pays nothing.

**Effect on the real-derivation share** — this was the point, and it worked:

| | before | after |
| --- | ---: | ---: |
| `lam_cong` calls | 1751 | 1751 |
| via the real derivation | 135 | **1373** |
| via the reflexivity fallback | 1328 | **144** |
| inner frames (depth ≥ 1) real | 133 / 1401 (9.5%) | **1126 / 1401 (80%)** |
| `body certificate is not the pointwise equation` | 22 | **0** |

**But the honest headline is 54 net new closures**, not 1238: of the 1373 real
derivations, 1319 are on lambdas that interpret identically, where reflexivity
would have sufficed anyway. The qualitative change — extensionality now applies
at depth, rather than never — is much larger than the coverage change. Recording
both numbers, because quoting only the first would be exactly the kind of
shortcut the current goal rules out.

**Π frames are deliberately *not* instantiated**, which deviates from my brief
and is right: `⟦Π⟧` is a symbol applied to the interpretation of the *raw de
Bruijn* body, so `pi_cong` is compositional over the un-instantiated subterm,
whereas `⟦λ⟧` is a graph built by opening the body at a local. The agent
measured both ways — instantiating Π frames too made `init-prelude` a net 10
gaps *worse*.

**028/029 were unaffected, and my hypothesis about them was wrong.** Each has
exactly 3 `lam_cong` calls and all 3 fail as `over an admitted premise`: the body
certificate is already a gap before extensionality is reached. Frame plumbing was
never what blocked them. What does is beta's typing obligation `⟦a⟧ ∈ ⟦A⟧`, which
the backend can discharge only for sorts and diagonal arrows.

Also corrected: I had listed `let-free-variable.ndjson` among files that must
stay at 0 gaps. It was 2 gaps at baseline — its assertion is specifically that
*no zeta gap* arises, not that the file is clean.

---

## 2026-07-30 — `pi_cong` derives properly, and closes nothing

`pi_cong` now reads its premise targets off the claim and discharges via
`ext::fs_cong` (non-dependent) or `derived::congr` (opaque `pi`), with the
result still checked against `⟦a⟧ = ⟦b⟧`. A new `retarget`/`match_term` re-aims
a certificate stated at the checker's *opened* locals at the raw de Bruijn form
the claim uses — the step the module docs had said "is not taken here".

**Real-vs-fallback moved 100%** (tutorial 457/573 → 1030/0; init-prelude
3746/1338 → 5084/0) and **no gaps closed at all**. Same pattern as `lam_cong`:
the reflexivity fallback fires exactly when both sides interpret to the same
term, which is also when congruence is trivial. Only 8 (tutorial) / 57
(init-prelude) of ~1030 / ~5084 conclusions relate genuinely different terms —
and that number is unchanged.

`fs_cong` is *provably* a no-op for coverage: it is two Leibniz steps plus
transitivity, so its conclusion is identical to what `derived::congr(fs, …)`
already produced. Wired in anyway as the intended lemma, at no cost.

**`dprod_ext` measured and declined.** Instrumenting for "a unary fibre would
suffice *and* both premises are real" gives **11 cases on init-prelude, 1 on the
tutorial corpus**. The rest needs an n-ary re-derivation of the whole `DProd`
stack inside `tg.rs` (which may not touch `derived/`), for ≤272 of 4634. Not
done, deliberately.

**What actually blocks the 4634**, now that `pi_cong` names gaps honestly
instead of reporting them all as its own:

| cause | count |
| --- | ---: |
| cascades from an already-admitted premise (mostly beta's typing obligation) | 2682 |
| encoding mismatch — one body mentions the binder, the other does not, so `pi` vs `fs` | 1196 |
| de Bruijn shift — `fs(⟦A⟧,⟦B⟧)` puts `A` and `B` one binder apart | 756 |

Two interpretation changes (exact non-dependence via `mentions_bvar`, and
re-basing a non-dependent Π's body indices) were implemented, measured, and
**reverted**: both raised `retarget` hit rates but gave byte-identical totals on
both corpora. They only shuffled gaps between sub-categories.

**The conclusion across three agents is now unanimous**: `lam_cong`, `pi_cong`
and the typing-hypothesis attempt all bottom out on the same thing — beta's
obligation `⟦a⟧ ∈ ⟦A⟧`, which the backend can discharge only for sorts and
diagonal arrows. That is the single remaining lever.

---

## 2026-07-30 — Beta's typing obligation becomes a carried assumption

`Certifier::beta` no longer admits when it cannot prove `⟦a⟧ ∈ ⟦A⟧`; it keeps
the membership as the antecedent of an already-conditional beta lemma, and the
assumption is propagated and discharged.

`TgCert` gains a **`Conditional { thm, hyps }`** variant — deliberately *not* a
field on `Proved`. Keeping them separate means `TgCert::thm()` retains its exact
old meaning (`Some` only for an unconditional equation), every existing consumer
is untouched, and the cardinal rule stays checkable by reading the `Proved`
sites alone. The theorem is literally `⊢ (h₁ ∧ … ∧ hₙ) → ⟦a⟧ = ⟦b⟧`, and the
internal `CondEq` constructor *checks* that `hyps` really is the antecedent — a
rule cannot advertise an assumption list it does not have.

| | before | after |
| --- | ---: | ---: |
| `beta: argument not shown to lie in the binder's domain` | 206 | **0** |
| tutorial total gaps | 726 | **586** |
| `init-prelude` gaps | 23812 | **18025** |
| `028_peano2` | 32 | **8** (0 escaped) |
| `029_peano3` | 59 | **9** (1 escaped, *reported as a gap*) |
| tutorial files at 0 gaps | 64/91 | 64/91, none regressed |

**The escape ledger is the load-bearing safeguard.** Conditional certificates
are counted when created (including in a hand-written `Clone`, since a copy is a
second obligation) and when consumed by a rule; the difference is reported as a
gap and included in `TOTAL gaps`. The residual error direction is stated in the
code and is one-way: it can **over**-report, never under. I verified the
invariant that matters — of the 64 tutorial files reporting zero gaps, **zero**
have a nonzero escape count.

Escapes are real, not noise: an assumption `⟦a⟧ ∈ D` can only be discharged at a
binder when `a` *is* that binder's variable, and the corpus's beta arguments are
constants and applications. 128 tutorial and 2507 prelude certificates therefore
finish conditional and are counted as gaps rather than dropped.

**Two gap reasons are newly *visible*, not newly caused** — `beta: the lambda's
graph was not built` and `beta: derived equation does not match the reduction`
were previously masked because the domain premise was tested first and returned
early.

**`MAX_HOLES` has stopped being free.** It used to be provably irrelevant —
coverage was byte-identical at 2/4/8/16/∞ — *because* the domain premise was the
binding constraint. It no longer is: 8 → 18025 prelude gaps @5.4 s; 16 → 16830
@6.8 s; 64 → 16199 @10.2 s. Left at 8 for now, with the measured table replacing
the now-false "this cap is free" claim. This is exactly the kind of
small-corpus-shaped shortcut the current goal rules out, and it is now the next
thing to address.

Runtime +22% (4.40 → 5.36 s on `init-prelude`), and not quadratic: the largest
assumption set anywhere is 8 against a cap of 12. Confirmed by building the same
tree with only the introduction site disabled — the cost is work now actually
being done.

---

## 2026-07-31 — A constant-fibre dependent product *is* the function space

`ext::dprod_const_fibre` :
`⊢ ∀A ∀B. ((∀x. (x ∈ A → b(x) = B)) → dprod(A) = fs(A, B))`

This bridges the two ways the checker interprets `Π` — function space when the
body does not mention the binder, dependent product when it does — which was the
second-largest gap category (1196 on `init-prelude`).

**Derived in full generality: no inhabitation antecedent, empty domain
included.** The agent declined the route I sketched, and was right to: going via
`⋃img(A) = B` genuinely needs `A` inhabited, since `⋃img(∅) = ∅` whatever the
fibre. It is also avoidable — the two codomains are never compared as sets.

Instead, three new supporting lemmas:

* `app_of_pair` : `⊢ ∀f ∀x ∀y. ((sv(f) ∧ ⟨x,y⟩ ∈ f) → app(f,x) = y)`
* `funspace_app_mem` : `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)`
* `funspace_retarget` : `⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ ∀x ∈ a. app(f,x) ∈ c) → f ∈ fs(a,c))`

`funspace_retarget` is the key: a function's codomain may be swapped for any set
its *values* land in, so the constant-fibre case never needs the image
computed. The empty domain then goes through unchanged — every `x ∈ A`
quantifier is vacuous — and there is an end-to-end test instantiating at `A := ∅`
and discharging the fibre hypothesis by ex falso.

Verified independently, including that the two sides are different head symbols
rather than the same term. The stack is *checked* rather than assumed: `fs_ax`,
`dprod_def`, `img_ax` and `prod_ax` are each compared against independently
rebuilt conditions, so a mismatched product, fibre or `DProd` returns `None` —
tested four ways.

Note the new API takes the `Product` that `fs` was carved out of; the checker
will have to thread it through when wiring this in.

---

## 2026-07-31 — `MAX_HOLES` removed; the lever was sharing, not speed

The cap is **gone**. `beta: the lambda's graph was not built` and
`lam congruence: graph was not built` are both **0** across the corpus, down
from 1228/24 and 102.

| | before | after |
| --- | ---: | ---: |
| `init-prelude` gaps | 18,025 | **16,009** |
| tutorial gaps | 586 | **538** |
| tutorial files at 0 gaps | 64/91 | 64/91, none regressed |
| runtime / peak RSS | 5.4 s / 23 MB | 8.9 s / 99 MB |

**The profile said the fix could not be "make construction faster".** Of the
~130 µs per skeleton, ~100 µs was `lambda_n`, and 88% of *that* was the
Extensionality-uniqueness proof inside `derived::define_by_membership` —
irreducible without touching `derived/`. The fix had to be *fewer*
constructions.

**And it was.** A skeleton contains only `app`/`proj`/`Π` structure, canonical
variables, and nested lambdas' graph symbols. With a per-declaration `Env` those
symbols differ every time, so the *same shape* produced a *different term* per
declaration: **32,388 distinct skeleton terms for 1,566 distinct shapes**, a
factor of 20 of pure repetition. Moving the signature (`Env`, `Syms`,
`hole_vars`, the lemma caches) into a per-thread `Shared` cell collapses it to
2,651, and `lambda_n` drops 2,261 ms → 164 ms at the old cap. That headroom paid
for removing the cap entirely.

**No finite cap was ever principled.** Hole distribution over 2,651 skeletons:
34% need 1–4, 22% need 5–8, 21% need 9–16, 14% need 17–32, 6% need 33–64, **3%
need more than 64**, reaching past 128. The tail thins but does not stop — every
cap is a bet on the corpus, which is exactly what the current goal rules out.

**Where the remaining 8.9 s goes is derivation, not overhead**: `beta_step` is
3.8 s against 0.66 s for every graph in the run. A redex over a `k`-hole lambda
instantiates a formula whose size grows with `k`, one quantifier at a time —
O(k²) in the kernel's `open`/`close`. That is work that buys coverage, which is
why it is no longer hidden behind a constant.

Two things recorded rather than fixed:

* **Counters now accumulate across a run** — 40,264 symbols and 463,129
  variables on `init-prelude` (~225 vars/declaration), against `u32` each. Three
  orders of magnitude more approaches the variable limit; the kernel uses
  `checked_add`, so that is a panic, never an aliased variable. The remedy
  (drop `SHARED` and start fresh) is noted in the code.
* **Tried and rejected**: pre-instantiating each lambda's beta lemma and body
  definition with the hole prefix. ~10% faster for 3–5× the memory (285–466 MB).
  Not taken, not left in the code.

---

## 2026-07-31 — A dependent `Π` is a dependent *product*

`⟦Π x:A. B⟧` was `fs(⟦A⟧,⟦B⟧)` when the body ignored the binder and an opaque
`pi(⟦A⟧,⟦B⟧)` otherwise. The second is now `dprod_C(s⃗, ⟦A⟧)` — a real
definitional extension over a fibre symbol built by the *same* skeleton
decomposition the lambdas use, so the binder is opened at a local and the fibre
symbol carries the body's binder-free subterms as a parameter prefix.

**The unary `derived::ext` API does not reach the checker.** A `Π` body
generally interprets to a term with free variables besides the binder's, which a
unary symbol may not contain; a previous measurement put the unary case at 11
occurrences on `init-prelude`. So `image_symbol`, `dprod_symbol`,
`dprod_const_fibre` and `dprod_ext` are repeated in `checker/src/tg.rs` in
parameter-threading form (`*_n`), exactly as `lambda_n`/`beta_conditional_n`/
`lam_ext_n` already were, with the `b`-independent halves of the bridge
(`app_of_pair`, `funspace_app_mem`, `funspace_retarget`) hoisted into the
thread's prelude. Each is pinned to its exact conclusion by a test, and each
rejects a mismatched fibre, image, product or axiom — tested six ways.

**The prelude had two ordered pairs.** `Apply::new` and
`funspace::Development::new` each build their own `Sets`, so `app`'s pairing and
`fs`'s were different symbols. That was free while no lemma mentioned both; the
bridge (`f ∈ fs(A,B) → app(f,x) ∈ B`) is exactly such a lemma, so the
development is now assembled by hand over `ap.sets`.

**`def_eq_binder_aux` now instantiates `Π` frames** at the locals above them, as
it already did for `λ` frames. It deliberately did not, *because* `⟦Π⟧` was
built over the raw de Bruijn body; that reason is gone. Measured, the change is
worth 143 prelude gaps on its own — without it the bridge and the Extensionality
route are unreachable below the outermost binder.

| | before | after |
| --- | ---: | ---: |
| `init-prelude` gaps | 16,009 | **15,954** |
| … `pi congruence`, all reasons | 4538 | 4480 |
| … dependent/non-dependent interpret differently | 1196 | **0** |
| … cascade: the body premise was itself admitted | 2427 | 2868 |
| … the body certificate does not make the fibre constant | — | 621 |
| … the body certificate is not the fibres' pointwise equation | — | 283 |
| tutorial gaps | 538 | **535** |
| tutorial files at 0 gaps | 64/91 | **65/91** |
| runtime / peak RSS | 8.8 s / 100 MB | 8.5 s / 127 MB |

`028_peano2` (8) and `029_peano3` (9) are unchanged, no tutorial file
regressed, and of the 65 files at zero gaps **zero** have a nonzero escape
count.

**The headline is the third row, and the fourth explains why it is not larger.**
The encoding mismatch is gone as a category. What it turned into is mostly not
`pi_cong`'s to fix: of the 621 bridge failures, ~500 are cases where the
certificate handed down is *reflexive and mentions neither body*. `app_cong` is
handed sub-certificates rather than terms, so a certificate reaching a binder
need not be about that binder's bodies at all; `pi_cong` checks and reports a
gap rather than bending it. The largest category by far remains the cascade — a
beta step below whose typing obligation is undischargeable — which no congruence
rule can repair, and which grew because cases that used to be settled by the
reflexivity fallback now relate genuinely different terms.

**Also gone: the de Bruijn shift**, 756 gaps where the claim carried two
different `bvar` symbols for one binder. With every binder in a `Π` tower opened,
an interpreted term contains no `bvar` symbols at all.

**Cost: +27 MB peak RSS, no runtime.** Every distinct `Π` body shape now carries
a fibre, a Replacement image and a Separation, derived once per thread and
shared; the extra residency is those symbols and their axioms. Runtime is
unchanged at 8.5 s against 8.8 s.

---

## 2026-07-31 — Dependent Π becomes a real dependent product

`⟦Π x:A. B⟧` is now `fs(⟦A⟧,⟦B⟧)` when the body ignores the binder and a genuine
`dprod` when it does; the opaque `syms.pi` survives only as an unreachable
fallback. `interp_pi` mirrors `interp_lambda` — opens the binder at a local,
reuses the skeleton machinery, keys a per-thread cache on the skeleton — and
non-dependence is now decided *exactly* (does the interpreted body mention the
binder's variable) rather than from a loose-bvar upper bound.

This required n-ary ports of the `derived::ext` dependent-product API inside
`tg.rs`, because the unary form cannot reach the checker: a Π body has free
variables besides the binder's. `derived/` was left untouched.

| | before | after |
| --- | ---: | ---: |
| `pi congruence: dependent and non-dependent Π interpret differently` | **1196** | **0** |
| `pi congruence: de Bruijn shift` | **748** | **0** |
| `init-prelude` total gaps | 16,009 | 15,954 |
| tutorial gaps / files at 0 | 538 / 64 | **535 / 65** |
| runtime / RSS | 8.75 s / 100 MB | 8.50 s / 127 MB |

**Two whole categories eliminated, and the net is −55.** They mostly became
*other* gaps rather than derivations, and the instrumented reason is the useful
part: of 621 bridge failures, **~500 have a body certificate that is reflexive
and mentions neither of the two bodies**.

That is the same defect I fixed for `pi_cong` and `lam_cong` earlier, in a rule
I did not then revisit: **`app_cong` is handed sub-certificates rather than
terms, so it cannot check what it proves.** A certificate arriving at a binder
need not be about that binder's bodies at all. `pi_cong` detects this and reports
a gap rather than bending it — correct behaviour, and it makes the real culprit
visible.

The principle was already recorded once: *every rule that concludes something
about two specific terms must be handed those terms.* It was applied to
`lam_cong`/`pi_cong` and not carried through to `app_cong`, `trans` or `symm`.
That is now the largest remaining lever after the typing bridge.

**Two changes worth flagging beyond the brief:**

* `def_eq_binder_aux` now instantiates **Π frames** as well as λ frames. It
  deliberately did not, *because* `⟦Π⟧` was built over the raw de Bruijn body —
  a reason that this change removes. Worth 143 prelude gaps on its own, and the
  bridge is unreachable below the outermost binder without it. Note this
  reverses an earlier measured decision, correctly: the measurement that
  justified *not* instantiating Π frames was taken when Π was opaque.
* The prelude built **two different ordered-pair symbols** — `Apply::new` and
  `funspace::Development::new` each construct their own `Sets`. Harmless until
  the bridge, which mentions both. The development is now assembled by hand over
  one `Sets`, and `domain_premise`'s `fs(a,a) ∈ U(a)` had to be re-derived over
  the new stack.
