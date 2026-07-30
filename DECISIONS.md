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
