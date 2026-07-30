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
