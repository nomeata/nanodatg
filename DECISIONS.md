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
