# Claude handoff

Snapshot: 2026-08-14 UTC. This is a delta/update for Claude's imported
conversation context, not a replacement for the design documents.

## Executive state

The main checkout is on `master` at `b654c98`, and local `origin/master` is at
the same commit. The worktree is clean except for the long-standing untracked
`scripts/__pycache__/`; preserve it. Bacon, the only active Codex subagent, was
explicitly stopped at the owner's request. Its worktree and branch are clean,
with no interrupted changes to recover.

The main thrust has made substantial progress and remains the priority. The
level-polymorphism tranche is complete on a separate branch but deliberately
not integrated. Modelgen is being turned into a standalone repository/product
elsewhere and is strictly out of scope here: do not modify it.

## Owner decisions and non-negotiable architecture

The two historical pipelines are not alternatives. They are one checker:

- one parse;
- one `Instantiations::compute`;
- one loop over declaration groups;
- one dispatch on declaration kind;
- inductive, mutual-inductive, and quotient construction is handled by the
  former Mini implementation;
- axioms, definitions, theorems, and opaque definitions are checked by nanoda
  and produce TG evidence in that same call;
- each declaration group is accepted/type-checked exactly once;
- no fallback to the other checker, no repair sweep, and no post-loop second
  validation pass;
- `--naive` selects the historical whole-file Mini checker and is the only way
  to run that policy;
- a nanoda-accepted ordinary declaration is mirrored *unchecked* into the
  former Mini syntactic environment so a later Mini-owned inductive can refer
  to it;
- TG gaps are certification debt: the normal CLI exits 4 while any remain;
  `--acceptance-only` intentionally ignores certification debt.

The top-level `mini` crate/directory is gone. Its surviving implementation is
inside the checker crate, principally under `checker/src/mini/`. Do not restore
a separate crate or binary. The production policy and loop are in
`checker/src/mini/route.rs`; the nanoda group adapter is in
`checker/src/routed.rs`; the CLI is `checker/src/bin/checker.rs`.

The semantic ownership rule is equally important: Mini-owned inductive
carriers, constructor graphs, recursors, projection packages, and certificates
are authoritative. TG must consume those exact objects/evidence. It must not
reconstruct a parallel carrier or recursor, rerun reduction, invoke the other
checker, or hide failure behind a fallback.

## Unified-checker work already landed

The integration sequence from the pre-merge baseline `a10bf90` is:

| Commit | Result |
| --- | --- |
| `44e2de4` | Records the unified-pipeline decision. |
| `4e86d46` | Removes the top-level Mini crate and moves it into `checker`. |
| `8815abb` | Implements one declaration loop and one dispatch; removes force-route modes, fallback checking, and the post-loop checker sweep. |
| `18212fc` | Makes Mini's `Nat` carrier/constructors/recursor and shared `NatClause` authoritative to TG. |
| `02ab90f` | Makes TG consume Mini's class-(T) projection package for direct redexes and projection congruence. |
| `a3911d6`, `0e42cf3` | Threads memoized projection-subject reduction evidence into `proj_red`, with a readiness gate. |
| `b4127ac` | Consumes Mini's dependent iota evidence for parameterless fieldless inductives such as `Two`. |
| `fb1692c` | Consumes carrier, recursor, constructor-spine, and iota evidence for unary plain-recursive constructors such as `N.s n`. |
| `9b691cb` | Retains an inner projection proof and composes it under an application suffix; eliminates the remaining `proj_reduce` origins. |
| `cc5dfd5`, `4a1f567` | Replays exact lazy-delta traces, but retains recipes only when replay is sound and useful. |
| `4fc2f25` | Replays certificate-free, endpoint-checked structural equality recipes; eliminates the final `eq_cache` origin. |
| `b654c98` | Refuses to park conditional reduct certificates in memo traces; removes eight false escape/copy artifacts. |

The relevant production and regression code is concentrated in:

- `checker/src/mini/route.rs`
- `checker/src/routed.rs`
- `checker/src/tc.rs`
- `checker/src/reduct.rs`
- `checker/src/tg.rs`
- `checker/src/mini/interp.rs`
- `checker/src/mini/proj_data.rs`
- `checker/src/mini/nat_clause.rs`
- `checker/tests/unified_cli.rs`

`ENV-UNIFY.md` sections B6-B8 explain the first Nat/projection handoffs. Later
commits and `checker/tests/unified_cli.rs` are the current source of truth for
the subsequent projection work. Some earlier Track-D prose in `ENV-UNIFY.md`
still describes superseded force modes/fallbacks while narrating history; do
not mistake that historical stage for the current architecture.

## Current measured certification frontier

At `b654c98`, `proj_reduced_carrier.ndjson --verbose` reports:

- `TOTAL gaps`: **16** (down from 139 before the recursive-constructor handoff);
- dependent iota computations: **22**;
- conditional derivations: **433 made, 0 copies, 417 consumed, 16 escaped**;
- no `eq_cache` gap;
- no iota-origin gap;
- no `proj_reduce` gap;
- no whnf-origin gap;
- derived theorems: **1158**.

Other exact ratchets at this point:

- `proj_reduced_subject`: **2** gaps;
- `proj_stuck_subject`: **6** gaps;
- `field_in_u0_by_carrier`: **0** gaps;
- `nat_char_equations`: **152** gaps (the last checkpoint removed 12 parked
  conditional copies but did not change the underlying proofs).

The last checkpoint's instruction impact versus `4fc2f25` was noise-scale:

- carrier fixture: **+0.00623%** `instructions:u`;
- zero-gap control: **+0.00317%**.

The most recent green validation was:

- `cargo test -p nanoda_lib --features tg --test unified_cli`: 5/5;
- `cargo test -p nanoda_lib --features tg --test mini_designed`: 32/32;
- `cargo check -p nanoda_lib --no-default-features --all-targets`: passed
  (existing warnings only).

A full no-default unit-test run is not a gate: it exposed four pre-existing
Mini-test failures and one unrelated test running longer than 60 seconds, so it
was stopped. The no-default all-target *check* above is the established gate.

## Exact remaining main blocker

All 16 remaining carrier-fixture gaps are honest conditional certificates that
reach a declaration boundary. Temporary classification instrumentation was
reverted; the branch is clean. Across the 16 certificates there are 135
antecedent atoms:

- **8** exact typings of context locals, `⟦w⟧ ∈ ⟦A⟧`;
- **50** guarded-family closures;
- **77** raw beta argument-typing obligations;
- **0** projection-field assumptions.

By declaration/certificate family:

```text
recAddNZ      raw 1
recAddNS      raw 1 + family 1
N.brecOn.go   four certificates: local 5 + raw 5 + family 1 total
addN          local 1 only
addNZ         raw 7 + family 6
addNS         raw 5 + family 11
dblN          local 1 only
dblNZ         raw 13
dblNS         raw 10 + family 6
leN           local 1 only
leNZ          raw 12 + family 3
leNSZ         raw 13 + family 9
leNSS         raw 10 + family 13
```

Exactly three escaping certificates (`addN`, `dblN`, `leN`) contain only an
ambient local's own typing. The other thirteen require real typing evidence
for raw beta obligations; the family wrappers largely carry the same debt.

### Why typed de Bruijn keys did not already solve this

The owner's intuition here is correct. TG's local identity is
`LocalKey::Level(level, interpreted_binder_type)`, so the term and its exact
typing premise remain available and same-level/different-type locals cannot
alias. The problem is not a lost context or a cache-key mismatch.

The missing information is *scope provenance*. TG can derive the real theorem

```text
⊢ ⟦w⟧ ∈ ⟦A⟧ → ⟦a⟧ = ⟦b⟧
```

but a bare equality cache/boundary asks for `⊢ ⟦a⟧ = ⟦b⟧`. A local may be:

1. ambient, already in the declaration context Γ, in which case its typing
   premise is part of the semantic interpretation of `Γ ⊢ a ≡ b` and should be
   abstracted at the judgement boundary; or
2. opened inside this definitional-equality query, in which case its premise
   must be discharged by the binder rule before the query returns.

The `(level, type)` key proves identity but not which operation owns the
binder. Production currently has no equality-query baseline/open-close marker
that distinguishes these cases. The escape ledger therefore conservatively
charges every conditional answer reaching the boundary. The explanatory
comments near "What the escapes actually are" and the escape ledger in
`checker/src/tg.rs` are accurate and should be read before changing this.

### Recommended next tranche

1. Add explicit equality-query scope provenance: capture a baseline at the
   outer `def_eq` entry and track locals opened beneath it.
2. At the judgement boundary, abstract only exact local-own-typing antecedents
   proven ambient relative to that baseline.
3. Query-opened locals must still be consumed/discharged or reported as
   escapes. Add an adversarial regression that would fail if a query local were
   misclassified as ambient.
4. First target only `addN`, `dblN`, and `leN`. A clean result should remove
   three escapes; do not broaden the rule merely because the key contains a
   local.
5. Reclassify the mixed `N.brecOn.go` certificates afterward. Ambient
   abstraction may remove some antecedent atoms there, but will not close a
   certificate that still carries raw/family debt.
6. Independently, derive actual typing evidence for the 77 raw beta premises.
   Do not relabel them as ambient and do not globally retain conditional
   certificates. The guarded-family atoms should be peeled only when the
   underlying typing obligation is genuinely discharged.

No implementation of scope provenance was in progress when Bacon was stopped.
The clean branch `joachim/equality-scope-provenance` points at `b654c98`, as
does its durable worktree
`/home/joachim/nanodatg/.claude/worktrees/equality-scope-provenance`.

## Main thrust after the boundary work

Re-measure `nat_char_equations` after the scope/raw-beta tranches. The larger
goal remains certification of the characteristic Nat equations, not merely a
zero projection-origin row. The earlier measured plan was:

1. get the exact Eq-refl theorem declarations in the fixture certified by the
   nanoda/TG path;
2. factor/consume the relevant equality cash/generalisation evidence from
   `checker/src/mini/eq_cash.rs` and `checker/src/mini/quot_classes.rs` without
   running the Mini checker again;
3. build the neutral `derived::nat::BleClauses` / `ble_transfer` path around
   `derived/src/nat/ble_unique.rs`;
4. ratchet the exact source clauses in
   `checker/tests/fixtures/nat_char_equations.lean`.

Do not synthesize new clauses merely to make them checker-routed failures, and
do not fall back to Mini for their checking. The projection and boundary work
has changed the gap census substantially, so inspect current provenance before
assuming the old ordering is still exact.

## Queued second thrust: level polymorphism

Main has priority. The level-poly work is complete but isolated on
`explore/level-poly-target` at `6fa6b19` (`mini: Eq.rec at two symbolic levels,
28 constants and two exits`) and was pushed to `origin/explore/level-poly-target`.
Its recorded result is:

- Gate A byte-identical;
- Gate B exits `32/57/2 → 34/55/2`;
- zone-B successes `208 → 236 / 362`;
- values OK `117 → 118 / 146`;
- value evidence `71 → 72`;
- stored `116 → 118`;
- ground instructions `+0.0033%`;
- `--poly` instructions `+8.21%`, because 28 Eq.rec nests now complete;
- its full test suite was green, including mutation regressions.

The branch predates the crate move and its worktree is
`/home/joachim/nanodatg/.claude/worktrees/lp2`. Do not blindly cherry-pick it
onto current master: port/rebase its former `mini/` paths into
`checker/src/mini/`, resolve against the unified environment deliberately, and
rerun both its gates and the unified CLI ratchets. Do this only after the main
thrust or explicit reprioritisation by the owner.

## Commands and operating constraints

Useful focused commands:

```bash
cargo test -p nanoda_lib --features tg --test unified_cli
cargo test -p nanoda_lib --features tg --test mini_designed
cargo check -p nanoda_lib --no-default-features --all-targets
cargo run -p nanoda_lib --features tg --bin checker -- \
  --no-modelgen --verbose checker/tests/fixtures/proj_reduced_carrier.ndjson
```

For commands that may use substantial memory, apply an explicit limit. Prior
work used 8 GiB per process, for example:

```bash
(ulimit -v 8388608; cargo test -p nanoda_lib --features tg --test unified_cli)
```

Keep aggregate resident memory below 50 GB and monitor it with:

```bash
systemd-cgtop -m user.slice/user-1001.slice
```

This is a shared machine. Use `perf stat -e instructions:u` rather than wall
time for performance comparisons. Put large temporary artifacts under the
project-local `_tmp/`, not `/tmp` or another tmpfs. Commit and push coherent
green checkpoints early. Keep the main checkout on `master`, fast-forward or
cherry-pick reviewed agent commits onto it, and push `master` as commits land.

Do not delete or modify unrelated Claude worktrees/branches. In particular,
modelgen-related worktrees belong to the separate product effort.

Two Codex-created worktrees were initially outside the repository's durable
area. They have been recreated, clean and branch-identical, at:

- `/home/joachim/nanodatg/.claude/worktrees/inductive-tg`
  (`joachim/inductive-tg`, `18212fc`); and
- `/home/joachim/nanodatg/.claude/worktrees/equality-scope-provenance`
  (`joachim/equality-scope-provenance`, `b654c98`).

There is no longer any project worktree at `/home/joachim/nanodatg-*`.
