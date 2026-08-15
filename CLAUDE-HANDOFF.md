# Claude handoff

Originally written 2026-08-14; **substantially rewritten 2026-08-15** after 94
commits. This is a delta/update for Claude's imported conversation context, not
a replacement for the design documents. Sections below marked as history are
kept because the reasoning is still useful; the *current* numbers are all in
"Current measured certification frontier" and the gate list.

**The four documents that now carry the live scoping**, in the order a new
reader should take them: `ORIGIN-RANKING.md` (every gap origin ranked by
bitmask and deletion over both populations), `SEAM-DESIGN.md` (where the
TG/mini seam belongs, plus §9's inventory of what crosses it and §10's
`fire_dep` findings), `TEST-INVENTORY.md` (every suite's true status, the
per-leg floors, and §4.5/§6 on structurally-untestable assertions), and
`MEASUREMENTS.md` (append-only; the 2026-08-14/15 sections are this arc).

## Executive state

Snapshot updated **2026-08-15**, 94 commits after the original handoff. The main
checkout is on `master` at `d73c94f`. The worktree is clean except for the
long-standing untracked `scripts/__pycache__/`; preserve it. **`git push` does
not work in this environment** — `origin` is GitHub with no credentials, so every
commit below is local. All seat branches are merged into `master`;
`explore/level-poly-target` is deliberately separate.

**`init-prelude` now ACCEPTS.** It reached declaration 1 and declined this
morning; it now reports `accept  1822 declarations`, certified prefix 152, pairs
32, in ~39 s. What stops it is no longer acceptance but *interpretation debt* —
see "The init-prelude frontier" below.

**Modelgen is out of scope: do not modify it.** It is being turned into a
standalone product elsewhere.

The level-polymorphism branch is paused cleanly with its restart head, pick-up
list and a *what-not-to-redo* list in `LEVELPOLY.md` §5.3.0.

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

Measured on `master` `d73c94f`, verified independently rather than inherited.

### The three populations

| fixtures (14 of them carry gaps, **215** total) | | Lean's 91 exports (**16** carry gaps, **168** total) |
| --- | --- | --- |
| `nat_char_equations` 61 · `mutual_aux_encoding` 49 · `ctor_abbrev_major` 23 · `proj_reduced_carrier` 13 · `quot_lift_reduction` 12 · `delta_inside_a_proof` 11 · `nested_roundtrip` 11 · `transport_through_eq_rec` 11 · `proj_stuck_subject` 6 · `whnf_of_a_proof` 6 · `ground_unit_subsingleton` 4 · `mono_prefix` 4 · `proj_reduced_subject` 2 · `reducible_ctor_binders` 2 | | `076_listRecReduction` 45 · `077_RBTree.id_spec` 28 · **74 exports fully certified** |

`budget_decline` is excluded deliberately: it is 2100 nested `succ`s built to
exhaust a budget, a pathology fixture rather than a certification target.

**And the third population is the one that matters: `init-prelude`, at 10 262
gaps, which nobody ranked until 2026-08-15.** It is **not** a scaled-up version
of the other two — its rank 1 is worth more than the entire small-population
frontier. See `ORIGIN-RANKING.md`.

**The exports and `init-prelude` are the completeness claim; the fixtures are
the development signal.** Completeness is measured against Lean, never against
fixtures we wrote. Where they disagree, believe the larger population:
`proj_reduce` was worth −74 on a fixture and **zero** on the exports, while the
`Nat` bridge was worth −11 on a fixture and **−3 780** on `init-prelude` — where
the second half carries its own lesson, because that −3 780 was then measured to
be **unreachable** (see the frontier, item 0). A large number on the right
population is a reason to *look*, not a reason to build.

Movement over the arc: exports **217 → 168**, `nat_char_equations` 152 → 61,
`mutual_aux_encoding` 96 → 49, `ctor_abbrev_major` 46 → 23,
`proj_reduced_carrier` 16 → 13.

### The init-prelude frontier

`checker --verbose --mutual --nested vendor/arena-tests/good/init-prelude.ndjson`
— **all three flags are needed**; under `--no-modelgen` it declines at
declaration 1 on `Lean.Syntax`, and with modelgen but no gates it declines on the
*mutual* inductive the nested splice emits.

    accept  1822 declarations
    untranslated: 91 declarations, 10 eliminators
    uncertified:  32 const typings, 29 type typings
    tg gaps: 11909      prefix declarations=152 pairs=32      exit 4

Of the 11 909 gaps, **6 683 are `trans over an admitted premise`** — relays, not
origins. Exit 4 is correct: it is certification debt, not rejection.

What stops it now is **interpretation debt**, in two named families:

* **`type former spine`** — the heterogeneous-operator classes (`HAdd`, `HSub`,
  `HMul`, `HPow`, `HAnd`, `HOr`, `HXor`, `HShiftLeft/Right`, `HAppend`,
  `HAndThen`, `HOrElse`, `HDiv`, `HMod`, `HSMul`), the `Monad*` classes,
  `Membership`, `EStateM.Backtrackable` — 2 each, `Trans` 4.
* **`field type uninterpretable`** — the machine words `UInt8/16/32/64`,
  `USize`, plus `Char`, `String`, `Fin`, `BitVec`, `ByteArray`, `Substring.Raw`,
  `Hashable`, and the `Lean.*` syntax types.

Plus recursor declines: `False` and `PEmpty` (class (S) eliminator, no
constructors) and `HEq` (a result index is not a bare field).

### Performance, for calibration

`init-prelude` went **28.211 T → 0.507 T `instructions:u`** and **2126.7 s →
38.7 s** across four changes, each with a byte-identical verdict and every
`gap: <reason>` row unchanged across all fixtures and all 91 exports: a
closed-pair `def_eq` decision cache, a persistent `infer_type` gap memo, a
`whnf` reduction memo, and a five-line syntactic-equality shortcut. Separately,
mimalloc was linked into the production `checker` binary (it had only ever been
on `nanoda_bin`) for **−41 to −44 % task-clock**.

**Two measurement rules follow from that work.** `instructions:u` *understates*
allocation- or cache-shaped changes by 9–17 points — quote `task-clock`
alongside it for those. And **report rows, not totals**: two ratchets drifted for
134 commits because only a TOTAL was guarded.

## The gate list

**Corrected 2026-08-15, for the second time in a day, against a run of *every*
target on master `50605c4` with the arena corpus linked. The correction is not
another entry on the list — it is that the list stops naming targets at all.**

The rule from the previous correction survives and is the right one:

> **A suite is either a gate or it has a written reason, with a measurement,
> for not being one.** "Not a gate" must never be readable as "unimportant" or
> as "expected to be red".

### Why an enumerated list was the defect

Three suites outside the gate list have been found red in one week —
`mini_designed` at 32/34 in the configuration the gate never ran, the two
crossing suites, and now `mini_tutorial`. Each time the remedy applied was *add
the missing suite to the list*, and each time it failed again within days,
because the failure is structural rather than a lapse of care:

**An enumerated gate list is a hand-maintained copy of the target list, and a
copy drifts.** The evidence that this is not about diligence is `d263be2`'s own
commit message, which reports *"Gates 6/6, 34/34, 35/35, 251/251, boundary
OK"*. The author ran the gate list. The list was wrong — `mini_tutorial` was
not on it — and the suite it omitted went red in that very commit and stayed
red for 286 commits.

So the gate no longer names targets. **`cargo test -p nanoda_lib`, with no
`--test` narrowing and no `--features`, runs the lib's unit tests and all 14
integration targets.** A suite written tomorrow is inside the gate on the day
it is written and there is no list to forget.

Two facts make that possible, and neither held when the previous list was set:

* **There is one build configuration.** `tg` selected `certify::Backend`
  between `NullCertifier` and the real backend; retiring the `Certifier` trait
  left one backend and the feature was deleted at `d746251`. The old list's two
  `--lib` lines were one configuration each; they are now the same command
  twice.
* **The whole package fits in under three minutes.** That was not believed to
  be true and the reason is the next section.

### Measured, master `50605c4`, corpus linked

| target | tests | time |
| --- | ---: | ---: |
| `src/lib.rs` (unit) | 299 | 8.7 s |
| `tests/corpus.rs` | 6 | **40.3 s** |
| `tests/tg_tutorial.rs` | 36 | **31.7 s** |
| `tests/mini_mutual.rs` | 12 | 28.2 s |
| `tests/mini_nested.rs` | 20, 2 ignored | **17.2 s** |
| `tests/mini_tutorial.rs` | 16 | 16.4 s |
| `tests/mini_dump.rs` | 12 | 16.3 s |
| `tests/unified_cli.rs` | 6 | 5.4 s |
| `tests/mini_nat_equations.rs` | 2 | 4.2 s |
| `tests/mini_designed.rs` | 34 | 2.2 s |
| `tests/mini_envshare_cross.rs` | 14, 1 ignored | 0.3 s |
| `tests/mini_budget.rs` | 1 | 0.3 s |
| `tests/mini_envshare.rs` | 6 | 0.3 s |
| `tests/mini_route.rs` | 10, 2 ignored | 0.2 s |
| `tests/mini_infinitary.rs` | 1 | 0.2 s |
| doc-tests | 0, 8 ignored | 0.0 s |
| **total** | **476 passing** | **171.8 s** |

`kernel` + `derived` are **1049 across 109 targets** and run in seconds.

### The 175-second suite that is 17 seconds

This is the measurement that decides the shape above, and it refutes a number
this document, `TEST-INVENTORY.md` §1.1 and every recent handoff have repeated.

`mini_nested` was recorded at **175–177 s**, "of which two tests are
individually over 60 s", and that number was the sole stated reason for keeping
the full run off the per-commit gate. **It is 17.2 s** — measured twice, 17.17 s
inside a full package run and 17.26 s standing alone, with the same two tests
`#[ignore]`d as when the 175 s was taken. It is not the slowest suite in the
tree; it is the fifth, and `corpus.rs` at 40.3 s is more than twice it.

Nobody re-measured it because nobody needed to: it was quoted as the reason for
a decision, and a reason that is never re-checked outlives the fact it rests
on. The most likely cause is `d263be2`'s syntactic-equality shortcut — the same
commit that moved `mini_tutorial`'s conversion census, and whose whole subject
is not reducing a term to discover it equals itself, which is what a nested
interpretation does constantly. That attribution is **not measured** and is
offered as a hypothesis; the 17.2 s is measured.

**So there is no suite too slow to gate, and the merge-gate carve-out this
section used to make for `mini_nested` is withdrawn.**

### Gates — all of these must be green before a commit

```bash
ci/corpus-dir.sh --link          # in a worktree, FIRST — vendor/ is gitignored
cargo test -p nanoda_lib         # 299 unit + all 14 suites = 476, ~172 s
cargo test -p kernel -p derived  # 1049 across 109 targets, seconds
ci/check-boundary.sh             # OK
ci/test-boundary.sh              # OK
```

Five commands, and the second cannot omit a suite by construction. Without the
`ci/corpus-dir.sh --link` a worktree reports `ok … 0.00s` having checked
nothing, which is the input-dimension form of the same disease.

`kernel` and `derived` stay on the list for the reason they were added: `kernel`
is the entire trusted computing base, the only component that must be correct
for soundness, and it was on no list at all. `ci/test-boundary.sh` stays because
it was red on master when the inventory was taken and it is the file that proves
the boundary check can fail.

### What came off the list, and why

* `cargo test -p nanoda_lib --features tg --lib` — **the feature does not
  exist** (`d746251`). Passing it now is an error, not a stricter run.
* `cargo test -p nanoda_lib --no-default-features --lib` — `nanoda_lib` declares
  no default features, so this was always the same build as a plain one.
* `cargo check -p nanoda_lib --no-default-features --all-targets` — subsumed:
  `cargo test -p nanoda_lib` compiles every target it would have checked.
* The two "ratchet" lines, `--test unified_cli` and `--test mini_designed`.
  They were never a separate obligation — they are two of the fourteen, and
  naming a subset is the habit this correction is about. They are 6/6 and 34/34,
  inside the package run, in 7.6 s of its 172.

### Nothing is red

All 14 suites and the lib are green on master `50605c4` with the two
re-baselines on this branch. **The "Currently red, with the reason" block that
stood here is deleted rather than updated**, because a sentence in a handoff
telling the next reader that a red number is expected is how a real defect stays
hidden — this document already says so about its own previous wording, and then
carried such a block for four more days. The four reds it named are attributed
and re-based: `mini_tutorial`'s three pins at `d263be2`, and the three crossing
pins in `mini_envshare_cross` and `mini_route` at `18212fc`, each with the trade
written at the assertion.

If a suite goes red, it is red. There is no list of expected reds.

### The five ignored tests, and the eight ignored doctests

A `#[ignore]`d test is **absent**, not skipped, so each one is named here rather
than left to be discovered:

| test | file | stated reason |
| --- | --- | --- |
| `the_iota_dispatch_arm_fires_the_rules_its_model_proved`* | `mini_nested.rs` | `#[ignore = "33m20 and OOM at 12 GB on the filtered export"]` |
| `the_nested_declarations_interpretation_is_its_models`* | `mini_nested.rs` | `#[ignore = "51.8 M conversions, 26 minutes and over 7.5 GB"]` |
| `cross_sweep_tutorial` | `mini_envshare_cross.rs` | in the doc: the B4 measurement run, minutes over 91 exports, with the command to reproduce it |
| `skeleton_key_divergence_sweep` | `mini_route.rs` | in the doc: "a measurement run, minutes over the corpus" |
| `paired_subterm_lam_divergence` | `mini_route.rs` | **none — a bare `#[ignore]` with no reason anywhere in its 60-line header** |

*(\* the two `mini_nested` names are the two the 175 s figure was attributed to;
they are `#[ignore]`d for cost, and the suite is 17.2 s without them.)*

Four of the five are measurement sweeps that cost minutes to tens of minutes and
are right to be ignored — but only the two in `mini_nested` put the cost in the
`#[ignore]` attribute, where it is visible from a test listing. The fifth,
`paired_subterm_lam_divergence`, states **no** reason at all, and an ignored
test with no reason is indistinguishable from an abandoned one. **That is the
same rule as this section's, one level down: a test is either run or it has a
written reason, with a measurement, for not being.** None of the five has been
run recently; whether they still pass is unknown, and that is the honest status.

The 8 ignored doc-tests are prose examples in `inductive.rs` (5),
`pretty_printer.rs` (2) and `lib.rs` (1) — illustrative pseudo-code inherited
from nanoda, not assertions.

### Everything else in `ci/`

`ci/check.sh` is the merge gate and now has **26 steps**, not 29; it asserts its
own count, and the count matches. The three that went with the feature were
`feature-inert guard`, `tests (tg backend)` and `tests (cross-engine core)`.

**It needed no widening, and that was checked rather than assumed.** Its steps
24 and 26 are `cargo test -p nanoda_lib` and `cargo test -p nanoda_lib
--features stepcount`, both **bare** — no step in the file uses `--test` any
more — so all 14 integration targets run twice per invocation, and step 25
(`cargo test --workspace --exclude nanoda_lib`) is exactly `kernel` + `derived`.
Zero of the 14 are un-run. The one thing genuinely lost is
`ci/check-feature-inert.sh`, a *runtime* falsifier for the premise that let the
feature steps be `-p nanoda_lib`; with one backend that premise is gone, and
leg B of `ci/check-test-inputs.sh` covers what remains statically.

One item is left open by the feature's removal: **leg C of
`ci/check-test-inputs.sh` is now vacuous.** It refuses a `#![cfg(feature = "X")]`
suite in a package no `--features X` step selects, and its scan now matches
**zero** files, so it iterates zero times. Its self-test still proves it can
fire, so it is prospective rather than broken — but it is a leg with no subject,
which is item 5 of `TEST-INVENTORY.md` §2.1 arriving from the other direction.

So:

* **before a commit** — the gate block above, ~3 minutes;
* **before a merge to `master`** — `ci/check.sh`, in full.

A suite that is correct and unrun is indistinguishable from one that is absent.
The measurements behind that sentence are now three: 134 commits with two
ratchets unobserved, 286 commits with `mini_tutorial` red, and 67 commits with
the crossing pins stale — and 13 of the commits in the first range have empty
message bodies, so `git log` would not have recovered the attribution either.

## What is actually left, 2026-08-15

The section below this one is **history** — it described the carrier fixture at
16 gaps and the tranche that took it to 13. Read it for the reasoning, not the
numbers. What remains now, in the order the measurements put it:

0. **DO NOT BUILD the `Nat` bridge — measured and declined, 2026-08-15.** This
   item said "BUILD THIS NEXT" on −3 780 and named the two checks that had to
   refute it first. Both were taken and both fail
   (`MEASUREMENTS.md`, *"The `Nat.ble` tranche, refuted at its own gate"*).
   The census is right — `iota: the major premise is not a constructor` is 37 %
   of `init-prelude` from one origin, and **466 of 563 firings are
   `Bool.rec @ (Nat.ble <lit> <lit>)`, 51 distinct pairs, operands 0–12**
   (re-derived, not inherited). What is wrong is that anything reaches it:

   * **It is not a gate.** The numeral step is `Rule::Admitted(Admit::NatRed)`,
     and `Rule::Admitted` *is* "the backend has no rule for this"; the
     `Certifier` trait has no numeral method, so there is no disjunct to add.
     The tree's own `NANODA_NAT_RULED` simulation moves the origin 577 → 106
     straight onto `nat_reduce` 32 → 503 for **+942 gaps**.
   * **The headline is 30 % high.** −3 780 assumes the *ι* equation; a numeral
     construction can only assume the *numeral* equation. Measured ceiling
     **−2 630**, with escapes 1 074 → 1 777.
   * **The clauses cannot be had unconditionally.** `ble_transfer` `mp`s its
     three premises, and on the one input that contains them
     `checker` certifies `natBleZ`/`natBleSZ`/`natBleSS` only
     conditionally — **16 / 23 / 24 raw-beta atoms** from `Nat.ble`'s `brecOn`
     nest. `mini` certifies them unconditionally; `mini` does not own the ledger.

   **Reachable prize 0.** The standing "do not build the `Nat` bridge" decision
   was right all along, and now for a measured reason rather than a fixture's.
   Build item 6 instead.

1. **The escape population is the terminal wall, and it does not decompose.**
   Floor: 10 645 → 2 270 (79 %), of which **2 061 (91 %) are escapes** — up from
   89 % on a tree 18× smaller. The largest shape-group carries **3 182 atoms
   across 245 certificates and closes 6**, because a certificate closes only
   when *every* atom goes; single-shape constructions reach 309 of 1 074 (29 %),
   and the "thread it, don't derive it" prize is **1 gap**. Two earlier figures
   circulated in conversation — "ten shape-groups" and "raw-beta priced at 44
   tree-wide" — **were never written into the repo and do not reproduce**; the
   measured counts are 23/48 groups and 61 (small) / 625 (`init-prelude`).
   Likewise "scope provenance exhausted the ambient-local category" is not in
   the tree: *a context local's own typing* is still the largest or
   second-largest escape group.
2. **`076_listRecReduction`'s −35 is behind a *layer* of twelve walls, and
   should not be started.** `fire_dep`'s parameterised path is a run of
   constructions each written for `np == 0` — twelve of them, ten hard and two
   latent, **seven previously unknown** — and the 37-gap sub-tree **migrates
   intact** across each rather than shrinking, so there is **no partial credit**:
   0 until all ten land, then −35 on one file. The `np > 0` type-former adoption
   was built, confirmed working end to end on `Prod` and `List`, measured at
   **0**, and reverted.
3. **`077_RBTree.id_spec`'s −19 is blocked on task #38** and is *not* a
   consumption: `IndexedCtor::mem_lean`'s witness protocol demands closed,
   prenex witnesses at `derived`'s own working variables, while every consumer
   holds open-scope already-instantiated theorems whose scope assumptions are
   live hypotheses and therefore cannot be generalised back.
4. **The `Nat` bridge's fixture price, for the record.** −18 of 61 on
   `nat_char_equations`, zero additional certified theorems, 16 of 17 theorems
   carrying escapes under `*` identically to baseline. The fixture was right
   about the corpus for a reason it could not see: the −3 780 on `init-prelude`
   is real and **unreachable** (item 0).
6. **BUILD THIS NEXT: `iota: the major premise's domain is not this inductive`,
   −1 609 on `init-prelude`** — rank 2, terminal, 8 % ceiling overshoot, full
   acquisition, and it has a 10-gap development fixture (`074_prodRecEqns`)
   carrying the same cause. That is the best fixture-to-goal leverage in the
   tree. Then `proj_reduce` at −890, an extension of a construction that already
   landed once (`3eab691`) and beat its own price.
5. **`init-prelude`'s interpretation debt** — the `type former spine` and
   `field type uninterpretable` families listed above. This is a different kind
   of work from everything in this arc: *"what interprets a machine word and a
   type-former spine"*, not *"why does it stop"*.

**The pattern worth carrying forward**, found five times: *mini publishes the
fact and TG declines for want of a rule it could have stood on.* Variants seen —
published-and-unconsumed; published behind a guard whose own header says it is
about cost; **three independent mints of one carrier in a single binary**; and
published correctly but **consumed at the wrong arity**. `SEAM-DESIGN.md` §9 is
the inventory, and its **meetability column** is the point: a zero-consumer row
is a *question*, not a finding — one of the three that motivated it turned out
not to be an opportunity at all.

## History: the boundary blocker, as it stood at `b654c98`

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

## History: the Nat-equation plan, and why it was not taken

**Superseded — do not execute this.** The four-step plan below was written
before the census. Measured, the `Nat` bridge is worth **−11 gaps and zero
additional certified theorems**, and `nat_char_equations`' real wall was
`PProd` projection inside `brecOn` (closed, 152 → 65) and is now the escape
population (61, of which 22 escapes and 32 relays). Steps 1–2 were also
partly refuted on their own terms: `eq_cash`'s `cash`/`cash_stmt` do check
rather than assume, but they use `Direct::eq_ax` and **not** `Props::eq_sound`
as step 2 says; and a call from TG would not compile, because `TgBackend`
holds no `mini::Environment` — the seam question that `SEAM-DESIGN.md` was
written to settle. Kept because the reasoning about what the equations need is
still sound.

The earlier measured plan was:

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

**`--features tg` is gone** (`d746251`) — passing it is now an error, not a
stricter run. There is one build configuration, so every command below is a
plain one. `--no-default-features` is likewise a no-op: `nanoda_lib` declares
no default features.

```bash
cargo test -p nanoda_lib --test unified_cli
cargo test -p nanoda_lib --test mini_designed
cargo run -p nanoda_lib --bin checker -- \
  --no-modelgen --verbose checker/tests/fixtures/proj_reduced_carrier.ndjson
```

Narrowing with `--test` is for *iterating*, never for gating — see the gate
list above for why an enumerated target list is the defect it looks like a
convenience for.

For commands that may use substantial memory, apply an explicit limit. Prior
work used 8 GiB per process, for example:

```bash
(ulimit -v 8388608; cargo test -p nanoda_lib --test unified_cli)
```

Keep aggregate resident memory below 50 GB and monitor it with:

```bash
systemd-cgtop -m user.slice/user-1001.slice
```

**A measurement hazard that has bitten a seat:** running the verification
gates rebuilds `target/debug/checker` **without** `stepcount` and overwrites the
census binary, so a sweep run afterwards silently reports baselines. Build the
instrumented binary to a distinct path, or re-build with the feature before
every sweep. Release and debug were cross-checked and agree to the digit, so
either profile is fine as long as the feature is actually on.

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
