# The test and CI inventory

Every test target and every `ci/` step in this tree: what it covers, whether it
passes, and whether anything actually runs it.

**Measured on `joachim/ci-floors`, branched from master `36106d2`, 2026-08-15.**
Every status below was produced by running the thing, on this tree, with the
arena corpus linked (`ci/corpus-dir.sh --link`) and `NANODATG_REQUIRE_CORPUS=1`
set so that a skip is a failure. Nothing here is inferred from a name, a comment
or a handoff — three of the reds recorded below had been carried in handoffs as
something other than what they are.

## Why this document exists

Two suites turned out to have been silently red for an unknown length of time,
and both were found by accident. The reason is structural and is not a matter of
anyone's diligence: **the gate list named three `cargo test` invocations and one
`cargo check`, and everything else in the tree was outside it.** A suite outside
the gate is not "lower priority"; it is unobserved, and an unobserved suite
drifts red and stays there.

Running the inventory found **four** red suites, not two. Two of the four are
invisible to any gate anyone runs, and one of those two is red *only* in the
build configuration the gate never uses.

This is the same disease as `DECISIONS.md`'s "SKIP is not PASS" (sixteen-plus
recorded instances of a check reporting success having done nothing), in the
*suite* dimension rather than the *input* dimension. A suite nobody runs and a
check that examined nothing are the same fact about the same tree.

---

## 1. Rust test targets

`nanoda_lib` declares no default features, so `--no-default-features` and a
plain build are the same configuration; the two that differ are **plain**
(`NullCertifier`) and **`--features tg`** (the real Tarski–Grothendieck
backend). Both are measured, because they are not the same suite: four targets
compile to nothing without `tg`, and one target is red in the plain build only.

| target | covers | plain | `--features tg` | gated? |
| --- | --- | --- | --- | --- |
| `src/lib.rs` (unit) | the checker's own modules, `mini::*` | **244/244** (86.0 s) | **292/292** (86.1 s) | plain: yes. `tg`: only via `ci/check.sh` |
| `tests/corpus.rs` | good/bad export acceptance, arena corpus | **6/6** (0.3 s) | **6/6** (40.9 s) | only via `ci/check.sh` |
| `tests/mini_budget.rs` | declared budget declines | 1/1 | 1/1 | only via `ci/check.sh` |
| `tests/mini_designed.rs` | designed-fixture behaviour, indexed seam | **32/32** (was 32/34 — see §3.4) | **34/34** | **yes** (`tg` form only) |
| `tests/mini_dump.rs` | model dump shapes | 12/12 (18.9 s) | 12/12 (18.7 s) | only via `ci/check.sh` |
| `tests/mini_envshare.rs` | the ungated half of the `EnvCore` seam | 6/6 | 6/6 | only via `ci/check.sh` |
| `tests/mini_envshare_tg.rs` | crossing ledger, statement guards | *absent* (0 tests) | **12/15, 2 FAILED** | only via `ci/check.sh` |
| `tests/mini_infinitary.rs` | infinitary constructors | 1/1 | 1/1 | only via `ci/check.sh` |
| `tests/mini_mutual.rs` | mutual/nested encodings | 12/12 (71.8 s) | 12/12 (70.7 s) | only via `ci/check.sh` |
| `tests/mini_nat_equations.rs` | the characteristic Nat equations | 2/2 (14.3 s) | 2/2 (14.0 s) | only via `ci/check.sh` |
| `tests/mini_nested.rs` | nested declaration interpretation | 20/20, 2 ignored (**177.2 s**) | 20/20, 2 ignored (**175.2 s**) | only via `ci/check.sh` |
| `tests/mini_route_tg.rs` | the routed driver over one core | *absent* (0 tests) | **9/10, 1 FAILED**, 2 ignored | only via `ci/check.sh` |
| `tests/mini_tutorial.rs` | tutorial corpus under mini | 16/16 (18.9 s) | 16/16 (18.8 s) | only via `ci/check.sh` |
| `tests/tg_tutorial.rs` | **every defeq step discharged, no gaps** | *absent* (0 tests) | **31/34, 3 FAILED** | only via `ci/check.sh` |
| `tests/unified_cli.rs` | the unified CLI's ratchets | *absent* (0 tests) | **6/6** (15.2 s) | **yes** |
| `src/bin/*.rs` (unit) | — | 0 tests | 0 tests | — |
| `kernel/tests/*` (8 files) | the trusted base: rules, Tarski, Henkin, choice | **all green** | n/a | **no** |
| `derived/tests/*` (95 files) | derived rules and constructions | **all green** | n/a | **no** |

`kernel` and `derived` together are **1047 tests across 109 targets, 0 failed**
(`cargo test -p kernel -p derived`). They declare no features, so they have one
configuration. **Nothing in the established gate list runs either of them** —
including the eight test files covering the trusted computing base, which is the
only component that must be correct for soundness.

### 1.1 The suite that runs longer than 60 seconds

Named, so that it stops being a reason to abandon a run: **`tests/mini_nested.rs`,
175–177 s**, of which two tests account for nearly all of it —
`the_iota_dispatch_arm_fires_the_rules_its_model_proved` and
`the_nested_declarations_interpretation_is_its_models`, each individually over
60 s (cargo prints the warning). `src/lib.rs` at 86 s and `mini_mutual.rs` at
71 s are also over the minute.

A full `--features tg` run of every target is about **8 minutes** of test
execution. That is the real number behind "one unrelated test running longer
than 60 seconds, so it was stopped".

### 1.2 Four targets are *absent*, not skipped, in the plain build

`mini_envshare_tg.rs`, `mini_route_tg.rs`, `tg_tutorial.rs` and `unified_cli.rs`
open with `#![cfg(feature = "tg")]`. Without the feature they compile to nothing
and cargo prints `running 0 tests … test result: ok`. This is a *third* shape of
"skip is not pass", distinct from both the shell `exit 77` and
`ci/skip-guard.rs`: there is no skip to guard, because there is no test. What
holds it today is `ci/check-test-inputs.sh`, which refuses a `cfg(feature)`
suite in a package no `--features` step selects. That guard is only as good as
`ci/check.sh` being run.

---

## 2. `ci/` steps

Status is from running each script on this tree. "Gated" means: reachable from
`ci/check.sh`, which is the only aggregator — and which, before this branch, had
no floor on its own step list.

| script | checks | status | in `ci/check.sh`? |
| --- | --- | --- | --- |
| `check.sh` | the aggregator: 29 steps | driver | — |
| `check-boundary.sh` | kernel trusted-boundary rules 0–7, R6′, member coverage | **OK** | yes |
| `test-boundary.sh` | that `check-boundary.sh` can fail (~50 cells) | **was RED (2)** → OK, §3.3 | yes |
| `check-mini-scope.sh` | R6′ for `checker/src/mini` (60 files scanned) | **OK** | yes (+ self-test) |
| `check-mutual-blackbox.sh` | the two encoders name nothing on the evidence side | **OK** | yes |
| `check-test-guards.sh` | no test hand-rolls a silent skip (58 call sites) | **OK** | yes (+ self-test) |
| `check-test-inputs.sh` | the feature matrix covers every declared feature | **OK** | yes (+ self-test) |
| `check-uplift.sh` | `[profile.dev]` and `[profile.test]` uplift one inode | not run here (cargo) | yes (+ self-test) |
| `check-feature-inert.sh` | `NANODATG_ASSERT_FEATURE_INERT` really aborts | needs a built bin | yes |
| `check-arena.sh` | the arena corpus ratchet | needs the release build | yes (+ self-test) |
| `check-mini-vs-nanoda.sh` | mini vs nanoda, two tolerated divergence classes | needs the release build | yes (+ self-test) |
| `check-modelgen.sh` | `lake exe test` / `monotest`, both legs floored | SKIPs without Lean | yes (+ self-test) |
| `corpus-dir.sh` | corpus discovery from a worktree | **OK** (self-test) | yes (self-test) |
| `skip-guard.rs` | the one place a suite may decide "I cannot run" | **OK**, self-tests in 8 suites | via every suite |

### 2.1 Which legs had a floor, and which did not

`ci/skip-guard.rs` already exists, already self-tests its own panic path in
every suite that includes it, and is already enforced by
`ci/check-test-guards.sh`. It did not need replacing. What was missing was
**per-leg** application of it.

Floors that were already right, and are the model for the rest:
`check-mini-vs-nanoda.sh` (`REQUIRE_LEGS`, each leg parsed and floored
separately, with the argument written out: "a floor on the sum is satisfied by
either leg alone"); `check-modelgen.sh` (the monotest total split into corpus
and fixture legs by subtraction, each floored, with the corpus-present question
decided by the harness rather than inferred from output);
`check-boundary.sh` (a `< 1` non-vacuity floor on every scan);
`mini_tutorial.rs` (thirteen `skip_guard::no_inputs` calls, per directory).

Legs that had no floor of their own, in risk order:

1. **`ci/check.sh`'s own step list** — 29 steps, each judged individually, and
   nothing counting them. Deleting a `step` line left "all checks passed".
   *Fixed on this branch (§3.1).*
2. **`corpus.rs::arena_corpus`** — `good` and `bad` share one `checked`
   counter. Only `bad` carries weight; `good`'s 102 files satisfy the aggregate
   alone. *Fixed on this branch (§3.1).*
3. **`ci/check-arena.sh`** — `scripts/arena.sh` fuses `good` and `bad` into one
   `find` and reports one total, so an empty `bad/` passed behind a healthy
   `good/`, even though that script's own header says "the `bad` half is the
   part that matters". *Fixed on this branch:* each leg is counted and floored,
   and their sum must equal the total the run reported — the equality is what
   makes it a check on what executed rather than on what is on disk. The live
   corpus reads `154 files = 99 good + 55 bad`.
4. **`ci/check-test-guards.sh`** — `for d in $SCAN_DIRS; do [[ -d "$d" ]] ||
   continue`. Three scan directories, one aggregate `MIN_SITES=1`. All 58 sites
   are in `checker/tests`; `derived/tests` and `kernel/tests` contribute zero
   and their disappearance would be invisible. **Open.**
5. **`ci/check-test-inputs.sh`** — three matrix legs incrementing one shared
   `matrix` counter, floored once at the end. A leg iterating zero times is
   hidden by the other two. **Open.**
6. **`ci/test-boundary.sh`** — ~50 cells, no cell counter. Deleting cells is
   invisible. **Open.** (This is not theoretical: §3.3 is a cell that had
   stopped being able to fail.)

---

## 3. The reds, and what each one actually is

Four suites are red on master. **Only one of the four is in the improvement
direction**, which is not what the tranche brief predicted — it expected
`tg_tutorial`'s three to be improvements, and two of them are not.

### 3.1 Fixed here: floors, not assertions

Neither of these was red; both were *unfalsifiable*, which is worse.
`ci/check.sh` gained an `EXPECTED_STEPS` equality (29), and
`corpus.rs::arena_corpus` gained a floor per leg. Falsification for both is
recorded in the commit messages: a stubbed `check.sh` with one step deleted
reports 28-of-29 and exits 1 where it used to print "all checks passed"; an
arena corpus with the real `good` and an empty `bad` fails the new per-leg
assertion while reporting `checked=97`, which is exactly the number that kept
the old aggregate green with every negative case gone.

### 3.2 Stale assertions, in the improvement direction

**`tg_tutorial::partially_derived_files_stay_within_their_budget`** —
`076_listRecReduction: 9 gaps, budget 31 — an improvement; lower the budget`.
The `GAP_BUDGET` table is a two-sided ratchet (it panics on `gaps < budget`
too), so the file demands its own re-baseline. Gaps fell 31 → 9. **Left
unmoved deliberately**: see §3.5 — I can measure the new value but not yet
attribute it, and this project's rule is that a re-based ratchet has to say
*why*.

**`mini_envshare_tg`** (2) and **`mini_route_tg`** (1) — all three are the same
finding on the same fixtures, and all three are convergence rather than a
loosened guard:

| assertion | was | now |
| --- | ---: | ---: |
| `034_boolType` `declinedByCheckerTyping` | 3 | 0 |
| `034_boolType` `adoptedByCheckerTyping` | 0 | 3 |
| `084_projProp1` `declinedByCheckerTyping` | 13 | 4 |
| `084_projProp1` `adoptedByCheckerTyping` | 0 | 9 |
| `034_boolType` under `Split` (route) | 1 declined / 0 adopted | 0 declined / 1 adopted |

The evidence that this is convergence and not a weakened statement guard, in
order of strength:

1. `TgBackend::typing` returns `Derived` **only** when
   `u_concl(&thm, …) == want`, where `want = Formula::mem(⟦e⟧, ⟦ty⟧)` is built
   from the interpretation on the spot. An adopted typing is by construction a
   slot whose conclusion is literally the statement the reader asked for. There
   is no path by which a mismatched statement is adopted, so "the guard
   loosened" is not available as an explanation.
2. **The offer populations are conserved**: 3 = 0 + 3 and 13 = 4 + 9. The guard
   is still consulted on every offer; only the verdict moved. A guard that had
   stopped being consulted would have dropped the total.
3. `incoherent = 0`, `alias = 0`, `divergent = 0` throughout — no certificate is
   about the wrong carrier.
4. The sibling test `the_arrow_type_converged_because_its_pi_symbol_is_now_one`
   documents this exact transition for the Π table, in its own words: the cell
   "used to be this file, asserting `divergent = 1` and one counted decline. It
   asserts the opposite now, and the change is the merge working rather than a
   guard weakening."

So these three assertions are stale, and the *comments* around them are stale in
a way that matters more than the numbers: `a_mismatched_typing_is_declined_not_adopted`
says of `034_boolType` that "the two engines' carriers genuinely differ, so
nothing may cross", and that sentence is now false. **Left unmoved** for the
reason in §3.5.

### 3.3 A real defect, fixed: a guard that could not fire

`ci/test-boundary.sh` was **red on master** — 2 self-test failures — and it is a
step of `ci/check.sh`. One root cause: `4e86d46` merged the `mini` crate into
`checker`, which emptied `COVERED_ELSEWHERE`, which made
`check-boundary.sh`'s delegation branch **unreachable**.

The instructive half is the second failure. The cell named
`a delegate ci/check.sh never runs` asserts that the delegation check fires. It
could not fire, because there was nothing delegated — so it had been passing
vacuously for as long as the branch was dead, and only went red when the
*other* stale fixture (a `ws-ok.toml` still listing `mini`) met the emptied map.
A cell written to watch a guard fire, in the file whose entire purpose is
watching guards fire, had stopped watching anything.

Fixed by making the branch reachable from the environment rather than deleting
it, with all three of its outcomes now covered by live cells.

### 3.4 A real defect, fixed: red in the configuration the gate never runs

`mini_designed.rs` was **32/34 under `--no-default-features`** and 34/34 under
`--features tg`. The established gate runs only the `tg` form, so the red was
invisible to it — and the plain form is the one the `--lib` gate uses, so it
looked as though that configuration was covered.

Both failures spawn the `checker` binary through `run_unified`, and that binary
refuses the unified route without the feature: *"the unified checker requires a
`--features tg` build; use --naive only for the historical mini checker"*. They
were not measuring a weaker property in the plain build; they were failing on
the build configuration. Fixed by gating `run_unified` and its two callers on
`feature = "tg"`, with the hazard (a `cfg`-ed-out test is *absent*, not skipped)
named at the gate and the guard that holds it — `ci/check-test-inputs.sh` —
named with it. Now 32/32 plain, 34/34 `tg`.

### 3.5 Open, and deliberately not touched: two ratchets moved adversely

**`tg_tutorial::projection_reduction_is_a_rule_fed_by_inference`** —
`init-prelude: 678 proj_reduce gaps, ratchet 661`.
**`tg_tutorial::the_declaration_typing_ledger_accounts_for_every_declaration`** —
`1250 misses against a discarded typing, was 1244`.

Both moved in the **adverse** direction. That is not automatically a regression:
this exact ratchet was moved 630 → 661 once before with a written trade, on the
grounds that new inference *reached* 31 projection redexes the run had never
contracted, each an honest decline — "the population, not the rate".

The evidence available without further work points both ways, which is why it is
being reported rather than resolved:

* *For* a population change: `the_prelude_ledger_totals_are_ratcheted` **passes**
  — `TOTAL gaps` is still within its `<= 11821` ratchet, and it was 15423 when
  these rows were pinned. The tree improved overall by a wide margin while these
  two rows rose.
* *Against* assuming it: `DECISIONS.md`'s own rule for a loosened ratchet is that
  the evidence is the diff of the whole gap ledger, and the sentence to be able
  to write is **"no row rose"**. Here a row rose. That sentence cannot be
  written, so the trade cannot be taken on the strength of the total alone.

The ratchets were last set at `43bac38` / `3c4323b`; a dozen commits have landed
on the checker since, including the indexed dependent-iota integration and the
equality-scope provenance work. **Nobody re-ran `tg_tutorial` across any of
them, because it is not a gate.** That is the finding, and it is the same
finding as the rest of this document.

Resolving it needs the full ledger diff against `43bac38`, which means building
at that commit, and it lands in `checker/src/tg.rs` and `checker/src/tc.rs` —
both owned by live seats on other branches. Not this seat's to move.

**The same reasoning is why §3.2's stale assertions were left unmoved.** They
are stale in the improvement direction and the numbers are not in doubt, but
re-basing them means writing the reason into the test, and the honest reason is
"some commit between `43bac38` and `36106d2` merged these carriers" — which is a
provenance marker, not a derivation. The next seat to touch `tg.rs` will know
which commit, and should land the re-baseline with the trade written out.

---

## 4. Task #122: the three builds

**The premise as stated is no longer true.** `ci/check.sh` does not build the
workspace three times: the three feature runs are `-p nanoda_lib`, and
`kernel`/`derived` are built once and shared. Verified — after building
`nanoda_lib` under all three feature sets, `cargo build --workspace --exclude
nanoda_lib --all-targets` finishes in 0.02 s.

What is still true is that `nanoda_lib` itself — lib, 2 binaries, 14 integration
test binaries — is compiled three times, once per feature configuration.
Measured on this tree, rebuilding after `touch checker/src/lib.rs`, at
`CARGO_BUILD_JOBS=6`:

| configuration | `instructions:u` | `task-clock` |
| --- | ---: | ---: |
| plain | 1.384 T | 187.9 s |
| `--features stepcount` | 1.414 T | 195.0 s |
| `--features tg` | 1.605 T | 220.0 s |
| **total** | **4.403 T** | **602.9 s** |

Both counters are reported because `instructions:u` was measured this week to
understate allocation-shaped effects by 9–17 points; here they agree on the
ordering and on `tg` being the expensive one (+16 % instructions, +17 %
task-clock over plain).

**Not fixed, and it should not be.** `stepcount` and `tg` change `cfg`, so the
three are genuinely different compilations and cannot share artifacts. Removing
one removes a configuration from the matrix, which is coverage rather than
waste — and §3.4 is a live demonstration that the plain configuration catches
things the `tg` one does not.

The one genuine duplication is small and is *execution*, not compilation: the
step `tests (cross-engine core)` re-runs `mini_envshare_tg`, `mini_route_tg` and
`unified_cli`, all three of which `cargo test -p nanoda_lib --features tg`
already ran — about **15.8 s**. Its purpose is to name those files so
`ci/check-test-inputs.sh` can verify a `cfg(feature)` suite is selected by a
step, and that is worth more than 15.8 s. Recorded and left.

---

## 5. What is still open

1. **Per-leg counters in `check-test-guards.sh` and `check-test-inputs.sh`**
   (§2.1 items 4, 5), and a **cell counter** in `test-boundary.sh` (item 6).
2. **The two adverse ratchets** (§3.5) — needs the ledger diff and the owning
   seat.
3. **The three stale crossing assertions and one gap budget** (§3.2) — needs the
   attributing commit so the re-baseline can say why.
