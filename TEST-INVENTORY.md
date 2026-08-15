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
too), so the file demands its own re-baseline. Gaps fell 31 → 9.

**Attributed 2026-08-15, and the answer is that it is not one commit** — which
is why it resisted a targeted read. Measured on the same sweep as §3.5, on
`nanoda_bin`:

**Attributed and re-based.** It fell in **two** tranches, which is why a single
attributing commit could not be found and why the previous seat was right to
refuse to move it:

| commit | 076 gaps | what moved |
| --- | ---: | --- |
| `3c4323b` … `9b691cb` | 31 | — |
| **`cc5dfd5`** *(replay exact lazy delta evidence)* | **24** | derived 501 → **510**, conditional derivations 126 → 134 with all the extra accounted for by a rule, escapes flat at 17 |
| `4fc2f25` … `1fe03a0` | 24 | — |
| **`a29aad9`** *(equality-query scope provenance at the judgement boundary)* | **9** | **entirely escapes, 17 → 2**; conditional derivations byte-identical at 134 made / 0 copies / 117 by a rule |

Nine more theorems and seven fewer gaps at the first; at the second the
certificates were always being built and their `Γ` is now right, so fifteen
assumptions that used to reach the boundary are discharged instead. On
`init-prelude` `a29aad9` is the cleanest commit in the whole range — **no row
rose**, and the entire −1 221 on the total is that one escape row.

A previous seat's hypothesis that `5bf8342` ("the dependent arm takes the whole
origin") closed it is **refuted**: 076 is still 31 at `73dcc53` and `6483199`,
both of which are after `5bf8342`. The other three budgets are exact at master
(075 = 3, 116 = 10, 081 = 1). **`tg_tutorial` is now 35/35.**

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

### 3.5 Resolved: two ratchets moved adversely, and both are population changes

**Measured 2026-08-15.** Built at `3c4323b`, where both were last pinned, and at
master `83a95cf`, and diffed **every row** of the gap ledger — the evidence
`DECISIONS.md` requires and which had never been produced. Both runs are the
same dev profile, the same `--features tg`, and the same binary; the ratchets
are read off `nanoda_bin`, which has carried mimalloc since long before
`00a9a92` (that commit added it to `checker.rs`, a *different* binary), so there
is **no allocator asymmetry to correct for** — and gap counts are deterministic
anyway. A run is 15 s, not the four minutes `report`'s doc comment claims.

#### The whole-ledger diff

`TOTAL gaps` **15 734 → 10 386**, escapes **2 232 → 1 199**, and of the ledger's
**23 `gap:` rows exactly two rose**:

| row | 3c4323b | master |
| --- | ---: | ---: |
| `proj_reduce` | 659 | **678** |
| `iota: the major premise is not a constructor` | 486 | **550** |
| `trans over an admitted premise` | 8 457 | 5 370 |
| `undischarged assumption … survived to the boundary` | 2 232 | 1 199 |
| `pi congruence over an admitted body premise` | 1 147 | 722 |
| `congruence over an admitted premise` | 636 | 523 |
| `iota: this recursor has no curried interpretation` | 792 | *row closed* |
| *`iota: no interpretation — a nested inductive`* | — | *100 (new)* |
| *`iota: no interpretation — a K-like eliminator`* | — | *6 (new)* |

**"No row rose" cannot be written, and this is what replaces it**: two rows
rose, +83 against −5 348 on the total, and the second of the two is already
accounted for with its trade at the ι ratchet (the dependent arm closed 222 of
286 sites; 64 acquired a *better reason* rather than a closure). So
`proj_reduce` was the only unattributed gap-row rise in the tree.

#### Each rise, attributed

A ten-point sweep of the 103 first-parent commits. Both rows move **once**, and
they move at **different commits** — the two questions genuinely had two answers.

| checkpoint | proj_reduce | miss_cond | TOTAL | 076 |
| --- | ---: | ---: | ---: | ---: |
| `3c4323b` … `18212fc` | 659 | 1 244 | 15 734 → 11 821 | 31 |
| `b654c98` | **678** | 1 244 | 11 607 | 24 |
| `e23e9ac` | 678 | **1 250** | 11 607 | 24 |
| `b747f80` … master | 678 | 1 250 | **10 386** | **9** |

**`proj_reduce` +19 — population, and it is `b654c98` alone.** Every one of the
ten commits in that block was measured; nine are inert on this row (659 at each,
`TOTAL gaps` flat at 11 821) and the whole move is at **`b654c98` "checker: do
not park conditional reduct certificates"**.

**The mechanism is not the one the 630 → 661 move had**, and getting this right
mattered. That was new inference *contracting* redexes nothing had contracted.
This is the shape `the_prelude_ledger_totals_are_ratcheted` already records for
its own 15 423 → 15 455 move: **the gaps were always there and something was
hiding them.** In that one commit:

| | `4fc2f25` | `b654c98` |
| --- | ---: | ---: |
| conditional derivations made | 33 171 | 32 938 |
| …**of them copies** | **238** | **0** |
| escapes | 2 657 | **2 420** |
| `derived (real kernel Thm)` | 164 205 | **164 210** |
| `gap: proj_reduce` | 659 | **678** |
| `gap: trans over an admitted premise` | 5 366 | 5 370 |
| `TOTAL gaps` | 11 821 | **11 607** |

A parked conditional certificate was being re-served in place of the rule, and
it was escaping debt — 238 copies go to zero and 237 escapes go with them. What
it concealed is 19 projection reductions with no certificate, plus the 4 they
relay into `trans`. **Nothing that was derived before is admitted now**: the two
numbers that establish it are `derived` going **up** by 5 and escapes going
**down** by 237, and a commit that had lost 19 real certificates would have moved
both the other way. Corroborating, the four rows the test protects are
byte-identical across the entire range — `threaded` **9**, proof shortcut **34**,
proof λ's body clause **41**, admit fall-through **0** — and the origin bitmask
agrees: own 659 → 678, relayed 1 840 → 1 844, that +4 being exactly the +4 on
`trans`.

**miss_cond +6 — population, and the test said so in advance.** Attributed to
**`05f9bb6` "checker: type a redex subject at its contractum"** (`HtClause::
SubjectBeta`), confirmed by measuring the commit against its own parent:
`907984f` reads **1 244**, `05f9bb6` reads **1 250**, with `proj_reduce` already
at 678 on both. The declaration-typing ledger is **identical at every other row** —
`cond` 198, `gap` 2 667, `stored` 26, `hit` 1 326 all flat — while the store's
*ask* traffic rose 29 131 → 30 420. The assertion's own comment declares this
case ahead of time: *"A rise here with `cond` flat is attribution churn, not new
discarding; a rise **with** `cond` is the regression this pin is for."* The
rate fell, 4.27 % → 4.11 %. `05f9bb6` is the exact mirror of `43bac38`, the
commit that *set* the 1 244 pin and moved this row 1 161 → 1 165 the same way.

#### What was done

Both ratchets re-based **with the trade written at the assertion**: 661 → 678
and 1 244 → 1 250. Both whole-ledger totals **tightened**, which the symmetric
half of the rule requires: `TOTAL gaps` 11 821 → **10 386** and escapes
2 625 → **1 199**. Each had been carrying ~1 430 of slack, pinned at `1cbd603`
and never re-read — a guard that could not have seen a 1 400-gap regression
arrive, which is the standing task *"guards that assert a TOTAL are re-based by
neighbours' traffic"* happening in front of us.

#### The guard, and the one it is not

A new test, `the_whole_gap_ledger_is_accounted_for_row_by_row`, pins all 23
`gap:` rows and asserts (1) no row rose, (2) the table's rows are exactly the
report's, and (3) they sum to `TOTAL gaps`. All three falsified and restored.
Invariant (3) is the one that matters: over this very range a 792-gap row
**vanished** and 106 gaps arrived under two labels that did not exist before, and
against floors alone a rename banks itself as progress.

**But per-row floors are not what was missing here, and saying so is the point.**
`proj_reduce` *had* a per-row ratchet, and it fired correctly the first time it
was run. So did miss_cond's. The guards worked; **the suite was not run** —
`ci/check.sh`'s step `tests (tg backend)` covers `tg_tutorial`, and `ci/check.sh`
is not on the four-command gate list any seat actually runs. The new table
generalises the protection to the twenty-one rows that have *no* individual
ratchet; it does not fix the reason these two went unobserved. **That fix is a
gate-list change, and it is the finding of this whole document.**

#### Two things this entry previously said that the measurement refuted

Recorded because both were reasonable and both were wrong, and a seat reading
the old entry would have planned the wrong work.

* **"A dozen commits have landed on the checker since."** It is **134**
  commits, 103 of them on first-parent. More importantly the interesting ones
  are not the named tranches: the indexed dependent-ι integration, the
  equality-scope provenance work and the ι gate's direct-clause arm are all
  *after* both rises and moved neither. The rises are in a block of thirteen
  consecutive commits (`4e86d46`…`b654c98`) that have **no commit message body
  at all**, and that is why no amount of targeted reading could attribute them.
* **"Resolving it lands in `checker/src/tg.rs` and `checker/src/tc.rs`, owned
  by live seats."** It did not. The resolution is a measurement plus test-file
  and document edits; **no production file was touched**. The diagnosis needed
  neither owned file, and the previous seat's instinct to report rather than
  reach into them was right for a reason that turned out not to apply.

The `43bac38` / `3c4323b` pin was right, though, and worth stating: the
baseline reproduces the pinned numbers **exactly** — `proj_reduce` 659,
miss_cond 1 244, `TOTAL gaps` 15 734, escapes 2 232 — which is what makes the
diff above evidence rather than an anecdote.

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

## 4.5 The shadowed assertion — four instances, one rule

*Found on `joachim/icod-rung` while landing the indexed ι tranche, 2026-08-15.
Recorded here rather than in that tranche's design doc because it is a fact
about how this tree is tested, not about indexed families.*

**The rule.** *An assertion downstream of a gate that the same mutation trips is
untested.* The only way to know it works is to construct a mutation that
separates it from the gate — one that leaves the gate satisfied and trips only
the assertion. And **"gate" is wider than "an earlier `assert!`"**: an early
`return` in reporting code is a gate, a counter that names a different event is
a gate, and a reason string that cannot discriminate is a gate.

This is the same disease as §"Why this document exists" — an unobserved check —
one level down. There, a whole suite was outside the gate list. Here, an
assertion is inside a suite that runs, passes, and never exercises it.

**The four instances, in the order they were found.**

1. **An earlier assertion shadows a later one.** `mini_designed`'s indexed test
   asserts a decline label and *then* a readiness counter. Every mutation tried
   against the counter also moved the label, so the label assertion fired first
   and the counter assertion was never reached. Separated by a mutation that
   **keeps the label and zeroes the count** — making the fieldless-`IDEP` clause
   return the fielded error — at which point it fired on its own.

2. **A reporting early-return shadows every row behind it.** The indexed
   tranche's readiness rows (`ICOD`, `IDEP`, `PRE`, publication) lived inside
   `origin_report()`, which returns `String::new()` when `ORIGINS` is empty —
   i.e. when **nothing declined**. That is exactly the state the tranche was
   working towards. The moment the ι rule started certifying, every row vanished
   and the two tests reading them went red **on success**, costing several
   cycles hunting a regression that did not exist. *A readiness counter whose
   only witness is a failure is not a readiness counter.* Fixed by extracting
   `ix_readiness_report()`, emitted whatever the origin ledger says.

3. **A counter that names the wrong event shadows what it appears to check.**
   `assert_eq!(FIRED, PRE)` was added to pin the composite, and the mutation
   that drops step 4 **left it passing** — because the counter incremented when
   `fire_ix_dep` *returned an equation*, not when the site *certified*;
   `derive_iota_core` still has to join that equation against the reduct's own
   contraction. Renamed `composite BUILT`, and the thing that actually catches
   it — the fixtures' own gap counts — asserted instead.

4. **A tautological reason string shadows the diagnosis.** Asked why `RBTree`'s
   minor premises fail, `ht_shape` on the minor's declared *type* answers "a Π —
   needs `dprod_in_universe`" — which it answers for **every** minor premise of
   every recursor, because a minor's type is always a `Π`. It was about to be
   reported as a second site for the missing `Expr::Pi` arm. The `HtMiss`
   histogram settled it as `HtMiss::Lam` instead. A reason string that is
   constant over the population cannot distinguish a diagnosis from a
   restatement of the question.

**The adjacent disease: an error message that blames the wrong thing.** Two
defects in this tranche survived because the failure they cause is rare and its
message points elsewhere. The indexed nest was never marked `adopted`, so its
chain started at a head the redex's own interpretation is not — reported as
`"the reduct does not contract to what the recursor computes"`, which blames the
*reduct*. And a use-site domain written through its own nullary `def` is a
symbol `target_head_step` has no head to step; the recursor's declared minor
type never has that shape, so the path was never exercised. A misleading message
that survives because its failure is rare is the same fact as an assertion that
survives because its gate always fires first.

**What to do about it.** When adding an assertion, ask what mutation it is meant
to catch, then *make* that mutation and confirm it dies **there** rather than
earlier. Predicting the death point wrongly is itself worth recording — it has
happened on this branch, and each time the wrong prediction was the interesting
part.

## 5. What is still open

1. **Per-leg counters in `check-test-guards.sh` and `check-test-inputs.sh`**
   (§2.1 items 4, 5), and a **cell counter** in `test-boundary.sh` (item 6).
2. ~~The two adverse ratchets~~ — **resolved 2026-08-15** (§3.5). Both are
   population changes, both re-based with the trade written, both totals
   tightened, and a per-row ledger guard added.
3. **The three stale crossing assertions** (§3.2) — still open, and **two named
   candidates are now refuted by measurement**. `mini_envshare_tg` was run at
   `a29aad9^`, `a29aad9`, `887fa10^` and `887fa10`: it fails the same 2 at all
   four, so neither commit is where those counters converged. The change is
   earlier than `1fe03a0`. It could not be attributed from §3.5's ledger diff
   because these are counters on the **unified** checker (`checker.rs`, mini
   publication) and every number in §3.5 is `nanoda_bin`'s, which never runs
   mini — so they need a measurement on their own binary. The remaining
   suspects are the mini-unification commits `4e86d46`…`02ab90f`.
4. ~~The `076_listRecReduction` budget~~ — **resolved 2026-08-15** (§3.2), two
   tranches, both attributed, re-based 31 → 9 with the derivation written.
6. **The shadowed-assertion audit** (§4.5) — the rule is written and its four
   instances are named, but **the tree has not been swept for others**. A
   separate seat owns that; this entry exists so the sweep is not mistaken for
   done.
7. **The gate list is the real finding, and it is not fixed.** §3.5's two
   ratchets each fired correctly the first time they were run; nobody ran them
   for four days. `ci/check.sh`'s step `tests (tg backend)` does cover
   `tg_tutorial` — so this is not a missing step, it is that **`ci/check.sh`
   itself is not on the short gate list seats actually run**. Every guard this
   document adds is downstream of that.
