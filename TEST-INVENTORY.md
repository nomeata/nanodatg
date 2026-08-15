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
5. **The gate list is the real finding, and it is not fixed.** §3.5's two
   ratchets each fired correctly the first time they were run; nobody ran them
   for four days. `ci/check.sh`'s step `tests (tg backend)` does cover
   `tg_tutorial` — so this is not a missing step, it is that **`ci/check.sh`
   itself is not on the short gate list seats actually run**. Every guard this
   document adds is downstream of that.
6. **Shadowed assertions (§6), the unfixed remainder.** Four were fixed; three
   groups were not, and two of the three need a file this branch does not own:
   * `origin_report()`'s surviving early return and the `if asked > 0` report
     gates, both in `checker/src/tg.rs` — §6.4. Neither is read by a test today;
     the second makes a live `mini_designed.rs` assertion unfalsifiable.
   * `tg_tutorial.rs:1917` and `:1931` are the **same predicate**
     (`assert!(fired >= 92)`) on an unchanged local, carrying two different
     failure stories. The second cannot fail. Confirmed by inspection, not
     mutation — a literally identical predicate needs none.
   * `tg_tutorial.rs:721`'s `assert_eq!(counted, n)` compares two printings of
     one local (`escapes`, `global_report`), so it is `escapes == escapes`. The
     independent observation that *would* separate it exists and is unused:
     `escapes::report_from` recomputes the total from the `made`/`taken`/`closed`
     census rather than from the counter.
7. **729 of `derived/`'s 952 tests are unaudited for §6's pattern**, with named
   candidates carrying named surviving mutations — the fibre-lift rung pair
   (every call site in the repo passes `(1, 2)`, so `n` is never observed), and
   the `np <= 1` parameter spines in `le_index.rs`, `decl_proj.rs` and
   `telescope.rs`. None is verified; each is a hypothesis with a stated
   mutation, which is the form §6.6 asks for.

---

## 6. Shadowed assertions — an assertion that cannot fail on its own

**Audited 2026-08-15 on `joachim/shadowed-assertions`, branched from master
`f9b98ee`.** Every claim below that is marked *measured* was produced by
mutating production code, watching the red (or the green), and restoring; the
tree's production code is unchanged by this audit apart from the two test-side
fixes in §6.4.

### 6.1 The pattern

An assertion can be **structurally untestable** — present, plausible, and
incapable of failing — because something upstream fails first on every mutation
that would have tripped it.

> **Any assertion downstream of a gate that the same mutation trips is untested
> — and "gate" includes early returns in reporting code, `.expect(…)` on the
> value under test, a constructor's own guard, and a fixture instantiated where
> two readings agree, not just an earlier `assert!`.**

The five gates seen in this tree, in the order they cost time:

1. **An earlier assertion in the same test.** A label check and a counter check,
   where every mutation that moves the count also moves the label. The label
   fails first and the counter assertion has never once been exercised.
2. **An early return in reporting code.** The row the assertion reads is emitted
   only on the failure path, so it vanishes in exactly the success state the
   work is driving toward. *A readiness counter whose only witness is a failure
   is not a readiness counter.*
3. **The constructor's own guard.** `X::build(…)` ends in
   `(concl == want).then_some(out)`, and the test spells `want` with the same
   production calls. Every mutation makes the constructor return `None`, so the
   `.expect(…)` fires and the assertions about the result never discriminate.
4. **A degenerate instantiation.** The mutation yields a *true theorem about the
   wrong thing*, the constructor succeeds, nothing `expect`s — and the test
   still passes, because the fixture is instantiated at the one value where the
   correct and incorrect readings agree. `φ := y = y`, `⟨a,a⟩`, `subset(u,u)`,
   a one-element list, an adjacent rung pair, index 0.
5. **A predicate too symmetric for its subject.** `occurs_free(a) &&
   occurs_free(b)` cannot pin an *ordered* pair; `leq(l,r) && leq(r,l)`
   asserted only at pairs that are equal cannot pin antisymmetry.

### 6.2 The standing rule is insufficient, and this is why

`DECISIONS.md` (2026-08-10, "And the rule that found the bug in the fix") says:

> **A guard nobody has watched fail is a guard nobody has tested.**

That is right and it is not enough. **Confirming that a test goes red does not
establish that each of its assertions can go red.** Every instance in §6.3 sits
in a test that was falsified when it was written — the author mutated something,
saw the red, restored, and landed it. The red came from the *first* assertion
every time, and the assertion the test was named for was never reached.

The stronger form:

> **Falsify every assertion, not every test.** For each assertion, name the
> mutation that trips *that assertion and no earlier one*, and watch it fail at
> that line. An assertion for which no such mutation exists is not a weak
> assertion — it is not an assertion. Delete it, or replace it with one that
> pins something the earlier gate cannot reach.

Two corollaries that are cheaper than the full discipline and catch most of it:

* **Read the assertion's message as a claim and try to violate it directly.** If
  the message says "a count alone would not say *which*", ask what the count is
  pinned to three lines up. At a pinned zero the names say nothing.
* **When you cannot separate two assertions, say so at the assertion.** The
  precedent is `tg.rs`'s
  `a_redex_subject_is_typed_at_its_contractum_and_owes_betas_premise`, which
  records of its fourth assertion: *"It was attempted against three mutations …
  It stayed green through all three, because `Thm::mp` refuses … The assertion is
  kept as a recorded outcome, and its honest status is: enforced one layer
  below, unfalsifiable from here."* That is the correct disposition. An
  unfalsifiable assertion carrying a confident message is the defect; one
  carrying its own status is documentation.

### 6.3 The instances

The first five were found by one seat in one day, before this audit; the rest
are this audit's, and each was measured.

| # | gate | where | what was untested |
| --- | --- | --- | --- |
| 1 | earlier assertion | a decline label beside a firing count | the **counter** assertion had never been exercised; falsified only by a mutation that keeps the label and zeroes the count |
| 2 | reporting early return | `tg.rs::origin_report()` | `ICOD`/`IDEP`/`PRE`/publication rows were emitted inside a function that returns early when there are no gap origins. The rows vanished the moment the rule started certifying and two tests **went red on success**. Fixed by hoisting them to `ix_readiness_report` |
| 3 | wrong event | `assert_eq!(FIRED, PRE)` | `IX_FIRED` counts a function *returning* an equation, not the site *certifying*. Renamed to `composite BUILT` |
| 4 | earlier label | a conclusion spine's constructor position | the mutation produced a *true equation about the wrong pair* and died at a **label** assertion one step before the join check it was meant to exercise |
| 5 | degenerate instantiation | a Prop-rung `x = •` | the mutation gave a **true theorem**, so the constructor succeeded and nothing `expect`ed; the ground test passed because it instantiated at the value where the two readings agree |
| **6** | **degenerate instantiation** | **`kernel/tests/henkin.rs`** | **`closed_witness` fixes `φ := y = y`, so `φ[c/y]` *is* `c = c` and "the axiom is φ at the constant" is the reflexivity assertion above it. *Measured: a `henkin` that ignores φ outright and returns `⊢ c = c` leaves all 8 tests in the file green.* The rule's entire content was untested from inside the TCB. Fixed with a witness at `φ := y = d`** |
| **7** | **symmetric predicate** | **`kernel/tests/rules.rs`** | **`opair_description_mentions_both_components` asserts `occurs_free(a) && occurs_free(b)`, symmetric in `a` and `b`. *Measured: building `⟨b,a⟩` under the name `⟨a,b⟩` (`thm.rs:818`, singleton half naming `b`) leaves every test in the file green.* Fixed by rebuilding the Kuratowski formula from `is_singleton`/`is_upair`** |
| **8** | **degenerate instantiation** | **`checker/src/tests/level.rs`** | **all five assertions about `eq_antisymm` named a pair that *is* equal, so both conjuncts hold. *Measured: rewriting it as `leq(l,r) && leq(l,r)` — dropping antisymmetry — leaves `--no-default-features --lib` at 246/246.* It gates sort defeq (`tc.rs`) and constructor level agreement (`inductive.rs`), so the degenerate form accepts `Sort u ≡ Sort v` whenever `u ≤ v` — the unsound direction. Fixed with a strict pair in **both** argument orders** |
| **9** | **no reachable occupant** | **`checker/tests/mini_dump.rs`** | **the assertion named two reason strings (`"has no \`iota\` field"`, `"neither built nor tested"`) that had been **deleted from `dump.rs`**. No run could emit either, so no mutation could trip it — one line below a header warning against exactly that. Fixed by asserting the absence *shape*, at the one row nothing else in the test reaches** |

Instance 7 carries a trap worth keeping: `assert_ne!(is_opair(p,a,b),
is_opair(p,b,a))` is **not** a fix. `is_upair` is symmetric in meaning but not
in syntax, so the two descriptions differ structurally under the swapped rule
too and that assertion stays green. Only rebuilding from the constructors
separates them.

### 6.4 What was fixed, and what was reported instead

Fixed on this branch, each with its separating mutation watched red and
restored: instances **6, 7, 8, 9** (`kernel/tests/henkin.rs`,
`kernel/tests/rules.rs`, `checker/src/tests/level.rs`,
`checker/tests/mini_dump.rs`). `kernel/` production code is unchanged;
`git diff kernel/src/` is empty and both kernel mutations ran under a restore
trap.

**Reported rather than fixed, because `checker/src/tg.rs` is owned by another
seat:**

* **Instance 2's residue.** `origin_report()`'s early return survives, and now
  returns `ix_readiness_report()` — so the indexed readiness rows are safe in
  both branches. Everything *after* that point in `origin_report`'s body still
  vanishes when `ORIGINS` is empty: the `equations ACQUIRED` line, `indexed iota
  rule REACHED`, the indexed census, and `the top origin, by recursor` rows.
  **Verified: no test in the tree reads any of them**, so this is a measurement
  hazard and not a test hazard — `ORIGIN-RANKING.md` §2 already records it
  biting a measurement. The fix, if wanted, is the same one instance 2 got:
  emit unconditionally.
* **The `asked > 0` guards under a `> 0` report gate.** `mini_designed.rs`'s
  `tg_discharges_the_indexed_iota_rules_premise` asserts `asked > 0` off the
  `ICOD` and `IDEP` readiness rows, and `ix_readiness_report` emits each row
  only `if asked > 0`. The row exists iff the assertion holds, so the
  `contains(…)`/`unwrap_or_else(panic!)` above it catches the only state that
  would trip it. Separating it needs the *gate* changed, in `tg.rs`.

### 6.5 One claim this audit refuted

The largest family found — roughly sixty assertions across `mini_designed.rs`
and `mini_tutorial.rs` of the form "and the reason set is empty", each following
`assert_eq!(constEv, pairs)` — **is** shadowed: `Ledger::note_missing`
(`ledger.rs:612`) is the sole writer of `missing`, and it is the `Err` arm of the
same `match` whose `Ok` arm increments `const_ev_ok`, so `constEv == pairs`
implies the `waiting:` set is empty by construction.

The conclusion drawn from that — that the tranche's named-row ratchets are
"protected by exactly two integers" — **is wrong**, and it is the kind of claim
this document exists to check. The invariant those assertions restate is itself
tested, by `ledger.rs::every_reason_lands_in_a_counter_in_the_set`, on a fixture
built deliberately so that the equality is *"not `0 = 0` nor `n = n` over a
uniformly broken file"*. The sixty are redundant, not unguarded. **Redundancy
whose message overclaims is a documentation defect; it is not the same finding
as an unguarded invariant, and conflating them would have sent a seat to rewrite
sixty live assertions.**

### 6.6 The check to apply when writing a test

Before landing a test with more than one assertion, for each assertion after the
first:

1. **Name the mutation that trips this assertion and not the one above it.** If
   you cannot, the assertion is redundant — either delete it or write its status
   at the line, as §6.2 describes.
2. **Ask what gates it.** An `.expect(…)`/`.unwrap()` on the value under test; a
   `then_some(concl == want)` inside the constructor; a report row emitted under
   `if n > 0` or after an early return; an exit-status assertion that already
   subsumes every counter beneath it.
3. **Ask whether the fixture can tell the readings apart.** Two atoms cannot
   distinguish a **nesting**; two identical atoms cannot distinguish an
   **order**; an adjacent pair cannot distinguish `n` from `m+1`; `x = x` cannot
   distinguish an equation from its converse; a symmetric predicate cannot pin
   an ordered subject. Three elements, all distinct, is the default.
4. **If the assertion reads a counter, find its increment site.** Two counters
   bumped on the same line make `assert_eq!(a, b)` a tautology; a counter that
   is a `saturating_sub` of two others is not an independent observation.
5. **Grep every string literal you assert the absence of.** Instance 9 is the
   whole argument: a literal with no occupant in the tree is an assertion that
   can never fail, and it reads to the next person as coverage.

### 6.7 Denominator

**1 464 `#[test]` functions** in the tree (`checker/tests` 14 files,
`checker/src` `#[cfg(test)]` modules including `tg.rs`'s 48, `kernel/tests` 62,
`derived/tests` 952). **687 were examined closely**; 729 of `derived/`'s remain
unaudited, and the highest-yield names there are the `family_*`, `cumul_*`,
`verify_*` and `w*rec` groups.

Of those 687, **four were confirmed by mutation and fixed**, and one candidate —
`derived/tests/hyp.rs::binary_operations_union_merge` — was **refuted**: a
`close` that ignores its requested order goes red there, because the fixture's
`[p, q]` is not the canonical rank order. That refutation is the reason §6.6
step 3 distinguishes *nesting* from *order*: two atoms genuinely cannot
distinguish a left from a right nesting, but they distinguish `⟨p,q⟩` from
`⟨q,p⟩` perfectly well.

`ci/check-test-guards.sh` and `ci/skip-guard.rs` were read first and are **not**
this mechanism: they answer "a test that did not run", the *input* dimension.
This section is "an assertion that ran and could not fail". A suite can be fully
guarded by both and still contain every instance above.
