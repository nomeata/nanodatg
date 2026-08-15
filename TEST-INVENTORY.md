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

**Re-measured 2026-08-15 on master `50605c4`, and the shape of this table has
changed: there is now ONE build configuration.** The two columns below used to
be **plain** (`NullCertifier`) and **`--features tg`** (the real
Tarski–Grothendieck backend); retiring the `Certifier` trait left one backend,
so the feature had nothing to select and was deleted at `d746251`. Every target
is unconditional, `cargo test -p nanoda_lib` runs all fourteen, and **all 479
tests pass** (re-measured 2026-08-15 on master `4a2910d`; the table below sums to
that figure, which the previous total did not — it read 476 against rows summing
to 475). The two suffixed suites were renamed with the feature —
`mini_envshare_tg` → `mini_envshare_cross`, `mini_route_tg` → `mini_route` —
because a name that says "needs a special build" is how a suite is read as
optional; `tg_tutorial` keeps its name, where "tg" is the subject.

| target | covers | tests | time | gated? |
| --- | --- | ---: | ---: | --- |
| `src/lib.rs` (unit) | the checker's own modules, `mini::*` | **299/299** | 8.7 s | yes |
| `tests/corpus.rs` | good/bad export acceptance, arena corpus | **6/6** | 40.3 s | yes |
| `tests/tg_tutorial.rs` | **every defeq step discharged, no gaps** | **36/36** | 31.7 s | yes |
| `tests/mini_mutual.rs` | mutual/nested encodings | **12/12** | 28.2 s | yes |
| `tests/mini_nested.rs` | nested declaration interpretation | **23/23**, 2 ignored | 17.3 s | yes |
| `tests/mini_tutorial.rs` | tutorial corpus under mini | **16/16** | 16.4 s | yes |
| `tests/mini_dump.rs` | model dump shapes | **12/12** | 16.3 s | yes |
| `tests/unified_cli.rs` | the unified CLI's ratchets | **6/6** | 5.4 s | yes |
| `tests/mini_nat_equations.rs` | the characteristic Nat equations | **2/2** | 4.2 s | yes |
| `tests/mini_designed.rs` | designed-fixture behaviour, indexed seam | **35/35** | 2.3 s | yes |
| `tests/mini_envshare_cross.rs` | crossing ledger, statement guards (was `mini_envshare_tg`) | **14/14**, 1 ignored | 0.3 s | yes |
| `tests/mini_budget.rs` | declared budget declines | **1/1** | 0.3 s | yes |
| `tests/mini_envshare.rs` | the mini-side half of the `EnvCore` seam | **6/6** | 0.3 s | yes |
| `tests/mini_route.rs` | the routed driver over one core (was `mini_route_tg`) | **10/10**, 2 ignored | 0.2 s | yes |
| `tests/mini_infinitary.rs` | infinitary constructors | **1/1** | 0.2 s | yes |
| doc-tests | prose examples in `inductive.rs`, `pretty_printer.rs`, `lib.rs` | 0, **8 ignored** | 0.0 s | yes |
| `src/bin/*.rs` (unit) | — | 0 tests | 0.0 s | — |
| **`cargo test -p nanoda_lib`** | **all of the above, in one command** | **479 passing**, 13 ignored | **171.8 s** | **the gate** |
| `kernel/tests/*` (8 files) | the trusted base: rules, Tarski, Henkin, choice | **all green** | seconds | yes |
| `derived/tests/*` (97 files) | derived rules and constructions | **all green** | seconds | yes |

`kernel` and `derived` together are **1049 tests across 109 targets, 0 failed**
(`cargo test -p kernel -p derived`), and both are now on the gate list —
including the eight files covering the trusted computing base, which is the
only component that must be correct for soundness.

**"gated?" now has one answer for every row**, and that is the whole change of
2026-08-15: the gate is `cargo test -p nanoda_lib`, unnarrowed, so a target
cannot be outside it. The column used to read "only via `ci/check.sh`" on
eleven of these rows. See `CLAUDE-HANDOFF.md`, "Why an enumerated list was the
defect".

### 1.1 The suite that runs longer than 60 seconds — there is none

**This section said `tests/mini_nested.rs` runs 175–177 s and that a full run
of every target is about 8 minutes. Both numbers are wrong on master `50605c4`,
and the first was the sole stated reason for keeping the full run off the
per-commit gate.**

Measured twice, with the same two tests `#[ignore]`d as when the 175 s was
taken: **`mini_nested` is 17.2 s** — 17.17 s inside a full package run and
17.26 s standing alone. It is the *fifth* slowest target, not the first.
**The whole package — 299 unit tests and all 14 integration suites, 479
passing — is 171.8 s.** The slowest single target is `corpus.rs` at 40.3 s,
then `tg_tutorial` at 31.7 s and `mini_mutual` at 28.2 s. Nothing is over the
minute; `src/lib.rs`, recorded here at 86 s, is **8.7 s**.

The 175 s was quoted as the reason for a decision and never re-checked, and a
reason that is never re-checked outlives the fact it rests on — the same shape
as the assertions in §3, one level up. The likely cause is `d263be2`'s
syntactic-equality shortcut, whose whole subject is not reducing a term to
discover it equals itself, which is what a nested interpretation does
constantly; that attribution is a **hypothesis and was not measured**. The
17.2 s was.

The consequence is in `CLAUDE-HANDOFF.md`: there is no suite too slow to gate,
so the gate is the package rather than a list of targets.

### 1.2 Four targets were *absent*, not skipped, in the plain build — fixed

`mini_envshare_tg.rs`, `mini_route_tg.rs`, `tg_tutorial.rs` and `unified_cli.rs`
opened with `#![cfg(feature = "tg")]`. Without the feature they compiled to
nothing and cargo printed `running 0 tests … test result: ok`. This is a *third*
shape of "skip is not pass", distinct from both the shell `exit 77` and
`ci/skip-guard.rs`: there is no skip to guard, because there is no test. The
same shape cost `mini_designed.rs` two of its 34 tests, which is how it was
32/34 in the plain build and 34/34 under the feature.

**Resolved 2026-08-15 by removing the cause rather than guarding it.** The `tg`
feature selected `certify::Backend` between `NullCertifier` and the real
backend; retiring the `Certifier` trait left one backend, so the feature had
nothing to select and is gone (`checker/src/certify.rs`, "There is one backend,
and it is not selected"). All four suites and both `mini_designed` tests are
now unconditional, and there is one build configuration where there were two.

What was to hold the *general* shape is `ci/check-test-inputs.sh`, which refuses
a `cfg(feature)` suite in a package no `--features` step selects. **Measured
2026-08-15: that leg — leg C — has no subject on this tree.** Its scan
(`grep -rlE '^#!\[cfg\(feature = ...\)\]' checker/tests`) matches **zero**
files, so it iterates zero times; legs A and B still have subjects
(`stepcount`/`nanoda_lib`, and kernel/derived carrying no `cfg(feature)` of
their own).

**Fixed at `cbb949f`, and the vacuity was never the defect.** A guard against a
thing being *reintroduced* is not broken for having nothing to guard yet. What
was broken is that all three legs incremented one `matrix`, floored once at
`matrix == 0`, so the run printed `3 feature-matrix premises checked` over
1 + 2 + 0 and **leg C's silence was indistinguishable from leg C having run** —
on the leg whose entire job is catching a suite that compiles to an empty binary
and reports `running 0 tests … ok`. Each leg now reports its own count and leg C
prints `INAPPLICABLE` in so many words. Its `--self-test` is what proves leg C
can still fire, against a synthetic tree the real one cannot supply; four new
cells read the script's *output* rather than its exit code, because an exit code
cannot distinguish "examined nothing" from "examined something and was happy".
That is §2.1 item 5, and it is closed.

---

## 2. `ci/` steps

Status is from running each script on this tree. "Gated" means: reachable from
`ci/check.sh`, which is the only aggregator — and which, before this branch, had
no floor on its own step list.

| script | checks | status | in `ci/check.sh`? |
| --- | --- | --- | --- |
| `check.sh` | the aggregator: 26 steps | driver | — |
| `check-boundary.sh` | kernel trusted-boundary rules 0–7, R6′, member coverage | **OK** | yes |
| `test-boundary.sh` | that `check-boundary.sh` can fail (~50 cells) | **was RED (2)** → OK, §3.3 | yes |
| `check-mini-scope.sh` | R6′ for `checker/src/mini` (60 files scanned) | **OK** | yes (+ self-test) |
| `check-mutual-blackbox.sh` | the two encoders name nothing on the evidence side | **OK** | yes |
| `check-test-guards.sh` | no test hand-rolls a silent skip (60 call sites, per directory) | **OK** | yes (+ self-test) |
| `check-test-inputs.sh` | the feature matrix covers every declared feature | **OK** | yes (+ self-test) |
| `check-uplift.sh` | `[profile.dev]` and `[profile.test]` uplift one inode | not run here (cargo) | yes (+ self-test) |
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

1. **`ci/check.sh`'s own step list** — 29 steps at the time, each judged
   individually, and nothing counting them. Deleting a `step` line left "all
   checks passed". *Fixed on this branch (§3.1).* The list is **26** today:
   `d746251` dropped four `step` lines — `tests (tg backend)`,
   `tests (cross-engine core)`, `tests (rest, feature-inert)` and the
   `feature-inert guard` — and added one, `tests (rest)` over
   `--workspace --exclude nanoda_lib`. Net 29 → 26 (§4).
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
   continue`. Three scan directories, one aggregate `MIN_SITES=1`. All **60**
   sites are in `checker/tests`; `derived/tests` and `kernel/tests` contribute
   zero and their disappearance was invisible. **Fixed** (task #169 sweep): a
   configured scan directory that is **absent** is now a failure, and the
   per-directory counts are printed, so a tree that stopped being scanned reads
   differently from one that correctly has nothing to guard. Deliberately *not*
   a per-directory floor — `derived/tests` and `kernel/tests` have no optional
   inputs, so zero is their permanent and correct answer and flooring them would
   demand a guard that should not exist. Measured against master's copy: with
   `kernel/tests` renamed away it exited 0, printing `skip guards OK (60 call
   sites)`; it now exits 1 naming the directory.
5. **`ci/check-test-inputs.sh`** — three matrix legs incrementing one shared
   `matrix` counter, floored once at the end. A leg iterating zero times is
   hidden by the other two. **Fixed** at `cbb949f` (task #169): `mA`/`mB`/`mC`
   report separately, the floor moved to *members examined* (equivalent to the
   old `matrix == 0`, since every member lands in leg A or leg B), and leg C —
   whose input set is empty — prints `INAPPLICABLE` rather than counting zero
   into a total the other two legs also feed. See §1.2.
6. **`ci/test-boundary.sh`** — ~50 cells, no cell counter. Deleting cells is
   invisible. **Open.** (This is not theoretical: §3.3 is a cell that had
   stopped being able to fail.)

---

## 3. The reds, and what each one actually is

Four suites were red when this section was written. **All are now attributed
and resolved, and a fifth red — `mini_tutorial` — was found afterwards and is
recorded in §3.6.** The original entry read: *"Only one of the four is in the
improvement direction, which is not what the tranche brief predicted."* That
held for the ratchets; for the crossing assertions it did not, and §3.2 now
carries their attribution.

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
(075 = 3, 116 = 10, 081 = 1). **`tg_tutorial` was 35/35 when this was written and
is 36/36 today** (§1) — the suite gained a test, not a ratchet movement.

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
nothing may cross", and that sentence is now false.

**Attributed and re-based 2026-08-15**, on `joachim/red-suites`. All three move
at **one commit**, measured by building the suite at each commit of the
mini-unification block and reading the `cross` row it prints:

| commit | `034` adopted / declined / defeq / converged | `084` adopted / declined |
| --- | --- | --- |
| `4e86d46~1`, `4e86d46`, `8815abb` | 0 / 3 / 0 / 0 | 0 / 13 |
| **`18212fc`** *(checker: consume mini Nat certificates in TG)* | **3 / 0 / 1 / 1** | **9 / 4** |
| `02ab90f` … master | 3 / 0 / 1 / 1 | 9 / 4 |

The routed cell moves at the same commit: `8815abb` reads 1 declined / 0
adopted under `Split`, `18212fc` reads 0 / 1. §5 item 3's suspicion of this
block was right, and the two commits it had already refuted are both far later.

`18212fc` **declared the effect when it landed**, on a different fixture:
ENV-UNIFY.md B6 records `nat_char_equations.ndjson` at "mini typings adopted by
TG **0 → 15**, declined typings **16 → 3**" as TG stopped minting a second Nat
carrier and began reading mini's entries. Nobody re-ran these two suites, so
the pins outlived the change by 67 commits — which is the §5 item 7 finding
again, not a new one.

**A fourth assertion was stale behind the first**, and is the §6.1 pattern in
this very file: `034`'s `adoptedByCheckerDefeq = 0` reads **1**, and it never
ran because the line above it failed first. Its `converged` went 0 → 1 with no
decline beside it, so unlike the typing counters that offer is *new* rather
than re-decided — a weakened guard moves declines into adoptions, and there was
no decline there to move.

**And two mutations that were expected to bite do not.** Loosening the
statement guard — the failure these cells are named for — was applied twice
(accepting any offer at the `ty_const` read; making the obligation read's
`find` never locate the asked-for statement) and **both leave every test
green**. The fixtures offer at most one slot per key, so "pick the one whose
conclusion was asked for" and "pick the first" select the same certificate:
§6.1's fourth gate, a degenerate instantiation. The old comment's claim that a
loosened `has_type_const` "shows" on `084` was measured when `084` had 13
declines; the 9 that converged took the discriminating population with them.
Recorded at the assertion as a stated gap.

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
named with it.

**Superseded 2026-08-15, and the fix above is gone with the problem.** That
repair was a `cfg(feature = "tg")` on `run_unified` and its two callers — i.e. it
made two tests *absent* in the plain build on purpose, which is the third shape
of "skip is not pass" from §1.2 traded for the second. Retiring the `Certifier`
trait left one backend, the feature had nothing to select and was deleted
(`d746251`), and with one build configuration there is no plain/`tg` split for a
test to be red in. `mini_designed.rs` is **35/35, unconditional**. A count of the
form "32/32 plain, 34/34 `tg`" now names two configurations that do not exist,
and a ratchet phrased against a dead feature is itself an instance of §6 — which
is why it is corrected here rather than carried as history.

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

### 3.6 The fifth red, found after this document was written

**`mini_tutorial::tutorial_conversion_split`** — `moved` read **2914** against
a pin of **3461**, stale in the improvement direction. It is the third suite in
one week to be found red *outside* the gate list, and the one that made the
gate-list fix structural rather than another entry.

**Attributed to `d263be2` "checker: syntactic equality before reduction"**, one
commit, measured by building at its parent and at it and running the test's own
measurement over the 91 tutorial exports:

| commit | `moved` | `movedSealed` | `proved` | `gapped` |
| --- | ---: | ---: | ---: | ---: |
| `02581e4` *(parent)* | 3461 | 915 | 797 044 | 0 |
| **`d263be2`** | **2914** | **638** | **156 062** | 0 |

`d263be2`'s numbers are master's to the unit, so nothing in the 286 first-parent
commits after it touches this row. Three pins moved: 3461 → 2914, 2546 → 2276,
915 → 638, each with the trade written at the assertion.

**The trade.** A pointer-equality check now sits at the top of `def_eq_ev`,
ahead of proof irrelevance, literals and `whnf_conv`; a pair that is one
expression twice used to be normalised on *both* sides to discover it, and
those two `whnf` legs genuinely move, so they were counted. 640 982 conversions
stop being proved and only **547** were non-trivial — **99.91 % of the fall is
reflexivity**, which is the one thing the shortcut can prove and cannot fire on
a differing pair. `gapped` is still 0 and the whole corpus still certifies. The
favourable side is the commit's own: `init-prelude`'s certified prefix went
44 → 152 and the file ACCEPTS.

**One row rose**: `072_sortElimProp2Rec`'s `movedSealed` 1 → 4 with `moved`
flat. That is a tightening and cannot be a bookkeeping artefact — `free` reads
`Thm::hyps()`, the kernel's own list, and a hypothesis cannot be dropped
without a discharge rule.

**Why it went unobserved is the finding.** `d263be2`'s message reports
*"Gates 6/6, 34/34, 35/35, 251/251, boundary OK"*. The author **ran the gate
list**. `mini_tutorial` was not on it. Nothing was skipped and nothing was
ignored; an enumerated list is a hand-maintained copy of the target list, and a
copy drifts. That is why the fix in `CLAUDE-HANDOFF.md` is to stop enumerating.

**A §6 instance found in passing**: `assert_eq!(g("movedSealed"), 638)` is
**unfalsifiable**. With `moved` and `moved − movedSealed` both pinned it
follows by arithmetic, and the mutation aimed at it (bumping `moved_sealed` on
`moved` rather than `moved && free`) died at the difference assertion instead.
Its status is written at the line. The same shape holds for the two `declined`
constants in §3.2's cells.

## 4. Task #122: the three builds

**The premise as stated is no longer true.** `ci/check.sh` does not build the
workspace three times: the three feature runs are `-p nanoda_lib`, and
`kernel`/`derived` are built once and shared. Verified — after building
`nanoda_lib` under all three feature sets, `cargo build --workspace --exclude
nanoda_lib --all-targets` finishes in 0.02 s.

**And the rest of this section is now history, not status.** It was written when
there were three feature configurations; there are **two**, and the one it
argues hardest to keep is the one that was deleted. `tg` is gone with the
`Certifier` trait (`d746251`) — see §1 and §1.2 — so `nanoda_lib` is compiled
twice, plain and `--features stepcount`. The measurements are kept because the
*shape* of the argument is still the live one for `stepcount`, and because the
row that no longer exists is what makes the cost of a configuration concrete.

Measured 2026-08-15 (before the deletion) on this tree, rebuilding after
`touch checker/src/lib.rs`, at `CARGO_BUILD_JOBS=6`:

| configuration | `instructions:u` | `task-clock` |
| --- | ---: | ---: |
| plain | 1.384 T | 187.9 s |
| `--features stepcount` | 1.414 T | 195.0 s |
| ~~`--features tg`~~ *(deleted at `d746251`)* | 1.605 T | 220.0 s |
| **total, as it then was** | **4.403 T** | **602.9 s** |

Both counters are reported because `instructions:u` was measured this week to
understate allocation-shaped effects by 9–17 points; here they agree on the
ordering and on `tg` being the expensive one (+16 % instructions, +17 %
task-clock over plain).

**"Not fixed, and it should not be" — and then it was fixed, by deletion.** The
argument here was that a configuration is coverage rather than waste, and that
§3.4 demonstrated the plain build catching what `tg` did not. That was a good
argument for keeping a *split*, and it was answered by removing the reason there
was one: the feature selected `certify::Backend` between `NullCertifier` and the
real backend, and once the trait was retired it selected nothing. A
configuration that cannot vary any code is not coverage. `stepcount` still is —
it genuinely changes `cfg` — so the remaining two are two.

The duplication recorded here as "the one genuine duplication" is also gone: the
step `tests (cross-engine core)` re-ran `mini_envshare_tg`, `mini_route_tg` and
`unified_cli` for about **15.8 s**, and its stated purpose was to name those
files so `ci/check-test-inputs.sh` could verify a `cfg(feature)` suite is
selected by a step. With no `cfg(feature)` suites left there is nothing to
verify; `d746251` removed the step (29 → 26 in `ci/check.sh`), which is why
leg C now has no subject (§1.2).

**The general lesson, and it is §6's:** every claim in this section was true when
written and none of it was re-checked, because nothing reads it. A section that
argues for keeping a configuration outlives the configuration.

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
   `check-test-inputs.sh` has acquired a second, sharper form of the same
   problem since: its leg C now has **zero** subjects (§1.2).
1b. **`paired_subterm_lam_divergence` (`mini_route.rs`) carries a bare
   `#[ignore]` with no reason anywhere in its 60-line header.** An ignored test
   is *absent*, not skipped, and one with no reason is indistinguishable from
   an abandoned one. The other four ignored tests in the tree all state a cost;
   only the two in `mini_nested` put it in the `#[ignore]` attribute, where a
   test listing shows it. **None of the five has been run recently and whether
   they still pass is unknown** — that is the honest status, and the
   `mini_nested` pair cannot be run casually (33 min / 12 GB and 26 min /
   7.5 GB by their own attributes).
1c. **Six stale test-path references in `checker/src/`** — `lam_store.rs` (3),
   `routed.rs`, `const_store.rs`, `interp.rs`, `tg.rs` — all naming
   `mini/tests/…` paths removed at `4e86d46`, and now one degree staler after
   the `_tg` rename. That file set is another seat's surface, so they are
   reported here rather than fixed.
2. ~~The two adverse ratchets~~ — **resolved 2026-08-15** (§3.5). Both are
   population changes, both re-based with the trade written, both totals
   tightened, and a per-row ledger guard added.
3. ~~The three stale crossing assertions~~ — **resolved 2026-08-15** (§3.2).
   All three, plus a fourth that was shadowed behind them, move at **`18212fc`**
   alone. This entry's instinct was right: it named the block
   `4e86d46`…`02ab90f` as the remaining suspects and the answer is the third
   commit in it. The two candidates it had already refuted (`a29aad9`,
   `887fa10`) are both far later, and the reason §3.5's ledger diff could not
   see it — these are counters on the **unified** checker, and §3.5's numbers
   are all `nanoda_bin`'s — was also right, and is why the measurement had to
   be taken by building the suite itself at each commit.
4. ~~The `076_listRecReduction` budget~~ — **resolved 2026-08-15** (§3.2), two
   tranches, both attributed, re-based 31 → 9 with the derivation written.
6. **The shadowed-assertion audit** (§4.5) — the rule is written and its four
   instances are named, but **the tree has not been swept for others**. A
   separate seat owns that; this entry exists so the sweep is not mistaken for
   done.
7. ~~The gate list is the real finding, and it is not fixed.~~ — **fixed
   2026-08-15**, and not by adding entries. Three suites outside the list went
   red in one week and each time the remedy was to add the missing one, so the
   remedy was changed: the per-commit gate is now `cargo test -p nanoda_lib`,
   unnarrowed, which runs the lib's unit tests and all 14 integration targets
   and **cannot omit a suite by construction**. Two facts made it possible —
   one build configuration since `d746251`, and the package running in 171.8 s
   once §1.1's 175 s claim was re-measured at 17.2 s. `ci/check.sh` remains the
   merge gate; it needed no widening, which was checked rather than assumed
   (its steps 24 and 26 are both bare `-p nanoda_lib` runs). See
   `CLAUDE-HANDOFF.md`, "The gate list".
6. ~~**Shadowed assertions (§6), the unfixed remainder.**~~ — **resolved
   2026-08-15** on `joachim/shadowed-residue`; see §6.4 for the measurements.
   `origin_report()`'s early return is gone, the `if asked > 0` report gates hang
   off the seam publication instead, and `escaped_count` is pinned per fixture at
   `028` 0 / `029` 0 / `075` 3. **One lead in the old entry was not taken**, and
   it is still worth taking: `escapes::report_from` recomputes the escape total
   from the `made`/`taken`/`closed` census rather than from the counter, so
   asserting the gap row against *that* would make the ledger-balance check an
   independent observation instead of one number read twice. Pinning the count
   per fixture makes the test behavioural without it — a mutation leaking an
   assumption now fails — so this would strengthen a passing test rather than
   fix a broken one, which is why it was left. It is the right next step for
   this test if anyone returns to it.
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
| **10** | **the identical predicate** | **`checker/tests/tg_tutorial.rs`** | **`assert!(fired >= 92)` written **twice**, fourteen lines apart, on an unchanged local — once blaming the dependent arm, once the degenerate arm. The second could never execute a failing branch, and the "the degenerate arm stole a general site" story had no assertion of its own. Needs no mutation: an identical predicate on an unchanged local is shadowed by inspection. Folded into one assertion carrying both stories** |
| **11** | **vacuous fixture** | **`checker/src/tests/util.rs`** | **`hash_test0` ran **20 000 iterations of `None == None`**. Its config sets `nat_extension: false` and `string_extension: false`; both `mk_*_lit_quick` open with `if !…extension { return None }`, and the test does not unwrap. No mutation to hash-consing, `Ptr::get_hash` or literal allocation could fail it. Fixed with a config that has the extensions on, **plus an `is_some()` guard so the test fails rather than passes if a default ever moves back*** |

Instance 7 carries a trap worth keeping: `assert_ne!(is_opair(p,a,b),
is_opair(p,b,a))` is **not** a fix. `is_upair` is symmetric in meaning but not
in syntax, so the two descriptions differ structurally under the swapped rule
too and that assertion stays green. Only rebuilding from the constructors
separates them.

### 6.4 What was fixed, and what was reported instead

Fixed on this branch — instances **6–11**, five of the six with a separating
mutation watched red and restored (`kernel/tests/henkin.rs`, `kernel/tests/rules.rs`,
`checker/src/tests/level.rs`, `checker/tests/mini_dump.rs`,
`checker/tests/tg_tutorial.rs`, `checker/src/tests/util.rs`). `kernel/`
production code is unchanged; `git diff kernel/src/` is empty and both kernel
mutations ran under a restore trap.

Instance 10 is the one case where **no mutation was run, deliberately**: two
byte-identical predicates on an unchanged local are shadowed by inspection, and
there is no separating mutation to look for. That is the strongest form of the
finding, not a gap in the evidence.

Instance 11's fix has a second half worth copying. The vacuity was not a
mistake in the assertions — they are fine — but in the *fixture*, and a fixture
can drift back. So the test now asserts `is_some()` before comparing, and fails
at the point it would go vacuous. That is `ci/skip-guard.rs`'s rule ("a check
that examined nothing reports success") applied one level in: to an assertion
rather than to an input.

**Reported rather than fixed — all three now fixed**, on `joachim/shadowed-residue`
(2026-08-15), branched from master `4c6426a`. Kept here with what each one
actually cost, because two of the three turned out to be worse than reported.

> **Sequencing — resolved, and every entry below is closed on master.** The
> `tg.rs` half of this (commit `57bfb8c`, instance 2 and the `asked > 0` gates)
> was parked behind the `joachim/retire-certifier` refactor, which rewrites
> `impl Certifier for TgBackend` wholesale, and the open question was whether it
> would survive the rebase. **It did.** Verified 2026-08-15: `git merge-base
> --is-ancestor 57bfb8c master` succeeds, and the code says so directly —
> `origin_report` (`tg.rs:24604`) has no early return, gating only the table it
> computes from `ORIGINS` with `if !v.is_empty()`; `ix_readiness_report`
> (`tg.rs:24511`) hangs `ICOD`/`IDEP`/`PRE` off `IX_PUBLISHED`, with the reason
> written at the line and citing this section. Nothing here needs re-doing, and
> **no seat should be briefed from these entries as open work** — that mistake
> was made once, on 2026-08-15, from a task list rather than from the tree.

* **Instance 2's residue — fixed.** `origin_report()`'s early return is gone.
  The gate is drawn at the one block that is genuinely about origins: the table
  computed *from* `ORIGINS` (`own`/`relayed`/`SUBTREE`, its `TOTAL`, its `MULTI`
  line), which an empty ledger makes genuinely empty. Every other block reads a
  counter incremented at a site that does not decide whether an origin is
  recorded, and each already carried its own `> 0` guard, so they are emitted
  whatever the ledger says. **The report above understated it.** It reads as a
  hazard that needs `NANODA_ASSUME` to bite; measured, it was biting at
  baseline. `mutual_aux_encoding` and `ctor_abbrev_major` — the two fixtures
  that exercise the indexed ι rule — both leave `ORIGINS` **empty**, so `indexed
  iota rule REACHED` and the whole index-expression census were invisible on
  precisely the two inputs that produce them, with no environment variable
  involved. They print again: census `asked 9, typed 9` and `asked 2, typed 2`.
  Still a measurement hazard and not a test one — every rescued row is
  `stepcount`-gated, so a build without that feature emits byte-identical text
  and **no gate in §2 can observe this half**. (Written as "a plain
  `--features tg` build"; that feature is gone, and the sentence was always
  about `stepcount` being off, which is the default.) It was verified by direct
  measurement instead, and that is the honest status: adding a `stepcount`-only
  test would have been a check outside the gate list, which is the disease at
  the top of this document.
* **The `asked > 0` guards — fixed**, by changing the gate as this entry said it
  would need. `ix_readiness_report`'s `ICOD`/`IDEP`/`PRE` rows now hang off the
  *seam publication* (`IX_PUBLISHED`) rather than off each row's own count, so
  "mini handed us indexed evidence and the consumer never asked for `ICOD`"
  prints as `asked 0` instead of as silence — which is the observation that
  block's own doc comment was written for. Separated and watched in **both**
  directions, which is what makes the shadow a measurement rather than a
  reading:

  | mutation | pre-fix death | post-fix death |
  | --- | --- | --- |
  | zero `ICOD_ASKED` | `mini_designed.rs:3138`, "no ICOD readiness row" | `:3147`, "ICOD was never asked for: … asked 0, discharged 2" |
  | zero `IDEP_ASKED` | `:3160`, "no IDEP readiness row" | `:3167`, "… asked 0, declarations complete 8" |

  `PRE`'s `pn[0] > 0` was **not** shadowed and was left alone: its gate is
  `IDEP_ASKED`, its value is `PRE_DONE`, and the two are independent. The
  original entry was right to name only `ICOD` and `IDEP`.
* **`escaped_assumptions_are_reported_as_gaps` — fixed**, and the diagnosis
  above is confirmed exactly: `global_report` computes `let escapes = escaped()`
  once (`tg.rs:26801`) and prints it as the gap row, as a term of the `TOTAL
  gaps` sum, and as the `… {} escaped` field. Measured, then pinned per fixture:

  | file | escaped | conditional derivations |
  | --- | --- | --- |
  | `028_peano2` | **0** | 20 made, 20 accounted for by a rule |
  | `029_peano3` | **0** | 48 made, 48 accounted for |
  | `075_nRecReduction` | **3** | 95 made, 92 accounted for |

  Separating mutation, watched: `consume` skipping `note_consumed()` when
  `hyps.len() == 1` leaks exactly one assumption to the boundary on
  `028_peano2`. **The old test passed under it — run, green, 1/1** — and the new
  one dies at `tg_tutorial.rs:742` reading `left: 1  right: 0`. That is the
  tautology demonstrated rather than argued.

  **And the header this entry proposed to assert was itself wrong.** It said
  *"`028` discharges every one of its conditional derivations, `029` leaves one
  over"*. `029` leaves **nothing** over; the file with a residue is `075`, at 3.
  Had the values been guessed from the header rather than measured, the new
  ratchet would have been wrong on landing — which is the whole reason this
  entry refused to guess them, and the reason it was right to refuse. The two
  ledger-balance assertions are kept, with their honest status written at the
  line: they separate a *reporting* regression (row dropped, renamed, or left
  out of the sum, read back through three independent subprocess runs), which is
  a different subject from the one the test is named for.

Also corrected while there, being the same disease one file over: the row
`indexed iota rule REACHED at a use site, **premise outstanding**` was renamed
`… before its premise`. `IX_FIRE` is bumped where the rule instantiates, ahead
of any premise work, so the old label named an event it does not count — §4.5
instance 3 — and it sat directly beneath a `PRE … discharged` row carrying the
same number.

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

Of those 687, **six were confirmed and fixed** (five by mutation, one — instance
10 — by inspection, which is what an identical predicate admits), and one
candidate —
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

---

### 6.8 Re-audit against master — 2026-08-15

*Measured at `4a2910d`; findings 16 and 17 re-checked at `5964977`, master having
moved during the pass. Which of those two states a claim was taken in is noted
wherever it matters, because "master" is not a fixed thing over a day's work —
that is the same defect this section is about, one level up.*

**Why this section exists.** Twice on 2026-08-15 a seat was briefed from a task
entry describing work that had already landed: once on §6.4's `escaped_count`
item (fixed hours earlier at `25d9229`), once on instance 2 and the `asked > 0`
gates (fixed at `57bfb8c`, and on master). A task entry is a claim about the
past. **The base rate matters more than any one entry**, so it is recorded here.

### Closed since the original audit — four of four, verified in the tree

| entry | verified how | status |
| --- | --- | --- |
| §6.4 instance 2, `origin_report()`'s early return | `tg.rs:24604` gates only the `ORIGINS` table with `if !v.is_empty()` | **closed** |
| §6.4 the `asked > 0` guards | `tg.rs:24511` hangs `ICOD`/`IDEP`/`PRE` off `IX_PUBLISHED`; the reason is written at the line | **closed** |
| §6.4 `escaped_assumptions_are_reported_as_gaps` | pinned per fixture at `tg_tutorial.rs:742`; both pins perturbed and watched red | **closed** |
| §2.1 items 4 and 5, the two aggregate CI floors | both fixed; see those entries | **closed** |

The `57bfb8c` rebase question §6.4 left open — whether the fix would survive
`joachim/retire-certifier` rewriting `impl Certifier for TgBackend` wholesale —
is answered: `git merge-base --is-ancestor 57bfb8c master` succeeds.

**Strengthened past what the fixing commit claimed.** Reading the report off
`nanoda_bin` directly rather than through `escaped_count` — a second path, which
is the whole point — shows `028_peano2` at *20 made, 20 accounted for* and
`029_peano3` at *48 made, 48 accounted for*, so those two zeros are
**structurally forced** rather than an accident of the tree; and on
`075_nRecReduction`, `TOTAL gaps == escaped == 3`, so the escapes are that
file's **entire** gap population rather than a term in a sum where another
category could mask movement.

### The error rate is in the tracking, not in the findings

**Stated precisely, because this section is about not overclaiming.** This pass
did *not* re-derive instances 1–11 from scratch; each was fixed with a watched
mutation when it landed, and re-running eleven mutations was not the ask. What
was checked is narrower and is what the briefs got wrong: **the four entries
being tracked as open work, all four of which are closed** (table above), each
verified against the tree rather than against a task list. No finding was
refuted; §6.5 already records the one inference the audit itself refuted (the
"protected by exactly two integers" claim, not the shadowing under it).

So the measured error rate for 2026-08-15 is **2 of 2 task entries briefed as
open were already closed**, and **0 of the audit's findings were wrong**. Those
are different populations and conflating them is how the second brief got
written. The remediation is not more auditing — it is that a brief cites a
commit or a line, never a task entry.

### New: deleted configuration is where this class breeds

`d746251` retired the `tg` feature and one backend; `ad381f3` retired the
`Certifier` trait. Both landed after the original audit, and **an assertion or
a documented count that used to discriminate two configurations discriminates
nothing once there is one.** Swept for that shape; the live instances are below.
Ownership is noted because most of them are in files held by other seats.

| # | where | what is now false | owner |
| --- | --- | --- | --- |
| 12 | `checker/tests/mini_designed.rs:3237-3252`, `run_unified`'s header | Four independent false claims. It says the suite is *"32/34 under `--no-default-features` and 34/34 under `--features tg`"*, that the spawned binary *"refuses the unified route without it"*, that `ci/check.sh` runs `--features tg`, and that the two tests are *"removed only from the configuration in which they cannot mean anything"*. **Measured: no `cfg(feature)` remains in the file, the refusal string is absent from `checker/src/bin/checker.rs`, and the suite is 35/35 unconditional.** This is the canonical form — a test-count ratchet naming a dead feature. | free |
| 13 | `checker/tests/mini_route.rs:445` | The documented reproduction command for an `#[ignore]`d measurement is `cargo test -p nanoda_lib --features tg skeleton_key_divergence -- --ignored`. **Measured: `error: the package 'nanoda_lib' does not contain this feature: tg`.** Because the test is ignored, that line is the *only* path to the measurement, so the measurement is unreachable as documented. | free |
| 14 | `checker/src/tg.rs`, 11 doc blocks (`:22217`, `:22618`, `:22963`, `:23203`, `:23376`, `:23459`, `:23523`, `:23601`, `:23630`, `:23950`, `:27398`) | Counted directly, and `grep -rn 'trait Certifier' checker/src kernel/src` returns nothing, so every one of them describes a default of a trait that does not exist. `ad381f3` moved each rule's contract onto `TgBackend` and rewrote the intra-doc links, but not the sentences around them. They describe *default implementations* on a type that has none — e.g. `:23206` *"The default implementation delegates to [`TgBackend::admit`], so a backend that has nothing to say about iota keeps reporting a gap"*, contradicted by `certify.rs:298-302` (*"the `Certifier` trait's default implementation of `iota` … both are gone"*). Consequence beyond tidiness: these paragraphs promise a safe do-nothing floor that was deleted. Also `:27398`, a comment describing a `feature = "tg"` gate on the line that introduces `#[cfg(test)]` — the whole of that commit's diff to the file was removing that gate. | **unification seat** |
| 15 | `checker/src/tc.rs:1039` | *"Under the null backend every call here is a no-op, so it still pays nothing."* The null backend is gone; the call reaches `TgBackend::app_arg_checked`, which inserts into `arg_gapped`. The cost argument justifying an unconditional call rests on a deleted premise. | **unification seat** |
| 16 | ~~`kernel/Cargo.toml:17-23`~~ **fixed at `09ef335`**; `kernel/README.md:427` **still open** | The TCB's own soundness argument cited a live enforcement mechanism that no longer exists: *"`NullCertifier` sits in `checker/src/certify.rs` behind `cfg(not(feature = "tg"))`, so a `--features tg` build does not compile it at all."* The manifest half was corrected by its owner while this re-audit was running. **But `09ef335`'s own scope claim — *"the only live `cfg(not(feature = "tg"))` reference left in the tree — grep finds no other outside past-tense prose"* — is false**: `kernel/README.md:427` (*"it is compiled under `cfg(not(feature = "tg"))`"*) and `DECISIONS.md:1852` (*"so `--features tg`, which CI runs, contains no null…"*) are both present tense and both live. A fix that states its own coverage is right to; this one measured it over `.toml`/`.rs` and not over the prose that carries the same claim. | **`kernel/` — stop-and-report**; `DECISIONS.md` free |
| 17 | `checker/Cargo.toml:14`, `kernel/src/lib.rs:31-37` | Both describe the trusted boundary as *"the `Certifier` proof-backend trait and its null implementation"*. Re-checked against master `5964977`: both still stale. `certify.rs:14-17` already states the replacement correctly; these two are what should point at it. | manifest free; `kernel/` stop-and-report |
| 18 | `README.md:178` | *"With `--features tg`, **69 of 91** tutorial exports check…"* — the only surviving `tg`-feature instruction to a user. | free |
| 19 | `DOC-AUDIT.md:712` | *"Verified **true today**, and worth keeping as do-not-re-verify: `Certifier::iota` is still exactly `checker/src/certify.rs:174`"*. The worst form in the set: it instructs a future auditor to skip the check that would have caught it. | free |

Corrected in this pass, in place: §1's per-target counts and total, §2's step and
call-site counts, §2.1 items 4 and 5, §1.2's leg C paragraph, §3.4's
`32/32 plain, 34/34 tg`, §4 in full, and §6.4's sequencing note.

### One asymmetry the sweep found and did not close

`ci/check-test-inputs.sh` leg A walks *declared feature → step that runs it*.
There is **no inverse leg** — a step naming a feature no member declares — so a
resurrected `--features tg` line would not be caught statically. In practice
cargo hard-errors on an undeclared feature (measured above) and `ci/check.sh`'s
`step` wrapper turns that into a failure, so the hole is covered at runtime by
something louder than the grep. Recorded rather than fixed: adding a leg whose
only failure mode cargo already reports more clearly would be ceremony.

### 6.9 The general sweep — 2026-08-15, and what it is worth

The §6.8 pass swept *deleted configuration*. This is the other axis: assertions
that cannot fail on their own subject. It was run as a delegated sweep and then
**partly re-verified by hand**, and the two statuses are kept apart on purpose —
a sweep is a hypothesis, and this document's whole subject is what happens when
one is recorded as a result.

#### Verified first-hand, by direct measurement — seven

| # | site | measured |
| --- | --- | --- |
| **20** | `checker/tests/mini_designed.rs:2269` and `:2342` | `!text.split_whitespace().any(\|w\| w == "Nat" \|\| w == "PProd")` over a raw `.ndjson`. **An export line is one unbroken JSON object: measured, `proj_stuck_subject.ndjson` is 432 lines and 432 whitespace tokens, `proj_reduced_carrier.ndjson` 612 and 612.** `split_whitespace()` therefore yields whole lines and no token can ever equal `Nat` or `PProd`. Both guards are unfalsifiable whatever the fixture contains. **And the correct form would not merely pass:** `proj_reduced_carrier.ndjson` contains `PProd` once today (`Nat` zero times, so its own `Nat`-only assertion is substantively true). Rewriting these as substring checks is the fix, and whether that file is *meant* to be `PProd`-free is a question for its author — which is exactly the question a working assertion would have forced years earlier. |
| **21** | `checker/tests/mini_tutorial.rs:2076` | `k.starts_with("waiting:indexed-family(") && !k.contains(':')`. The prefix **itself contains `:` at index 7**, so the conjunction is unsatisfiable for any key whatsoever. Dead a second time over: the sole producer (`mini/ledger.rs:584`) is `format!("indexed-family({n}: {w})")`, a two-field variant that always interpolates a colon, so the bare spelling the comment says "must not come back" has no constructor to come back through. |
| **22** | `checker/tests/mini_tutorial.rs:2156-2158`, asserted at `:2160` | Three rows pinned at key `waiting:recursor(X: class (S) eliminator)`. `grep '"class (S) eliminator"' checker/src` returns **nothing** — every producer carries a `: <detail>` suffix (`rec_prop.rs:172,182,184,232,233,…`). The lookup is exact-key, so the key can never be present; and since `note_missing` is `+= 1`, no key can ever hold 0, so `unwrap_or(0) == 0` *is* "absent" — the statement the comment four lines up explicitly says it is not. |
| **23** | `checker/tests/tg_tutorial.rs:3002` | `assert_eq!(population, scheduled - skipped)`. `tg.rs:26516-26517` is `let (scheduled, skipped) = (st.pairs, st.skipped_pairs); let population = scheduled.saturating_sub(skipped);` — one line apart. The test re-derives the producer's own arithmetic. The two assertions above it (`reached + collapsed == scheduled`, `eligible == seen`) read counters bumped at different sites and **are** live; only this one is an identity. |
| **24** | `derived/tests/genrec.rs:1565` | `let (values, target) = ind.fibre_at(&mach, &qs); assert_eq!(target, target_of(&s, &values))`. `carrier.rs:747-748` computes `target` as `target_of(s, &values)` and returns both — so this is `f(x) == f(x)`. The comment above it says the codomain is *"rebuilt here from the telescopes rather than read back"*; it is not, `values` is `fibre_at`'s own output. A genuine rebuild is available — `fibre_summands_at` is public and is what the producer itself calls. |
| **25** | `checker/tests/mini_tutorial.rs:3231-3243` | A loop pinning six binder-congruence labels absent. **Three of the six have no producer.** `BinderRule::tag()` (`mini/ev.rs:81-91`) has range `dprod_ext_n`, `cond_ext_n`, `lam_ext_n`, and `format!("clauses differ: {} vs {}")` over `BinderClause` — which is a **two-variant** enum tagging exactly `dprod` and `cond` (`ev.rs:63-76`). So `fs_cong`, `clauses differ: dprod vs fs` and `fs vs dprod` can never be emitted; `fs_cong` is not a `BinderRule` at all but a derived prelude theorem, and `grep fs_cong checker/src/mini/` is empty. Doubly dead: the loop sits under `assert_eq!(reasons, expected)` at `:3225` with `expected` an **empty** map, so no iteration can reach a failing branch regardless. |
| **26** | `checker/src/tests/util.rs:82-89` | `check_empty` loops `for declar in export.declars.values()`. The fixture is `checker/test_resources/Empty/export`, **176 bytes and zero newlines** — the header object and nothing else — so `declars` is empty and `check_declar` is never called. No mutation to declaration checking can fail it. Same disease and same file as the already-fixed `hash_test0` `None == None`. |

#### Reported by the sweep, **not** individually re-verified — recorded as candidates

Roughly thirty more, in three groups. They are written down because the sweep
traced a data path for each and its six verified calls were all correct, but
**none of the below has been measured by a second reader** and none should be
acted on without one.

* **Earlier-gate cases** (an assertion unreachable under any mutation that would
  trip it): `mini_designed.rs:1805` and `:2163`; `mini_dump.rs:641`;
  `mini_tutorial.rs:1721`, `:2069`, `:2094`, `:2132`, `:2555`;
  `mini_infinitary.rs:200`.
* **A systemic cluster in `derived/tests` and `kernel/tests`** — this is the
  one worth a pass of its own. The idiom is building premises from `eq_refl` /
  `imp_refl` on a *single* atom, which exercises each rule exactly where its two
  possible readings coincide: `and_elim_left`/`right` at `p ∧ p`,
  `iff_mp`/`iff_mpr` at `p ↔ p`, `hyp_or_elim` with the same theorem in both
  branch slots, `syl`/`hyp_syl` with antecedent = middle = consequent,
  `congr_arg` at `eq_refl`, `inst_all` on a body whose second binder does not
  occur. Named: `rules.rs:19,47,64`; `propositional.rs:27,84,106`;
  `hypothesis.rs:53,84`; `sets.rs:189`; `separation.rs:70`; `quantifier.rs:105`;
  `deprec.rs:696`; `kernel/tests/rules.rs:11`; `kernel/tests/hypotheses.rs:372`.
  This is §6.6 rule 3 — *two atoms cannot distinguish a swap* — at scale, and it
  is the densest known concentration of the defect in the tree.
* **Medium-confidence singles**: `derived/tests/define.rs:80` (the leg named
  *"even the existence half alone is not enough"* builds `bare_exists` and then
  discards it with `let _ = bare_exists;` — the witness actually passed is
  `⊢ ∀x. x = x`, which contains no `∃` and is refused for the same reason as the
  line above, so the `∃` vs `∃!` distinction the test is named for is untested);
  `mini_envshare_cross.rs:103` and `:679`; `mini_nested.rs:1132`;
  `mini_designed.rs:2996`; `tg_tutorial.rs:531`; `natlit.rs:263`;
  `mini_mutual.rs:292`.

**One reason the second-reader rule above is not ceremony.** The sweep was asked
twice and reported twice, and between the two reports it **moved three findings
between confidence tiers** — `define.rs:80` and `mini_envshare_cross.rs:103`/
`:679` were "medium" in one and "dead by construction" in the other. Its six
verified calls were all correct, so this is not a competence question; it is that
a confidence label assigned without a second reader is itself unmeasured. The six
in the table above are the ones two readers have now looked at.

#### Eight candidates examined and dropped — the negative result, on record

`kernel/tests/rules.rs:139` (redundant, not unguarded — `tarski.rs:99,217`
rebuilds `equinumerous` from the constructors and pins the swap);
`derived/tests/err.rs`'s `ends_with("err.rs")` family (the `#[track_caller]`
line assertion beside it catches everything they would);
`mini_designed.rs:1148`; `mini_route.rs:604` (a real tautology, but `#[ignore]`d,
documented as one at `:457`, and floored); `mini_infinitary.rs:218`;
`unified_cli.rs`'s `!contains("gap: X")` family (all four literals confirmed
producible, and `TOTAL gaps` is pinned through a reader that panics on a missing
row); `mini_dump.rs:95`; `mini_designed.rs:3377` and `:3403`. Recorded because a
refuted candidate is worth as much as a confirmed one, and because §6.5 exists
for exactly this reason.

#### Coverage, stated so it is not mistaken for completeness

Read first-hand by the sweep: **all** of `checker/tests`, `checker/src/tests`
and `kernel/tests`, plus `derived/tests`' `define`, `hypothesis`,
`propositional`, `rules`, `sets`, `separation`, `quantifier`, `genrec`,
`deprec`, `err`. **Not individually read: the bulk of `derived/tests`** — the
`family_*`, `cumul_*`, `w*`, `nat`, `ext`, `isum*`, `quot*`, `funspace`,
`inductive`, `recursion`, `rec_acc` group, roughly 45 000 lines. Mechanical
scans (duplicate assertion, textually identical arguments, `Option == Option`,
absent literal without a producer, symmetric conjunct) covered those and found
nothing beyond the above — but a mechanical scan cannot see a degenerate
instantiation, and that group is the densest user of the very idiom the cluster
above is about. **That is the next pass, and until it is run this section is a
lower bound.**

#### All seven fixed — task #174, each with its own watched falsification

| # | fix | separating mutation, watched red |
| --- | --- | --- |
| 20a | `proj_stuck_subject`: name-table read `"str":"NAME"`, plus a **positive control** — `Tri`, the structure the fixture declares, must be *present*, so the same reader that reports `Nat` absent proves itself live | look for `Tri` instead of `PProd` → red at `:2283`, "`Tri` is in this export's name table" |
| 20b | `proj_reduced_carrier`: same reader, `Nat` only, control on `PProd` | assert `PProd` absent → red at `:2370` |
| 21 | strip the prefix, then look for the separator in the *payload* | empty the prefix so every key is "bare" → red naming all seven live keys |
| 22 | the three dead lookups **deleted, not restated** | the surviving prefix guard made to match a present key → red at `:1639` |
| 23 | kept, with its status written at the line: a *reporting* check, not a behavioural one | point the `POPULATION` row lookup at a neighbouring row → red at `:3020` |
| 24 | summands rebuilt from `fibre_summands_at` at `q⃗`, one layer below `fibre_at` | `.rev()` the rebuilt summands → red at `:1584`, "`fibre_at`'s summands are not the telescopes' at q⃗" |
| 26 | emptiness **asserted**, so the fixture cannot drift into a weak `check_declar` test | point at `ProjFromProp` → red, "the Empty fixture now has 8 declaration(s)" |

Three of these are worth more than the repair.

**22 was dead *and* redundant.** The same test already carries
`!totals.keys().any(|k| k.starts_with("waiting:recursor(") && k.contains("class (S)"))`
five hundred lines earlier — prefix-based, so it matches the producible key
*with* its `: no constructors` suffix and the five other `rec_prop.rs` spellings
that the exact-key form could not reach either. So the fix is deletion, and the
first draft of it — a broader `contains` scan — was itself withdrawn as a
duplicate. Replacing a dead assertion with a live one is right; replacing it
with a second copy of a live one is not.

**25 stopped enumerating payloads.** The list named six binder-congruence labels
and three had no producer, because the payload set moved when the `Fs` clause
went and the list did not. It reads the producer's stable prefix now, which
covers every present and future rule and names the offender in the message.
*Reported, not fixed:* `mini/ev.rs:53` still documents `Mismatch` as carrying
"`Dep` against `Fs`", and `BinderClause` has had two variants — `Dep` and
`Cond` — since at least `4e86d46`. That file is owned elsewhere.

**A correction to this document's own reading, made in the same pass.** Dumping
the live key set showed seven keys and no `waiting:` ones, and the first
conclusion drawn was that `totals` is the wrong map and a dozen assertions in
`tutorial_evidence_ledger` were dead by construction. **That was wrong.**
`Ledger::row` (`mini/ledger.rs:1133`) appends `\twaiting:{k}={v}` to the *same*
tab-separated `evidence` line the test parses, so `totals` is exactly the right
map and an empty `waiting:` set means the tutorial corpus fully certifies —
which `constEv == pairs == 218` asserts two hundred lines above, and which this
file's own §1 header states outright. The error was reading an observable (the
key dump) without checking what produces it, which is this section's subject
committed by this section's author. It is recorded because the near-miss is the
evidence that the discipline has to be applied to one's own findings too.

That correction changes the *status* of every `waiting:` guard here, including
20–22: their input is empty by construction, so **no mutation to the tree can
falsify them today** — they are guards against reintroduction, exactly like
`ci/check-test-inputs.sh` leg C. The mutations above therefore prove
*reachability* — that the filter runs over a real, non-empty key set and the
assertion fires — which is the strongest available statement and is a weaker one
than "a regression would be caught". Said here so nobody reads the table as more
than it is.

### 6.10 The degenerate-premise cluster — bounded pass, task #175

§6.9 named fourteen sites where a premise is built from `eq_refl`/`imp_refl` on
a **single** atom, so the rule under test is exercised exactly where its two
readings coincide. They were recorded as candidates, not findings. This pass
verified them **mechanically** and fixed only those where the rule is
load-bearing — the test being *"would a plausible implementation error survive
this test?"*, not *"is this fixture degenerate?"* Deliberately bounded: the
remainder is recorded below and left.

#### Fixed — four, each with the swap watched red

| site | degeneracy | mutation, watched |
| --- | --- | --- |
| `derived/tests/propositional.rs::conjunction_round_trip` | `and_intro(&p, &p)` at one `Thm`, so both projections returned the same formula | call `and_elim_right` where the test says left → red, "left projection did not return the left conjunct" |
| `derived/tests/propositional.rs::biconditional_projections` | built at `p ↔ p` from two copies of `imp_refl(p)` | call `iff_mpr` for the forward half → red, "iff_mp is not the forward half" |
| `derived/tests/hypothesis.rs::iff_projections_under_hypothesis` | `p ↔ p` **and** the two assertions were the identical predicate, written twice | call `hyp_iff_mp` for the backward half → red, "hyp_iff_mpr is not the backward half" |
| `derived/tests/rules.rs::eq_symm_derives` | ran only at `f(a) = f(a)`; the comment said so outright — *"a = b with a syntactically equal to b"* | expect the unswapped equation, i.e. a no-op `symm` → red, "symm did not swap the sides" |

`iff_mp` and `iff_mpr` are `and_elim_left` and `and_elim_right` under other
names (`rules.rs:303,307`), so three of the four were one rule pair, and the
whole biconditional interface rested on a fixture that could not tell its halves
apart. Getting a biconditional backwards is the archetypal way to prove
something in the wrong direction, which is why these were taken and a
tautological count assertion in a tutorial was not.

A genuine `⊢ p ↔ q` at **distinct** atoms needs no axiom, which is what made the
fix cheap and is worth writing down: both atoms are provable, `a1i` weakens `⊢ q`
to `⊢ p → q` and `⊢ p` to `⊢ q → p`, and `Formula::iff(p, q)` is exactly the
conjunction of those two. For `eq_symm`, `Thm::assume` gives `{a = b} ⊢ a = b`
with the sides syntactically different. Two atoms suffice throughout: the
question is a **swap**, not an ordering or a nesting.

#### Refuted — the fixture is degenerate and the rule is covered anyway

Measured by mutating the *implementation* in `derived/src/rules.rs` and running
the whole `derived` suite, then restoring (`git diff derived/src/` empty).

* **`syl` — refuted.** Made to return its first premise unchanged (`a → b`
  instead of `a → c`), which the `p → p ∘ p → p` fixture cannot see:
  `derived/tests/acc.rs` fails **16 of 16** immediately. Composition is pinned,
  heavily, elsewhere.
* **`congr_arg` — refuted.** Made to ignore its equation and return reflexivity
  at the unrewritten term: failures across many suites —
  `addition_computes_at_numerals`, `addition_satisfies_the_peano_equations`,
  `iota_computes_to_the_minor_and_not_to_a_constant`,
  `applying_the_successor_graph_computes_succ` and more.
* **`congr` — refuted by construction**, not by a separate run: it is a fold of
  `congr_arg` over positions chained with `eq_trans` (`rules.rs:167-181`), so it
  is subsumed by the coverage that caught `congr_arg`. Stated from the code, and
  labelled as such rather than as a measurement.
* **`kernel/tests/rules.rs::mp_rejects_mismatched_premises` and
  `kernel/tests/hypotheses.rs`'s order-of-arrival cell — not degenerate at all.**
  Read: the first uses three *distinct* atoms `pa`/`pb`/`pc`, and the second
  asserts `t.hyps() == swapped.hyps()` over two *different* hypotheses, which is
  a real canonicalisation property. The sweep was wrong to list them. (`kernel/`
  tests are no longer stop-and-report; there was simply nothing to do.)

That is **four real, four refuted** out of the eight examined — close to the rate
§6.9 warned about, and the reason those fourteen were filed as candidates.

#### Recorded and left, with owners

`derived/tests/separation.rs::hyp_syl` (the `syl` shape under a hypothesis —
almost certainly refuted for the same reason, unmeasured), `sets.rs:189` (case
analysis at `p ∨ p`), `quantifier.rs` (`inst_all` on a body whose second binder
does not occur), `deprec.rs:696`, `hypothesis.rs::hyp_mp_works_and_rejects`. All
in unowned files. None is a rule the derivation layer leans on in the way
`and_elim`/`iff_mp` are, and each carries a companion refusal assertion.

**The 45 000-line `derived/tests` pass flagged in §6.9 is not being taken.** It
stays recorded there as a stated lower bound. If it becomes the right work the
note will still be there; the priority is end-to-end completeness — whether the
checker handles what Lean handles, and whether anything is accepted by a
shortcut rather than certified.

---

## 7. End-to-end completeness — measured against the corpus, 2026-08-15

The owner's priority is *"end-to-end completeness and no implementation
shortcuts"*, and the standing rule is that a completeness claim needs an
**external** reference. This section is that measurement: the production route
run over all 99 non-`perf` `good/` exports of the Lean Kernel Arena corpus,
every refusal collected and grouped by reason. Nothing here is inferred from a
fixture or from the gap ledger's own totals.

**Provenance, because these numbers move under active work.** First taken at
master `b91dbfd`; **re-taken in full at `203b3ff`**, after `demand-closure` and
`splicer-names` landed — `4e3b28b` in particular converts model-route debt into
declines by name, which is exactly this section's subject. All three headline
figures are **unchanged** across that rebase: the production census at 76 clean
/ 3 declined / 20 carrying debt, the TG gap census at 11 279 gaps over 26 of 99
files, and `init-prelude`'s pinned verdict and reason. Stated rather than
assumed, because the seat that moved the code was moving the very declines
counted here, and "the numbers did not shift" is only worth anything if someone
looked.

### 7.1 The finding that reframes the rest: the gate and the product are two programs

`scripts/arena.sh` — the corpus gate, and the thing that licenses "102 good, all
accepted" — drives **`target/release/nanoda_bin`** (`ARENA_BIN`, `arena.sh:57`).
The production checker is **`target/release/checker`**: its own header says so
(`bin/checker.rs:71`, *"This is the production checker — every integration suite
spawns it through `CARGO_BIN_EXE_checker` and the split dispatch is its
default"*). They are different binaries taking different routes.

Measured, on the same 99 files:

| | `nanoda_bin` (what the arena gates) | `checker` (what ships) |
| --- | ---: | ---: |
| accepted | **99** | **96** |
| declined | 0 | **3** |
| of the accepted, carrying debt (exit 4) | — | **20** |

**The production checker declines `good/init-prelude.ndjson`** — the corpus's
flagship file — at a closed gate. The arena cannot see this, because
`nanoda_bin` takes the nanoda path and accepts. So the sentence "the corpus is
fully accepted" is true of the binary the gate runs and false of the binary the
project ships, and no check in §2 could tell them apart. Now pinned, by
`corpus.rs::the_production_checker_declines_the_prelude_at_a_named_gate`.

**Which gate fires depends on `modelgen`, and the first version of this section
got that wrong.** The counts above were taken with `--no-modelgen`, because the
tool was not built on this machine — and `mini/modelgen.rs:18` says the filter
pass is **on by default**, so that was a non-default configuration. `modelgen`
was then built (`lake build`, Lean is available here) and the census re-run in
the true default: **the counts are identical — 76 clean, 3 declined, 20 carrying
debt** — and only `init-prelude`'s reason moves.

| configuration | verdict | reason |
| --- | --- | --- |
| default (`modelgen` on) | decline, exit 2 | `Mutual inductive Lean.Syntax._model.0 not supported` |
| `--no-modelgen` | decline, exit 2 | `Nested inductive Lean.Syntax not supported` |
| `--mutual` (modelgen on) | decline, exit 2 | `Nested inductive Lean.Syntax not supported` |
| `--mutual --nested` | **accept**, exit 4 | 1 822 declarations, **91 declarations and 10 eliminators untranslated**, 11 556 TG gaps |

`modelgen` splices the model in as `T._model.0 … T._model.{n−1}`, a
`mutual … end` block, so with the filter on the *mutual* gate refuses that block
before the nested declaration is reached. Both are declines at exit 2 and both
name what stopped the file. `mini_nested.rs:204-206` already asserts exactly this
two-gate ladder on designed fixtures; the new test asserts it on the real export.

**The decline is correct, and the acceptance is the wrong number.**
`MODEL-BASIS.md` states the dispatch rule as three-way and total — basis
inductives get our own clauses, a non-basis inductive with a `_model` is
recognised and cased on, and one **without** is *"decline, loudly and by name;
there is no construction to fall back to, because the construction is gone."*
Measured, `--mutual --nested` accepts the file while leaving 91 declarations and
10 eliminators untranslated and 11 556 steps gapped: an acceptance that certifies
strictly less than the decline states, reached by opening the legacy
construct-it-ourselves path the pivot exists to retire. Rule 2 is not operative
yet — `MODEL-BASIS.md` is *"a design and measurement tranche, not a build"*, and
with the model spliced in and both gates open `Lean.Syntax` is still
untranslated. The splicer seat is building that projection now, and when it lands
the intended verdict becomes an acceptance with the model consumed; the test says
so at the assertion and asks to be re-pinned rather than deleted.

### 7.2 The three categories, and how they actually partition

They do **not** partition as a completeness audit would expect, and the shape is
worth stating before the numbers.

**(a) Lean accepts, we refuse — three files, two causes.**

| file | reason | seen by |
| --- | --- | --- |
| `good/level-index-out-of-order.ndjson` | `Back-refs must be continuous` | both binaries |
| `good/sparse-name-index.ndjson` | `Back-refs must be continuous` | both binaries |
| `good/init-prelude.ndjson` | a closed gate — see §7.1 for which, and why it is the right verdict | `checker` only |

The first two are a **parser policy**: the export format nowhere requires
back-reference indices to be dense or increasing, and this parser requires both.
Both files are four and six lines of handcrafted `axiom` over a `Sort`, so
nothing about typing is involved.

**(b) We accept without certifying — this is nearly everything.** Two separate
ledgers, and both had to be read:

* *TG certificates.* **11 279 gaps across 26 of 99 files, 28 distinct reasons.**
  92 % of them (10 386) are `init-prelude`; 6.5 % (737) are the four
  `undecidability/` files; 1.4 % (156) are 21 tutorial files. The largest
  reasons are `trans over an admitted premise` (5 740), the escape ledger
  (1 278), `proj_reduce` (804), `pi congruence over an admitted body premise`
  (792) and `congruence over an admitted premise` (609). Six of the 28 are
  *shape* declines — `iota: no interpretation — a nested inductive` (100), `— a
  K-like eliminator` (7), `— an indexed family` (6), `— several constructors`
  (1) — and the source carries **ten** such labels, so four have no occurrence
  on this corpus at all.
* *Interpretation.* Even with both gates open, `init-prelude` is accepted
  carrying untranslated declarations — **89 declarations and 10 eliminators**
  with `--no-modelgen` (1 774 accepted), **91 and 10** in the default
  configuration with the model spliced in (1 822 accepted). By reason: `type
  former spine` on 31 class-like inductives (`HAdd`, `HMul`, `MonadState`, …),
  `field type uninterpretable` on ~24 (`String`, `Char`, `Fin`, `BitVec`,
  `UInt*`, `Lean.Name`, …), `parameter type uninterpretable` on 4, `class (S)
  eliminator: no constructors` on `False` and `PEmpty`, `class (S) indexed
  eliminator: a result index is not a bare field` on `HEq`, and — in the
  unfiltered case only — `Lean.Syntax: no nested model in the export`.

  This is the literal form of "an implementation shortcut wearing an
  acceptance": the file exits `accept`, and ~100 declarations inside it were
  never translated. `ledger.rs:339-345` already says so in as many words — *"an
  untranslated declaration sits in a file mini **accepted**"*. **It is also the
  reason §7.1 concludes the decline is the right verdict**: this acceptance is
  what the gates are keeping out.

  *(By-reason figures are from the `--no-modelgen` run; the default-configuration
  totals were re-measured and are two declarations higher. The breakdown was not
  re-taken by reason, and is not claimed to be.)*

**(c) Lean rejects, we reject — complete.** All 55 `bad/` files are rejected and
`scripts/arena-accept.txt` is **empty**, so there is not one known lost
rejection. This category needs nothing.

**Why they do not partition.** The design admits rather than refuses — the
documented position is that being *more permissive* than the official kernel
costs nothing while the certificate is the guarantee (`scripts/arena.sh:16-20`).
So almost nothing lands in (a): an unsupported shape becomes a *gap* on an
accepted file, not a refusal. (a) and (b) are therefore not two sizes of the
same thing; (a) is three files and (b) is the entire remaining surface, and the
useful question is not "which category" but **"which of (b) is held by an
assertion"**.

### 7.3 What is held, and what is not

| population | gaps | ratcheted by |
| --- | ---: | --- |
| `init-prelude` | 10 386 | `GAP_LEDGER`, row by row, in `tg_tutorial.rs` |
| `undecidability/` (4 files) | 737 | **nothing** — no test names these files |
| `tutorial/`, 8 files | 39 | `GAP_BUDGET` |
| `tutorial/`, 13 files | 117 | **nothing** |

**854 gaps (7.6 %) carry no assertion of any kind**, including
`077_RBTree.id_spec` at 45 — the largest single tutorial file — and
`118_accRecReduction` and `105_structEta` at 12 each.

The zero side is looser still. Measured, **70 of 91 tutorial exports have zero
gaps**; `FULLY_DERIVED` and `RECURSOR_DERIVED` together assert 28 of them. So
**42 files sit at zero with nothing holding them there**, and a regression in
any of the 42 is a silent one. (The `README.md` figure "69 of 91" is a
measurement of the same quantity and is off by one today.)

*Method, and its cross-check.* Each file was run through `nanoda_bin` with the
arena's own config, and the `gap:` rows parsed. The eight files in `GAP_BUDGET`
reproduced their pinned numbers **exactly** — 3, 9, 1, 2, 2, 10, 10, 2 — which is
what says the harness measures the same quantity the tests pin. Release and
debug agree (`077` at 45 in both).
