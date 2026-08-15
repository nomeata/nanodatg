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
is unconditional, `cargo test -p nanoda_lib` runs all fourteen, and **all 476
tests pass**. The two suffixed suites were renamed with the feature —
`mini_envshare_tg` → `mini_envshare_cross`, `mini_route_tg` → `mini_route` —
because a name that says "needs a special build" is how a suite is read as
optional; `tg_tutorial` keeps its name, where "tg" is the subject.

| target | covers | tests | time | gated? |
| --- | --- | ---: | ---: | --- |
| `src/lib.rs` (unit) | the checker's own modules, `mini::*` | **299/299** | 8.7 s | yes |
| `tests/corpus.rs` | good/bad export acceptance, arena corpus | **6/6** | 40.3 s | yes |
| `tests/tg_tutorial.rs` | **every defeq step discharged, no gaps** | **36/36** | 31.7 s | yes |
| `tests/mini_mutual.rs` | mutual/nested encodings | **12/12** | 28.2 s | yes |
| `tests/mini_nested.rs` | nested declaration interpretation | **20/20**, 2 ignored | 17.2 s | yes |
| `tests/mini_tutorial.rs` | tutorial corpus under mini | **16/16** | 16.4 s | yes |
| `tests/mini_dump.rs` | model dump shapes | **12/12** | 16.3 s | yes |
| `tests/unified_cli.rs` | the unified CLI's ratchets | **6/6** | 5.4 s | yes |
| `tests/mini_nat_equations.rs` | the characteristic Nat equations | **2/2** | 4.2 s | yes |
| `tests/mini_designed.rs` | designed-fixture behaviour, indexed seam | **34/34** | 2.2 s | yes |
| `tests/mini_envshare_cross.rs` | crossing ledger, statement guards (was `mini_envshare_tg`) | **14/14**, 1 ignored | 0.3 s | yes |
| `tests/mini_budget.rs` | declared budget declines | **1/1** | 0.3 s | yes |
| `tests/mini_envshare.rs` | the mini-side half of the `EnvCore` seam | **6/6** | 0.3 s | yes |
| `tests/mini_route.rs` | the routed driver over one core (was `mini_route_tg`) | **10/10**, 2 ignored | 0.2 s | yes |
| `tests/mini_infinitary.rs` | infinitary constructors | **1/1** | 0.2 s | yes |
| doc-tests | prose examples in `inductive.rs`, `pretty_printer.rs`, `lib.rs` | 0, **8 ignored** | 0.0 s | yes |
| `src/bin/*.rs` (unit) | — | 0 tests | 0.0 s | — |
| **`cargo test -p nanoda_lib`** | **all of the above, in one command** | **476 passing** | **171.8 s** | **the gate** |
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
**The whole package — 299 unit tests and all 14 integration suites, 476
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
2026-08-15: that leg — leg C — is now vacuous.** Its scan
(`grep -rlE '^#!\[cfg\(feature = ...\)\]' checker/tests`) matches **zero**
files, so it iterates zero times; legs A and B still have subjects
(`stepcount`/`nanoda_lib`, and kernel/derived carrying no `cfg(feature)` of
their own), so `matrix == 3` and the script's own non-vacuity floor does not
trip. Its `--self-test` still proves leg C *can* fire against a synthetic tree,
so it is prospective rather than broken — but it is a leg with no subject,
which is §2.1 item 5 arriving from the other direction. Open.

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

> **Sequencing.** The `tg.rs` half of this (commit `57bfb8c`, instances 2 and
> the `asked > 0` gates) landed on `joachim/shadowed-residue` **before** the
> owner parked it behind the `joachim/retire-certifier` refactor, which rewrites
> `impl Certifier for TgBackend` wholesale. It is one isolated commit touching
> **only** `checker/src/tg.rs`, and only the two free reporting functions at the
> file's tail — `ix_readiness_report` and `origin_report`, around lines
> 24000–24180. It touches **no** `Certifier` method, so it should rebase or
> cherry-pick over that refactor cleanly; if it does not, the measurements above
> are what need reproducing, not the diff. The `tg_tutorial` and `derived/`
> commits are independent of it.

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
  `stepcount`-gated, so a plain `--features tg` build emits byte-identical text
  and **no gate in §2 can observe this half**. It was verified by direct
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
