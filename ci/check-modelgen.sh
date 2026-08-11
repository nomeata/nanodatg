#!/usr/bin/env bash
# `modelgen`'s own two suites, which nothing ran.
#
# `mini` **execs** `modelgen` on its hot path (`mini/src/modelgen.rs`,
# `MODELGEN.md` §1) — the 2117-line Rust generator it replaced was deleted — and
# `rg modelgen ci/check.sh` returned nothing. The consequence was measured
# rather than imagined: the suite was **10 checks red** on master, for five
# fixtures whose coverage had been gone since `6ae6515`, and nobody was told.
#
#   `lake exe test`      the four oracles of `MODELGEN.md` §4 over
#                        `modelgen/tests`, `checker/tests/fixtures`' filtered
#                        copies, `vendor/arena-tests`' `init-prelude` when it is
#                        there, and the CLI contract of §1.4 against the built
#                        binary. 456 checks measured 2026-08-11 (248 when this
#                        was first written).
#   `lake exe monotest`  the monomorphiser (`MONOMORPH.md`), over
#                        `modelgen/monotests` and the 99 `good/` corpus files.
#                        109 checks measured 2026-08-11, as 10 + 99; see the
#                        two legs below.
#
# Neither number is pinned here — the suites own their own tables, and a count
# repeated in a third place is a count that goes stale. What is pinned is that
# the count exists and is not zero; see below.
#
# # Why this does not put Lean on `cargo test`'s critical path
#
# It does not touch `cargo test`. `mini`'s Rust suite is hermetic by design —
# fixtures are committed already filtered and every harness passes
# `--no-modelgen` — and that is a property worth keeping: it is why the Rust
# tests run on a machine with no `elan`. This step is a *separate* step that
# needs the toolchain, and it is the only one in `ci/check.sh` that does.
#
# # What it does when there is no toolchain, and why that is not a PASS
#
# It exits **77**, which `ci/check.sh` prints as `SKIP` and lists again in its
# summary. A skipped step is not a passed one and the summary says which: the
# failure mode to avoid above all others is a step that reports success when it
# did not run, and that is exactly the shape of bug this whole script exists
# because of.
#
# # Counting what executed
#
# Both binaries print how many checks they ran, and this parses the count and
# **fails on zero**. An exit status alone would accept a suite that silently
# stopped iterating — `Test.lean`'s tables are `List Row`s walked in `main`, and
# an empty table exits 0. `monotest`'s count varies with `vendor/arena-tests`
# (measured 2026-08-11: **109** with it, 9 without — the corpus contributes its
# 99 files *and* the one byte-identity check on `001_basicDef`), so what is
# pinned is `> 0` and not a number; the per-fixture counts are `Test.lean`'s and
# `MonoTest.lean`'s business.
#
# ## …per leg, because one counter lets a healthy leg hide a dead one
#
# That total was, until this was written, the *only* floor, and `monotest`'s
# total is a sum over two independent legs: 10 checks from
# `modelgen/monotests`' own table, and one per corpus file — 99 of them. A floor
# on the sum is satisfied by either leg alone. So the corpus leg could go to
# zero — `walkDir` returning nothing through the `vendor/arena-tests` symlink,
# the `.ndjson` suffix filter ceasing to match, `readExport` starting to return
# `none` and being swallowed by MonoTest.lean's `| continue` — and the run would
# print `corpus: 0 files, 0 declarations in, 0 out`, then `monotest: 10 checks,
# all pass`, and this script would have accepted it: 10 > 0. Ninety-nine files of
# coverage, gone with a green tick, which is the exact shape of the defect this
# whole file exists because of, one level in.
#
# So both legs are floored, and the two are kept **distinguishable rather than
# merged**:
#
#   * whether the corpus is there is decided **here**, by `-d` on the same path
#     `MonoTest.lean` builds (`$ROOT/vendor/arena-tests/good`), not inferred
#     from the output. The producer and the harness must therefore agree about
#     which world they are in, and a disagreement in *either* direction is
#     BROKEN: a `corpus:` line with no corpus under it says the two are reading
#     different paths, and no `corpus:` line with a corpus present says the leg
#     silently did not run.
#   * with a corpus, the `corpus: N files, …` line must parse **exactly** and
#     `N > 0`. Loose parsing is how a floor stops measuring: a
#     `sed -nE '…([0-9]+) files…'` that stops matching yields an empty string,
#     and an empty string that is not distinguished from a zero is a floor that
#     has quietly turned itself off. Unparsable is BROKEN, not zero and not pass.
#   * the fixture leg is `total − N`, and is floored too — the mirror image, in
#     which `modelgen/monotests`' table empties and 99 corpus files carry the
#     total over the line on their own.
#
# `MonoTest.lean` is the producer and belongs to another seat; nothing here asks
# it to print anything new. What is here is the reading of what it already
# prints, made strict enough that a change in the producer shows up as BROKEN
# rather than as a smaller number nobody is watching.
#
# # Cost
#
# ~1.0 s and ~0.4 s to run, plus `lake build`: about 80 s from cold (most of it
# `Modelgen.Model:c.o`) and nothing when `modelgen/.lake` is warm. `ci/check.sh`
# is **986 s measured** (2026-08-09; it was ~2 824 s while the feature matrix
# still ran the whole workspace three times), so this is well under a percent of
# the total even on a cold build.
#
# `--self-test` runs the count guard against canned output — a suite that
# reports zero, and one that reports nothing — and the per-leg floor against
# canned output for both worlds, because "report BROKEN on zero" is worth
# exactly what its own negative control is worth. It needs no toolchain.
# `ci/test-boundary.sh` is the same idea for `check-boundary.sh`.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MG="$ROOT/modelgen"

fails=0

# The last suite's output and parsed count, for the per-leg checks below. A
# second run to re-read them would be a second measurement and could disagree
# with the one that was floored.
LAST_OUT=""; LAST_N=""

# `$ROOT` rather than `..`: `Test.lean` and `MonoTest.lean` resolve every
# fixture against the root they are given, and `ci/check.sh` may be run from
# anywhere.
run_suite() {
  local name="$1" pattern="$2"; shift 2
  local out rc n
  out="$( "$@" 2>&1 )"; rc=$?
  LAST_OUT="$out"; LAST_N=""
  printf '%s\n' "$out"
  if (( rc )); then
    echo "  $name failed (exit $rc)" >&2
    fails=$((fails+1))
    return 1
  fi
  n="$(printf '%s\n' "$out" | sed -nE "s/$pattern/\1/p" | tail -1)"
  if [[ -z "$n" ]]; then
    echo "  BROKEN: $name exited 0 without reporting a check count" >&2
    fails=$((fails+1))
    return 1
  elif (( n == 0 )); then
    echo "  BROKEN: $name ran 0 checks" >&2
    fails=$((fails+1))
    return 1
  fi
  LAST_N="$n"
  echo "  $name: $n checks"
}

TEST_PAT='^([0-9]+) checks, 0 failed$'
MONO_PAT='^monotest: ([0-9]+) checks, all pass$'
# `MonoTest.lean`'s corpus line, in full. Anchored at both ends and with every
# field spelled out: this is the parse that must break loudly if the producer's
# format moves, rather than degrade into "no number found" and then into a pass.
CORPUS_PAT='^corpus: ([0-9]+) files, [0-9]+ declarations in, [0-9]+ out$'
# The path `MonoTest.lean` tests with `System.FilePath.isDir`. `-d` follows the
# symlink `ci/corpus-dir.sh --link` leaves in a worktree, as Lean's does.
CORPUS_GOOD="$ROOT/vendor/arena-tests/good"

# monotest_legs <corpus present: 0|1> <total checks> <monotest output>
#
# Splits `monotest`'s single total into the two legs that produced it and floors
# each. See "…per leg" in the header for what each branch is closing.
monotest_legs() {
  local present="$1" total="$2" out="$3" line n fixture
  line="$(printf '%s\n' "$out" | grep -E '^corpus:' | tail -1)"

  if (( ! present )); then
    if [[ -n "$line" ]]; then
      echo "  BROKEN: monotest reported a corpus leg — \"$line\" — but there is" >&2
      echo "  no corpus at $CORPUS_GOOD. The suite and this harness are looking" >&2
      echo "  at different paths, so neither number below can be trusted." >&2
      fails=$((fails+1)); return 1
    fi
    echo "  modelgen monotest: fixture leg $total checks; corpus leg absent (no $CORPUS_GOOD)"
    return 0
  fi

  if [[ -z "$line" ]]; then
    echo "  BROKEN: there is a corpus at $CORPUS_GOOD but monotest printed no" >&2
    echo "  \`corpus:\` line — the corpus leg did not run, and its ~99 files are" >&2
    echo "  missing from a total that still cleared the floor on the other leg." >&2
    fails=$((fails+1)); return 1
  fi
  n="$(printf '%s\n' "$line" | sed -nE "s/$CORPUS_PAT/\1/p")"
  if [[ -z "$n" ]]; then
    echo "  BROKEN: monotest's corpus line does not parse: \"$line\"" >&2
    echo "  Expected \`corpus: N files, D declarations in, D out\`. A floor that" >&2
    echo "  cannot read its input is not a floor; fix the pattern here to match" >&2
    echo "  modelgen/MonoTest.lean, do not delete the check." >&2
    fails=$((fails+1)); return 1
  fi
  if (( n == 0 )); then
    echo "  BROKEN: the corpus leg checked 0 files, with a corpus present at" >&2
    echo "  $CORPUS_GOOD. The total ($total) came entirely from the fixture leg." >&2
    fails=$((fails+1)); return 1
  fi
  fixture=$((total - n))
  if (( fixture <= 0 )); then
    echo "  BROKEN: the fixture leg ran $fixture checks — modelgen/monotests'" >&2
    echo "  own table contributed nothing and the $n corpus files carried the" >&2
    echo "  total on their own." >&2
    fails=$((fails+1)); return 1
  fi
  echo "  modelgen monotest: fixture leg $fixture checks, corpus leg $n files"
}

if [[ "${1:-}" == "--self-test" ]]; then
  bad=0
  expect_broken() { # name, then a command whose output must be rejected
    local want="$1"; shift
    fails=0
    if run_suite "self-test" "$TEST_PAT" "$@" >/dev/null 2>&1; then
      echo "SELF-TEST FAILED: $want was accepted" >&2; bad=1
    elif (( fails != 1 )); then
      echo "SELF-TEST FAILED: $want did not count a failure" >&2; bad=1
    else
      echo "  ok: $want is rejected"
    fi
  }
  expect_broken "a suite reporting 0 checks"      echo "0 checks, 0 failed"
  expect_broken "a suite reporting no count"      echo "done"
  expect_broken "a suite reporting failures"      echo "12 checks, 3 failed"
  expect_broken "a suite that exits nonzero"      false
  fails=0
  if run_suite "self-test" "$TEST_PAT" echo "248 checks, 0 failed" >/dev/null && (( fails == 0 )); then
    echo "  ok: a real count is accepted"
  else
    echo "SELF-TEST FAILED: a real count was rejected" >&2; bad=1
  fi

  # ── the per-leg floor ──────────────────────────────────────────────────────
  # Canned `monotest` output in both worlds. `monotest_legs` takes the
  # corpus-present flag as an argument precisely so this can drive both without
  # a corpus, a toolchain, or a 100-file run.
  leg() { # leg <broken|ok> <name> <present> <total> <output...>
    local want="$1" name="$2" present="$3" total="$4"; shift 4
    local out rc
    # The capture is a subshell, so `fails` is incremented in a copy; the return
    # status is what crosses back, and the two are set together above.
    out="$(monotest_legs "$present" "$total" "$(printf '%s\n' "$@")" 2>&1)"; rc=$?
    fails=0
    if [[ "$want" == broken ]]; then
      if (( rc != 0 )) && [[ "$out" == *BROKEN* ]]; then
        echo "  ok: $name is rejected"
      else
        echo "SELF-TEST FAILED: $name was accepted" >&2
        printf '%s\n' "$out" | sed 's/^/    /' >&2; bad=1
      fi
    else
      if (( rc == 0 )) && [[ "$out" != *BROKEN* ]]; then
        echo "  ok: $name is accepted"
      else
        echo "SELF-TEST FAILED: $name was rejected" >&2
        printf '%s\n' "$out" | sed 's/^/    /' >&2; bad=1
      fi
    fi
  }
  #                                                        present total
  leg ok     "both legs alive"                                   1   106 \
      "corpus: 99 files, 4321 declarations in, 5678 out" "monotest: 106 checks, all pass"
  leg broken "a corpus leg of 0 files behind a healthy total"    1    10 \
      "corpus: 0 files, 0 declarations in, 0 out" "monotest: 10 checks, all pass"
  leg broken "a corpus present but no corpus line at all"        1    10 \
      "monotest: 10 checks, all pass"
  leg broken "a corpus line the harness cannot parse"            1   106 \
      "corpus: ninety-nine files" "monotest: 106 checks, all pass"
  leg broken "a corpus line whose fields have moved"             1   106 \
      "corpus: 99 files, 4321 decls in, 5678 out" "monotest: 106 checks, all pass"
  leg broken "a fixture leg the corpus carried over the line"    1    99 \
      "corpus: 99 files, 4321 declarations in, 5678 out" "monotest: 99 checks, all pass"
  leg ok     "no corpus, no corpus line — the honest skip"       0     9 \
      "monotest: 9 checks, all pass"
  leg broken "a corpus line with no corpus under it"             0   106 \
      "corpus: 99 files, 4321 declarations in, 5678 out" "monotest: 106 checks, all pass"

  # The pattern is only worth what its agreement with the producer is worth,
  # and every cell above feeds it a string this file wrote. This one is read
  # out of `modelgen/MonoTest.lean` itself, so the day the `IO.println` moves,
  # this fails here rather than on a machine that happens to have a corpus.
  fails=0
  producer="$(grep -oE 'corpus: \{files\} files, \{din\} declarations in, \{dout\} out' \
                "$MG/MonoTest.lean" 2>/dev/null)"
  if [[ -z "$producer" ]]; then
    echo "SELF-TEST FAILED: modelgen/MonoTest.lean no longer prints the \`corpus:\`" >&2
    echo "  line this file parses — CORPUS_PAT and the producer have drifted apart" >&2
    bad=1
  else
    # Substitute plausible numbers for the interpolations and re-parse.
    concrete="${producer//\{files\}/99}"; concrete="${concrete//\{din\}/4321}"
    concrete="${concrete//\{dout\}/5678}"
    if [[ -n "$(printf '%s\n' "$concrete" | sed -nE "s/$CORPUS_PAT/\1/p")" ]]; then
      echo "  ok: CORPUS_PAT parses the line MonoTest.lean actually prints"
    else
      echo "SELF-TEST FAILED: CORPUS_PAT does not match MonoTest.lean's line: $concrete" >&2
      bad=1
    fi
  fi

  exit $bad
fi

if ! command -v lake >/dev/null || ! command -v elan >/dev/null; then
  echo "  NOTICE: no Lean toolchain (\`lake\`/\`elan\` not on PATH)." >&2
  echo "  Neither modelgen suite ran. \`mini\` execs this binary at" >&2
  echo "  runtime; install elan and re-run ci/check.sh to cover it." >&2
  exit 77
fi

# `lake exe test` asserts the CLI contract against `modelgen/.lake/build/bin/
# modelgen` and reports a *failure* rather than a skip when it is missing
# (`Test.lean`'s `runCli`), so the build is part of the check and not a
# convenience.
echo "building modelgen (toolchain: $(cat "$MG/lean-toolchain"))"
if ! ( cd "$MG" && lake build ); then
  echo "modelgen does not build" >&2
  exit 1
fi

suite() { ( cd "$MG" && lake exe "$1" "$ROOT" ); }

run_suite "modelgen test"     "$TEST_PAT" suite test
if run_suite "modelgen monotest" "$MONO_PAT" suite monotest; then
  if [[ -d "$CORPUS_GOOD" ]]; then present=1; else present=0; fi
  monotest_legs "$present" "$LAST_N" "$LAST_OUT"
fi

echo
if (( fails )); then
  echo "$fails modelgen suite(s) failed" >&2
  exit 1
fi
echo "modelgen suites OK"
