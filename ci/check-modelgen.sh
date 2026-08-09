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
#                        `modelgen/tests`, `mini/tests/fixtures`' filtered
#                        copies, `vendor/arena-tests`' `init-prelude` when it is
#                        there, and the CLI contract of §1.4 against the built
#                        binary. 248 checks when this was written.
#   `lake exe monotest`  the monomorphiser (`MONOMORPH.md`), over
#                        `modelgen/monotests` and the 99 `good/` corpus files.
#                        107 checks when this was written.
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
# (106 with it, 7 without), so what is pinned is `> 0` and not a number; the
# per-fixture counts are `Test.lean`'s and `MonoTest.lean`'s business.
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
# reports zero, and one that reports nothing — because "report BROKEN on zero"
# is worth exactly what its own negative control is worth. It needs no
# toolchain. `ci/test-boundary.sh` is the same idea for `check-boundary.sh`.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MG="$ROOT/modelgen"

fails=0

# `$ROOT` rather than `..`: `Test.lean` and `MonoTest.lean` resolve every
# fixture against the root they are given, and `ci/check.sh` may be run from
# anywhere.
run_suite() {
  local name="$1" pattern="$2"; shift 2
  local out rc n
  out="$( "$@" 2>&1 )"; rc=$?
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
  echo "  $name: $n checks"
}

TEST_PAT='^([0-9]+) checks, 0 failed$'
MONO_PAT='^monotest: ([0-9]+) checks, all pass$'

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
run_suite "modelgen monotest" "$MONO_PAT" suite monotest

echo
if (( fails )); then
  echo "$fails modelgen suite(s) failed" >&2
  exit 1
fi
echo "modelgen suites OK"
