#!/usr/bin/env bash
# Watch the feature-matrix guard fire.
#
# `ci/check.sh` no longer runs `cargo test --workspace` three times. The two
# feature runs are `-p nanoda_lib`, because `stepcount` and `tg` are the
# checker's features and `kernel`, `derived` and `mini` cannot observe them.
# The argument is in `checker/src/certify.rs` next to `FEATURE_INERT_VAR`; the
# short form is that every item the two features gate is reachable only through
# a `TypeChecker`, which builds its backend in its constructor, so a process
# that never builds a backend cannot tell the three builds apart.
#
# `ci/check.sh` enforces that by running the non-checker half of the workspace
# under `NANODATG_ASSERT_FEATURE_INERT=1`, which makes building a backend panic.
# This script is the other half of the deal: **it watches that panic happen.**
# A guard nobody has seen fail is not known to work — three real gates in this
# repo were found unrun by accident — so the guard is exercised on every run,
# against a process that certainly does build a backend, and the run fails if
# it comes back green.
#
# Two cells, both required:
#
#   1. `nanoda_bin` under the variable must **abort**, naming the variable.
#   2. the same `nanoda_bin` on the same fixture, without it, must **succeed** —
#      otherwise cell 1 proves nothing but that the fixture is broken.
#
# The count guard is the point of the pair: this fails on zero cells run, the
# way `check-arena.sh` fails on zero corpus files.
#
# # What it does when it cannot run
#
# Exits **77** (SKIP) when `target/debug/nanoda_bin` has not been built —
# `ci/check.sh`'s "workspace builds" step is what builds it, so in a full run it
# is there. It needs no corpus and no Lean toolchain. ~0.1 s.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

BIN="${NANODA_BIN:-$ROOT/target/debug/nanoda_bin}"
FIXTURE="${INERT_FIXTURE:-$ROOT/checker/tests/fixtures/good/arrow.ndjson}"
VAR=NANODATG_ASSERT_FEATURE_INERT

if [[ ! -x "$BIN" ]]; then
  echo "  nanoda_bin: NOT BUILT ($BIN)"
  echo
  echo "The feature-matrix guard was not watched firing; this step did not run." >&2
  exit 77
fi
if [[ ! -f "$FIXTURE" ]]; then
  echo "BROKEN: the fixture $FIXTURE is missing" >&2
  exit 1
fi

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
CFG="$TMP/cfg.json"
# The same flags `checker/tests/corpus.rs` uses: we are exercising the guard,
# not the axiom whitelist.
printf '{"export_file_path": "%s",\n "unpermitted_axiom_hard_error": false,\n "unsafe_permit_all_axioms": true,\n "nat_extension": true,\n "string_extension": true,\n "print_success_message": false}\n' \
  "$FIXTURE" > "$CFG"

cells=0
fails=0

# cell 2 first: the control. If the fixture does not check, cell 1 is vacuous.
cells=$((cells+1))
if out="$(env -u "$VAR" "$BIN" "$CFG" 2>&1)"; then
  echo "  ok: without $VAR the checker runs the fixture"
else
  echo "FAIL: the control cell — $BIN cannot check $FIXTURE at all, so the" >&2
  echo "      guard cell below would prove nothing." >&2
  printf '%s\n' "$out" | sed 's/^/        /' >&2
  fails=$((fails+1))
fi

cells=$((cells+1))
if out="$(env "$VAR=1" "$BIN" "$CFG" 2>&1)"; then
  echo "FAIL: $VAR=1 did not stop the checker building a proof backend." >&2
  echo '      The guard that holds ci/check.sh’s narrowed feature matrix up' >&2
  echo '      is not working, so the matrix is narrowing in silence.' >&2
  fails=$((fails+1))
elif ! printf '%s\n' "$out" | grep -q "$VAR"; then
  echo "FAIL: $VAR=1 stopped the checker, but not with the guard's message —" >&2
  echo "      so this cell is watching some other failure." >&2
  printf '%s\n' "$out" | tail -5 | sed 's/^/        /' >&2
  fails=$((fails+1))
else
  echo "  ok: $VAR=1 aborts the checker where it builds its backend"
fi

# `0` and the empty string are off, the way `ci/check.sh` treats
# `NANODATG_REQUIRE_CORPUS` — a guard with a surprising off-switch gets left on
# by accident and then turned off with a bigger hammer.
for off in "" "0"; do
  cells=$((cells+1))
  if env "$VAR=$off" "$BIN" "$CFG" >/dev/null 2>&1; then
    echo "  ok: $VAR='$off' is off"
  else
    echo "FAIL: $VAR='$off' should be off, and stopped the checker" >&2
    fails=$((fails+1))
  fi
done

echo "  $cells cells"
if (( cells == 0 )); then
  echo "BROKEN: no cells ran, so nothing was watched firing" >&2
  exit 1
fi
if (( fails )); then echo "$fails cell(s) failed" >&2; exit 1; fi
