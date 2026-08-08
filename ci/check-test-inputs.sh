#!/usr/bin/env bash
# Are the optional inputs the Rust suites want actually here? SKIP (77) if not.
#
# `ci/skip-guard.rs` makes a corpus-dependent test *fail* instead of skipping,
# but only under `NANODATG_REQUIRE_CORPUS` — and `ci/check.sh` sets that only
# when `vendor/arena-tests` is genuinely present, because a machine that has not
# fetched the 17 MB corpus is not broken, it is unequipped, and turning that into
# a red would train people to ignore it.
#
# Which leaves exactly the gap this script fills: on such a machine dozens of
# `#[test]` functions still report `ok` having executed nothing, and without a
# step that says so the summary ends "all checks passed". Exit 77 makes it end
# "all checks that ran passed" instead — the same distinction the arena,
# mini-vs-nanoda and modelgen steps already draw, applied to the Rust suites.
#
# This step is *reporting*, not enforcement; `ci/check-test-guards.sh` is the
# enforcement and needs no inputs, so it runs where this one SKIPs.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

CORPUS="${CORPUS_DIR:-$ROOT/vendor/arena-tests}"
MODELGEN="${MODELGEN_BIN:-$ROOT/modelgen/.lake/build/bin/modelgen}"
CHECK_SH="${CHECK_SH:-$ROOT/ci/check.sh}"
SCAN_DIRS="${SCAN_DIRS:-$ROOT/checker/tests $ROOT/mini/tests}"

self_test() {
  TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
  local sfails=0
  expect() { # expect <rc> <name> [env...]
    local want="$1" name="$2"; shift 2
    local rc; env "$@" "$0" >/dev/null 2>&1; rc=$?
    if [[ $rc -eq $want ]]; then echo "  ok: $name (rc=$rc)"
    else echo "SELFTEST FAIL: $name wanted rc=$want, got $rc" >&2; env "$@" "$0" >&2; sfails=$((sfails+1)); fi
  }
  echo "self-testing $0"
  mkdir -p "$TMP/empty"
  # An absent input is a SKIP, not a pass and not a failure.
  expect 77 "an absent corpus SKIPs" CORPUS_DIR="$TMP/nope" MODELGEN_BIN="$TMP/nope"
  # A corpus that unpacked short is BROKEN, not a skip: the directory test that
  # every call site used to do would have called this one present.
  expect 1  "a present-but-empty corpus is BROKEN" CORPUS_DIR="$TMP/empty" MODELGEN_BIN="$TMP/nope"
  # The corpus is there but nothing required it — this is the state the whole
  # change exists to prevent, and it must not be reported as a pass.
  expect 1  "a corpus present with the variable unset is BROKEN" \
            CORPUS_DIR="$ROOT/vendor/arena-tests" MODELGEN_BIN="$TMP/nope" NANODATG_REQUIRE_CORPUS=
  # …and the ci/check.sh grep.
  printf '#!/bin/sh\nstep "tests" cargo test --workspace\n' > "$TMP/no-tg.sh"
  expect 1  "a ci/check.sh with no --features tg step is BROKEN" \
            CHECK_SH="$TMP/no-tg.sh" CORPUS_DIR="$TMP/nope" MODELGEN_BIN="$TMP/nope"
  echo
  if (( sfails )); then echo "$sfails self-test failure(s)" >&2; return 1; fi
  echo "test-input self-test OK"
}
if [[ "${1:-}" == --self-test ]]; then self_test; exit $?; fi

# ── A feature-gated suite compiles to an EMPTY test binary ──────────────────
# `checker/tests/tg_tutorial.rs` opens `#![cfg(feature = "tg")]`. Without the
# feature it is not "skipped" — it does not exist, and cargo prints
# `running 0 tests … ok`. Measured: 28 tests become 0 and the run stays green.
# So the only thing standing between those 28 and a silent zero is the
# `--features tg` step in `ci/check.sh`, exactly the way the only thing standing
# between `mini/` and an unscanned R6′ is the delegation `ci/check-boundary.sh`
# greps for. Same rule, same reason.
gated=$(grep -rhoE '^#!\[cfg\(feature = "([a-z_]+)"\)\]' --include='*.rs' $SCAN_DIRS 2>/dev/null \
        | sed -E 's/.*"([a-z_]+)".*/\1/' | sort -u)
for f in $gated; do
  if grep -qE "cargo test .*--features ([a-z_]+ )*$f\b" "$CHECK_SH"; then
    echo "  feature-gated suites behind \`$f\`: run by a --features $f step"
  else
    echo "BROKEN: a test suite is behind \`#![cfg(feature = \"$f\")]\` and $CHECK_SH" >&2
    echo "        has no \`cargo test --features $f\` step — those tests compile to an" >&2
    echo "        empty binary and report \`running 0 tests … ok\`." >&2
    exit 1
  fi
done

# How much is riding on this — counted, not asserted from memory, so the number
# cannot rot the way a comment would.
sites=$(grep -rE 'skip_guard::(absent|no_inputs|tool_absent)\b' \
          --include='*.rs' "$ROOT/checker/tests" "$ROOT/mini/tests" 2>/dev/null \
        | grep -vcE ':[[:space:]]*(//|\*)')

missing=0

if [[ -d "$CORPUS" ]]; then
  n=$(find "$CORPUS" -name '*.ndjson' -type f 2>/dev/null | wc -l)
  if (( n == 0 )); then
    echo "BROKEN: $CORPUS exists but holds no .ndjson exports" >&2
    exit 1
  fi
  echo "  arena corpus: $n exports at $CORPUS"
  if [[ "${NANODATG_REQUIRE_CORPUS:-}" == "" || "${NANODATG_REQUIRE_CORPUS:-}" == "0" ]]; then
    echo "BROKEN: the corpus is present but NANODATG_REQUIRE_CORPUS is not set —" >&2
    echo "        the corpus-dependent tests could skip and still report \`ok\`." >&2
    echo "        ci/check.sh is supposed to export it here." >&2
    exit 1
  fi
  echo "  NANODATG_REQUIRE_CORPUS=$NANODATG_REQUIRE_CORPUS — a skip is a failure"
else
  echo "  arena corpus: ABSENT ($CORPUS)"
  missing=1
fi

if [[ -x "$MODELGEN" ]]; then
  echo "  modelgen: built at $MODELGEN"
  if [[ "${NANODATG_REQUIRE_MODELGEN:-}" == "" || "${NANODATG_REQUIRE_MODELGEN:-}" == "0" ]]; then
    echo "BROKEN: modelgen is built but NANODATG_REQUIRE_MODELGEN is not set" >&2
    exit 1
  fi
else
  echo "  modelgen: NOT BUILT ($MODELGEN)"
  missing=1
fi

echo "  $sites guarded skip sites in checker/tests and mini/tests"

if (( missing )); then
  echo
  echo "Inputs are missing, so the tests behind those $sites guard sites will SKIP —" >&2
  echo "and \`cargo test\` reports a skip as \`ok\`. This step did not run; the summary" >&2
  echo "must not claim those tests passed." >&2
  exit 77
fi

echo "  every optional input is present and required"
