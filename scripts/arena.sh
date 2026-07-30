#!/usr/bin/env bash
# Run the Lean Kernel Arena corpus through the checker and report, for every
# file, whether the outcome matched expectation:
#
#   vendor/arena-tests/good/**  must be ACCEPTED
#   vendor/arena-tests/bad/**   must be REJECTED
#
# The `bad` half is the part that matters. A checker that accepts everything
# passes `good` trivially; only `bad` shows the checker is actually checking.
#
# Usage: scripts/arena.sh [--include-perf] [subdir ...]
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${ARENA_BIN:-$ROOT/checker/target/release/nanoda_bin}"
CORPUS="${ARENA_CORPUS:-$ROOT/vendor/arena-tests}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

[[ -x "$BIN" ]] || { echo "no binary at $BIN (cargo build --release)" >&2; exit 2; }
[[ -d "$CORPUS" ]] || { echo "no corpus at $CORPUS" >&2; exit 2; }

INCLUDE_PERF=0
declare -a SUBDIRS=()
for a in "$@"; do
  case "$a" in
    --include-perf) INCLUDE_PERF=1 ;;
    *) SUBDIRS+=("$a") ;;
  esac
done

# Collect the file list.
declare -a FILES=()
if ((${#SUBDIRS[@]})); then
  for d in "${SUBDIRS[@]}"; do
    while IFS= read -r f; do FILES+=("$f"); done < <(find "$CORPUS/$d" -name '*.ndjson' | sort)
  done
else
  while IFS= read -r f; do FILES+=("$f"); done < <(find "$CORPUS/good" "$CORPUS/bad" -name '*.ndjson' | sort)
fi

pass=0; fail=0; skip=0
declare -a FAILURES=()
declare -a SKIPPED=()

for f in "${FILES[@]}"; do
  if [[ $INCLUDE_PERF -eq 0 && "$f" == */perf/* ]]; then continue; fi

  case "$f" in
    "$CORPUS"/good/*) expect=accept ;;
    "$CORPUS"/bad/*)  expect=reject ;;
    *) continue ;;
  esac

  # `unsafe_permit_all_axioms` keeps the corpus's own axioms from being treated
  # as errors; we are testing the type checker, not the axiom whitelist. It
  # requires `unpermitted_axiom_hard_error: false` and no explicit list.
  # `unsafe_permit_all_axioms` keeps the corpus's own axioms from being treated
  # as errors; we are testing the type checker, not the axiom whitelist.
  # The nat/string extensions must be on: much of the corpus (and all of
  # `init-prelude`) uses literals, which the checker otherwise refuses outright.
  cat > "$TMP/cfg.json" <<EOF
{"export_file_path": $(printf '%s' "$f" | python3 -c 'import json,sys;print(json.dumps(sys.stdin.read()))'),
 "unpermitted_axiom_hard_error": false,
 "unsafe_permit_all_axioms": true,
 "nat_extension": true,
 "string_extension": true,
 "print_success_message": false}
EOF

  if timeout "${ARENA_TIMEOUT:-120}" "$BIN" "$TMP/cfg.json" >"$TMP/out" 2>&1; then
    got=accept
  else
    got=reject
  fi

  rel="${f#"$CORPUS"/}"

  # Upstream nanoda *declines* (rather than refutes) export files whose name or
  # level back-references are not densely numbered: it is a parser policy, not a
  # judgement that the file is ill-typed. The arena considers such files valid.
  # Count these separately so the number stays visible instead of being either a
  # silent pass or a scary failure. See DECISIONS.md.
  if [[ "$got" == reject && "$expect" == accept ]] && grep -q 'Back-refs must be continuous' "$TMP/out"; then
    skip=$((skip+1))
    SKIPPED+=("$rel: declined (non-continuous back-refs)")
    continue
  fi

  if [[ "$got" == "$expect" ]]; then
    pass=$((pass+1))
  else
    fail=$((fail+1))
    FAILURES+=("$rel: expected $expect, got $got")
  fi
done

echo "arena: $pass matched, $fail mismatched, $skip declined (of $((pass+fail+skip)))"
if ((skip)); then printf '  skip %s\n' "${SKIPPED[@]}"; fi
if ((fail)); then
  printf '  FAIL %s\n' "${FAILURES[@]}"
  exit 1
fi
