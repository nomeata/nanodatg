#!/usr/bin/env bash
# A raw per-file sweep of the corpus for the one-loop restructure: verdict tag,
# exit code, and every machine-readable row `mini --verbose` prints.
#
# Not a gate — the gates are `ci/check.sh`. This is the *diff* instrument: run
# it before and after and `diff` the two outputs, so a row that moves is named
# rather than inferred from an aggregate.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BIN="${MINI_BIN:-$ROOT/target/debug/mini}"
CORPUS="${1:-$ROOT/vendor/arena-tests}"

# `-L`: in a worktree `vendor/arena-tests` is a symlink (`ci/corpus-dir.sh
# --link`), and an unfollowed one makes this script iterate over nothing —
# which is the "a step that ran over no input" failure `ci/check-arena.sh`'s
# `(of N)` guard exists for. The count below is that guard.
files=$(find -L "$CORPUS" -name '*.ndjson' -not -path '*/perf/*' | sort)
n=$(echo "$files" | grep -c .)
if (( n == 0 )); then echo "no corpus under $CORPUS" >&2; exit 1; fi
echo "# sweep of $n files"
for f in $files; do
  rel="${f#$CORPUS/}"
  # `--no-modelgen`, exactly as `mini/tests/tutorial.rs` runs it: no corpus
  # export has a nested inductive, so the filter is the identity and costs an
  # exec (and a Lean toolchain this machine's worktrees do not all have).
  out="$("$BIN" --no-modelgen --verbose --mutual "$f" 2>&1)"
  rc=$?
  echo "== $rel rc=$rc"
  # Drop the reject message body and anything with a path in it: those are
  # multi-line and machine-unstable. Keep the tagged rows.
  echo "$out" | grep -E '^(facts|ledger|evidence|untranslated|conv|frame|clauses|elim|route|prefix)\b|	(accept|reject|decline)	' \
    | sed "s|$ROOT||g"
done
