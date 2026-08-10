#!/usr/bin/env bash
# `scripts/oneloop-sweep.sh` over `mini/tests/fixtures/` instead of the arena
# corpus — the population where the `mutual … end` encoder and the nested-model
# keying actually run. No corpus file has either, so the corpus sweep says
# nothing about them.
#
# `--mutual --nested` because both gates are off by default and both are the
# point. `--no-modelgen` for the corpus sweep's reason and one more: a nested
# fixture's model is committed *in* the `.ndjson`, so re-running the filter
# would be checking the filter and not this.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BIN="${MINI_BIN:-$ROOT/target/debug/mini}"

files=$(find -L mini/tests/fixtures -name '*.ndjson' | sort)
n=$(echo "$files" | grep -c .)
if (( n == 0 )); then echo "no fixtures" >&2; exit 1; fi
echo "# sweep of $n fixtures"
for f in $files; do
  out="$("$BIN" --no-modelgen --verbose --mutual --nested "$f" 2>&1)"
  echo "== ${f#mini/tests/fixtures/} rc=$?"
  echo "$out" | grep -E '^(facts|ledger|evidence|untranslated|conv|frame|clauses|elim|route|prefix)\b|	(accept|reject|decline)	'
done
