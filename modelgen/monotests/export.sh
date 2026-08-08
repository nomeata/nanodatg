#!/usr/bin/env bash
# Export this directory's `.lean` sources to `.ndjson`, using the repository's
# own `scripts/export-fixture.sh` — same toolchain, same `lean4export` revision,
# same `--#export` convention — without writing into `mini/tests/fixtures`.
#
#   ./modelgen/monotests/export.sh [NAME.lean ...]
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
FIX="$ROOT/mini/tests/fixtures"
declare -a SRCS=()
if (($#)); then for a in "$@"; do SRCS+=("$HERE/$(basename "$a")"); done
else while IFS= read -r f; do SRCS+=("$f"); done < <(find "$HERE" -name '*.lean' | sort); fi
for s in "${SRCS[@]}"; do
  b="$(basename "$s" .lean)"
  cp "$s" "$FIX/$b.lean"
  trap 'rm -f "$FIX/$b.lean" "$FIX/$b.ndjson"' EXIT
  bash "$ROOT/scripts/export-fixture.sh" "$b.lean"
  mv "$FIX/$b.ndjson" "$HERE/$b.ndjson"
  rm -f "$FIX/$b.lean"
  trap - EXIT
done
