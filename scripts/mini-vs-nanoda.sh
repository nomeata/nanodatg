#!/usr/bin/env bash
# MINI-DESIGN.md §11.3: a two-column verdict table over the arena corpus.
#
# Both checkers see the same export files and the same parser, so a divergence
# is information: either mini has a port bug, or nanoda has one, or the two
# disagree about what "declined" means. Negative agreement matters as much as
# positive — a checker that accepts everything passes the good corpus.
#
#   ./scripts/mini-vs-nanoda.sh [good|bad|all]     (default: all)
#
# Columns: file, mini's verdict, nanoda's verdict, and AGREE/DIFFER.
# Exit status is nonzero when the two disagree about *acceptance* (a decline on
# one side and a reject on the other is reported but not a failure: nanoda
# signals both by exiting nonzero and only distinguishes them in its message).
#
# One divergence is deliberate and is reported as `out-of-scope` rather than as
# an acceptance failure: mini declines an export that declares an axiom of its
# own, because such an axiom's inhabitation is not derivable in principle and a
# run that stops at the first missing derivation would stop there for ever
# (MINI-DESIGN.md §0.6). nanoda accepts those files, and is right to — the two
# checkers are answering different questions about them.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

WHICH="${1:-all}"
CORPUS="vendor/arena-tests"
if [[ ! -d "$CORPUS" ]]; then
  echo "no corpus at $CORPUS (gitignored); nothing to compare" >&2
  exit 0
fi

cargo build --release -p mini -p nanoda_lib >/dev/null 2>&1 || {
  echo "build failed" >&2; exit 1; }
MINI="$ROOT/target/release/mini"
NANODA="$ROOT/target/release/nanoda_bin"

tmpcfg="$(mktemp -t mini-vs-nanoda-XXXXXX.json)"
trap 'rm -f "$tmpcfg"' EXIT

nanoda_verdict() {
  # Same flags as checker/tests/corpus.rs: we are comparing type checkers, not
  # axiom whitelists.
  cat >"$tmpcfg" <<EOF
{"export_file_path": "$1",
 "unpermitted_axiom_hard_error": false,
 "unsafe_permit_all_axioms": true,
 "nat_extension": true,
 "string_extension": true,
 "print_axioms": false,
 "print_success_message": false}
EOF
  local out rc
  out="$("$NANODA" "$tmpcfg" 2>&1)"; rc=$?
  if [[ $rc -eq 0 ]]; then echo accept
  elif grep -q "^Declined:" <<<"$out"; then echo decline
  else echo reject
  fi
}

mini_verdict() {
  local out rc
  # `--acceptance-only`: this script compares two *type checkers*, so the only
  # axis it may read is whether the file was accepted. mini otherwise exits 4
  # when it accepted a file and left an obligation underived, which is not a
  # judgement about the file and would show up here as a spurious divergence.
  # `--no-modelgen`: the two columns have to be about the **same file**. mini
  # runs the `modelgen` filter by default (`mini/src/modelgen.rs`), which for a
  # file with a nested inductive splices a model in and changes the declaration
  # count; nanoda is handed the path as it stands. Comparing a filtered run
  # against an unfiltered one would report a difference this script's whole
  # point is to attribute to a port bug. No corpus export has a nested
  # inductive, so today the flag changes nothing but an exec — it is here so
  # that the day one does, the table does not start lying.
  out="$("$MINI" --no-modelgen --acceptance-only "$1" 2>/dev/null)"; rc=$?
  case $rc in
    0) echo accept;;
    1) echo reject;;
    2) if grep -q 'non-standard axiom' <<<"$out"; then echo out-of-scope; else echo decline; fi;;
    *) echo crash;;
  esac
}

dirs=()
[[ "$WHICH" == "good" || "$WHICH" == "all" ]] && dirs+=("$CORPUS/good/tutorial")
[[ "$WHICH" == "bad"  || "$WHICH" == "all" ]] && dirs+=("$CORPUS/bad/tutorial")

printf '%-42s %-8s %-8s %s\n' file mini nanoda ''
differ=0
for d in "${dirs[@]}"; do
  [[ -d "$d" ]] || continue
  echo "── $d"
  for f in "$d"/*.ndjson; do
    m="$(mini_verdict "$f")"
    n="$(nanoda_verdict "$f")"
    if [[ "$m" == "$n" ]]; then tag=AGREE
    elif [[ "$m" == out-of-scope ]]; then tag="out-of-scope(declared axiom)"
    elif [[ "$m" == accept || "$n" == accept ]]; then tag="DIFFER(acceptance)"; differ=$((differ+1))
    else tag="differ(reason)"
    fi
    printf '%-42s %-8s %-8s %s\n' "$(basename "$f")" "$m" "$n" "$tag"
  done
done

echo
if (( differ )); then
  echo "$differ acceptance divergence(s)" >&2
  exit 1
fi
echo "no acceptance divergences"
