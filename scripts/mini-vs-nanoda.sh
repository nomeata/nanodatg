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
# Columns: file, mini's verdict, nanoda's verdict, and the outcome.
#
# # The five outcomes
#
# | mini           | nanoda         | outcome                                   |
# |----------------|----------------|-------------------------------------------|
# | crash/timeout  | anything       | `CRASH` — **FAIL**. Not a verdict at all. |
# | anything       | crash/timeout  | `CRASH` — **FAIL**.                       |
# | same verdict   | same verdict   | `AGREE`. The normal case.                 |
# | `out-of-scope` | anything       | counted and **named in the summary**.     |
# | accepted       | not accepted   | **FAIL** — an acceptance divergence.      |
# | not accepted   | accepted       | **FAIL** — an acceptance divergence.      |
# | not accepted   | not accepted,  | `reason-only`, counted and named.         |
# |                | other reason   |                                           |
#
# The rows are in the order the script tests them, so `out-of-scope` beats the
# acceptance rule and a crash beats everything.
#
# A decline on one side and a reject on the other is `reason-only` and not a
# failure: nanoda signals both by exiting nonzero and only distinguishes them in
# its message, so the two columns cannot be compared at that resolution.
#
# One divergence is deliberate and is reported as `out-of-scope` rather than as
# an acceptance failure: mini declines an export that declares an axiom of its
# own, because such an axiom's inhabitation is not derivable in principle and a
# run that stops at the first missing derivation would stop there for ever
# (MINI-DESIGN.md §0.6). nanoda accepts those files, and is right to — the two
# checkers are answering different questions about them.
#
# A **crash** — a panic, a signal, or the `MVN_TIMEOUT` — used to land in the
# `reason-only` bucket and pass, so a `mini` panic on a file nanoda rejects was
# a green run. It is a failure now: an exit code outside `0`/`1`/`2` is not a
# judgement about the file, and a gate that tolerates one is not comparing two
# checkers, it is comparing one checker against a corpse.
#
# # Why there is no waiver list here, and `scripts/arena.sh` has one
#
# `arena.sh`'s `bad/` ratchet needs `scripts/arena-accept.txt` because each lost
# rejection there is *its own* unprincipled loss with its own cause, and the only
# honest record is one line per file with a reason on it. The non-AGREE outcomes
# here are not like that. There are exactly two of them and each is a **stated
# rule about a property of the file**, not a fact about a filename:
#
#   * `out-of-scope` is read off the reason `mini` itself prints — a file that
#     declares an axiom is outside what `mini` answers, per MINI-DESIGN.md §0.6,
#     and that is true of the next such file too.
#   * `reason-only` is the resolution limit of nanoda's exit status, above.
#
# A list of the file names those rules currently select would be a list whose
# every entry carries the same reason, restating the rule less accurately than
# the rule does — and it would go stale the first time `vendor/arena-tests` is
# re-fetched, since the corpus is gitignored and pulled from a URL that is not
# pinned. `arena-accept.txt` accepts that exposure because its entries buy
# something; a second list next to it would only cost.
#
# What the outcomes *do* get is the thing the list exists to provide: they are
# **counted and named on every run**, in the summary line and one row each, so
# the population is visible rather than inferred from a 133-line table. If the
# count moves, the row that moved says which file and why.
#
# # Two legs, two counts, two floors
#
# The comparison runs over `good/tutorial` (~91 files) and `bad/tutorial` (~42),
# and they answer different questions: `good/` asks whether either checker
# refuses something it should take, `bad/` whether either takes something it
# should refuse. **Only `bad/` can catch an over-permissive checker**, and it is
# the smaller of the two.
#
# One count over both is therefore a floor the big leg satisfies by itself. If
# `bad/tutorial` were emptied — re-fetched wrong, renamed, its suffix changed —
# it would expand to nothing under `nullglob`, the loop would produce no rows,
# and the summary would read `(of 91)`: a large, healthy-looking number with the
# negative half of the gate silently gone. So each leg prints its own count and
# is floored on its own, here and again in `ci/check-mini-vs-nanoda.sh`.
#
# A leg *directory* that is missing is worse still and exits 2. It used to be a
# bare `[[ -d "$d" ]] || continue`, which is a hand-rolled silent skip — what
# `ci/skip-guard.rs` bans in the Rust suites for exactly this reason.
#
# # Exit status
#
#   0  no acceptance divergences
#   1  at least one acceptance divergence, or a crash
#   2  could not run — no corpus, a missing or empty corpus leg, no checker
#      binary, or the build failed
#
# **2 is not 0.** This exited 0 when `vendor/arena-tests` was absent, which is
# indistinguishable from a clean run for anything reading the status; `ci/
# check-mini-vs-nanoda.sh` turns the absence into a 77/SKIP, which is a third
# outcome and is repeated by name in `ci/check.sh`'s summary.
#
# Env: MVN_CORPUS, MVN_MINI, MVN_NANODA, MVN_TIMEOUT. They are the seams
# `ci/check-mini-vs-nanoda.sh --self-test` drives with a synthetic corpus and a
# pair of fake checkers; setting either binary also suppresses the build below.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

WHICH="${1:-all}"
CORPUS="${MVN_CORPUS:-vendor/arena-tests}"
if [[ ! -d "$CORPUS" ]]; then
  echo "no corpus at $CORPUS (gitignored; see README.md \"Corpus tests\")" >&2
  exit 2
fi

MINI="${MVN_MINI:-$ROOT/target/release/mini}"
NANODA="${MVN_NANODA:-$ROOT/target/release/nanoda_bin}"
# A hand run builds what it needs; a run under `ci/check-mini-vs-nanoda.sh` is
# handed both paths and must not build, both because the harness already did and
# because the self-test's checkers are shell scripts.
if [[ -z "${MVN_MINI:-}${MVN_NANODA:-}" ]]; then
  if ! out="$(cargo build --release -p mini -p nanoda_lib 2>&1)"; then
    printf '%s\n' "$out" >&2
    echo "build failed" >&2
    exit 2
  fi
fi
for b in "$MINI" "$NANODA"; do
  [[ -x "$b" ]] || { echo "no checker at $b (cargo build --release)" >&2; exit 2; }
done

TIMEOUT="${MVN_TIMEOUT:-120}"

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
  out="$(timeout "$TIMEOUT" "$NANODA" "$tmpcfg" 2>&1)"; rc=$?
  # nanoda has one success code and folds every refusal into a nonzero exit, so
  # `reject` is the catch-all — but a *signal* or the timeout is not a refusal,
  # and reading one as `reject` would let a segfault agree with mini.
  if [[ $rc -eq 0 ]]; then echo accept
  elif (( rc >= 124 )); then echo "crash($rc)"
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
  out="$(timeout "$TIMEOUT" "$MINI" --no-modelgen --acceptance-only "$1" 2>&1)"; rc=$?
  case $rc in
    0) echo accept;;
    1) echo reject;;
    2) if grep -q 'non-standard axiom' <<<"$out"; then echo out-of-scope; else echo decline; fi;;
    # Everything else is a panic, a signal, or the timeout. `--acceptance-only`
    # already rules out 4, and 3 needs `--block`, which is not passed.
    *) echo "crash($rc)";;
  esac
}

dirs=()
[[ "$WHICH" == "good" || "$WHICH" == "all" ]] && dirs+=("$CORPUS/good/tutorial")
[[ "$WHICH" == "bad"  || "$WHICH" == "all" ]] && dirs+=("$CORPUS/bad/tutorial")

# A requested leg that is not there is an **incomplete corpus**, and it exits 2
# ("could not run") rather than being skipped. What stood here was
# `[[ -d "$d" ]] || continue` — a hand-rolled silent skip, the shell spelling of
# the shape `ci/skip-guard.rs` bans in the Rust suites and `ci/check-test-guards.sh`
# ratchets: the loop moved on, the summary counted the other leg, and the run
# was green. Losing `bad/tutorial` that way loses the negative half of the
# comparison, which is the half that can fail.
for d in "${dirs[@]}"; do
  [[ -d "$d" ]] && continue
  echo "missing corpus leg: $d" >&2
  echo "The corpus at $CORPUS is incomplete. A leg that is not there is not a" >&2
  echo "leg that agreed; refusing to report a partial comparison as a whole one." >&2
  exit 2
done

printf '%-42s %-12s %-12s %s\n' file mini nanoda ''
agree=0; differ=0; oos=0; reason=0
declare -a FAILURES=() NAMED=() LEGS=()
shopt -s nullglob
for d in "${dirs[@]}"; do
  leg="${d#"$CORPUS"/}"; legn=0
  echo "── $d"
  for f in "$d"/*.ndjson; do
    legn=$((legn+1))
    rel="${f#"$CORPUS"/}"
    m="$(mini_verdict "$f")"
    n="$(nanoda_verdict "$f")"
    if [[ "$m" == crash* || "$n" == crash* ]]; then
      tag="CRASH"; differ=$((differ+1))
      FAILURES+=("$rel: mini=$m nanoda=$n — a crash is not a verdict")
    elif [[ "$m" == "$n" ]]; then
      tag=AGREE; agree=$((agree+1))
    elif [[ "$m" == out-of-scope ]]; then
      tag="out-of-scope(declared axiom)"; oos=$((oos+1))
      NAMED+=("out-of-scope $rel: mini declines a declared axiom (MINI-DESIGN.md §0.6); nanoda says $n")
    elif [[ "$m" == accept || "$n" == accept ]]; then
      tag="DIFFER(acceptance)"; differ=$((differ+1))
      FAILURES+=("$rel: mini=$m nanoda=$n — exactly one of them accepted the file")
    else
      tag="reason-only"; reason=$((reason+1))
      NAMED+=("reason-only   $rel: mini=$m nanoda=$n — neither accepted it")
    fi
    printf '%-42s %-12s %-12s %s\n' "$(basename "$f")" "$m" "$n" "$tag"
  done
  LEGS+=("$leg $legn")
done

echo
# ── the count lines ─────────────────────────────────────────────────────────
# **One per leg, and then the total.** The total alone was a floor a single
# healthy leg could satisfy on its own: `good/tutorial` is ~91 of the ~133
# files, so a `bad/tutorial` that expanded to nothing under `nullglob` — the
# directory emptied, re-fetched wrong, or the `*.ndjson` suffix changed — left
# `(of 91)`, a number comfortably over zero, with the entire negative half of
# the comparison missing. Nothing in the output said so, because a leg that
# contributes nothing to a sum looks exactly like a leg that contributed no
# divergences.
#
# So each leg prints its own count and floors it here, and
# `ci/check-mini-vs-nanoda.sh` re-checks both floors against these lines — the
# harness cannot re-derive them, and a floor only the producer enforces is a
# floor that leaves with the producer.
for l in "${LEGS[@]}"; do echo "mini-vs-nanoda leg ${l% *}: ${l##* } files"; done
echo "mini-vs-nanoda: $agree agree, $differ diverged, $oos out-of-scope, $reason reason-only (of $((agree+differ+oos+reason)))"
if ((${#NAMED[@]})); then printf '  %s\n' "${NAMED[@]}"; fi
empty=0
for l in "${LEGS[@]}"; do
  (( ${l##* } == 0 )) || continue
  echo "empty corpus leg: ${l% *} matched no *.ndjson under $CORPUS" >&2
  empty=1
done
if (( empty )); then
  echo "A leg that compared nothing cannot agree; the total above is one leg's." >&2
  exit 2
fi
if ((differ)); then
  printf '  FAIL   %s\n' "${FAILURES[@]}"
  echo "$differ acceptance divergence(s)/crash(es)" >&2
  exit 1
fi
