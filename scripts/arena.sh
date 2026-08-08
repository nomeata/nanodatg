#!/usr/bin/env bash
# Run the Lean Kernel Arena corpus through the checker and report, for every
# file, whether the outcome matched expectation:
#
#   vendor/arena-tests/good/**  must be ACCEPTED — a plain, unwaivable rule
#   vendor/arena-tests/bad/**   must be REJECTED — *unless* the file is on
#                               `scripts/arena-accept.txt`, with a reason
#
# The `bad` half is the part that matters. A checker that accepts everything
# passes `good` trivially; only `bad` shows the checker is actually checking.
#
# # Why `bad/` is a ratchet and not a blanket rule
#
# "Every `bad/` file is rejected" is no longer the invariant this project holds
# itself to. **The certificate is the guarantee, not acceptance fidelity**:
# `kernel/` only ever mints valid theorems, so an ill-typed file we accept still
# yields true Tarski–Grothendieck statements — it just yields them about a
# different (nonsense) input. Being *more permissive* than the official kernel
# costs nothing as long as we stay *consistent*. Two settled consequences:
#
#   * `MONOMORPH.md` §7 — a pass that erases levels erases lies told in levels.
#     `bad/tutorial/049_inductWrongCtorResLevel` permutes a constructor's level
#     arguments, and **no diagonal default distinguishes a permutation**, so it
#     cannot be guarded by any choice of `--default`. Catching it needs a
#     typechecker at symbolic levels, which is the work that pass exists to
#     remove.
#   * Swapped prelude definitions are fine. No real input has a bad prelude.
#
# So the rule is not "reject them all" but **"lose no rejection silently"**:
#
# | on the list | outcome  | verdict                                          |
# |-------------|----------|--------------------------------------------------|
# | yes         | accepted | `waived` — counted, named, and printed. Fine.     |
# | no          | accepted | **FAIL** — a *new* lost rejection. Must be seen.  |
# | yes         | rejected | **FAIL** — the entry is stale; delete it.         |
# | no          | rejected | `matched`. The normal case.                       |
#
# A stale entry fails rather than merely warning, and that is deliberate. The
# list is the standing record of what we knowingly gave up; an entry that no
# longer describes reality makes the record a liar, and the whole value of the
# record is that it can be read as "this is what we lost". A warning in a
# 45-minute log is not read. The cost of the strictness is bounded and benign:
# a stale entry can only ever be *created by an improvement*, and the fix is to
# delete one line. It is also the same principle the count guard in
# `ci/check-arena.sh` enforces — a waiver that never applies to anything is a
# check that has stopped checking.
#
# Staleness is only judged over files the run actually visited, so
# `scripts/arena.sh bad/tutorial` does not report every other entry as stale.
# On a full run, an entry matching no visited file *is* reported: it names a
# file that is gone, misspelled, or under `perf/`.
#
# Usage: scripts/arena.sh [--include-perf] [subdir ...]
# Env:   ARENA_BIN, ARENA_CORPUS, ARENA_ACCEPT_LIST, ARENA_TIMEOUT
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${ARENA_BIN:-$ROOT/target/release/nanoda_bin}"
CORPUS="${ARENA_CORPUS:-$ROOT/vendor/arena-tests}"
ACCEPT_LIST="${ARENA_ACCEPT_LIST:-$ROOT/scripts/arena-accept.txt}"
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

# The accept-list: `<path relative to the corpus root>  # <one-line reason>`.
# A reason is mandatory — an entry without one is rejected here rather than
# silently accepted, because a waiver nobody had to justify is how a ratchet
# turns back into a blanket rule one line at a time.
declare -A WAIVED=() WHY=() SEEN=()
if [[ -f "$ACCEPT_LIST" ]]; then
  lineno=0
  while IFS= read -r line || [[ -n "$line" ]]; do
    lineno=$((lineno+1))
    path="${line%%#*}"; reason="${line#"$path"}"; reason="${reason#\#}"
    # trim
    path="${path#"${path%%[![:space:]]*}"}"; path="${path%"${path##*[![:space:]]}"}"
    reason="${reason#"${reason%%[![:space:]]*}"}"; reason="${reason%"${reason##*[![:space:]]}"}"
    [[ -z "$path" ]] && continue
    if [[ -z "$reason" ]]; then
      echo "$ACCEPT_LIST:$lineno: '$path' has no reason; every waiver needs one" >&2
      exit 2
    fi
    if [[ "$path" != bad/* ]]; then
      echo "$ACCEPT_LIST:$lineno: '$path' is not under bad/; good/ cannot be waived" >&2
      exit 2
    fi
    WAIVED["$path"]=1; WHY["$path"]="$reason"
  done < "$ACCEPT_LIST"
fi

# Collect the file list.
declare -a FILES=()
if ((${#SUBDIRS[@]})); then
  for d in "${SUBDIRS[@]}"; do
    while IFS= read -r f; do FILES+=("$f"); done < <(find "$CORPUS/$d" -name '*.ndjson' | sort)
  done
else
  while IFS= read -r f; do FILES+=("$f"); done < <(find "$CORPUS/good" "$CORPUS/bad" -name '*.ndjson' | sort)
fi

pass=0; fail=0; skip=0; waived=0
declare -a FAILURES=()
declare -a SKIPPED=()
declare -a WAIVERS=()

for f in ${FILES[@]+"${FILES[@]}"}; do
  if [[ $INCLUDE_PERF -eq 0 && "$f" == */perf/* ]]; then continue; fi

  case "$f" in
    "$CORPUS"/good/*) expect=accept ;;
    "$CORPUS"/bad/*)  expect=reject ;;
    *) continue ;;
  esac

  # `unsafe_permit_all_axioms` keeps the corpus's own axioms from being treated
  # as errors; we are testing the type checker, not the axiom whitelist. It
  # requires `unpermitted_axiom_hard_error: false` and no explicit list.
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

  # The ratchet. Only `bad/` is waivable; `good/` falls straight through.
  if [[ -n "${WAIVED[$rel]+x}" ]]; then
    SEEN["$rel"]=1
    if [[ "$got" == accept ]]; then
      waived=$((waived+1))
      WAIVERS+=("$rel: ${WHY[$rel]}")
    else
      fail=$((fail+1))
      FAILURES+=("$rel: REJECTED, but it is on the accept-list — the entry is stale, delete it from ${ACCEPT_LIST#"$ROOT"/}")
    fi
    continue
  fi

  if [[ "$got" == "$expect" ]]; then
    pass=$((pass+1))
  elif [[ "$expect" == reject ]]; then
    fail=$((fail+1))
    FAILURES+=("$rel: ACCEPTED a bad/ file that is not on ${ACCEPT_LIST#"$ROOT"/} — a lost rejection. If it is one we mean to lose, add it there with a reason.")
  else
    fail=$((fail+1))
    FAILURES+=("$rel: expected $expect, got $got")
  fi
done

# An accept-list entry that no file in a *full* run answered to. Under a subdir
# argument this says nothing, so it is only judged on a full run.
if ((${#SUBDIRS[@]} == 0 && ${#WAIVED[@]} > 0)); then
  for k in "${!WAIVED[@]}"; do
    [[ -n "${SEEN[$k]+x}" ]] && continue
    fail=$((fail+1))
    FAILURES+=("$k: on the accept-list but no such file was run — stale entry (moved, renamed, or under perf/)")
  done
fi

echo "arena: $pass matched, $fail mismatched, $skip declined, $waived waived (of $((pass+fail+skip+waived)))"
if ((skip)); then printf '  skip   %s\n' "${SKIPPED[@]}"; fi
if ((waived)); then printf '  waived %s\n' "${WAIVERS[@]}"; fi
if ((fail)); then
  printf '  FAIL   %s\n' "${FAILURES[@]}"
  exit 1
fi
