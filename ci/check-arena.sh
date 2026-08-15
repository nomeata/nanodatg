#!/usr/bin/env bash
# The Lean Kernel Arena corpus, as a CI step. `scripts/arena.sh` has been a real
# pass/fail gate since 2026-07-30 and nothing in `ci/check.sh` ran it.
#
#   good/**  must be ACCEPTED
#   bad/**   must be REJECTED, unless waived in `scripts/arena-accept.txt`
#
# The ratchet, the four cells, and why a stale waiver *fails* are argued in
# `scripts/arena.sh`'s header — that is where the policy lives; this file is the
# harness around it.
#
# # What it does when it cannot run
#
# `vendor/arena-tests` is gitignored (17 MB, 12 MB of it performance data) and
# is fetched per `README.md`:
#
#     mkdir -p vendor/arena-tests
#     curl -sSL https://arena.lean-lang.org/lean-arena-tests.tar.gz \
#       | tar xz -C vendor/arena-tests
#
# Without it this exits **77**, which `ci/check.sh` prints as `SKIP` and repeats
# by name in its summary. A skipped step is not a passed one. Same for a machine
# with no `cargo`. Note the ordering: the corpus is checked *before* the release
# build, so a machine without the corpus does not pay 60 s to discover it.
#
# # Counting what executed
#
# `arena.sh` prints `(of N)` and this **fails on N = 0**. Exit status alone
# would accept a run that iterated over nothing — which is precisely how this
# corpus went un-run for a month, and precisely the failure `ci/check.sh`'s
# whole SKIP-is-not-PASS design exists to make impossible. `--self-test` proves
# the guard and all four ratchet cells against a synthetic five-file corpus and
# a fake checker; it needs neither the corpus nor a toolchain, so it runs on
# every machine even where the step above SKIPs. `ci/test-boundary.sh` and
# `ci/check-modelgen.sh --self-test` are the same idea.
#
# # Cost
#
# Measured 2026-08-08, `CARGO_BUILD_JOBS=2`:
#
#   release build   ~60 s cold, ~0.02 s warm
#   154-file run    ~4 s (init-prelude's 2059 declarations are under a second)
#   --self-test     ~1 s, and needs neither corpus nor toolchain
#
# Those shares were taken against a `ci/check.sh` of ~45 min — of which
# `mini/tests/nested.rs` alone was ~10 min in each of three profiles — giving
# **~2.4% cold and ~0.2% warm**. The script is now **986 s measured**
# (2026-08-09) because the two feature sweeps are `-p nanoda_lib` and no longer
# re-run `mini`, so the shares are nearer 6.5%/0.6%; it still goes in the
# ordinary run and still needs no special placement.
#
# The build is the whole cost, and it is a cost only because the release
# profile (`lto = true`, `opt-level = 3`) is a *third* profile: `ci/check.sh`
# otherwise builds only `dev` and `test`. Nothing else here needs it, so it
# does not amortise.
#
# `perf/` stays excluded, and the reason is memory rather than time: the three
# files are only 12 s more and all three pass today, but `good/perf/app-lam`
# peaks at **3.6 GB RSS** on its own. This machine kills the whole user session
# past ~50 GB across all seats, and a 3.6 GB spike inside a 45-minute run that
# is already building three cargo profiles is not worth three files. Run
# `scripts/arena.sh --include-perf` by hand when that is what you want.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

fails=0

# Run something that prints an `arena:` summary line, and require the line to
# exist and to have counted a nonzero number of files.
run_corpus() {
  local name="$1"; shift
  local out rc n
  out="$( "$@" 2>&1 )"; rc=$?
  printf '%s\n' "$out"
  if (( rc )); then
    echo "  $name failed (exit $rc)" >&2
    fails=$((fails+1))
    return 1
  fi
  n="$(printf '%s\n' "$out" | sed -nE 's/^arena: .*\(of ([0-9]+)\)$/\1/p' | tail -1)"
  if [[ -z "$n" ]]; then
    echo "  BROKEN: $name exited 0 without reporting a file count" >&2
    fails=$((fails+1))
    return 1
  elif (( n == 0 )); then
    echo "  BROKEN: $name ran 0 corpus files" >&2
    fails=$((fails+1))
    return 1
  fi
  LAST_N="$n"
  echo "  $name: $n files"
}

# ── A floor per leg, because the two legs are not interchangeable ────────────
# Task #137: "one counter lets a healthy leg hide a dead one." `scripts/arena.sh`
# fuses `good/` and `bad/` into a single `find` and reports one total, and the
# guard above floors only that total — so an empty `bad/` behind a healthy
# `good/` passes, on a script whose own header says "The `bad` half is the part
# that matters." A checker that accepts everything passes `good/` trivially;
# `bad/` is the entire negative coverage of this step.
#
# So each leg is counted here and required to be non-empty, and their sum is
# required to equal what the run reported. The equality is the part that makes
# this a check on what *executed* rather than on what is on disk: a leg present
# but skipped by the runner changes the total without changing the file counts.
#
# `perf/` is excluded to match `scripts/arena.sh`, which skips it unless
# `--include-perf` — see this file's header for why (3.6 GB RSS on one file).
ARENA_LEGS="${ARENA_LEGS:-good bad}"
check_legs() { # check_legs <corpus> <reported-total>
  local c="$1" reported="$2" sum=0 n leg rc=0
  for leg in $ARENA_LEGS; do
    n=$(find "$c/$leg" -name '*.ndjson' 2>/dev/null | grep -cv '/perf/')
    if (( n == 0 )); then
      echo "  BROKEN: the \`$leg\` leg holds 0 export files at $c/$leg." >&2
      echo "          The total above is the other leg's alone. \`bad/\` is the" >&2
      echo "          negative coverage of this step; a checker that accepts" >&2
      echo "          everything passes \`good/\` without it." >&2
      rc=1
    else
      echo "  leg $leg: $n files"
    fi
    sum=$((sum+n))
  done
  if (( rc == 0 && sum != reported )); then
    echo "  BROKEN: the run counted $reported file(s) but the legs hold $sum." >&2
    echo "          A leg is present on disk and was not run, or was run twice." >&2
    rc=1
  fi
  return $rc
}

# ── the self-test ───────────────────────────────────────────────────────────
# A synthetic corpus and a fake checker that accepts exactly the files whose
# *name* says ACCEPTME (it greps the config `arena.sh` hands it). Every cell of
# the ratchet table is then a two-line fixture. `ARENA_BIN`, `ARENA_CORPUS` and
# `ARENA_ACCEPT_LIST` are the seams; they exist for this.
if [[ "${1:-}" == "--self-test" ]]; then
  bad=0
  TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

  cat > "$TMP/fakebin" <<'EOF'
#!/usr/bin/env bash
# Accept iff the export path the config names says ACCEPTME.
grep -q ACCEPTME "$1" && exit 0
echo "type mismatch at <fake>" >&2
exit 1
EOF
  chmod +x "$TMP/fakebin"

  # corpus <dir> <relpath>...
  corpus() {
    local d="$TMP/$1"; shift
    rm -rf "$d"
    local p
    for p in "$@"; do mkdir -p "$d/$(dirname "$p")"; echo '{}' > "$d/$p"; done
    mkdir -p "$d/good" "$d/bad"
    printf '%s' "$d"
  }
  list() { local f="$TMP/$1"; shift; printf '%s\n' "$@" > "$f"; printf '%s' "$f"; }

  # cell <expectation> <name> <corpus dir> <accept-list file>
  cell() {
    local want="$1" name="$2" c="$3" l="$4"
    local out rc
    out="$(ARENA_CORPUS="$c" ARENA_BIN="$TMP/fakebin" ARENA_ACCEPT_LIST="$l" \
             "$ROOT/scripts/arena.sh" 2>&1)"; rc=$?
    if [[ "$want" == pass && $rc -ne 0 ]] || [[ "$want" == fail && $rc -eq 0 ]]; then
      echo "SELF-TEST FAILED: expected a $want, got exit $rc — $name" >&2
      printf '%s\n' "$out" | sed 's/^/    /' >&2
      bad=1
    else
      echo "  ok ($want): $name"
    fi
  }

  # The baseline both `bad/` cells vary: one good file we accept, one bad file
  # we reject, no waivers. If this does not pass, nothing below means anything.
  BASE="$(corpus base good/ACCEPTME-fine.ndjson bad/wrong.ndjson)"
  EMPTY="$(list empty.txt '')"
  cell pass "cell 4 — a bad/ file we reject, not on the list" "$BASE" "$EMPTY"

  # cell 1: on the list, accepted → waived, no failure.
  C1="$(corpus c1 good/ACCEPTME-fine.ndjson bad/wrong.ndjson bad/ACCEPTME-known.ndjson)"
  L1="$(list l1.txt 'bad/ACCEPTME-known.ndjson # known: the level lie the mono pass erases')"
  cell pass "cell 1 — a bad/ file on the list, accepted" "$C1" "$L1"
  # …and it must actually say so, not quietly count it as matched.
  if ! ARENA_CORPUS="$C1" ARENA_BIN="$TMP/fakebin" ARENA_ACCEPT_LIST="$L1" \
       "$ROOT/scripts/arena.sh" 2>&1 | grep -q '1 waived'; then
    echo "SELF-TEST FAILED: cell 1 did not report the waiver" >&2; bad=1
  else
    echo "  ok: cell 1 names the waiver in the summary"
  fi

  # cell 2: the same file, no longer on the list → a lost rejection.
  cell fail "cell 2 — a bad/ file we accept that is NOT on the list" "$C1" "$EMPTY"

  # cell 3: on the list, but we reject it → the entry is stale.
  L3="$(list l3.txt 'bad/wrong.ndjson # stale on purpose')"
  cell fail "cell 3 — a bad/ file on the list that we reject" "$BASE" "$L3"

  # An entry naming nothing at all is stale too, and a full run must say so.
  L5="$(list l5.txt 'bad/ghost.ndjson # names a file that is not there')"
  cell fail "an accept-list entry matching no file in a full run" "$BASE" "$L5"

  # good/ is not waivable and must not be weakened: rejecting a good file fails,
  # and an attempt to waive one is refused outright.
  CG="$(corpus cg good/ACCEPTME-fine.ndjson good/refused.ndjson bad/wrong.ndjson)"
  cell fail "a good/ file we reject" "$CG" "$EMPTY"
  LG="$(list lg.txt 'good/refused.ndjson # waiving a good file')"
  cell fail "an accept-list entry under good/" "$CG" "$LG"

  # A waiver without a reason is refused: an unjustified entry is how a ratchet
  # decays into a blanket rule one line at a time.
  LN="$(list ln.txt 'bad/ACCEPTME-known.ndjson')"
  cell fail "an accept-list entry with no reason" "$C1" "$LN"

  # …and the count guard, which is the whole reason this file counts anything.
  fails=0
  EMPTYC="$(corpus emptyc)"
  if run_corpus "empty corpus" env ARENA_CORPUS="$EMPTYC" ARENA_BIN="$TMP/fakebin" \
       ARENA_ACCEPT_LIST="$EMPTY" "$ROOT/scripts/arena.sh" >/dev/null 2>&1; then
    echo "SELF-TEST FAILED: a corpus of 0 files was accepted" >&2; bad=1
  elif (( fails != 1 )); then
    echo "SELF-TEST FAILED: a corpus of 0 files did not count a failure" >&2; bad=1
  else
    echo "  ok: a corpus of 0 files is BROKEN, not PASS"
  fi
  fails=0
  if run_corpus "no summary" echo "done" >/dev/null 2>&1; then
    echo "SELF-TEST FAILED: a run reporting no count was accepted" >&2; bad=1
  else
    echo "  ok: a run that prints no summary line is BROKEN"
  fi
  fails=0
  if run_corpus "real count" echo "arena: 152 matched, 0 mismatched, 2 declined, 0 waived (of 154)" \
       >/dev/null && (( fails == 0 )); then
    echo "  ok: a real count is accepted"
  else
    echo "SELF-TEST FAILED: a real count was rejected" >&2; bad=1
  fi

  # ── the per-leg floor ─────────────────────────────────────────────────────
  # The cell that matters is the second: a healthy `good/` and an empty `bad/`
  # is precisely what the single total cannot see. Falsifier: delete the
  # `(( n == 0 ))` branch of `check_legs` and it goes green, because the sum
  # still equals the reported total when the runner also saw no `bad/` files.
  LEGOK="$(corpus legok good/a.ndjson good/b.ndjson bad/c.ndjson)"
  if check_legs "$LEGOK" 3 >/dev/null 2>&1; then
    echo "  ok: two non-empty legs summing to the reported total pass"
  else
    echo "SELF-TEST FAILED: a healthy two-leg corpus was rejected" >&2; bad=1
  fi

  LEGBAD="$(corpus legbad good/a.ndjson good/b.ndjson)"
  if check_legs "$LEGBAD" 2 >/dev/null 2>&1; then
    echo "SELF-TEST FAILED: an empty \`bad\` leg passed behind a healthy \`good\`" >&2; bad=1
  else
    echo "  ok: an empty \`bad\` leg is BROKEN even when the total is nonzero"
  fi

  # …and a leg that is on disk but was not run. The file counts are healthy;
  # only the equality catches it.
  if check_legs "$LEGOK" 2 >/dev/null 2>&1; then
    echo "SELF-TEST FAILED: a leg present but unrun was accepted" >&2; bad=1
  else
    echo "  ok: a total that does not match the legs on disk is BROKEN"
  fi

  echo
  if (( bad )); then echo "arena self-test FAILED" >&2; exit 1; fi
  echo "arena self-test OK"
  exit 0
fi

# ── the real thing ──────────────────────────────────────────────────────────
# `vendor/` is gitignored, so a `git worktree` has no corpus at `$ROOT` even on
# a machine that has one — which is every seat on this project. `corpus-dir.sh`
# falls back to the main checkout; see its header.
CORPUS="${ARENA_CORPUS:-$("$ROOT/ci/corpus-dir.sh")}"
if [[ ! -d "$CORPUS/good" || ! -d "$CORPUS/bad" ]]; then
  echo "  NOTICE: no arena corpus at $CORPUS." >&2
  echo "  It is gitignored for size. README.md \"Corpus tests\":" >&2
  echo "    mkdir -p vendor/arena-tests && curl -sSL \\" >&2
  echo "      https://arena.lean-lang.org/lean-arena-tests.tar.gz | tar xz -C vendor/arena-tests" >&2
  exit 77
fi
if ! command -v cargo >/dev/null; then
  echo "  NOTICE: no \`cargo\` on PATH; the release checker cannot be built." >&2
  exit 77
fi

# The release profile — `lto = true`, `opt-level = 3` — is not built by any
# other step, so this is a build and not a no-op the first time. It is part of
# the check: `arena.sh` exits 2 rather than 0 when the binary is missing, but
# exit 2 is a FAIL here and not a SKIP, because a workspace that does not build
# is a red and not an absence.
echo "building the release checker (a third profile; ~60 s cold, ~0 s warm)"
if ! ( cd "$ROOT" && cargo build --release -p nanoda_lib --bin nanoda_bin ); then
  echo "the release checker does not build" >&2
  exit 1
fi

# `ARENA_CORPUS` explicitly: `scripts/arena.sh` defaults to its *own*
# `$ROOT/vendor/arena-tests`, so without this it would look somewhere else than
# the directory checked above the moment the two differ — which is exactly what
# a worktree makes happen.
LAST_N=0
if run_corpus "arena corpus" env ARENA_CORPUS="$CORPUS" "$ROOT/scripts/arena.sh"; then
  check_legs "$CORPUS" "$LAST_N" || fails=$((fails+1))
fi

echo
if (( fails )); then
  echo "the arena corpus is red" >&2
  exit 1
fi
echo "arena corpus OK"
