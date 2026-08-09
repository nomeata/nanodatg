#!/usr/bin/env bash
# `mini` against `nanoda` over the arena corpus, as a CI step.
#
# `scripts/mini-vs-nanoda.sh` has been a real pass/fail gate — it exits 1 when
# exactly one of the two checkers accepts a file — and nothing in `ci/check.sh`
# ran it. That makes three: `modelgen` had no step, `monotest`'s 107 checks were
# entirely un-run, and this.
#
# The five outcomes, why a decline-against-reject is not a failure, and why
# there is **no waiver list** here when `scripts/arena.sh` has one, are argued in
# that script's header — the policy lives there and this file is the harness
# around it.
#
# # What this gate is for
#
# It is *not* "mini must accept exactly what nanoda accepts". The settled
# position is that `mini` may be more permissive than Lean's kernel, because the
# guarantee is the **certificate** and not acceptance fidelity — `kernel/` only
# ever mints valid theorems. So a divergence is not automatically a bug. What
# the gate buys is that every divergence is a **known and named** one: two rules
# name the tolerated classes (`out-of-scope`, `reason-only`), each run prints
# their population by file, and anything outside them fails.
#
# # What it does when it cannot run
#
# `vendor/arena-tests` is gitignored (17 MB) and is fetched per `README.md`:
#
#     mkdir -p vendor/arena-tests
#     curl -sSL https://arena.lean-lang.org/lean-arena-tests.tar.gz \
#       | tar xz -C vendor/arena-tests
#
# Without it this exits **77**, which `ci/check.sh` prints as `SKIP` and repeats
# by name in its summary. A skipped step is not a passed one. Same for a machine
# with no `cargo`. The corpus is checked *before* the build, so a machine with no
# corpus does not pay two minutes to find out.
#
# A build that **fails** is a FAIL and not a SKIP: a workspace that does not
# build is a red, not an absence.
#
# # Counting what executed
#
# `mini-vs-nanoda.sh` prints `(of N)` and this **fails on N = 0**. Exit status
# alone would accept a run that compared nothing — and until today that script
# exited **0** when the corpus was missing, which is exactly that failure with a
# green tick on it. `--self-test` proves the count guard and all six outcome
# cells against a synthetic corpus and a pair of fake checkers; it needs neither
# the corpus nor a toolchain, so it runs on every machine even where the step
# above SKIPs. `ci/check-arena.sh --self-test` and `ci/check-modelgen.sh
# --self-test` are the same idea.
#
# # Cost
#
# Measured 2026-08-08 in an empty worktree, `CARGO_BUILD_JOBS=3`:
#
#   release build   ~118 s for both binaries and every dependency from nothing,
#                   ~0 s warm. Of that ~79 s is `mini`'s own crate plus `lto`,
#                   which is the **marginal** cost over `ci/check-arena.sh` —
#                   the two steps share the release profile and no other step
#                   builds it, so whichever runs first pays and the second does
#                   not. They are adjacent for that reason.
#   133-file run    ~30 s, repeatable to the second: 266 process launches at
#                   ~0.11 s each, and the per-file cost is startup and parse
#                   rather than checking.
#   --self-test     ~1 s, and needs neither corpus nor toolchain.
#
# Those shares were taken against a `ci/check.sh` of ~45 min: **~5.5 % cold and
# ~1.2 % warm**, or ~4 % cold counting only the marginal build. `check-arena.sh`
# came in at ~2.4 %/~0.2 %, so this is the more expensive of the two but not by
# an order: it needs **no special placement and no gate**. The script has since
# been measured at **986 s** (2026-08-09), which roughly triples both shares
# without changing that conclusion. It goes after the arena steps and before the
# `cargo test` steps, so a corpus divergence is reported before the ~13 minutes
# of tests rather than after them.
#
# (The 123 s previously recorded for the run does not reproduce; two
# back-to-back runs measured 30 s each on a machine under load 11, with the
# corpus in page cache. The earlier figure most likely included a build.)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

fails=0

# Run something that prints a `mini-vs-nanoda:` summary line, and require the
# line to exist and to have compared a nonzero number of files.
run_compare() {
  local name="$1"; shift
  local out rc n
  out="$( "$@" 2>&1 )"; rc=$?
  printf '%s\n' "$out"
  if (( rc )); then
    echo "  $name failed (exit $rc)" >&2
    fails=$((fails+1))
    return 1
  fi
  n="$(printf '%s\n' "$out" | sed -nE 's/^mini-vs-nanoda: .*\(of ([0-9]+)\)$/\1/p' | tail -1)"
  if [[ -z "$n" ]]; then
    echo "  BROKEN: $name exited 0 without reporting a file count" >&2
    fails=$((fails+1))
    return 1
  elif (( n == 0 )); then
    echo "  BROKEN: $name compared 0 corpus files" >&2
    fails=$((fails+1))
    return 1
  fi
  echo "  $name: $n files"
}

# ── the self-test ───────────────────────────────────────────────────────────
# A synthetic corpus and two fake checkers that read their verdict out of the
# *file name*: `M<verdict>` for mini's column and `N<verdict>` for nanoda's, so
# one three-token name is one cell of the table above. `MVN_CORPUS`, `MVN_MINI`,
# `MVN_NANODA` and `MVN_TIMEOUT` are the seams; they exist for this.
if [[ "${1:-}" == "--self-test" ]]; then
  bad=0
  TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

  # mini is handed `--no-modelgen --acceptance-only <path>`; the path is last.
  cat > "$TMP/fakemini" <<'EOF'
#!/usr/bin/env bash
f="${*: -1}"
case "$f" in
  *MACCEPT*)  exit 0 ;;
  *MREJECT*)  echo "type mismatch at <fake>"; exit 1 ;;
  *MAXIOM*)   echo "declined: non-standard axiom: Fake.ax"; exit 2 ;;
  *MDECLINE*) echo "declined: mutual inductive"; exit 2 ;;
  *MPANIC*)   echo "thread 'main' panicked"; exit 101 ;;
  *MHANG*)    sleep 30; exit 0 ;;
esac
echo "fakemini: no verdict token in $f" >&2; exit 9
EOF
  # nanoda is handed a config file naming the export; it greps it, as the real
  # one parses it.
  cat > "$TMP/fakenanoda" <<'EOF'
#!/usr/bin/env bash
f="$(cat "$1")"
case "$f" in
  *NACCEPT*)  exit 0 ;;
  *NREJECT*)  echo "type mismatch at <fake>"; exit 1 ;;
  *NDECLINE*) echo "Declined: Back-refs must be continuous"; exit 1 ;;
  *NPANIC*)   echo "signal"; exit 134 ;;
esac
echo "fakenanoda: no verdict token" >&2; exit 9
EOF
  chmod +x "$TMP/fakemini" "$TMP/fakenanoda"

  # corpus <dir> <relpath>... — the script only looks at good/tutorial and
  # bad/tutorial, so both always exist even when empty.
  corpus() {
    local d="$TMP/$1"; shift
    rm -rf "$d"; mkdir -p "$d/good/tutorial" "$d/bad/tutorial"
    local p
    for p in "$@"; do mkdir -p "$d/$(dirname "$p")"; echo '{}' > "$d/$p"; done
    printf '%s' "$d"
  }

  # cell <pass|fail> <name> <corpus dir> [extra env...]
  cell() {
    local want="$1" name="$2" c="$3"; shift 3
    local out rc
    out="$(env MVN_CORPUS="$c" MVN_MINI="$TMP/fakemini" MVN_NANODA="$TMP/fakenanoda" \
             "$@" "$ROOT/scripts/mini-vs-nanoda.sh" 2>&1)"; rc=$?
    if [[ "$want" == pass && $rc -ne 0 ]] || [[ "$want" == fail && $rc -eq 0 ]]; then
      echo "SELF-TEST FAILED: expected a $want, got exit $rc — $name" >&2
      printf '%s\n' "$out" | sed 's/^/    /' >&2
      bad=1
    else
      echo "  ok ($want): $name"
    fi
  }

  # The baseline the rest vary: one file both accept, one both reject. If this
  # does not pass, nothing below means anything.
  BASE="$(corpus base good/tutorial/MACCEPT-NACCEPT-fine.ndjson \
                      bad/tutorial/MREJECT-NREJECT-caught.ndjson)"
  cell pass "AGREE — both accept, both reject" "$BASE"

  # The two acceptance divergences, one in each direction. These are the whole
  # point of the gate.
  D1="$(corpus d1 good/tutorial/MACCEPT-NACCEPT-fine.ndjson \
                  bad/tutorial/MACCEPT-NREJECT-lost.ndjson)"
  cell fail "mini accepts what nanoda rejects" "$D1"
  D2="$(corpus d2 good/tutorial/MREJECT-NACCEPT-refused.ndjson)"
  cell fail "mini rejects what nanoda accepts" "$D2"

  # The two tolerated classes. Both must pass *and* be named — a tolerated
  # outcome nobody can see in the summary is a silent one, and the argument for
  # having no waiver file rests on these rows existing.
  OOS="$(corpus oos good/tutorial/MAXIOM-NACCEPT-declared.ndjson)"
  cell pass "out-of-scope — mini declines a declared axiom, nanoda accepts" "$OOS"
  RO="$(corpus ro bad/tutorial/MDECLINE-NREJECT-both-no.ndjson)"
  cell pass "reason-only — neither accepted, different reason" "$RO"
  named() { # <corpus> <label>
    if ! MVN_CORPUS="$1" MVN_MINI="$TMP/fakemini" MVN_NANODA="$TMP/fakenanoda" \
         "$ROOT/scripts/mini-vs-nanoda.sh" 2>&1 | grep -q "^  $2 "; then
      echo "SELF-TEST FAILED: $2 was not named in the summary" >&2; bad=1
    else
      echo "  ok: $2 is named in the summary"
    fi
  }
  named "$OOS" out-of-scope
  named "$RO"  reason-only

  # A crash is not a verdict. Both directions, and the timeout, because the
  # `reason-only` bucket used to swallow all three.
  CP="$(corpus cp bad/tutorial/MPANIC-NREJECT-boom.ndjson)"
  cell fail "mini panics" "$CP"
  CN="$(corpus cn bad/tutorial/MREJECT-NPANIC-boom.ndjson)"
  cell fail "nanoda dies on a signal" "$CN"
  CH="$(corpus ch bad/tutorial/MHANG-NREJECT-slow.ndjson)"
  cell fail "mini exceeds MVN_TIMEOUT" "$CH" MVN_TIMEOUT=1

  # Not running is not passing. This is the defect that motivated the step: the
  # script exited 0 with no corpus at all.
  out="$(MVN_CORPUS="$TMP/nowhere" MVN_MINI="$TMP/fakemini" MVN_NANODA="$TMP/fakenanoda" \
           "$ROOT/scripts/mini-vs-nanoda.sh" 2>&1)"; rc=$?
  if (( rc == 0 )); then
    echo "SELF-TEST FAILED: a missing corpus exited 0" >&2; bad=1
  else
    echo "  ok: a missing corpus exits $rc, not 0"
  fi
  out="$(MVN_CORPUS="$BASE" MVN_MINI="$TMP/nosuchbin" MVN_NANODA="$TMP/fakenanoda" \
           "$ROOT/scripts/mini-vs-nanoda.sh" 2>&1)"; rc=$?
  if (( rc == 0 )); then
    echo "SELF-TEST FAILED: a missing checker binary exited 0" >&2; bad=1
  else
    echo "  ok: a missing checker binary exits $rc, not 0"
  fi

  # …and the count guard, which is the whole reason this file counts anything.
  # First against a real (if synthetic) run, because everything below feeds
  # `run_compare` canned strings and so cannot notice the day the two scripts
  # stop agreeing on the format of the line. The step itself cannot notice
  # either: on a machine with no corpus it SKIPs before reaching the parse.
  fails=0
  if run_compare "two-file corpus" env MVN_CORPUS="$BASE" MVN_MINI="$TMP/fakemini" \
       MVN_NANODA="$TMP/fakenanoda" "$ROOT/scripts/mini-vs-nanoda.sh" 2>/dev/null \
       | grep -q '^  two-file corpus: 2 files$' && (( fails == 0 )); then
    echo "  ok: the harness parses the count the script actually prints"
  else
    echo "SELF-TEST FAILED: the summary line and the parser have drifted apart" >&2; bad=1
  fi
  fails=0
  EMPTYC="$(corpus emptyc)"
  if run_compare "empty corpus" env MVN_CORPUS="$EMPTYC" MVN_MINI="$TMP/fakemini" \
       MVN_NANODA="$TMP/fakenanoda" "$ROOT/scripts/mini-vs-nanoda.sh" >/dev/null 2>&1; then
    echo "SELF-TEST FAILED: a corpus of 0 files was accepted" >&2; bad=1
  elif (( fails != 1 )); then
    echo "SELF-TEST FAILED: a corpus of 0 files did not count a failure" >&2; bad=1
  else
    echo "  ok: a corpus of 0 files is BROKEN, not PASS"
  fi
  fails=0
  if run_compare "no summary" echo "done" >/dev/null 2>&1; then
    echo "SELF-TEST FAILED: a run reporting no count was accepted" >&2; bad=1
  else
    echo "  ok: a run that prints no summary line is BROKEN"
  fi
  fails=0
  if run_compare "real count" \
       echo "mini-vs-nanoda: 130 agree, 0 diverged, 2 out-of-scope, 1 reason-only (of 133)" \
       >/dev/null && (( fails == 0 )); then
    echo "  ok: a real count is accepted"
  else
    echo "SELF-TEST FAILED: a real count was rejected" >&2; bad=1
  fi

  echo
  if (( bad )); then echo "mini-vs-nanoda self-test FAILED" >&2; exit 1; fi
  echo "mini-vs-nanoda self-test OK"
  exit 0
fi

# ── the real thing ──────────────────────────────────────────────────────────
CORPUS="${MVN_CORPUS:-$ROOT/vendor/arena-tests}"
if [[ ! -d "$CORPUS/good/tutorial" || ! -d "$CORPUS/bad/tutorial" ]]; then
  echo "  NOTICE: no arena corpus at $CORPUS." >&2
  echo "  It is gitignored for size. README.md \"Corpus tests\":" >&2
  echo "    mkdir -p vendor/arena-tests && curl -sSL \\" >&2
  echo "      https://arena.lean-lang.org/lean-arena-tests.tar.gz | tar xz -C vendor/arena-tests" >&2
  exit 77
fi
if ! command -v cargo >/dev/null; then
  echo "  NOTICE: no \`cargo\` on PATH; neither checker can be built." >&2
  exit 77
fi

# The release profile — `lto = true`, `opt-level = 3` — is shared with
# `ci/check-arena.sh` and built by no other step, so one of the two pays for it
# and the other does not. Building here rather than inside
# `scripts/mini-vs-nanoda.sh` keeps the build's output and its failure visible as
# a FAIL, and lets the run below be handed both binaries by path — which is also
# the seam the self-test uses.
echo "building both checkers in release (shared with the arena step; ~2 min cold, ~0 s warm)"
if ! ( cd "$ROOT" && cargo build --release -p mini -p nanoda_lib ); then
  echo "the release checkers do not build" >&2
  exit 1
fi

run_compare "mini vs nanoda" env MVN_CORPUS="$CORPUS" \
  MVN_MINI="$ROOT/target/release/mini" MVN_NANODA="$ROOT/target/release/nanoda_bin" \
  "$ROOT/scripts/mini-vs-nanoda.sh"

echo
if (( fails )); then
  echo "mini and nanoda diverge on acceptance" >&2
  exit 1
fi
echo "mini vs nanoda OK"
