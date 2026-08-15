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
# The *input* half of this step is reporting rather than enforcement;
# `ci/check-test-guards.sh` is the enforcement and needs no inputs, so it runs
# where this one SKIPs. The **feature-matrix half at the top of the script is
# enforcement**, exits 1, and runs before any input is looked at, so it runs on
# every machine.
#
# # Finding the corpus, and counting it
#
# "Absent" has to mean absent, and it did not. `vendor/` is gitignored, so a
# `git worktree` — which is how every seat on this project works — has no
# corpus at `$ROOT/vendor/arena-tests` even when the machine has one, and this
# script hard-coded that path twice. `ci/corpus-dir.sh` answers the question
# properly (main checkout via `git rev-parse --git-common-dir`), and the two
# self-test cells that needed a *present* corpus now build a synthetic one
# instead of borrowing the real one, so they hold on a machine that has none.
#
# The count uses `find -L`, because the corpus a worktree reaches is a symlink
# and `find` does not descend one named on its command line: measured, plain
# `find` said 0 where `find -L` said 157, and this step called BROKEN on a
# corpus the suites beside it were reading. Zero remains a hard failure — that
# is the guard, and two cells hold it down, one plain and one through a link.
#
# # The feature matrix (the top half)
#
# `ci/check.sh` runs the two feature variants over `-p nanoda_lib` rather than
# over the whole workspace, because `stepcount` is the checker's
# features and nothing else can observe them. The saving is two thirds of the
# heaviest thing in the run. What is checked here is the *premise*:
#
#   A. every feature the matrix names is declared by exactly one workspace
#      member, and that is the member the step selects;
#   B. no other member carries a `cfg(feature = …)` of its own, so no other
#      member's code can vary at all;
#   C. every suite hidden behind `#![cfg(feature = "X")]` lives in a package
#      the `--features X` step actually selects.
#
# A fourth leg — that no other member reaches the checker code the features
# *do* change — used to be a runtime assertion, `NANODATG_ASSERT_FEATURE_INERT`,
# because at module granularity every module in `checker/src` mentions
# `certify`. It was retired with the `tg` feature on 2026-08-15: it held up a
# matrix of *two* narrowed feature runs, and there is one left. See
# `checker/src/certify.rs`.
#
# **Leg C has no input on this tree.** Crate-level `#![cfg(feature = …)]` went
# with the `tg` feature, so the grep leg C runs matches zero files — measured,
# not assumed. That is not a fault: leg C guards against such a suite being
# *reintroduced* without a matching `--features` step. It is a fault to be
# unable to tell that state apart from having run, so each leg carries its own
# counter and leg C says which case it is in. See the per-leg counters below and
# task #137 (`83a95cf`, `ci/check-arena.sh`).

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# `vendor/` is gitignored, so a `git worktree` does not get the corpus and
# `$ROOT/vendor/arena-tests` is the wrong answer in the environment every seat
# on this project actually works in. `ci/corpus-dir.sh` falls back to the main
# checkout's copy; when there is none anywhere it echoes the local path anyway,
# so the "ABSENT" message below still names the path README.md tells you to
# unpack into. See that script's header.
CORPUS="${CORPUS_DIR:-$("$ROOT/ci/corpus-dir.sh")}"
MODELGEN="${MODELGEN_BIN:-$ROOT/modelgen/.lake/build/bin/modelgen}"
CHECK_SH="${CHECK_SH:-$ROOT/ci/check.sh}"
SCAN_DIRS="${SCAN_DIRS:-$ROOT/checker/tests}"
# One directory per workspace member, so the self-test can point the
# feature-matrix checks at a synthetic tree.
MEMBER_DIRS="${MEMBER_DIRS:-$ROOT/kernel $ROOT/derived $ROOT/checker}"

self_test() {
  TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
  local sfails=0
  expect() { # expect <rc> <name> [env...]
    local want="$1" name="$2"; shift 2
    local rc; env "$@" "$0" >/dev/null 2>&1; rc=$?
    if [[ $rc -eq $want ]]; then echo "  ok: $name (rc=$rc)"
    else echo "SELFTEST FAIL: $name wanted rc=$want, got $rc" >&2; env "$@" "$0" >&2; sfails=$((sfails+1)); fi
  }
  # An exit code cannot tell "leg C examined nothing" from "leg C examined
  # something and was happy" — both are 0 — which is why the defect this pins
  # survived a self-test that only ever read `$?`. These cells read the output.
  expect_says() { # expect_says <rc> <substring> <name> [env...]
    local want="$1" want_out="$2" name="$3"; shift 3
    local out rc
    out="$(env "$@" "$0" 2>&1)"; rc=$?
    if [[ $rc -eq $want ]] && grep -qF -- "$want_out" <<<"$out"; then
      echo "  ok: $name (rc=$rc)"
    else
      echo "SELFTEST FAIL: $name wanted rc=$want and output containing" >&2
      echo "               '$want_out', got rc=$rc and:" >&2
      printf '%s\n' "$out" >&2
      sfails=$((sfails+1))
    fi
  }
  echo "self-testing $0"
  # A synthetic corpus — one directory holding one export — and the two
  # symlinked shapes of it. Synthetic and not the real thing on purpose: this
  # block used to point the "present corpus" cells at
  # `$ROOT/vendor/arena-tests`, which is gitignored and therefore *absent* in
  # every `git worktree`, so on the machine every seat actually works on the
  # cell got a SKIP where it wanted a BROKEN and the self-test was 1 FAIL. A
  # self-test that only holds where the optional input happens to be installed
  # is the very thing this script exists to forbid.
  mkdir -p "$TMP/empty" "$TMP/corpus"
  : > "$TMP/corpus/x.ndjson"
  ln -s "$TMP/corpus" "$TMP/linked"
  ln -s "$TMP/empty"  "$TMP/linked-empty"
  # An absent input is a SKIP, not a pass and not a failure.
  expect 77 "an absent corpus SKIPs" CORPUS_DIR="$TMP/nope" MODELGEN_BIN="$TMP/nope"
  # A corpus that unpacked short is BROKEN, not a skip: the directory test that
  # every call site used to do would have called this one present.
  # `NANODATG_REQUIRE_CORPUS=1` is what makes this cell *about the count guard*:
  # without it the run also exits 1 down at the variable check, so the cell
  # passed with the count guard deleted and pinned nothing.
  expect 1  "a present-but-empty corpus is BROKEN" \
            CORPUS_DIR="$TMP/empty" MODELGEN_BIN="$TMP/nope" NANODATG_REQUIRE_CORPUS=1
  # The corpus is there but nothing required it — this is the state the whole
  # change exists to prevent, and it must not be reported as a pass.
  expect 1  "a corpus present with the variable unset is BROKEN" \
            CORPUS_DIR="$TMP/corpus" MODELGEN_BIN="$TMP/nope" NANODATG_REQUIRE_CORPUS=
  # A corpus reached through a symlink — the shape a worktree gets, and the one
  # `find` without `-L` reports as zero. Reaching 77 means it got past the
  # count guard and stopped only for the missing modelgen. Falsifier: drop the
  # `-L` from the count below and this cell returns 1.
  expect 77 "a symlinked corpus is counted, not reported empty" \
            CORPUS_DIR="$TMP/linked" MODELGEN_BIN="$TMP/nope" NANODATG_REQUIRE_CORPUS=1
  # …and `-L` must not have bought that by making the zero guard unfalsifiable:
  # a symlink to a genuinely empty corpus is still BROKEN.
  expect 1  "a symlink to an empty corpus is still BROKEN" \
            CORPUS_DIR="$TMP/linked-empty" MODELGEN_BIN="$TMP/nope" NANODATG_REQUIRE_CORPUS=1
  # The exit code alone would accept a link that yielded *some* wrong number, so
  # pin the count itself: through the link it must equal the count in the
  # directory the link points at.
  local nlink ndir
  count_of() {
    env CORPUS_DIR="$1" MODELGEN_BIN="$TMP/nope" NANODATG_REQUIRE_CORPUS=1 "$0" 2>/dev/null \
      | sed -nE 's/^  arena corpus: ([0-9]+) exports.*/\1/p'
  }
  nlink="$(count_of "$TMP/linked")"; ndir="$(count_of "$TMP/corpus")"
  if [[ "$nlink" == "$ndir" && "$nlink" == "1" ]]; then
    echo "  ok: the count through a symlink equals the count in the directory ($nlink)"
  else
    echo "SELFTEST FAIL: linked corpus counted '$nlink', directory counted '$ndir', wanted 1" >&2
    sfails=$((sfails+1))
  fi
  # …and the ci/check.sh grep.
  # Against the *real* member crates: `stepcount` is declared and this fake
  # `check.sh` runs no `--features` step at all, so the declared-but-unrun rule
  # must fire. (Until 2026-08-15 this cell named `tg`; that feature is gone —
  # see `checker/src/certify.rs` — and the rule it exercises is unchanged.)
  printf '#!/bin/sh\nstep "tests" cargo test --workspace\n' > "$TMP/no-feat.sh"
  expect 1  "a ci/check.sh with no --features step for a declared feature is BROKEN" \
            CHECK_SH="$TMP/no-feat.sh" CORPUS_DIR="$TMP/nope" MODELGEN_BIN="$TMP/nope"

  # ── the feature matrix ────────────────────────────────────────────────────
  # A synthetic two-member workspace: `feat` declares a feature and holds the
  # gated suite, `plain` declares none. Everything below varies one thing.
  member() { # member <name> <features…>
    local n="$1"; shift
    mkdir -p "$TMP/w/$n/src" "$TMP/w/$n/tests"
    { printf '[package]\nname = "%s"\n' "$n"
      if (( $# )); then printf '\n[features]\n'; printf '%s = []\n' "$@"; fi
      printf '\n[dependencies]\n'; } > "$TMP/w/$n/Cargo.toml"
    : > "$TMP/w/$n/src/lib.rs"
  }
  member feat gated
  member plain
  printf '#![cfg(feature = "gated")]\n' > "$TMP/w/feat/tests/gated_suite.rs"
  local WD="$TMP/w/feat $TMP/w/plain" SD="$TMP/w/feat/tests $TMP/w/plain/tests"
  local NOIN="CORPUS_DIR=$TMP/nope MODELGEN_BIN=$TMP/nope"

  # The healthy shape: a narrowed step that does select the package. This must
  # pass all three premises and go on to SKIP for want of inputs — if it does
  # not, every red below is red for the wrong reason.
  printf '#!/bin/sh\nstep "f" cargo test -p feat --features gated\n' > "$TMP/ok.sh"
  expect 77 "a narrowed step that selects the right package passes" \
            CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  # A. the step names the feature but selects the wrong package. This is the
  #    hole narrowing the matrix opens, and the old word-grep let it through.
  printf '#!/bin/sh\nstep "f" cargo test -p plain --features gated\n' > "$TMP/wrongpkg.sh"
  expect 1  "a --features step selecting the wrong package is BROKEN" \
            CHECK_SH="$TMP/wrongpkg.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  # …and --workspace with the declaring package excluded is the same hole.
  printf '#!/bin/sh\nstep "f" cargo test --workspace --exclude feat --features gated\n' \
    > "$TMP/excluded.sh"
  expect 1  "a --workspace step that excludes the declaring package is BROKEN" \
            CHECK_SH="$TMP/excluded.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  # …while plain --workspace still passes, so the check is not just banning -p.
  printf '#!/bin/sh\nstep "f" cargo test --workspace --features gated\n' > "$TMP/ws.sh"
  expect 77 "a --workspace --features step still passes" \
            CHECK_SH="$TMP/ws.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  # B. a crate the feature steps no longer build growing a cfg of its own.
  printf 'pub fn f() -> bool { cfg!(feature = "x") }\n' > "$TMP/w/plain/src/lib.rs"
  expect 1  "a cfg(feature) in a crate no feature step builds is BROKEN" \
            CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  : > "$TMP/w/plain/src/lib.rs"
  # C. a gated suite in a package no step selects. Same file, moved.
  rm -f "$TMP/w/feat/tests/gated_suite.rs"
  printf '#![cfg(feature = "gated")]\n' > "$TMP/w/plain/tests/gated_suite.rs"
  expect 1  "a gated suite in a package the step does not select is BROKEN" \
            CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  rm -f "$TMP/w/plain/tests/gated_suite.rs"
  # …and the count guard: pointed at nothing, it must not report success.
  expect 1  "a feature-matrix check that examined nothing is BROKEN" \
            CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$TMP/nope" SCAN_DIRS="$TMP/nope" $NOIN

  # ── Each leg reports its own count ────────────────────────────────────────
  # The tree is now in the shape this repository is actually in: members present
  # and healthy, no gated suite anywhere. This is the cell that would have caught
  # the defect — before per-leg counters the run printed
  # `3 feature-matrix premises checked` with leg C contributing 0, and no line of
  # output told the two cases apart.
  #
  # Falsifier for all four: collapse `mA`/`mB`/`mC` back into one `matrix` and
  # every one of them reds, because no `leg …:` line is printed at all.
  expect_says 77 "leg C: INAPPLICABLE" \
              "leg C says so when no gated suite exists" \
              CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  # …and the inapplicability report has to be a measurement, not a constant: put
  # the gated suite back where it belongs and leg C must count it instead.
  printf '#![cfg(feature = "gated")]\n' > "$TMP/w/feat/tests/gated_suite.rs"
  expect_says 77 "leg C: 1 crate-level feature-gated suite" \
              "leg C counts a suite it did examine" \
              CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  rm -f "$TMP/w/feat/tests/gated_suite.rs"
  # …and legs A and B, so neither can hide behind the other's count either.
  expect_says 77 "leg A: 1 declared feature" "leg A reports its own count" \
              CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  expect_says 77 "leg B: 1 member" "leg B reports its own count" \
              CHECK_SH="$TMP/ok.sh" MEMBER_DIRS="$WD" SCAN_DIRS="$SD" $NOIN
  echo
  if (( sfails )); then echo "$sfails self-test failure(s)" >&2; return 1; fi
  echo "test-input self-test OK"
}
if [[ "${1:-}" == --self-test ]]; then self_test; exit $?; fi

# ── The feature matrix, and the premise that lets it be narrow ──────────────
# Two failure shapes, both of which report `ok`:
#
#   * A suite behind `#![cfg(feature = "X")]` without an `--features X` step is
#     not "skipped" — it does not exist. `checker/tests/tg_tutorial.rs` opened
#     with that line while the `tg` feature existed; measured then, its 28 tests
#     became 0 and the run stayed green. Both the feature and the line are gone
#     (that suite's 33 tests are unconditional today), which is why leg C's
#     input set is empty and why it now reports that instead of counting into a
#     total the other two legs also feed.
#   * A `--features X` step that no longer *selects* the crate holding such a
#     suite is the same hole with the step still in place. Since the matrix was
#     narrowed from `--workspace` to `-p nanoda_lib`, that is now the shape to
#     worry about, and grepping only for the words `--features X` would miss it.
#
# So: which package holds what, and which step selects which package.

# The `name = "…"` of a member — `checker/` is the package `nanoda_lib`, and
# the difference between the directory and the package is exactly what a `-p`
# check has to get right.
pkg_name() { sed -nE 's/^name *= *"([^"]+)".*/\1/p' "$1/Cargo.toml" | head -1; }

# Every non-default feature a member declares, as `<dir> <pkg> <feature>`.
declared_features() {
  local d p
  for d in $MEMBER_DIRS; do
    [[ -f "$d/Cargo.toml" ]] || continue
    p="$(pkg_name "$d")"
    awk -v d="$d" -v p="$p" '
      /^\[features\]/ { inf = 1; next }
      /^\[/           { inf = 0 }
      inf && /^[A-Za-z_][A-Za-z0-9_-]*[[:space:]]*=/ {
        split($0, a, "="); gsub(/[[:space:]]/, "", a[1])
        if (a[1] != "default") print d, p, a[1]
      }' "$d/Cargo.toml"
  done
}

# The `cargo test … --features F …` lines of ci/check.sh that name feature F.
steps_for_feature() {
  grep -E "cargo test .*--features[= ]+([A-Za-z0-9_-]+,)*$1([,[:space:]]|$)" "$CHECK_SH"
}

# Does this command line run package P? `--workspace` does unless P is excluded;
# `-p P` / `--package P` does.
line_selects_pkg() {
  local l="$1" p="$2"
  grep -qE -- "(-p|--package)[= ]+$p([[:space:]]|$)" <<<"$l" && return 0
  grep -qE -- '(--workspace|--all)([[:space:]]|$)' <<<"$l" \
    && ! grep -qE -- "--exclude[= ]+$p([[:space:]]|$)" <<<"$l" && return 0
  return 1
}

# A. Every feature any member declares must be run by a step that selects that
#    member. A declared-but-unrun feature is a whole build configuration nobody
#    checks, which is how `tg_tutorial.rs` would go quiet.
#
# ── One counter per leg, because a leg with nothing to do has to say so ──────
# Task #137's per-leg floors (`83a95cf`, `ci/check-arena.sh`): "one counter lets
# a healthy leg hide a dead one." This script had exactly that shape, on the leg
# whose entire job is to catch a suite that compiles to an empty binary and
# reports `running 0 tests … ok`. All three legs incremented one `matrix`, the
# only guard was `matrix == 0`, and leg C's input set is empty on this tree — so
# the run printed `3 feature-matrix premises checked` over 1 + 2 + 0 and leg C's
# silence was indistinguishable from leg C having run.
#
# The floor is on **members examined**, not on the sum: every member with a
# manifest lands in leg A (once per feature it declares) or in leg B, so
# `members == 0` is exactly the "pointed at nothing" condition the old guard's
# message already described, and it fires on the same inputs the old one did.
#
# Leg C deliberately gets **no floor**. Its input is a thing that must not be
# reintroduced unguarded; none existing is the healthy state, not a broken
# check. What is unacceptable is silence, so it prints which of the two cases it
# is in. Its liveness is pinned by the self-test cell `a gated suite in a
# package the step does not select is BROKEN`, which builds the input this tree
# does not have — the tree cannot exercise leg C, so the self-test must.
mA=0 mB=0 mC=0 members=0
while read -r d p f; do
  [[ -n "$f" ]] || continue
  mA=$((mA+1))
  ok=0
  while IFS= read -r line; do
    line_selects_pkg "$line" "$p" && ok=1
  done < <(steps_for_feature "$f")
  if (( ! ok )); then
    echo "BROKEN: $p declares the feature \`$f\` and $CHECK_SH has no" >&2
    echo "        \`cargo test … --features $f\` step that selects $p." >&2
    echo "        A feature nobody builds under is a configuration nobody checks;" >&2
    echo "        a step that names the feature but not the package is the same" >&2
    echo "        hole with the words still there." >&2
    exit 1
  fi
  echo "  feature \`$f\` of $p: run by a step that selects $p"
done < <(declared_features)

# B. …and no *other* member may carry a `cfg(feature = …)` of its own. The two
#    feature steps are `-p nanoda_lib`, so `kernel`, `derived` and `mini` are
#    built exactly once; that is only harmless while none of their own code
#    varies with a feature. The day one of them grows a `cfg(feature)`, this
#    fails the build instead of the matrix quietly not covering it.
#
#    The complementary leg — that those crates do not reach the *checker* code
#    the features change — cannot be a grep. It was a runtime assertion until
#    the `tg` feature was retired; see the header.
for d in $MEMBER_DIRS; do
  [[ -f "$d/Cargo.toml" ]] || continue
  p="$(pkg_name "$d")"
  # Counted here and not in leg A because this is the one loop that visits every
  # member exactly once, whether or not it declares a feature. This is the
  # quantity the floor below is on.
  members=$((members+1))
  # `grep -c`, not `grep -q`: under `pipefail`, `-q`'s early exit SIGPIPEs
  # `declared_features` the moment a *later* member also declares features —
  # the whole pipeline then reports failure for a member whose row matched.
  # Latent while `checker` was the last (and only) feature-declaring member;
  # exposed the day `mini` declared one. `-c` reads the stream to the end.
  [[ "$(declared_features | grep -c "^$d $p ")" -gt 0 ]] && continue
  mB=$((mB+1))
  hits=$(grep -rlE 'cfg!?\([^)]*feature[[:space:]]*=' --include='*.rs' "$d/src" "$d/tests" 2>/dev/null)
  if [[ -n "$hits" ]]; then
    echo "BROKEN: $p declares no features, so ci/check.sh's feature steps do not" >&2
    echo "        build it — but its own code is now feature-conditional:" >&2
    printf '          %s\n' $hits >&2
    echo "        Either drop the cfg or widen the --features steps to select $p." >&2
    exit 1
  fi
  echo "  $p: no cfg(feature) of its own, so one build of it is every build"
done

# C. Every suite hidden behind a crate-level `#![cfg(feature = "X")]` must live
#    in a package some `--features X` step selects.
while IFS= read -r file; do
  [[ -n "$file" ]] || continue
  f=$(sed -nE 's/^#!\[cfg\(feature = "([a-z_]+)"\)\].*/\1/p' "$file" | head -1)
  [[ -n "$f" ]] || continue
  # …/<member>/tests/<suite>.rs
  d=$(dirname "$(dirname "$file")")
  p="$(pkg_name "$d")"
  mC=$((mC+1))
  ok=0
  while IFS= read -r line; do
    line_selects_pkg "$line" "$p" && ok=1
  done < <(steps_for_feature "$f")
  if (( ! ok )); then
    echo "BROKEN: ${file#$ROOT/} is behind \`#![cfg(feature = \"$f\")]\` and" >&2
    echo "        $CHECK_SH has no \`cargo test … --features $f\` step selecting $p." >&2
    echo "        Those tests compile to an empty binary and report" >&2
    echo "        \`running 0 tests … ok\`." >&2
    exit 1
  fi
  echo "  ${file#$ROOT/}: behind \`$f\`, run by a step that selects $p"
done < <(grep -rlE '^#!\[cfg\(feature = "[a-z_]+"\)\]' --include='*.rs' $SCAN_DIRS 2>/dev/null)

if (( members == 0 )); then
  echo "BROKEN: the feature-matrix check examined nothing — no member manifests" >&2
  echo "        were found under MEMBER_DIRS, so it cannot have proved anything." >&2
  exit 1
fi
echo "  leg A: $mA declared feature(s), each run by a step that selects its member"
echo "  leg B: $mB member(s) declaring none, none of them feature-conditional"
if (( mC == 0 )); then
  echo "  leg C: INAPPLICABLE — 0 crate-level \`#![cfg(feature = …)]\` suites exist"
  echo "         under the scanned trees, so there is nothing for it to examine."
  echo "         It guards against one being reintroduced without a --features"
  echo "         step; \`$0 --self-test\` is what keeps it live meanwhile."
else
  echo "  leg C: $mC crate-level feature-gated suite(s), each in a selected package"
fi
echo "  $((mA + mB + mC)) feature-matrix premises checked over $members member manifest(s)"

# How much is riding on this — counted, not asserted from memory, so the number
# cannot rot the way a comment would.
sites=$(grep -rE 'skip_guard::(absent|no_inputs|tool_absent)\b' \
          --include='*.rs' "$ROOT/checker/tests" 2>/dev/null \
        | grep -vcE ':[[:space:]]*(//|\*)')

missing=0

if [[ -d "$CORPUS" ]]; then
  # `-L`, and it is not decoration. A seat working in a `git worktree` reaches
  # the gitignored corpus through a symlink, and `find` does not descend a
  # symlink *named on its command line*. Measured 2026-08-09: plain `find`
  # reported 0 exports for a linked corpus that `find -L` counted 157 in — so
  # this step called BROKEN on a corpus that the suites running beside it were
  # reading perfectly well through ordinary path resolution. A step that
  # contradicts the tests next to it teaches the reader to discount it.
  n=$(find -L "$CORPUS" -name '*.ndjson' -type f 2>/dev/null | wc -l)
  if (( n == 0 )); then
    echo "BROKEN: $CORPUS is reachable but holds no .ndjson exports." >&2
    echo "        Zero is never a pass here. Either the corpus unpacked short," >&2
    echo "        or this step cannot see files the suites beside it can read." >&2
    echo "        Both are reds; neither is an absence." >&2
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

echo "  $sites guarded skip sites in checker/tests"

if (( missing )); then
  echo
  echo "Inputs are missing, so the tests behind those $sites guard sites will SKIP —" >&2
  echo "and \`cargo test\` reports a skip as \`ok\`. This step did not run; the summary" >&2
  echo "must not claim those tests passed." >&2
  exit 77
fi

echo "  every optional input is present and required"
