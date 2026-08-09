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
# # The feature matrix (the top half)
#
# `ci/check.sh` runs the two feature variants over `-p nanoda_lib` rather than
# over the whole workspace, because `stepcount` and `tg` are the checker's
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
# The fourth leg — that no other member reaches the checker code the features
# *do* change — is not a grep, because at module granularity every module in
# `checker/src` mentions `certify`. It is a runtime assertion instead:
# `ci/check.sh` runs the non-checker half of the workspace under
# `NANODATG_ASSERT_FEATURE_INERT`, and `ci/check-feature-inert.sh` watches it
# fire. See `checker/src/certify.rs`.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

CORPUS="${CORPUS_DIR:-$ROOT/vendor/arena-tests}"
MODELGEN="${MODELGEN_BIN:-$ROOT/modelgen/.lake/build/bin/modelgen}"
CHECK_SH="${CHECK_SH:-$ROOT/ci/check.sh}"
SCAN_DIRS="${SCAN_DIRS:-$ROOT/checker/tests $ROOT/mini/tests}"
# One directory per workspace member, so the self-test can point the
# feature-matrix checks at a synthetic tree.
MEMBER_DIRS="${MEMBER_DIRS:-$ROOT/kernel $ROOT/derived $ROOT/checker $ROOT/mini}"

self_test() {
  TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
  local sfails=0
  expect() { # expect <rc> <name> [env...]
    local want="$1" name="$2"; shift 2
    local rc; env "$@" "$0" >/dev/null 2>&1; rc=$?
    if [[ $rc -eq $want ]]; then echo "  ok: $name (rc=$rc)"
    else echo "SELFTEST FAIL: $name wanted rc=$want, got $rc" >&2; env "$@" "$0" >&2; sfails=$((sfails+1)); fi
  }
  echo "self-testing $0"
  mkdir -p "$TMP/empty"
  # An absent input is a SKIP, not a pass and not a failure.
  expect 77 "an absent corpus SKIPs" CORPUS_DIR="$TMP/nope" MODELGEN_BIN="$TMP/nope"
  # A corpus that unpacked short is BROKEN, not a skip: the directory test that
  # every call site used to do would have called this one present.
  expect 1  "a present-but-empty corpus is BROKEN" CORPUS_DIR="$TMP/empty" MODELGEN_BIN="$TMP/nope"
  # The corpus is there but nothing required it — this is the state the whole
  # change exists to prevent, and it must not be reported as a pass.
  expect 1  "a corpus present with the variable unset is BROKEN" \
            CORPUS_DIR="$ROOT/vendor/arena-tests" MODELGEN_BIN="$TMP/nope" NANODATG_REQUIRE_CORPUS=
  # …and the ci/check.sh grep.
  printf '#!/bin/sh\nstep "tests" cargo test --workspace\n' > "$TMP/no-tg.sh"
  expect 1  "a ci/check.sh with no --features tg step is BROKEN" \
            CHECK_SH="$TMP/no-tg.sh" CORPUS_DIR="$TMP/nope" MODELGEN_BIN="$TMP/nope"

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
  echo
  if (( sfails )); then echo "$sfails self-test failure(s)" >&2; return 1; fi
  echo "test-input self-test OK"
}
if [[ "${1:-}" == --self-test ]]; then self_test; exit $?; fi

# ── The feature matrix, and the premise that lets it be narrow ──────────────
# Two failure shapes, both of which report `ok`:
#
#   * A suite behind `#![cfg(feature = "X")]` without an `--features X` step is
#     not "skipped" — it does not exist. `checker/tests/tg_tutorial.rs` opens
#     with that line; measured, its 28 tests become 0 and the run stays green.
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
matrix=0
while read -r d p f; do
  [[ -n "$f" ]] || continue
  matrix=$((matrix+1))
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
#    the features change — cannot be a grep, and is the runtime assertion
#    `ci/check-feature-inert.sh` watches fire.
for d in $MEMBER_DIRS; do
  [[ -f "$d/Cargo.toml" ]] || continue
  p="$(pkg_name "$d")"
  declared_features | grep -q "^$d $p " && continue
  matrix=$((matrix+1))
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
  matrix=$((matrix+1))
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

if (( matrix == 0 )); then
  echo "BROKEN: the feature-matrix check examined nothing — no member manifests" >&2
  echo "        were found under MEMBER_DIRS, so it cannot have proved anything." >&2
  exit 1
fi
echo "  $matrix feature-matrix premises checked"

# How much is riding on this — counted, not asserted from memory, so the number
# cannot rot the way a comment would.
sites=$(grep -rE 'skip_guard::(absent|no_inputs|tool_absent)\b' \
          --include='*.rs' "$ROOT/checker/tests" "$ROOT/mini/tests" 2>/dev/null \
        | grep -vcE ':[[:space:]]*(//|\*)')

missing=0

if [[ -d "$CORPUS" ]]; then
  n=$(find "$CORPUS" -name '*.ndjson' -type f 2>/dev/null | wc -l)
  if (( n == 0 )); then
    echo "BROKEN: $CORPUS exists but holds no .ndjson exports" >&2
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

echo "  $sites guarded skip sites in checker/tests and mini/tests"

if (( missing )); then
  echo
  echo "Inputs are missing, so the tests behind those $sites guard sites will SKIP —" >&2
  echo "and \`cargo test\` reports a skip as \`ok\`. This step did not run; the summary" >&2
  echo "must not claim those tests passed." >&2
  exit 77
fi

echo "  every optional input is present and required"
