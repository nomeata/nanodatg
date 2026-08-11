#!/usr/bin/env bash
# The ratchet behind ci/skip-guard.rs: no Rust test may hand-roll a silent skip.
#
# `cargo test` reports a test that returns early as `ok`, and swallows its
# `eprintln!` unless `--nocapture` is passed. Measured on this repository with
# `vendor/arena-tests` out of reach: **41 `#[test]` functions** across four files
# reported `ok` having executed nothing — 12 of them (`mini/tests/tutorial.rs`)
# in 0.00 s, and two printed no message at all.
#
# `ci/skip-guard.rs` closes that: every skip goes through one predicate, which
# panics under `NANODATG_REQUIRE_CORPUS` / `NANODATG_REQUIRE_MODELGEN`. This
# script is what keeps it closed, because the hole was not introduced on purpose
# — it accreted one `if !dir.is_dir() { return }` at a time, and the next one
# would too.
#
# Three rules, and a count guard on the scan itself:
#
#   S1  No hand-rolled skip: a negated path predicate (`!p.is_dir()`,
#       `!p.is_file()`, `!p.exists()`), an empty-input test, or a `read_dir`
#       `let Ok(..) = .. else`, whose branch is a bare `return`. Those must call
#       the guard instead.
#   S2  No hand-rolled skip *message*: `eprintln!("SKIP…` / `"skipping…` in a
#       test source. The guard is the only thing allowed to announce a skip, so
#       that the announcement and the failure mode cannot drift apart.
#   S3  A file that declares `mod skip_guard` must call it, and a file that
#       calls it must declare it — an import nobody uses is exactly the vacuous
#       allowlist ci/check-boundary.sh rejects elsewhere.
#   C   The scan must find call sites at all, and the guard must still have a
#       failing path. A grep that matches nothing reports success having checked
#       nothing, which is the same defect one level up.
#
# `--self-test` plants a violation of each rule and asserts this script rejects
# it, and asserts a clean tree passes. It needs neither the corpus nor a Lean
# toolchain, so it runs where the corpus-dependent steps SKIP.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Overridable so --self-test can point the scan at fixture trees.
SCAN_DIRS="${SCAN_DIRS:-$ROOT/checker/tests $ROOT/derived/tests $ROOT/kernel/tests}"
# The guard's own source is exempt: it is where the banned shapes are supposed
# to live.
GUARD="${GUARD:-$ROOT/ci/skip-guard.rs}"
# Not a ratchet on the exact count — sites legitimately come and go — but zero
# means the guard is not wired up to anything.
MIN_SITES="${MIN_SITES:-1}"

self_test() {
  # Not `local`: the EXIT trap runs after the function has returned, and under
  # `set -u` a local would be unbound by then.
  TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
  local sfails=0

  # A clean fixture: one guarded skip, declared and used.
  mk_clean() {
    local d="$1"; mkdir -p "$d"
    cat > "$d/suite.rs" <<'EOF'
#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

#[test]
fn a_guarded_test() {
    let dir = std::path::Path::new("vendor/arena-tests");
    if skip_guard::absent(dir) {
        return
    }
    assert!(dir.exists());
}
EOF
  }

  expect() { # expect pass|fail <name> <dir> [env...]
    local want="$1" name="$2" d="$3"; shift 3
    local rc; env SCAN_DIRS="$d" "$@" "$0" >/dev/null 2>&1; rc=$?
    if [[ "$want" == pass && $rc -eq 0 ]] || [[ "$want" == fail && $rc -ne 0 ]]; then
      [[ "$want" == fail ]] && echo "  ok: detects $name" || echo "  ok: accepts $name"
    else
      echo "SELFTEST FAIL: '$name' expected to $want, got rc=$rc" >&2
      env SCAN_DIRS="$d" "$@" "$0" >&2
      sfails=$((sfails+1))
    fi
  }

  echo "self-testing $0"

  d="$TMP/clean"; mk_clean "$d"; expect pass "a clean suite" "$d"

  # S1, in each of its three shapes.
  d="$TMP/s1_isdir"; mk_clean "$d"; cat >> "$d/suite.rs" <<'EOF'
#[test]
fn t() {
    let dir = std::path::Path::new("x");
    if !dir.is_dir() {
        return
    }
}
EOF
  expect fail "a bare !is_dir() skip" "$d"

  d="$TMP/s1_empty"; mk_clean "$d"; cat >> "$d/suite.rs" <<'EOF'
#[test]
fn t() {
    let files: Vec<u8> = Vec::new();
    if files.is_empty() {
        return
    }
}
EOF
  expect fail "a bare is_empty() skip" "$d"

  d="$TMP/s1_readdir"; mk_clean "$d"; cat >> "$d/suite.rs" <<'EOF'
#[test]
fn t() {
    let Ok(e) = std::fs::read_dir("x") else {
        return
    };
    let _ = e;
}
EOF
  expect fail "a bare read_dir let-else skip" "$d"

  # …and the exemption: prose describing the shape is not the shape.
  d="$TMP/s1_comment"; mk_clean "$d"; cat >> "$d/suite.rs" <<'EOF'
/// This used to read `if !dir.is_dir() {
///     return
/// }` and that is exactly what the guard replaced.
#[test]
fn t() {}
EOF
  expect pass "a comment describing the banned shape" "$d"

  # S2.
  d="$TMP/s2"; mk_clean "$d"
  echo 'fn note() { eprintln!("SKIP: no corpus"); }' >> "$d/suite.rs"
  expect fail "a skip message outside the guard" "$d"

  # S3, both directions.
  d="$TMP/s3_unused"; mkdir -p "$d"
  printf '#[path = "../../ci/skip-guard.rs"]\nmod skip_guard;\n#[test]\nfn t() {}\n' > "$d/suite.rs"
  expect fail "a declared-but-unused guard" "$d"

  d="$TMP/s3_undeclared"; mkdir -p "$d"
  printf '#[test]\nfn t() { if skip_guard::absent(std::path::Path::new("x")) { return } }\n' > "$d/suite.rs"
  expect fail "a called-but-undeclared guard" "$d"

  # C: a suite tree with no guard anywhere. This is the state the repository was
  # in before ci/skip-guard.rs, and the scan must not call it clean.
  d="$TMP/c_none"; mkdir -p "$d"
  printf '#[test]\nfn t() { assert!(true); }\n' > "$d/suite.rs"
  expect fail "a tree with no guard call sites at all" "$d"

  # C: a guard that can no longer fail passes every grep above and is worthless.
  d="$TMP/c_toothless"; mk_clean "$d"
  sed 's/assert!(/let _ = (/' "$GUARD" > "$TMP/toothless.rs"
  expect fail "a guard with no failing path" "$d" GUARD="$TMP/toothless.rs"

  echo
  if (( sfails )); then echo "$sfails self-test failure(s)" >&2; return 1; fi
  echo "skip-guard self-test OK"
}

if [[ "${1:-}" == --self-test ]]; then self_test; exit $?; fi

fails=0
fail() { echo "SKIP-GUARD VIOLATION: $*" >&2; fails=$((fails+1)); }
ok()   { echo "  ok: $*"; }

sources() {
  local d
  for d in $SCAN_DIRS; do
    [[ -d "$d" ]] || continue
    find "$d" -name '*.rs' -type f
  done | grep -vF "$GUARD"
}

# ── S1: a hand-rolled skip ───────────────────────────────────────────────────
# awk over each file: a candidate guard line, then a bare `return` within the
# next four. Comment lines are skipped, so prose describing the shape — which
# several of these files now carry, explaining what the guard replaced — does
# not trip the rule.
s1=$(sources | while IFS= read -r f; do
  awk -v F="$f" '
    /^[[:space:]]*(\/\/|\*)/ { next }
    {
      if ($0 ~ /^[[:space:]]*return[[:space:]]*;?[[:space:]]*$/)
        for (i = NR - 4; i < NR; i++)
          if (i in cand) { print F ":" i ": " cand[i]; delete cand[i] }
      if ($0 ~ /if[[:space:]]*![A-Za-z_].*\.(is_dir|is_file|exists)\(\)/ ||
          $0 ~ /if[[:space:]]+[A-Za-z_][A-Za-z0-9_.]*\.is_empty\(\)[[:space:]]*\{/ ||
          $0 ~ /let[[:space:]]+Ok\(.*\)[[:space:]]*=[[:space:]]*std::fs::read_dir/)
        cand[NR] = $0
    }' "$f"
done)
if [[ -n "$s1" ]]; then
  fail "hand-rolled skip — call skip_guard::absent / no_inputs / tool_absent instead"
  printf '%s\n' "$s1" >&2
else
  ok "S1 no hand-rolled skips"
fi

# ── S2: a hand-rolled skip message ───────────────────────────────────────────
s2=$(sources | xargs -r grep -nE 'eprintln!\("(SKIP|skipping)' 2>/dev/null)
if [[ -n "$s2" ]]; then
  fail "a skip announced outside ci/skip-guard.rs"
  printf '%s\n' "$s2" >&2
else
  ok "S2 no skip messages outside the guard"
fi

# ── S3: the guard is imported where it is used, and used where imported ──────
sites=0; s3=0
while IFS= read -r f; do
  # Comment lines are stripped first: several of these files now *describe* the
  # guard in prose, and a doc comment is not a call site.
  n=$(grep -vE '^[[:space:]]*(//|\*)' "$f" | grep -cE 'skip_guard::(absent|no_inputs|tool_absent)\b')
  sites=$((sites + n))
  if grep -q 'mod skip_guard;' "$f" && (( n == 0 )); then
    fail "$f declares \`mod skip_guard\` and never calls it"; s3=1
  fi
  if (( n > 0 )) && ! grep -q 'mod skip_guard;' "$f"; then
    fail "$f calls the guard without declaring it — this will not compile"; s3=1
  fi
done < <(sources)
(( s3 )) || ok "S3 every \`mod skip_guard\` is declared where used and used where declared"

# ── C: the scan and the guard are both non-vacuous ───────────────────────────
if (( sites < MIN_SITES )); then
  fail "the scan found $sites guard call site(s), expected at least $MIN_SITES — the guard is wired to nothing, so this check proves nothing"
else
  ok "C $sites guard call sites found"
fi
if [[ ! -f "$GUARD" ]]; then
  fail "$GUARD is missing"
elif ! grep -q 'assert!(' "$GUARD"; then
  fail "$GUARD no longer fails on a required-but-absent input"
else
  ok "C the guard still has a failing path"
fi

echo
if (( fails )); then echo "$fails skip-guard violation(s)" >&2; exit 1; fi
echo "skip guards OK ($sites call sites)"
