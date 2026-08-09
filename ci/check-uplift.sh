#!/usr/bin/env bash
# Two binaries, one path: `cargo build` and `cargo test` must not disagree
# about what lives at `target/debug/<bin>`.
#
# # The defect
#
# `mini/tests/{nested,designed,dump,mutual,tutorial,nat_equations,infinitary}.rs`
# all spawn `env!("CARGO_BIN_EXE_mini")`. Cargo expands that, at the time it
# compiles the test, to the **uplift** path — literally `target/debug/mini`, as
# `strings` on any of those test binaries shows. The `dev` and `test` profiles
# both uplift into `target/debug`, so while their settings differ they produce
# two different `mini` binaries and hardlink them, in turn, to that one name.
# Measured on this tree before the profiles were matched:
#
#   cargo build --bin mini        target/debug/mini -> 44 859 744 bytes, opt 0
#   cargo test  --no-run          target/debug/mini -> 61 052 224 bytes, opt 1
#
# Cargo itself is consistent — `cargo test` re-uplifts before it runs anything.
# The trap is the artefact that outlives the command: a test binary sitting in
# `target/debug/deps/` is what a measuring seat runs directly under `perf`, and
# *that* reads whatever the last cargo command left at the path. A `cargo build`
# in another window is enough. It **corrupted two measurement runs before it was
# noticed** and the numbers looked plausible, which is the part that matters:
# the failure was silent.
#
# # The fix this checks
#
# Cargo compares profiles by settings, not by name, so that `dev` and `test` can
# be one unit when they agree — the deduplication is deliberate and documented
# in cargo's own source. The root `Cargo.toml` therefore gives the two tables
# identical contents, and then there is only one `mini` and nothing to get
# wrong. This script is what stops the two tables drifting apart again: it
# copies them, verbatim, into a throwaway crate with one bin and one integration
# test, runs `cargo build` and then `cargo test --no-run`, and compares the
# **inode** at the uplift path. Same inode, same file, no trap.
#
# It tests cargo's actual behaviour rather than asserting a rule about it, which
# matters because the rule is cargo's and could change under us.
#
# `--self-test` runs the same two cells against a deliberately divergent pair of
# profiles and requires the check to go red — a guard nobody has watched fail is
# not known to work.
#
# # Cost and when it cannot run
#
# ~2 s: the throwaway crate is two empty `fn main`s and has no dependencies, so
# both builds are a single rustc each. Exits **77** (SKIP) with no `cargo` on
# the machine. Needs no corpus, no toolchain and no network.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="${UPLIFT_MANIFEST:-$ROOT/Cargo.toml}"

if ! command -v cargo >/dev/null 2>&1; then
  echo "  cargo: NOT FOUND"
  echo
  echo "The dev/test uplift collision was not checked; this step did not run." >&2
  exit 77
fi

# Pull `[profile.dev]` and `[profile.test]` out of a manifest, verbatim.
profiles() {
  awk '
    /^\[profile\.(dev|test)\]/ { keep = 1; print; next }
    /^\[/                      { keep = 0 }
    keep                       { print }
  ' "$1"
}

# Build the throwaway crate with the given profile text and report what sits at
# the uplift path after `cargo build` and after `cargo test --no-run`.
# Prints "<inode> <size>|<inode> <size>" — the inode is the decisive half, since
# two builds of an identical crate can well be the same *size* and still be two
# different files hardlinked to one name at different times.
probe() { # probe <dir> <profile-text-file>
  local d="$1" prof="$2"
  mkdir -p "$d/src" "$d/tests"
  { printf '[package]\nname = "uplift_probe"\nversion = "0.0.0"\nedition = "2021"\npublish = false\n\n'
    printf '[[bin]]\nname = "uplift_probe"\npath = "src/main.rs"\n\n'
    cat "$prof"; } > "$d/Cargo.toml"
  printf 'fn main() {}\n' > "$d/src/main.rs"
  printf 'fn main() {}\n' > "$d/tests/spawn.rs"
  ( cd "$d" && CARGO_INCREMENTAL=0 cargo build --bin uplift_probe -q ) >/dev/null 2>&1 || return 1
  local a; a="$(stat -c '%i %s' "$d/target/debug/uplift_probe")" || return 1
  ( cd "$d" && CARGO_INCREMENTAL=0 cargo test --no-run -q ) >/dev/null 2>&1 || return 1
  local b; b="$(stat -c '%i %s' "$d/target/debug/uplift_probe")" || return 1
  printf '%s|%s' "$a" "$b"
}

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

# ── the self-test ───────────────────────────────────────────────────────────
# Cell 2 below proves the *probe* can tell two profiles apart on every run.
# This proves the *script* goes red when they are: it re-runs itself against a
# manifest whose two tables disagree, exactly as the root manifest's did before
# they were matched, and requires exit 1.
if [[ "${1:-}" == --self-test ]]; then
  echo "self-testing $0"
  printf '[profile.dev]\ndebug = "line-tables-only"\n\n[profile.test]\nopt-level = 1\noverflow-checks = true\ndebug = "line-tables-only"\n' \
    > "$TMP/split.toml"
  UPLIFT_MANIFEST="$TMP/split.toml" "$0" >/dev/null 2>&1
  rc=$?
  if (( rc == 1 )); then
    echo "  ok: the pre-fix dev/test pair is rejected (rc=$rc)"
  else
    echo "SELFTEST FAIL: the pre-fix dev/test pair wanted rc=1, got $rc" >&2
    UPLIFT_MANIFEST="$TMP/split.toml" "$0" >&2
    exit 1
  fi
  # …and a manifest with no profile tables at all must be BROKEN, not a pass:
  # an empty read is how a check quietly stops checking.
  printf '[package]\nname = "x"\n' > "$TMP/none.toml"
  UPLIFT_MANIFEST="$TMP/none.toml" "$0" >/dev/null 2>&1
  rc=$?
  if (( rc == 1 )); then
    echo "  ok: a manifest with no [profile] tables is BROKEN (rc=$rc)"
  else
    echo "SELFTEST FAIL: an empty profile read wanted rc=1, got $rc" >&2
    exit 1
  fi
  # …and the matched pair the repo now carries must pass, or the two cells
  # above are agreeing with each other about nothing.
  printf '[profile.dev]\nopt-level = 1\noverflow-checks = true\ndebug = "line-tables-only"\n\n[profile.test]\nopt-level = 1\noverflow-checks = true\ndebug = "line-tables-only"\n' \
    > "$TMP/match.toml"
  UPLIFT_MANIFEST="$TMP/match.toml" "$0" >/dev/null 2>&1
  rc=$?
  if (( rc == 0 )); then
    echo "  ok: a matched dev/test pair passes (rc=$rc)"
  else
    echo "SELFTEST FAIL: a matched dev/test pair wanted rc=0, got $rc" >&2
    UPLIFT_MANIFEST="$TMP/match.toml" "$0" >&2
    exit 1
  fi
  echo
  echo "uplift self-test OK"
  exit 0
fi

cells=0
fails=0

# ── cell 1: this repo's profiles must agree ─────────────────────────────────
cells=$((cells+1))
profiles "$MANIFEST" > "$TMP/prof-real"
if [[ ! -s "$TMP/prof-real" ]]; then
  echo "BROKEN: $MANIFEST declares neither [profile.dev] nor [profile.test], so" >&2
  echo "        this check read nothing and cannot have proved anything." >&2
  exit 1
fi
if ! out="$(probe "$TMP/real" "$TMP/prof-real")"; then
  echo "BROKEN: the probe crate would not build; the check did not run." >&2
  exit 1
fi
build_side="${out%%|*}"; test_side="${out##*|}"
if [[ "$build_side" == "$test_side" ]]; then
  echo "  ok: cargo build and cargo test uplift the same file (inode/size $build_side)"
else
  echo "FAIL: [profile.dev] and [profile.test] have drifted apart, so" >&2
  echo "      \`cargo build\` and \`cargo test\` put *different* binaries at the one" >&2
  echo "      path CARGO_BIN_EXE_<bin> names:" >&2
  echo "        after cargo build   inode/size $build_side" >&2
  echo "        after cargo test    inode/size $test_side" >&2
  echo "      Every mini/tests suite spawns that path, and a prebuilt test binary" >&2
  echo "      run out of target/debug/deps/ will read whichever cargo command was" >&2
  echo "      last. That silently corrupted two measurement runs once already." >&2
  echo "      Make the two tables in $MANIFEST identical again." >&2
  fails=$((fails+1))
fi

# ── cell 2: …and the check can tell, which is the only reason cell 1 means
# anything. Deliberately divergent profiles must come back different.
cells=$((cells+1))
printf '[profile.dev]\nopt-level = 0\n\n[profile.test]\nopt-level = 1\n' > "$TMP/prof-split"
if ! out="$(probe "$TMP/split" "$TMP/prof-split")"; then
  echo "BROKEN: the divergent probe crate would not build; cell 2 did not run." >&2
  exit 1
fi
if [[ "${out%%|*}" == "${out##*|}" ]]; then
  echo "FAIL: profiles differing in opt-level uplifted the *same* file, so this" >&2
  echo "      check cannot see the defect it exists for. Either cargo changed how" >&2
  echo "      it names uplift artefacts, or the probe is not measuring anything." >&2
  fails=$((fails+1))
else
  echo "  ok: divergent profiles are detected (${out%%|*} vs ${out##*|})"
fi

echo "  $cells cells"
if (( cells < 2 )); then
  echo "BROKEN: no cells ran, so nothing was checked" >&2
  exit 1
fi
if (( fails )); then echo "$fails cell(s) failed" >&2; exit 1; fi
