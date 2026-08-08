#!/usr/bin/env bash
# Everything CI runs. Also the thing to run before committing.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

fails=0
declare -a skipped=()
# Exit 77 is SKIP — the autotools convention — and it is **not** PASS. A step
# that needs something the machine may not have (today: a Lean toolchain, for
# `check-modelgen.sh`) must be able to say "I did not run" in a way the summary
# repeats, because a step that reports success without running is the one
# failure mode a check script cannot recover from. `ci/check-modelgen.sh` exists
# because `modelgen` had no step at all and was 10 checks red for weeks.
step() {
  local name="$1"; shift
  echo
  echo "───── $name ─────"
  "$@"; local rc=$?
  case $rc in
    0)  echo "  PASS" ;;
    77) echo "  SKIP — this step did not run"; skipped+=("$name") ;;
    *)  echo "  FAIL" >&2; fails=$((fails+1)) ;;
  esac
}

# The trusted boundary, and the self-test proving the boundary check can fail.
step "kernel boundary"           ./ci/check-boundary.sh
step "boundary check self-test"  ./ci/test-boundary.sh
# R6′ for `mini`. `check-boundary.sh` applies R6′ to `derived/` and `checker/`
# and delegates `mini/` here — and *checks* that it does, so a workspace member
# cannot go unscanned the way it did when this was a blanket ban. See
# MINI-DESIGN.md §4.4.
step "mini hypothesis discipline" ./ci/check-mini-scope.sh
# The two encoders' own boundary: `mini/src/mutual_aux.rs` turns a block
# into Lean-world syntax and `mini/src/nested.rs` specialises a nested
# declaration; neither may look inside a certificate. The script
# carries the argument and its own self-test.
step "encoder black box"         ./ci/check-mutual-blackbox.sh

# The kernel is the only crate held to a no-warnings standard. The checker is a
# fork of upstream nanoda and carries its pre-existing clippy lints; tidying
# those would inflate the diff against upstream for no soundness benefit.
step "kernel builds clean"       cargo build -p kernel --all-targets
step "kernel clippy"             cargo clippy -p kernel --all-targets -- -D warnings
step "derived clippy"            cargo clippy -p derived --all-targets -- -D warnings
# `mini` is new code rather than a fork, so it is held to the same standard as
# `kernel` and `derived`; the pre-existing-lint exemption is for `checker/` only.
# `--no-deps`: `-D warnings` would otherwise be applied to `checker`, which is
# a fork and carries upstream's lints.
step "mini clippy"               cargo clippy -p mini --all-targets --no-deps -- -D warnings

# `modelgen` is a Lean package `mini` **execs** at runtime, and it had no step
# here at all until one was added — its own suite was 10 checks red on master
# and nothing said so. The only step that wants a Lean toolchain; it SKIPs
# loudly rather than passing when there is none, and counts what it ran.
# ~1.5 s warm, ~80 s from a cold `lake build`.
step "modelgen suites"           ./ci/check-modelgen.sh
# …and the self-test proving the count guard can fail, which needs no
# toolchain and so runs even where the step above SKIPs.
step "modelgen count self-test"  ./ci/check-modelgen.sh --self-test

# The Lean Kernel Arena corpus. `scripts/arena.sh` has been a real pass/fail
# gate since 2026-07-30 and no step ran it. `bad/` is a *ratchet* against
# `scripts/arena-accept.txt`, not a blanket must-reject — see that script's
# header. SKIPs when `vendor/arena-tests` is absent (it is gitignored for size).
# ~60 s for the release build the first time, ~4 s for the run.
step "arena corpus"              ./ci/check-arena.sh
# …and the self-test for its four ratchet cells and its count guard, which
# needs neither the corpus nor a toolchain and so runs where the step SKIPs.
step "arena ratchet self-test"   ./ci/check-arena.sh --self-test

# `mini` against `nanoda` over the same corpus. Also a real pass/fail gate since
# it was written, also run by nothing — the third found this way. It is not
# "mini must match nanoda": `mini` is allowed to be more permissive, so the gate
# names the two tolerated divergence classes and fails on anything else, plus on
# a crash, which used to pass. Reuses the release profile `check-arena.sh` just
# built, so it is ~30 s here; ~2 min if it is the one that has to build it.
step "mini vs nanoda"            ./ci/check-mini-vs-nanoda.sh
# …and the self-test for its five outcomes, its crash rule and its count guard,
# which needs neither the corpus nor a toolchain and so runs where the step
# SKIPs.
step "mini-vs-nanoda self-test"  ./ci/check-mini-vs-nanoda.sh --self-test

step "workspace builds"          cargo build --workspace --all-targets
step "tests"                     cargo test --workspace
# The step-counting probe must not change behaviour, only observe it.
step "tests (stepcount)"         cargo test --workspace --features stepcount
# The real Tarski-Grothendieck backend: builds actual kernel derivations, and
# must not change what the checker accepts.
step "tests (tg backend)"        cargo test --workspace --features tg

echo
if (( ${#skipped[@]} )); then
  echo "${#skipped[@]} step(s) SKIPPED and did not run: ${skipped[*]}" >&2
fi
if (( fails )); then echo "$fails step(s) failed" >&2; exit 1; fi
if (( ${#skipped[@]} )); then echo "all checks that ran passed"; exit 0; fi
echo "all checks passed"
