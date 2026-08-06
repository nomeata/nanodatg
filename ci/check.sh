#!/usr/bin/env bash
# Everything CI runs. Also the thing to run before committing.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

fails=0
step() {
  echo
  echo "───── $1 ─────"
  shift
  if "$@"; then echo "  PASS"; else echo "  FAIL" >&2; fails=$((fails+1)); fi
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

step "workspace builds"          cargo build --workspace --all-targets
step "tests"                     cargo test --workspace
# The step-counting probe must not change behaviour, only observe it.
step "tests (stepcount)"         cargo test --workspace --features stepcount
# The real Tarski-Grothendieck backend: builds actual kernel derivations, and
# must not change what the checker accepts.
step "tests (tg backend)"        cargo test --workspace --features tg

echo
if (( fails )); then echo "$fails step(s) failed" >&2; exit 1; fi
echo "all checks passed"
