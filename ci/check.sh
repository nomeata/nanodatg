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

# The kernel is the only crate held to a no-warnings standard. The checker is a
# fork of upstream nanoda and carries its pre-existing clippy lints; tidying
# those would inflate the diff against upstream for no soundness benefit.
step "kernel builds clean"       cargo build -p kernel --all-targets
step "kernel clippy"             cargo clippy -p kernel --all-targets -- -D warnings

step "workspace builds"          cargo build --workspace --all-targets
step "tests"                     cargo test --workspace
# The step-counting probe must not change behaviour, only observe it.
step "tests (stepcount)"         cargo test --workspace --features stepcount

echo
if (( fails )); then echo "$fails step(s) failed" >&2; exit 1; fi
echo "all checks passed"
