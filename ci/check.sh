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

# ── The gitignored corpus, before anything looks for it ─────────────────────
# `vendor/` is gitignored (17 MB), so `git worktree add` does not carry the
# arena corpus into a worktree — and every seat on this project works in one.
# Three steps below default their corpus to `$ROOT/vendor/arena-tests`, so on a
# machine that *has* the corpus a worktree got three SKIPs and one FAIL, and two
# seats independently spent a day filing it as environmental. A step that cannot
# see its input in the one environment everybody uses is the 2026-08-08 "SKIP is
# not PASS" defect wearing a different hat, and it trains the reader to discount
# a red, which is how a real one eventually gets laundered.
#
# `ci/corpus-dir.sh --link` resolves it once, here, before any step: it finds
# the main checkout's copy (`git rev-parse --git-common-dir`) and symlinks it to
# the local path. A path and not merely an exported variable, because the Rust
# suites build theirs from `CARGO_MANIFEST_DIR` and cannot be handed one — and
# `NANODATG_REQUIRE_CORPUS` below is a promise about *them*, so setting it off a
# corpus they cannot reach would turn 41 honest skips into 41 panics.
# `NANODATG_NO_CORPUS_LINK=1` opts out; a worktree then SKIPs like any other
# unequipped machine. Nothing changes in the main checkout, where the corpus is
# already at the local path and `--link` is a stat.
if ./ci/corpus-dir.sh --link >/dev/null; then corpus_present=1; else corpus_present=0; fi

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

# The corpus discovery the three corpus steps below share, self-tested first.
# It builds a throwaway repository and a real `git worktree` of it, so the cell
# that matters — a worktree with no `vendor/` finding the main checkout's copy —
# is exercised rather than asserted. Needs neither corpus nor toolchain, ~0.3 s.
step "corpus discovery self-test" ./ci/corpus-dir.sh --self-test

# The Lean Kernel Arena corpus. `scripts/arena.sh` has been a real pass/fail
# gate since 2026-07-30 and no step ran it. `bad/` is a *ratchet* against
# `scripts/arena-accept.txt`, not a blanket must-reject — see that script's
# header. SKIPs when no corpus is reachable — it is gitignored for size, and
# `ci/corpus-dir.sh` above has already looked in the main checkout as well as
# in this one, so a SKIP here means the machine really has not fetched it.
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

# Two binaries, one path. `mini/tests/*` spawn `CARGO_BIN_EXE_mini`, which is
# the uplift path `target/debug/mini`, and `dev` and `test` both uplift there —
# so while their settings differ, `cargo build` and `cargo test` leave
# *different* `mini` binaries at the one name and a prebuilt test binary run out
# of `deps/` gets whichever was last. That silently corrupted two measurement
# runs. The root `Cargo.toml` now gives the two profiles identical settings, so
# cargo builds one artefact; this is what keeps them identical. ~0.6 s, no
# inputs, and it watches its own falsifier on every run.
step "dev/test uplift"           ./ci/check-uplift.sh
step "uplift self-test"          ./ci/check-uplift.sh --self-test

# Everything compiles — in the same two halves the test steps below use, and for
# a reason that is not cosmetic. `nanoda_lib`'s dev-dependencies (`rand`, and
# `num-bigint` with `rand` turned on) are in the graph whenever its own test
# targets are, and under resolver 2 that changes the features `num-bigint` is
# built with, hence `nanoda_lib`, hence `mini`. Measured here: `mini` is
# 61 238 368 bytes when the checker's tests are in the graph and 61 056 280 when
# they are not. So `cargo build --workspace --all-targets` followed by
# `cargo test --workspace --exclude nanoda_lib` compiles `mini` and all seven of
# its integration-test binaries *twice*. Matching the halves keeps it to once.
step "builds (rest)"             cargo build --workspace --exclude nanoda_lib --all-targets
step "builds (checker)"          cargo build -p nanoda_lib --all-targets

# ── SKIP is not PASS, one layer down ────────────────────────────────────────
# Everything above is the shell half of that rule. The Rust suites had the same
# hole and it is the larger surface: measured with `vendor/arena-tests` out of
# reach, **41 `#[test]` functions** across `checker/tests/{corpus,tg_tutorial}.rs`
# and `mini/tests/{tutorial,dump}.rs` returned early and `cargo test` reported
# every one of them `ok` — `mini/tests/tutorial.rs` managed 12 passes in 0.00 s,
# and two of the 41 printed no message at all. `ci/skip-guard.rs` routes every
# such skip through one predicate that *panics* under the variables exported
# below; `ci/check-test-guards.sh` is the ratchet that stops the next
# `if !dir.is_dir() { return }` from being written.
#
# The variables are set only when the input is genuinely there. A machine that
# has not fetched the 17 MB gitignored corpus is unequipped, not broken, and
# `README.md` promises it a useful `cargo test` off the committed fixtures — so
# `check-test-inputs.sh` reports that case as a SKIP instead, and the summary
# ends "all checks that ran passed".
#
# "Genuinely there" used to be `[[ -d vendor/arena-tests ]]`, which is false in
# every `git worktree` — `vendor/` is gitignored, so `git worktree add` does not
# carry it — and every seat on this project works in one. That turned a machine
# that *has* the corpus into an unequipped one three steps running, and two
# seats spent a day each concluding it was environmental.
#
# `corpus-dir.sh --link` at the top of this script is what fixes it, and the
# answer it reached is `$corpus_present` here.
if (( corpus_present )); then export NANODATG_REQUIRE_CORPUS=1; fi
if [[ -x modelgen/.lake/build/bin/modelgen ]]; then export NANODATG_REQUIRE_MODELGEN=1; fi
step "corpus-dependent tests"    ./ci/check-test-inputs.sh
# …and its self-test, which needs no inputs and so runs where it SKIPs. It also
# covers the third shape of this defect, which is neither a skip nor a shell
# step: `checker/tests/tg_tutorial.rs` opens `#![cfg(feature = "tg")]`, so
# without the feature its 28 tests are not skipped but *absent* —
# `running 0 tests … ok`. Dropping `--features tg` from the step below would
# retire them in silence. Since the feature steps are now `-p nanoda_lib` and
# not `--workspace`, the step's *existence* is no longer enough to look for:
# `check-test-inputs.sh` resolves each package's name from its manifest and
# requires the step to select the package the gated suite lives in, and to
# select the package that declares the feature. It also refuses a
# `cfg(feature)` in any crate the narrowed steps no longer build.
step "test-input self-test"      ./ci/check-test-inputs.sh --self-test
# The ratchet, and the self-test proving it can fail — eight planted violations
# and the two clean cases that must still pass, one of them a comment that
# *describes* the banned shape. Neither needs the corpus nor a toolchain,
# so both run where the step above SKIPs. The guard's *own* panic path is
# watched firing on every run too: `ci/skip-guard.rs` carries three `#[test]`s
# that are compiled into each suite that includes it.
step "skip guards"               ./ci/check-test-guards.sh
step "skip-guard self-test"      ./ci/check-test-guards.sh --self-test

# ── The feature matrix, over the crates the features can reach ──────────────
# This used to be `cargo test --workspace` three times: plain,
# `--features stepcount`, `--features tg`. Measured, `mini/tests/nested.rs`
# alone is 17.76 T instructions, so that one file cost 53.3 T per run of this
# script — and two thirds of it bought nothing. `stepcount` and `tg` are
# `nanoda_lib`'s features; `kernel` and `derived` do not link `nanoda_lib` at
# all, and `mini` links it for the export parser, the level pre-pass and the
# shared `tg::EnvCore` — never `tc.rs`. So the feature runs are
# `-p nanoda_lib`, plus one narrow `-p mini --features tg` step for the
# cross-engine seam suite (`mini` declares `tg = ["nanoda_lib/tg"]` for
# exactly that file).
#
# Narrowing a matrix is how coverage is lost, so the premise is checked rather
# than believed, in three places:
#
#   * `ci/check-test-inputs.sh` refuses a feature that no step builds, a step
#     that names a feature without selecting the crate that declares it, and a
#     `cfg(feature)` appearing in any crate the feature steps no longer build;
#   * the plain run below is split so that everything except the checker runs
#     under `NANODATG_ASSERT_FEATURE_INERT`, which makes
#     `certify::new_backend` panic — the moment `mini` starts driving the
#     checker, the plain run goes red and says the matrix has to widen;
#   * `ci/check-feature-inert.sh` watches that panic actually happen, because a
#     guard nobody has seen fail is not known to work.
#
# The split costs nothing: the two halves run the same test binaries the single
# `--workspace` run did, and between them they run all of them.
step "tests (checker)"           cargo test -p nanoda_lib
step "tests (rest, feature-inert)" \
     env NANODATG_ASSERT_FEATURE_INERT=1 cargo test --workspace --exclude nanoda_lib
# …and the guard that holds the two steps below to `-p nanoda_lib`, watched
# firing against a process that certainly does build a backend.
step "feature-inert guard"       ./ci/check-feature-inert.sh
# The step-counting probe must not change behaviour, only observe it.
step "tests (stepcount)"         cargo test -p nanoda_lib --features stepcount
# The real Tarski-Grothendieck backend: builds actual kernel derivations, and
# must not change what the checker accepts.
step "tests (tg backend)"        cargo test -p nanoda_lib --features tg
# Both engines over one shared `EnvCore` in one process — the environment-
# unification seam (ENV-UNIFY.md §3.3) and the routed driver over it
# (ENV-UNIFY.md §5 track D). `mini/tests/envshare_tg.rs` and
# `mini/tests/route_tg.rs` need the checker's backend compiled in, hence the
# feature; the ungated half of the seam (`mini/tests/envshare.rs`) already
# ran in the plain step above. Both test files are named here because a
# `cfg(feature)` suite a step does not select is not skipped but *absent* —
# the defect this script's own comments document.
step "tests (cross-engine core)" cargo test -p mini --features tg --test envshare_tg --test route_tg

echo
if (( ${#skipped[@]} )); then
  echo "${#skipped[@]} step(s) SKIPPED and did not run: ${skipped[*]}" >&2
fi
if (( fails )); then echo "$fails step(s) failed" >&2; exit 1; fi
if (( ${#skipped[@]} )); then echo "all checks that ran passed"; exit 0; fi
echo "all checks passed"
