#!/usr/bin/env bash
# Enforce the trusted-boundary rules on the `kernel` crate.
#
# The kernel is the only component that must be correct for soundness, so the
# rules that keep it small and auditable are checked mechanically rather than by
# code review. Run in CI; fails the build on any violation.
#
# Some of these are also enforced by the compiler (`#![forbid(unsafe_code)]`) or
# by Cargo (an empty `[dependencies]` table). Checking them here too is
# deliberate: those enforcements can be quietly removed in the same commit that
# violates them, and this script makes that show up as a failure.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Overridable so ci/test-boundary.sh can point the checker at fixture crates
# that deliberately violate each rule, and assert that it complains.
K="${KERNEL_DIR:-$ROOT/kernel}"
fails=0

fail() { echo "BOUNDARY VIOLATION: $*" >&2; fails=$((fails+1)); }
ok()   { echo "  ok: $*"; }

# grep the kernel sources for a pattern, ignoring matches that occur in comments.
# `grep -rIn` prefixes each hit with `path:line:`, so the comment test has to
# skip that prefix rather than anchoring at `^`.
grep_code() {
  grep -rInE "$1" --include='*.rs' "$K/src" 2>/dev/null \
    | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*|#!\[)'
}

echo "checking kernel boundary in $K"

# ── 0. Every scan below must have something to scan ──────────────────────────
# Rules 1, 3, 4 and 5 are greps over `$K/src`, all of them with `2>/dev/null` on
# the grep and `|| true` semantics from the enclosing `if`. Point `$K` at a
# directory that is not there and five of the six report `ok:` over nothing;
# measured, the only thing that stopped an absent kernel from passing outright
# was the `#![forbid(unsafe_code)]` grep, which fails for an unrelated reason
# and prints a misleading message while doing it. That is the shape this
# project has now been bitten by five times (`DECISIONS.md` 2026-08-08, "SKIP
# is not PASS"): a check that examines nothing is indistinguishable from a
# check that examined everything and found nothing wrong.
#
# So the scan is counted, the way `ci/check-test-guards.sh`'s rule C counts its
# call sites. Not a ratchet on the exact number — the kernel is allowed to grow
# and shrink — but zero means the scan is wired to nothing.
if [[ ! -d "$K/src" ]]; then
  fail "the kernel source directory ($K/src) does not exist — rules 1-5 would scan nothing"
else
  kernel_files=$(find "$K/src" -name '*.rs' -type f 2>/dev/null | wc -l)
  if (( kernel_files < 1 )); then
    fail "no .rs files under $K/src — rules 1-5 would scan nothing and report ok"
  else
    ok "rules 1-5 scan $kernel_files kernel source file(s)"
  fi
fi

# ── 1. No `unsafe` ───────────────────────────────────────────────────────────
# Match `unsafe` as a word, but not the `#![forbid(unsafe_code)]` attribute or
# the token `unsafe_code` itself.
if grep_code '\bunsafe\b' | grep -v 'unsafe_code' | grep -q .; then
  fail "\`unsafe\` found under kernel/src"
  grep_code '\bunsafe\b' | grep -v 'unsafe_code' >&2
else
  ok "no unsafe"
fi

# The crate-level forbid must be present — it is the compiler-enforced half.
if ! grep -q '#!\[forbid(unsafe_code)\]' "$K/src/lib.rs"; then
  fail "kernel/src/lib.rs is missing #![forbid(unsafe_code)]"
else
  ok "#![forbid(unsafe_code)] present"
fi

# ── 2. No external dependencies ──────────────────────────────────────────────
# The sanctioned future exception is a single vetted bignum crate for native
# arithmetic (milestone 4). If one is added it must be named here *and*
# documented as a TCB entry in kernel/README.md.
ALLOWED_DEPS_RE='^(num-bigint)$'
# Comments are stripped first: a `#` line inside the table that happens to
# contain an `=` is prose, not a dependency, and reading it as one produced a
# spurious violation.
#
# The awk needs the `[dependencies]` header to find anything, so its silence has
# two readings — an empty table, or a manifest it never parsed. A missing
# manifest, or one with no such table, is therefore a failure rather than the
# `ok: no external dependencies` it used to produce: the reading that matters
# for soundness is "the table is empty", and only a parsed table can say that.
if [[ ! -f "$K/Cargo.toml" ]]; then
  fail "$K/Cargo.toml is missing — the dependency scan would parse nothing"
elif ! grep -q '^\[dependencies\]' "$K/Cargo.toml"; then
  fail "$K/Cargo.toml has no [dependencies] table — the dependency scan would parse nothing"
fi
deps=$(awk '/^\[dependencies\]/{f=1;next} /^\[/{f=0} f {sub(/#.*/,"")} f && /=/{split($0,a,"="); gsub(/[ \t]/,"",a[1]); if (a[1] != "") print a[1]}' "$K/Cargo.toml" 2>/dev/null)
if [[ -n "$deps" ]]; then
  while IFS= read -r d; do
    [[ -z "$d" ]] && continue
    if [[ "$d" =~ $ALLOWED_DEPS_RE ]]; then
      if ! grep -q "$d" "$K/README.md" 2>/dev/null; then
        fail "dependency '$d' is allowed but not documented as a TCB entry in kernel/README.md"
      else
        ok "sanctioned dependency '$d' (documented in README)"
      fi
    else
      fail "kernel has external dependency '$d'"
    fi
  done <<< "$deps"
else
  ok "no external dependencies"
fi

# ── 3. No public constructor for `Thm`; no public fields ─────────────────────
# `Thm`'s integrity is the whole LCF argument: if a client can build one without
# going through an inference rule, the system proves nothing.
#
# The awk below reads a file *list*, and that list used to be the glob
# `"$K/src"/*.rs` — top level only — while rules 1 and 4 beside it use
# `grep -rInE` and recurse. Measured: a `pub struct Thm { pub leak: u32 }` in
# `$K/src/sub/hidden.rs` printed `ok: Thm has no public fields`. That is not a
# vacuous *scan*, it is a scan that reads less than its name says, and it is the
# same defect wearing a third hat. `kernel/src` is flat today (three files), so
# nothing escaped in fact; the glob is a `find` now so that adding a
# subdirectory cannot quietly open the hole.
kernel_srcs() { find "$K/src" -name '*.rs' -type f -print0 2>/dev/null; }

# The whole rule is conditional on a `Thm` type existing, and a kernel that
# declares none silently skipped every check inside it — measured: a kernel
# whose type is called `Sequent` exits 0 with no mention of rule 3 at all. The
# type this entire boundary is *about* must be findable, so its absence is a
# failure rather than an exemption.
if ! grep -rIqE 'pub\s+(struct|enum)\s+Thm\b' --include='*.rs' "$K/src" 2>/dev/null; then
  fail "the kernel declares no \`pub struct/enum Thm\` — rule 3 would check nothing"
else
  # Having a public `Thm` type is expected; what must not exist is public
  # *fields* on it or a public constructor.
  if grep -rInE 'pub\s+struct\s+Thm\s*\(' --include='*.rs' "$K/src" | grep -qvE '\(\s*\)'; then
    fail "Thm appears to be a tuple struct with public field(s)"
  fi
  # Any `pub` field inside the Thm struct body. The trailing `:` is what makes
  # this a field declaration rather than the `pub struct Thm {` header line.
  if kernel_srcs | xargs -0 -r awk '/pub struct Thm/,/^}/' 2>/dev/null \
       | grep -qE '^[[:space:]]*pub[[:space:]]+[a-z_][a-z0-9_]*[[:space:]]*:'; then
    fail "Thm has public field(s)"
  else
    ok "Thm has no public fields"
  fi
fi
# A `pub fn new`/`from_parts` etc. producing a Thm outside the rule set would be
# a forged-theorem hole. Inference rules are the only sanctioned producers.
# Two shapes to catch: an explicit `-> Thm` on a generically-named function, and
# any such function returning `Self` from inside an `impl Thm` block.
ESCAPE='pub[[:space:]]+(unsafe[[:space:]]+)?fn[[:space:]]+(new|new_unchecked|from_parts|from_raw|mk|axiom_unchecked)\b'
if grep_code "${ESCAPE}[^;]*->[[:space:]]*Thm\b" | grep -q .; then
  fail "public escape-hatch constructor returning Thm"
  grep_code "${ESCAPE}[^;]*->[[:space:]]*Thm\b" >&2
elif kernel_srcs | xargs -0 -r awk '/^impl([[:space:]]|<).*Thm/,/^}/' 2>/dev/null \
       | grep -qE "${ESCAPE}[^;]*->[[:space:]]*(Self|Thm)\b"; then
  fail "public escape-hatch constructor returning Self inside impl Thm"
else
  ok "no escape-hatch Thm constructor"
fi

# ── 4. No I/O, no serialization, no printing of derivations ──────────────────
# A kernel that can print or serialize a derivation invites a workflow where the
# derivation is the artifact; the LCF design is that derivations are transient.
# NB: no trailing `\b` after the macro alternatives — a word boundary cannot
# match between `!` and `(`, so `\bprintln!\b` never fires. (Caught by
# ci/test-boundary.sh.)
IO_RE='(\bprintln!|\beprintln!|\bprint!|\beprint!|\bdbg!|\bstd::fs\b|\bstd::io\b|\bFile::|\bserde\b|\bSerialize\b|\bDeserialize\b)'
if grep_code "$IO_RE" | grep -q .; then
  fail "I/O, printing, or serialization under kernel/src"
  grep_code "$IO_RE" >&2
else
  ok "no I/O / serialization / printing"
fi

# ── 5. Size budget ───────────────────────────────────────────────────────────
# "A few hundred lines. If it grows past this, something has leaked in that
# belongs in check/ or interp/." Counted excluding comments and blank lines, so
# documentation (which we want lots of) does not eat the budget.
#
# The budget was 1000 while the crate also carried the `Certifier` trait and
# `NullCertifier`. Those moved to `checker/src/certify.rs` — they construct no
# `Thm` and cannot affect soundness — taking the crate from 670 to 612 lines, and
# the budget came down with them. A ceiling with 388 lines of slack under it is
# not a boundary, it is a number nobody has to think about; at 700 the next
# addition to the trusted surface has to be small, or deliberate enough to raise
# this line and say why in `kernel/README.md`.
#
# `kernel_srcs` and not the glob `"$K/src"/*.rs`, for the reason given at rule 3:
# the glob is top level only, so a subdirectory's lines were free. A budget that
# a `mkdir` gets you out of is not a budget.
BUDGET=700
code_lines=$(kernel_srcs | xargs -0 -r cat 2>/dev/null | grep -vE '^\s*(//|$)' | wc -l)
echo "  kernel non-comment lines: $code_lines"
if (( code_lines > BUDGET )); then
  fail "kernel exceeds $BUDGET non-comment lines ($code_lines) — something has leaked in"
else
  ok "size within budget ($code_lines <= $BUDGET)"
fi

# ── 7. The Henkin primitive has exactly one caller ───────────────────────────
# `kernel::thm::henkin` mints a fresh constant out of a proved `∃`. It is the
# newest item in the trusted base and the one the project owner asked to be able
# to take back out — "in case we regret that choice later and build it
# differently" — so the property that makes it replaceable is *checked* rather
# than intended: **one call site in the whole workspace, and it is
# `derived/src/choice/epsilon.rs`.**
#
# Three failures, not one, and the third is the point:
#
#   * a call site anywhere else — the encapsulation is gone, and every consumer
#     that went around `derived::choice::Epsilon` is a place a replacement would
#     have to be re-derived;
#   * two call sites in the home module — one seam, not two;
#   * **zero call sites while the primitive exists** — an unused rule in the
#     trusted base is one nobody reads and nobody deletes. The day `epsilon.rs`
#     is rewritten over a derived well-ordering (see its header) this reds, and
#     the primitive comes out of `thm.rs` with it rather than staying behind.
#
# If the kernel declares no `henkin` at all, the rule is vacuous **and the
# compiler enforces it** — a call to a function that is not there does not
# build — so it says so and moves on. That is the one reading of "nothing to
# scan" this project accepts (`DECISIONS.md` 2026-08-08, "SKIP is not PASS"),
# and it is stated rather than left as silence.
#
# The scan reads the *workspace*, not one crate, because the property is about
# who may call in from outside. `$K` itself is excluded — the rule's definition,
# its doc comment and `kernel/tests/henkin.rs` are not callers in the sense that
# matters — and so are `target*`, `vendor/` and `.claude/`, the last because a
# `git worktree` under `.claude/worktrees/` is a second copy of this repository
# and would otherwise read as a second caller.
HENKIN_HOME="${HENKIN_HOME:-derived/src/choice/epsilon.rs}"
HENKIN_ROOT="${HENKIN_SCAN_ROOT:-$ROOT}"
#
# The exclusions are **anchored at `$HENKIN_ROOT`** and not written as `*/…/*`
# globs. Measured: `-not -path '*/.claude/*'` excluded the entire tree, because
# every seat on this project works in a worktree under `.claude/worktrees/`, so
# the root itself contains that component and the scan read zero files. An
# unanchored exclusion is a rule about the *absolute* path of the checkout,
# which is not a property of this repository.
henkin_files() { # henkin_files <-print|-print0>
  find "$HENKIN_ROOT" -name '*.rs' -type f -not -path "$K/*" \
    -not -path "$HENKIN_ROOT/target*" -not -path "$HENKIN_ROOT/vendor/*" \
    -not -path "$HENKIN_ROOT/.git/*" -not -path "$HENKIN_ROOT/.claude/*" \
    -not -path '*/target/*' "$@" 2>/dev/null
}
# `-H` is load-bearing, not decoration: `grep` omits the filename when handed a
# single file, so on a workspace with one candidate file both the comment filter
# (which skips `path:line:`) and the home-module test (which matches on the path)
# silently stopped applying. The self-test's rule 7 cells caught it.
henkin_calls() {
  henkin_files -print0 | xargs -0 -r grep -HInE 'thm::henkin[[:space:]]*\(' 2>/dev/null \
    | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*)'
}
if ! grep -rIqE 'pub fn henkin\b' --include='*.rs' "$K/src" 2>/dev/null; then
  ok "no Henkin primitive in this kernel — rule 7 is vacuous and the compiler enforces it"
elif (( $(henkin_files -print | wc -l) < 1 )); then
  fail "rule 7 matched no .rs files under $HENKIN_ROOT — the single-caller scan would read nothing"
else
  henkin_home=$(henkin_calls | grep -c "/${HENKIN_HOME}:")
  henkin_other=$(henkin_calls | grep -v "/${HENKIN_HOME}:")
  if [[ -n "$henkin_other" ]]; then
    fail "\`kernel::thm::henkin\` is called outside $HENKIN_HOME"
    printf '%s\n' "$henkin_other" >&2
    echo "  The Henkin constant has exactly one seam, so that a replacement has one" >&2
    echo "  place to cut. Go through \`derived::choice::Epsilon\`." >&2
  elif (( henkin_home == 0 )); then
    fail "\`kernel::thm::henkin\` has no caller — an unused primitive must leave the trusted base, not sit in it"
  elif (( henkin_home > 1 )); then
    fail "\`kernel::thm::henkin\` is called $henkin_home times in $HENKIN_HOME — one seam, not two"
  else
    ok "kernel::thm::henkin has exactly one caller, in $HENKIN_HOME"
  fi
fi

# ── 6′. The hypothesis discipline outside the kernel ─────────────────────────
# `Thm` is a sequent `Γ ⊢ φ`, and `Thm::assume` is the only rule that puts
# anything in `Γ`.
#
# This rule used to be a **ban**: no `Thm::assume`/`Thm::implies_intr` in
# `derived/` or `checker/` at all. That was wrong. Building `P ⊢ P` and carrying
# `P` in `Γ` is precisely what the sequent judgement is for, and it is sound —
# `assume` asserts nothing about `P`. The ban was written as a transition guard
# in the same commit that made `Thm` a sequent, and it protected two *engineering*
# weaknesses rather than any soundness property:
#
#   * `Thm::gen` **panics** when the generalised variable is free in a hypothesis.
#     It kept an infallible signature because no caller could reach the panic.
#   * A `Thm` establishes its conclusion only when `hyps()` is empty, so a store
#     keyed on anything that does not mention `Γ`, or a bare `concl() == expected`
#     comparison, is correct only while `Γ` is always empty.
#
# The ban froze both in place, and it was already ineffective: it did not scan
# `mini/`, which legitimately holds Γ-carrying theorems. So it constrained
# producers while the hazard lives in consumers, and exempted the one crate that
# actually produces.
#
# R6′ answers the two weaknesses at their sites instead, per crate:
#
#   I1  `Thm::assume`/`Thm::implies_intr` appear only in a named introduction
#       module, which must exist and must actually call `assume` (or the
#       allowlist is vacuous). `derived/src/discharge.rs` is its module and
#       `checker/src/scope.rs` is the checker's. Its house rule remains the
#       consumer half — every public entry checks `hyps().is_empty()` as well as
#       pinning its conclusion.
#
#       This paragraph used to read "`derived/` has no such module: it
#       *derives*, it does not assume." That was a true description of the code
#       and it is corrected rather than appended to, because a reader who
#       believed it would audit the wrong file. What changed: `derived::nat`
#       proves a dozen lemmas that are ten-link equational chains under an
#       induction hypothesis, and building those out of `S` and `K` — the
#       `a1i`/`syl`/`hyp_eq_trans` toolkit — makes every link a `syl` whose two
#       implications must be spelled out. The ban was buying readability at a
#       cost this crate can no longer pay, and it was never buying soundness:
#       `assume` asserts nothing about `h`, as this header already says three
#       paragraphs up. The two weaknesses it *was* protecting are answered in
#       `discharge.rs`'s own header, which is where the argument lives.
#   I3  `Thm::gen(` — the panicking wrapper — appears nowhere; `gen_checked` is
#       the only entry, so a hypothetical theorem yields a counted gap rather
#       than an abort. **Not applied to `derived/`**, which still has ~700 `gen`
#       call sites; there I1 is what keeps the panic unreachable, and saying so
#       here is better than leaving it implicit.
#   I4  the persistence funnel is a `Sealed` newtype whose only constructor
#       checks `hyps().is_empty()`. Enforced by the type; what is grepped is
#       that the field stays private and no second constructor appears.
#
# Test code is **not** exempt from I1: a test that wants a hypothetical theorem
# gets it from the introduction module's `test_support`, which keeps I1 a
# single-file property rather than a single-file-plus-cfg property. That is
# strictly stronger than the ban this replaces, which did exempt test code.
#
# Coverage is checked mechanically below, because the way the old rule failed
# was by silently not covering a crate.

# Overridable so ci/test-boundary.sh can self-test against fixture crates.
D="${DERIVED_DIR:-$ROOT/derived}"
C="${CHECKER_DIR:-$ROOT/checker}"
HYP_RE='Thm::assume|Thm::implies_intr'

# grep a crate's shipped sources, skipping comments. Integration tests (under a
# `tests/` directory) are excluded from the *`gen`* scan only; I1 covers them.
#
# A missing directory is reported as "violations found" (return 0) rather than
# "clean", so a crate that vanishes cannot buy itself a pass — but the caller
# then prints a hit list, and an empty one under a message like "Thm::assume
# outside checker/src/scope.rs" is a lie about why. The absence is printed
# instead, so the diagnostic matches the reason.
#
# This branch is belt and braces, not the tested guarantee: the counted-file
# guard below reds an absent `$C` on its own, which is why the self-test cell
# for an absent checker/ pins that guard's message. Turning this `return 0`
# into a `return 1` reds no cell — deliberately, because a cell that cannot
# fail is worse than no cell.
crate_scan() { # crate_scan <dir> <regex> [<path-substring to allow>]
  local d="$1" re="$2" allow="${3:-}"
  if [[ ! -d "$d" ]]; then
    echo "  (no such directory: $d — an unscannable crate is a violation, not a pass)"
    return 0
  fi
  local hits
  hits=$(grep -rInE "$re" --include='*.rs' "$d" 2>/dev/null \
         | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*|#!\[)')
  if [[ -n "$allow" ]]; then
    hits=$(printf '%s\n' "$hits" | grep -vE "$allow")
  fi
  printf '%s' "$hits" | grep -E '.'
}

# ── I1, derived/: exactly one introduction module ───────────────────────────
# `derived/src/discharge.rs` is the sanctioned place, and the scan is a ban
# everywhere else — but only over *shipped* code. Its test suite builds hypothetical theorems on purpose:
# that is how the consumer-side house rule (`derived::establishes`,
# `derived::all_unconditional`) is pinned, and there are twenty-odd such
# fixtures. So integration tests (anything under a `tests/` directory) and
# `#[cfg(test)]` items are skipped here. `checker/` needs no such exemption,
# because it has a sanctioned test entry point (`scope::test_support`) and I1 is
# therefore a single-*file* property there rather than a single-file-plus-cfg one.
DERIVED_SCOPE="${DERIVED_SCOPE:-src/discharge.rs}"
# The file list and the scan over it are separate, because the count is the
# thing that says the scan happened. `derived_files -print` counts; `-print0`
# feeds the scan. Both apply the same exclusions, so the number printed is the
# number of files the rule actually reads.
derived_files() { # derived_files <-print|-print0>
  find "$D" -name '*.rs' -type f -not -path '*/tests/*' -not -path "*/$DERIVED_SCOPE" "$@" 2>/dev/null
}
derived_scan() {
  derived_files -print0 \
    | xargs -0 -r awk -v re="$HYP_RE" '
        FNR == 1 { skip = 0 }
        # A test-only item in column 0; rustfmt closes such an item with a `}`
        # in column 0, which ends the skip. Both `#[cfg(test)]` and
        # `#[cfg(all(test, ...))]` count — the latter appears when a test module
        # is also gated on a feature, and matching only the bare form silently
        # un-exempts it. That is a false positive rather than a missed
        # violation, but a boundary rule that fires on correct code gets
        # deleted, so it matters.
        # NB: no apostrophes anywhere in this awk program. It is inside single
        # quotes, and one apostrophe ends it and hands the rest to bash.
        /^#\[cfg\(test\)\]/ { skip = 1; next }
        /^#\[cfg\(all\(test[,)]/ { skip = 1; next }
        skip { if (/^\}/) skip = 0; next }
        /^[[:space:]]*(\/\/|\*)/ { next }
        $0 ~ re { printf "%s:%d:%s\n", FILENAME, FNR, $0 }
      '
}
#
# **The scan must find something to scan.** This function opened with
# `[[ -d "$D" ]] || return 0` — an absent directory was a *pass* — and its
# `find` had no counted-N guard either, so a scan matching no files was
# indistinguishable from a scan that read every file and found nothing wrong.
# Measured before the fix: `DERIVED_DIR=/nonexistent` and `DERIVED_DIR=<empty
# dir>` both printed `ok: derived/ introduces hypotheses only in
# src/discharge.rs` and exited 0. No worktree can trip it today — every
# directory named here is committed, `vendor/` is the only gitignored input in
# this repository and no boundary rule reads it — so this is prevention. It is
# still worth writing: this is the fifth time the same shape has produced an
# incident here (`ci/check.sh` missing its modelgen step; monotest's 107 tests
# unrun; mini-vs-nanoda passing a crash; 41 Rust tests reporting `ok` with no
# corpus, twice, most recently at `4b463f1`), and the standing rule from
# `DECISIONS.md` 2026-08-08 is that SKIP is not PASS.
#
# The third case is the one a `-d` test alone would miss: a `derived/` that
# exists and holds only the allowlisted `$DERIVED_SCOPE`. The directory is
# there, the crate looks real, and the scan still reads zero files.
if [[ ! -d "$D" ]]; then
  fail "derived/ ($D) does not exist — I1's scan would have nothing to scan"
elif (( $(derived_files -print | wc -l) < 1 )); then
  fail "I1's scan matched no .rs files under $D (excluding tests/ and $DERIVED_SCOPE) — the rule would pass over nothing"
elif derived_scan | grep -q .; then
  fail "\`Thm::assume\`/\`Thm::implies_intr\` outside derived/$DERIVED_SCOPE"
  derived_scan >&2
  echo "  derived/$DERIVED_SCOPE is the one sanctioned introduction point. Route the" >&2
  echo "  derivation through \`discharge::under\`, which pairs the assumption with its" >&2
  echo "  discharge, rather than calling the kernel rules here." >&2
else
  ok "derived/ introduces hypotheses only in $DERIVED_SCOPE ($(derived_files -print | wc -l) file(s) scanned)"
fi
# The allowlist must not be vacuous: a module that never assumes would let I1
# pass while the rule protects nothing, which is how this check would rot.
#
# This used to run only `if [[ -f "$D/src/lib.rs" ]]`, because `ci/test-boundary.sh`
# pointed DERIVED_DIR at an empty directory for its clean baseline and a rule
# demanding an introduction module would have failed there. That made the
# non-vacuity check itself vacuous on exactly the input it most needed to
# reject, and the self-test's baseline is now a real one-file `derived/`
# fixture (`mk_derived`) instead — the guard's premise was the fixture, so the
# fixture is what changed. It is unconditional now, matching checker/'s.
if grep -q 'Thm::assume' "$D/$DERIVED_SCOPE" 2>/dev/null; then
  ok "derived/$DERIVED_SCOPE is the introduction point"
else
  fail "derived/$DERIVED_SCOPE does not call Thm::assume — I1 is now vacuous"
fi

# ── I1, checker/: exactly one introduction module ───────────────────────────
# Counted first, for the same reason as the kernel and derived scans: I1 and I3
# below are greps, and a grep over no files is silent in the same way a grep
# over clean files is. `crate_scan` fails closed on an absent directory, so this
# is about the *empty* case, which it cannot see.
checker_files=$(find "$C" -name '*.rs' -type f 2>/dev/null | wc -l)
if (( checker_files < 1 )); then
  fail "no .rs files under $C — I1 and I3 would scan nothing and report ok"
else
  ok "checker/ I1/I3 scan $checker_files file(s)"
fi
CHECKER_SCOPE="${CHECKER_SCOPE:-src/scope.rs}"
CHECKER_SCOPE_ALLOW="/${CHECKER_SCOPE}:"
# The former mini checker now lives as a checker module and retains its own
# scope implementation. Its stricter module-local discipline is checked by
# check-mini-scope.sh; exclude that one file from this crate-wide allowlist too.
if [[ -f "$C/src/mini/scope.rs" ]]; then
  CHECKER_SCOPE_ALLOW="${CHECKER_SCOPE_ALLOW}|/src/mini/scope.rs:"
fi
if crate_scan "$C" "$HYP_RE" "$CHECKER_SCOPE_ALLOW" >/dev/null; then
  fail "\`Thm::assume\`/\`Thm::implies_intr\` outside the checker scope modules"
  crate_scan "$C" "$HYP_RE" "$CHECKER_SCOPE_ALLOW" >&2
  echo "  Open a scope instead: \`crate::scope::Scopes::open\` in shipped code," >&2
  echo "  \`crate::scope::test_support::assume\` in a test." >&2
else
  ok "checker/ introduces hypotheses only in $CHECKER_SCOPE"
fi
# The allowlist must not be vacuous, or I1 says nothing.
if ! grep -q 'Thm::assume' "$C/$CHECKER_SCOPE" 2>/dev/null; then
  fail "checker/$CHECKER_SCOPE does not call Thm::assume — I1 is now vacuous"
else
  ok "checker/$CHECKER_SCOPE is the introduction point"
fi

# ── I3, checker/: no panicking generalisation ───────────────────────────────
# `Thm::gen(` is the panicking wrapper; `gen_checked` is a different token and
# the trailing `(` does not match it.
if crate_scan "$C" 'Thm::gen\(' >/dev/null; then
  fail "\`Thm::gen(\` — the panicking generalisation — is called in checker/"
  crate_scan "$C" 'Thm::gen\(' >&2
  echo "  Use \`Thm::gen_checked\` and let the side condition become a counted gap." >&2
else
  ok "checker/ generalises only through gen_checked"
fi

# ── I4, checker/: the persistence funnel ────────────────────────────────────
SEALED="${SEALED_FILE:-$C/src/sealed.rs}"
if [[ ! -f "$SEALED" ]]; then
  fail "the Sealed funnel ($SEALED) is missing — nothing checks what reaches a store"
elif grep -qE 'pub struct Sealed\(pub ' "$SEALED"; then
  fail "Sealed's field is public — the persistence funnel is open"
elif [[ "$(grep -cE '^\s*pub fn new\(' "$SEALED")" != "1" ]]; then
  fail "$SEALED does not have exactly one \`pub fn new\` (Sealed's)"
elif ! grep -q 'hyps().is_empty()' "$SEALED"; then
  fail "Sealed's constructor no longer checks hyps().is_empty()"
else
  ok "Sealed is a closed funnel with one checking constructor"
fi

# ── Coverage: no workspace member may go unscanned ──────────────────────────
# Rule 6 became ineffective within hours of being written because it named two
# directories and a third crate appeared. This asserts that every member of the
# workspace is accounted for by *something*: by rules 1–5 (the kernel), by R6′
# above, or by a named sibling script that exists and is run from ci/check.sh.
declare -A COVERED_HERE=( [kernel]="rules 1-5" [derived]="R6' I1" [checker]="R6' I1/I3/I4" )
declare -A COVERED_ELSEWHERE=()
# Both overridable so ci/test-boundary.sh can point the coverage check at a
# fixture workspace and assert that an unscanned member is caught.
WS_MANIFEST="${WS_MANIFEST:-$ROOT/Cargo.toml}"
CHECK_SH="${CHECK_SH:-$ROOT/ci/check.sh}"
members=$(awk '/^members[[:space:]]*=/{gsub(/.*\[|\].*/,""); gsub(/[",]/," "); print}' "$WS_MANIFEST" 2>/dev/null)
# …and the enumeration must enumerate. A missing manifest, or one whose
# `members` line this awk does not match, left `$members` empty and the loop
# below ran zero times — printing no `ok:` lines, raising no failure, and
# reporting a fully covered workspace. Measured: `WS_MANIFEST` pointing at a
# manifest with no parseable `members` exited 0 with "kernel boundary OK". The
# check that exists *because* rule 6 silently stopped covering a crate could
# itself silently stop covering every crate.
if [[ ! -f "$WS_MANIFEST" ]]; then
  fail "the workspace manifest ($WS_MANIFEST) is missing — the coverage check would enumerate nothing"
elif [[ -z "${members//[[:space:]]/}" ]]; then
  fail "no workspace members parsed from $WS_MANIFEST — the coverage check would enumerate nothing"
fi
for m in $members; do
  m="${m##*/}"
  if [[ -n "${COVERED_HERE[$m]:-}" ]]; then
    ok "workspace member '$m' covered here (${COVERED_HERE[$m]})"
  elif [[ -n "${COVERED_ELSEWHERE[$m]:-}" ]]; then
    sib="${COVERED_ELSEWHERE[$m]}"
    if [[ ! -x "$ROOT/$sib" ]]; then
      fail "workspace member '$m' is delegated to $sib, which is missing or not executable"
    elif ! grep -q "$sib" "$CHECK_SH" 2>/dev/null; then
      fail "workspace member '$m' is delegated to $sib, which ci/check.sh does not run"
    else
      ok "workspace member '$m' covered by $sib"
    fi
  else
    fail "workspace member '$m' is scanned by no hypothesis-discipline check — add it here or delegate it"
  fi
done

echo
if (( fails )); then
  echo "$fails boundary violation(s)" >&2
  exit 1
fi
echo "kernel boundary OK"
