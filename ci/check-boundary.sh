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
deps=$(awk '/^\[dependencies\]/{f=1;next} /^\[/{f=0} f {sub(/#.*/,"")} f && /=/{split($0,a,"="); gsub(/[ \t]/,"",a[1]); if (a[1] != "") print a[1]}' "$K/Cargo.toml")
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
if grep -rInE 'pub\s+(struct|enum)\s+Thm\b' --include='*.rs' "$K/src" | grep -q .; then
  # Having a public `Thm` type is expected; what must not exist is public
  # *fields* on it or a public constructor.
  if grep -rInE 'pub\s+struct\s+Thm\s*\(' --include='*.rs' "$K/src" | grep -qvE '\(\s*\)'; then
    fail "Thm appears to be a tuple struct with public field(s)"
  fi
  # Any `pub` field inside the Thm struct body. The trailing `:` is what makes
  # this a field declaration rather than the `pub struct Thm {` header line.
  if awk '/pub struct Thm/,/^}/' "$K/src"/*.rs 2>/dev/null \
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
elif awk '/^impl([[:space:]]|<).*Thm/,/^}/' "$K/src"/*.rs 2>/dev/null \
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
BUDGET=700
code_lines=$(cat "$K/src"/*.rs 2>/dev/null | grep -vE '^\s*(//|$)' | wc -l)
echo "  kernel non-comment lines: $code_lines"
if (( code_lines > BUDGET )); then
  fail "kernel exceeds $BUDGET non-comment lines ($code_lines) — something has leaked in"
else
  ok "size within budget ($code_lines <= $BUDGET)"
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
#       allowlist is vacuous). `derived/` has no such module: it *derives*, it
#       does not assume, and its house rule is the consumer half — every public
#       entry checks `hyps().is_empty()` as well as pinning its conclusion.
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
crate_scan() { # crate_scan <dir> <regex> [<path-substring to allow>]
  local d="$1" re="$2" allow="${3:-}"
  [[ -d "$d" ]] || return 0
  local hits
  hits=$(grep -rInE "$re" --include='*.rs' "$d" 2>/dev/null \
         | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*|#!\[)')
  if [[ -n "$allow" ]]; then
    hits=$(printf '%s\n' "$hits" | grep -v "$allow")
  fi
  printf '%s' "$hits" | grep -E '.'
}

# ── I1, derived/: no introduction module, so no introduction ────────────────
# `derived/` has no sanctioned place to assume, so the scan is a ban — but only
# over *shipped* code. Its test suite builds hypothetical theorems on purpose:
# that is how the consumer-side house rule (`derived::establishes`,
# `derived::all_unconditional`) is pinned, and there are twenty-odd such
# fixtures. So integration tests (anything under a `tests/` directory) and
# `#[cfg(test)]` items are skipped here. `checker/` needs no such exemption,
# because it has a sanctioned test entry point (`scope::test_support`) and I1 is
# therefore a single-*file* property there rather than a single-file-plus-cfg one.
derived_scan() {
  [[ -d "$D" ]] || return 0
  find "$D" -name '*.rs' -type f -not -path '*/tests/*' -print0 2>/dev/null \
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
if derived_scan | grep -q .; then
  fail "\`Thm::assume\`/\`Thm::implies_intr\` in shipped derived/ code — it has no sanctioned introduction module"
  derived_scan >&2
  echo "  derived/ derives; it does not assume. If a construction genuinely needs a" >&2
  echo "  hypothesis, give derived/ a scope module and allowlist it here, the way" >&2
  echo "  checker/src/scope.rs is allowlisted." >&2
else
  ok "derived/ introduces no hypothesis in shipped code"
fi

# ── I1, checker/: exactly one introduction module ───────────────────────────
CHECKER_SCOPE="${CHECKER_SCOPE:-src/scope.rs}"
if crate_scan "$C" "$HYP_RE" "/${CHECKER_SCOPE}:" >/dev/null; then
  fail "\`Thm::assume\`/\`Thm::implies_intr\` outside checker/$CHECKER_SCOPE"
  crate_scan "$C" "$HYP_RE" "/${CHECKER_SCOPE}:" >&2
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
declare -A COVERED_ELSEWHERE=( [mini]="ci/check-mini-scope.sh" )
# Both overridable so ci/test-boundary.sh can point the coverage check at a
# fixture workspace and assert that an unscanned member is caught.
WS_MANIFEST="${WS_MANIFEST:-$ROOT/Cargo.toml}"
CHECK_SH="${CHECK_SH:-$ROOT/ci/check.sh}"
members=$(awk '/^members[[:space:]]*=/{gsub(/.*\[|\].*/,""); gsub(/[",]/," "); print}' "$WS_MANIFEST")
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
