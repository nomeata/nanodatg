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
deps=$(awk '/^\[dependencies\]/{f=1;next} /^\[/{f=0} f && /=/{split($0,a,"="); gsub(/[ \t]/,"",a[1]); if (a[1] != "") print a[1]}' "$K/Cargo.toml")
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
# "A few hundred lines. If it grows past ~1000, something has leaked in that
# belongs in check/ or interp/." Counted excluding comments and blank lines, so
# documentation (which we want lots of) does not eat the budget.
code_lines=$(cat "$K/src"/*.rs 2>/dev/null | grep -vE '^\s*(//|$)' | wc -l)
echo "  kernel non-comment lines: $code_lines"
if (( code_lines > 1000 )); then
  fail "kernel exceeds 1000 non-comment lines ($code_lines) — something has leaked in"
else
  ok "size within budget ($code_lines <= 1000)"
fi

echo
if (( fails )); then
  echo "$fails boundary violation(s)" >&2
  exit 1
fi
echo "kernel boundary OK"
