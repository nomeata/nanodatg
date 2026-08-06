#!/usr/bin/env bash
# **The mutual pipeline is a black box over the evidence layer.**
#
# The design of `mini/src/mutual_aux.rs` rests on one claim: the machinery that
# turns a `mutual … end` block into an auxiliary inductive and a list of
# ordinary definitions is *completely ignorant of what is inside a `Term` or a
# `Thm`*. It emits Lean-world syntax, the evidence-producing checker consumes
# it, and what comes back is a TG term and a typing proof for every constant of
# the block. Nothing in the encoder inspects, destructures or decides on a
# certificate.
#
# That claim is worth exactly as much as a check that can fail, so this is it.
# The precedent is `ci/check-boundary.sh` and `ci/check-mini-scope.sh`, and the
# reason `mutual_aux.rs` is a file of its own rather than a section of
# `kernel.rs` is that at file granularity the rule is writable and at function
# granularity it is not.
#
# **What is banned, and why each.**
#
# * `Term`, `Thm`, `Formula` — the kernel's own types. Naming one is the
#   definition of looking inside.
# * `Ev`, `Gap`, `Sealed` — mini's evidence wrappers. A module that decided
#   anything from a `Gap` would be branching on whether a certificate exists.
# * `Interp`, `interp::` — the interpretation store. Reading `⟦·⟧` is reading
#   the other side of the boundary.
# * `as_eq`, `as_mem`, `concl`, `Parts`, `skeleton` — the accessors a consumer
#   would use to read a theorem's statement.
#
# **What is allowed, and the list is short.** `mini::Expr` and `mini::Name`,
# `env::{Declaration, ConstantInfo, Environment}`, and `kernel::add` — whose
# entire output is accept-or-reject plus a syntactic environment. Reading a
# `ConstantInfo::Recursor`'s declared type and rules is reading *zone A's*
# syntax, which is how the encoder states its theorems without inventing them.
#
# A violation is not necessarily a bug. It is a design finding: it means some
# step of the encoding could not be done in Lean world, and that is the thing
# that decides whether the nested-inductive repeat is cheap. Report it; do not
# silence it.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILE="mini/src/mutual_aux.rs"
fails=0

if [[ ! -f "$FILE" ]]; then
  echo "  FAIL: $FILE is missing — the mutual encoder is supposed to live there" >&2
  exit 1
fi

# The body only: the module header *describes* the boundary and has to be able
# to name the things on the other side of it. Doc comments are prose, code is
# the claim. `///` and `//!` and `//` all go; a banned name inside a string
# literal would survive, and there are none.
BODY="$(sed -E 's:[[:space:]]*//.*$::' "$FILE")"

# `\b` on both sides so `Term` does not match `Terminal` and `Ev` does not match
# `Every`. `Formula` and `Sealed` have no such neighbours but are spelled the
# same way for uniformity.
for sym in Term Thm Formula Ev Gap Sealed Interp Parts; do
  if grep -qE "\\b${sym}\\b" <<<"$BODY"; then
    echo "  FAIL: $FILE names \`$sym\`" >&2
    grep -nE "\\b${sym}\\b" <<<"$BODY" | head -5 >&2
    fails=$((fails+1))
  fi
done

for sym in as_eq as_mem concl skeleton interp:: kernel::Checker; do
  if grep -qF "$sym" <<<"$BODY"; then
    echo "  FAIL: $FILE uses \`$sym\`" >&2
    grep -nF "$sym" <<<"$BODY" | head -5 >&2
    fails=$((fails+1))
  fi
done

# The `kernel` crate is the trusted base; the encoder must not depend on it at
# all. `crate::kernel` is mini's own checker and is allowed.
if grep -qE "(^|[^:[:alnum:]_])kernel::(Term|Thm|Formula)" <<<"$BODY"; then
  echo "  FAIL: $FILE reaches into the trusted kernel" >&2
  fails=$((fails+1))
fi

# **The check must be able to fail**, or it is decoration. `ci/test-boundary.sh`
# makes the same argument for the boundary check; here it is one line, because
# the check is one grep over one file.
PROBE="$(mktemp)"
trap 'rm -f "$PROBE"' EXIT
{ cat "$FILE"; echo 'fn _probe(_t: kernel::Thm) {}'; } > "$PROBE"
if grep -qE '\bThm\b' <(sed -E 's:[[:space:]]*//.*$::' "$PROBE"); then
  echo "  ok: the check fires on a planted \`Thm\`"
else
  echo "  FAIL: the self-test did not fire — this check cannot detect anything" >&2
  fails=$((fails+1))
fi

if (( fails )); then
  echo "mutual black-box check FAILED ($fails)" >&2
  exit 1
fi
echo "  ok: $FILE names nothing on the evidence side of the boundary"
echo "mutual black-box OK"
