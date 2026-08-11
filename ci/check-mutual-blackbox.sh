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
# `env::{Declaration, ConstantInfo, Environment}`, and exactly two entry points
# into mini's checker: `kernel::add`, whose whole output is accept-or-reject
# plus a syntactic environment, and `kernel::sort_under`, whose whole output is
# a `Level`. Reading a `ConstantInfo::Recursor`'s declared type and rules is
# reading *zone A's* syntax, which is how the encoder states its theorems
# without inventing them.
#
# **Asking the checker a question is not the banned thing; reading its
# certificates is.** The encoder needs the sort an index type lives in, and
# that is not derivable from the declaration — an index of type `N` is
# `Sort 1` only because `N`'s declaration says so. So it asks. The allowlist
# below is by name and is the whole of the licence: a third entry point cannot
# appear without someone editing this rule and saying why.
#
# A violation is not necessarily a bug. It is a design finding: it means some
# step of the encoding could not be done in Lean world, and that is the thing
# that decides whether the nested-inductive repeat is cheap. Report it; do not
# silence it.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# **Three files, one invariant.** `mutual_aux.rs` turns a `mutual … end` block
# into Lean-world syntax; `nested.rs` turns a *nested* declaration into a mutual
# block, asks the checker whether it is well-formed, and restores what comes
# back; `nested_splice.rs` recognises the model `modelgen` spliced into the
# export and hands the evidence layer a `(Name, σ) -> Name` table saying which
# model constant carries which export constant's interpretation. All three are
# consumers of the checker and none may look inside a certificate, so they are
# scanned by the same rule rather than by three rules that could drift apart.
#
# The third is the one whose membership is least obvious and most worth having:
# it *produces the keying*, so if any file in the pipeline were going to need to
# read a `Term` it would be that one. It does not — the table is syntax, and
# `zoneb::model_alias` is where a certificate is first touched.
#
# *This list had a fourth entry, `mini/src/nested_ev.rs`, which generated the
# model in Rust. `modelgen/` generates it now, as an export filter, and the file
# is deleted; the boundary it was scanned for is not weakened by that — a Lean
# package cannot name a `Term` at all.*
#
# **A new encoder is added here or its header's boundary claim is unchecked.**
# `nested_ev.rs` shipped with that claim in its header for the length of one
# commit before this line existed, which is the reason the sentence is here.
FILES=(checker/src/mini/mutual_aux.rs checker/src/mini/nested.rs checker/src/mini/nested_splice.rs)

for f in "${FILES[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "  FAIL: $f is missing — a black-box consumer is supposed to live there" >&2
    exit 1
  fi
done

# Exactly two entry points into mini's checker are licensed. See the header.
ALLOWED="add sort_under"

# One function, run twice: on the file, where it must find nothing, and on the
# file with violations planted, where it must find them. A check that has never
# been seen to fail is not evidence — `ci/test-boundary.sh` makes the same
# argument for the kernel boundary at greater length.
#
# `$1` is the *body*: the header describes the boundary and has to be able to
# name the things on the other side of it, so comments are stripped before the
# scan. Doc comments are prose; code is the claim.
scan() {
  local body="$1" quiet="$2" fails=0
  local sym used
  # `\b` on both sides so `Term` does not match `Terminal` and `Ev` does not
  # match `Every`.
  for sym in Term Thm Formula Ev Gap Sealed Interp Parts; do
    if grep -qE "\\b${sym}\\b" <<<"$body"; then
      [[ $quiet == quiet ]] || { echo "  FAIL: $FILE names \`$sym\`" >&2
        grep -nE "\\b${sym}\\b" <<<"$body" | head -5 >&2; }
      fails=$((fails+1))
    fi
  done
  for sym in as_eq as_mem concl skeleton interp:: kernel::Checker; do
    if grep -qF "$sym" <<<"$body"; then
      [[ $quiet == quiet ]] || { echo "  FAIL: $FILE uses \`$sym\`" >&2
        grep -nF "$sym" <<<"$body" | head -5 >&2; }
      fails=$((fails+1))
    fi
  done
  # Every `kernel::<lowercase>` must be on the allowlist.
  while read -r used; do
    [[ -z "$used" ]] && continue
    if ! grep -qw -- "$used" <<<"$ALLOWED"; then
      [[ $quiet == quiet ]] || echo "  FAIL: $FILE calls \`kernel::$used\`, not on the allowlist ($ALLOWED)" >&2
      fails=$((fails+1))
    fi
  done < <(grep -oE "kernel::[a-z_][A-Za-z0-9_]*" <<<"$body" | sed 's/^kernel:://' | sort -u)
  echo "$fails"
}

strip() { sed -E 's:[[:space:]]*//.*$::' ; }

real=0
BODY=""
for f in "${FILES[@]}"; do
  FILE="$f"
  b="$(strip < "$f")"
  real=$((real + $(scan "$b" loud)))
  BODY="$BODY
$b"
done

# The self-test plants one of each kind of violation: a banned type, and a
# kernel entry point that is not on the allowlist.
PLANTED="$(printf '%s\nfn _probe(_t: kernel::Thm) { crate::kernel::infer_type(); }\n' "$BODY")"
planted="$(scan "$PLANTED" quiet)"

if (( planted < 2 )); then
  echo "  FAIL: the self-test found $planted of 2 planted violations — this check cannot detect anything" >&2
  exit 1
fi
echo "  ok: the check finds both planted violations (a \`Thm\`, an unlisted kernel entry point)"

if (( real )); then
  echo "black-box check FAILED ($real)" >&2
  exit 1
fi
echo "  ok: ${FILES[*]} name nothing on the evidence side of the boundary"
echo "black-box OK"
