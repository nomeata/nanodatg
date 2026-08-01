#!/usr/bin/env bash
# R6′ — the hypothesis discipline for `mini/` (MINI-DESIGN.md §4.4).
#
# `ci/check-boundary.sh` rule 6 *bans* `Thm::assume`/`Thm::implies_intr` outside
# the kernel, for two engineering reasons rather than a soundness one:
# `Thm::gen`'s infallible signature panics on a hypothetical theorem, and a
# `concl()` read without a `hyps()` read trusts a sequent it should not. Mini
# needs hypotheses — a constant-cost local context is the whole reason the
# sequent judgement exists — so it answers those two hazards at their sites
# instead, and this script checks the answers.
#
#   I1  `Thm::assume` / `Thm::implies_intr` appear only in mini/src/scope.rs.
#   I3  `Thm::gen(` — the panicking wrapper — appears nowhere; `gen_checked`
#       is the only entry.
#   I4  the persistence funnel is `Sealed`, whose only constructor checks
#       `hyps().is_empty()`. Checked by type rather than by grep; what is
#       grepped here is that no *other* module reconstructs one.
#
# Note rule 6 does not scan `mini/` today, so nothing in this file overlaps with
# it; if that scan is ever widened, `mini/src/scope.rs` is the allowlist entry.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
M="${MINI_DIR:-$ROOT/mini}"
fails=0
fail() { echo "R6' VIOLATION: $*" >&2; fails=$((fails+1)); }
ok()   { echo "  ok: $*"; }

echo "checking mini's hypothesis discipline in $M"

# Comments and the allowlisted module are excluded; a mention in prose calls
# nothing, and the whole point of I1 is that one file may call these.
scan() {
  grep -rInE "$1" --include='*.rs' "$M/src" 2>/dev/null \
    | grep -v '^[^:]*/scope\.rs:' \
    | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*|#!\[)'
}

# ── I1 ───────────────────────────────────────────────────────────────────────
if scan 'Thm::(assume|implies_intr)' | grep -q .; then
  fail "\`Thm::assume\`/\`Thm::implies_intr\` outside mini/src/scope.rs"
  scan 'Thm::(assume|implies_intr)' >&2
else
  ok "hypotheses are introduced only in scope.rs"
fi

# scope.rs must actually be the introduction point, or I1 is vacuous and the
# scoping machinery has been bypassed some other way.
if ! grep -q 'Thm::assume' "$M/src/scope.rs" 2>/dev/null; then
  fail "mini/src/scope.rs no longer calls Thm::assume — I1 is now vacuous"
else
  ok "scope.rs is the introduction point"
fi

# ── I3 ───────────────────────────────────────────────────────────────────────
# `Thm::gen(` is the panicking wrapper. `gen_checked` is a different token and
# is not matched by the trailing `(`.
if grep -rInE 'Thm::gen\(' --include='*.rs' "$M/src" 2>/dev/null \
     | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*)' | grep -q .; then
  fail "\`Thm::gen(\` — the panicking generalisation — is called in mini"
  grep -rInE 'Thm::gen\(' --include='*.rs' "$M/src" >&2
else
  ok "no panicking generalisation (gen_checked only)"
fi

# ── I4 ───────────────────────────────────────────────────────────────────────
# `Sealed` is a newtype whose only constructor checks emptiness. A second
# constructor, or a public field, would reopen the funnel.
if grep -qE 'pub struct Sealed\(pub ' "$M/src/ev.rs" 2>/dev/null; then
  fail "Sealed's field is public — the persistence funnel is open"
else
  ok "Sealed's field is private"
fi
if [[ "$(grep -cE '^\s*pub fn new\(' "$M/src/ev.rs" 2>/dev/null)" != "1" ]]; then
  fail "mini/src/ev.rs does not have exactly one \`pub fn new\` (Sealed's)"
else
  ok "Sealed has exactly one constructor"
fi

echo
if (( fails )); then
  echo "$fails R6' violation(s)" >&2
  exit 1
fi
echo "mini hypothesis discipline OK"
