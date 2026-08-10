#!/usr/bin/env bash
# R6′ — the hypothesis discipline for `mini/` (MINI-DESIGN.md §4.4).
#
# `ci/check-boundary.sh` used to *ban* `Thm::assume`/`Thm::implies_intr` outside
# the kernel, for two engineering reasons rather than a soundness one:
# `Thm::gen`'s infallible signature panics on a hypothetical theorem, and a
# `concl()` read without a `hyps()` read trusts a sequent it should not. Mini
# needs hypotheses — a constant-cost local context is the whole reason the
# sequent judgement exists — so it answered those two hazards at their sites
# instead, and this script checks the answers. The ban is gone: task #30 replaced
# it with R6' for `derived/` and `checker/` too, and this script is what
# `check-boundary.sh`'s coverage check delegates `mini/` to.
#
#   I1  `Thm::assume` / `Thm::implies_intr` appear only in mini/src/scope.rs.
#   I3  `Thm::gen(` — the panicking wrapper — appears nowhere; `gen_checked`
#       is the only entry.
#
#       **This rule has a blind spot by construction, and it is a spelling ban
#       rather than a reachability ban.** `derived::gen_all` calls `Thm::gen`
#       internally and is callable from any crate, so a `mini/` site that
#       generalises through it is equally exposed to the side condition and
#       invisible here. That is not hypothetical: the `u ≥ 1` quotient clauses
#       had three such sites, one spelled `Thm::gen` and caught by this check
#       and two spelled `derived::gen_all` and not — all three wrong for the
#       same reason, that `derived`'s theorems are unconditional by
#       construction while mini's `Γ` is live. Anyone adding a banned primitive
#       here should assume the same hole: **a path-based ban catches the
#       spelling, not the route.** Closing it needs a call-graph check rather
#       than a grep and has not been attempted; what is written down instead is
#       that the check covers less than its name says.
#   I4  the persistence funnel is `Sealed`, whose only constructor checks
#       `hyps().is_empty()`. Checked by type rather than by grep; what is
#       grepped here is that no *other* module reconstructs one.
#
# `check-boundary.sh` does not scan `mini/`; it asserts that this script exists,
# is executable, and is run from `ci/check.sh`. Widening that scan instead of
# keeping this one is fine — `mini/src/scope.rs` is then the allowlist entry —
# but one of the two must hold, and the coverage check is what says so.

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
# The persistence funnel is `Sealed` — since ENV-UNIFY.md B3 **the checker's
# type, re-exported** (`checker/src/sealed.rs`, whose private field, single
# checking constructor and `hyps().is_empty()` gate `ci/check-boundary.sh`'s
# own I4 already pins). What is checked here is that mini really does route
# through that one funnel: the re-export is present, and no module of mini's
# defines a `Sealed` of its own — a second newtype would be a second funnel
# with whatever gate its author remembered to give it.
if ! grep -q 'pub use nanoda_lib::sealed::Sealed' "$M/src/ev.rs" 2>/dev/null; then
  fail "mini/src/ev.rs no longer re-exports the checker's Sealed — the one-funnel identity (ENV-UNIFY B3) is gone"
else
  ok "Sealed is the checker's type, re-exported"
fi
if grep -rInE 'struct Sealed' --include='*.rs' "$M/src" 2>/dev/null \
     | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(//|\*)' | grep -q .; then
  fail "a mini module defines its own Sealed — a second persistence funnel"
  grep -rInE 'struct Sealed' --include='*.rs' "$M/src" >&2
else
  ok "no second Sealed newtype in mini"
fi

echo
if (( fails )); then
  echo "$fails R6' violation(s)" >&2
  exit 1
fi
echo "mini hypothesis discipline OK"
