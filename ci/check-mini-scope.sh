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
#   C   the scan found files at all, and each ban has a non-vacuity partner.
#       See below — this was the last `ci/*.sh` without a rule of this shape.
#
# `check-boundary.sh` does not scan `mini/`; it asserts that this script exists,
# is executable, and is run from `ci/check.sh`. Widening that scan instead of
# keeping this one is fine — `mini/src/scope.rs` is then the allowlist entry —
# but one of the two must hold, and the coverage check is what says so.
#
# # C — counting what was scanned, and why a pure ban is not enough
#
# I1, I3 and I4's second half are **bans**: they pass when a grep matches
# nothing. A grep matches nothing when the ban holds, and it also matches
# nothing when there is nothing to grep — `mini/src` renamed or split, a second
# crate growing beside it, `--include='*.rs'` stopping to match. Those two
# outcomes are printed identically (`ok: …`) and exit identically (0), so
# without a count this script cannot tell "mini is clean" from "mini is not
# here", and it would report the second as the first. That is `ci/
# check-test-guards.sh`'s rule C one level over, and this was the only
# `ci/*.sh` that did not have it: every neighbour (`check-arena.sh`'s `(of N)`,
# `check-feature-inert.sh`'s and `check-uplift.sh`'s `cells`, `check-modelgen.sh`'s
# check counts) says how much it measured, and this said nothing.
#
# So three things are pinned, and the two greps that anchor them use the *same*
# `--include='*.rs'` recursion the bans use, so anything that blinds the bans
# blinds the count too rather than only one of them:
#
#   * **a file count with a floor** (`MIN_FILES`, default 10). Not a ratchet on
#     the exact number — mini has 62 modules today and they come and go — but a
#     tree that has lost an order of magnitude of them is a tree the bans are
#     no longer scanning. Two files is what remains when only the anchors below
#     survive, which is exactly the state that must not read as green.
#   * **I1's partner**: `scope.rs` really does call `Thm::assume`. Already here.
#   * **I3's partner**: some non-comment line really does call
#     `Thm::gen_checked(`. "`gen_checked` is the only entry" is a claim about a
#     door that is used; if nothing in mini generalises at all, banning the
#     panicking spelling proves nothing about the fallible one being preferred.
#
# I4's partner is its own first half: the `Sealed` re-export must be present,
# which is a positive check already.
#
# # `--self-test`
#
# Plants a violation of each rule — including each C cell — against a fixture
# tree handed in through `MINI_DIR`, and asserts this script rejects it; and
# asserts a clean fixture passes. It needs no corpus and no Lean toolchain, so
# it runs on every machine. `ci/check-test-guards.sh --self-test` and
# `ci/check-modelgen.sh --self-test` are the same idea; a guard nobody has
# watched fail is not known to work.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
M="${MINI_DIR:-$ROOT/mini}"
# Zero would make the floor unfalsifiable; 62 would make it a ratchet on a
# number nobody owns. See "C" above.
MIN_FILES="${MIN_FILES:-10}"
fails=0
fail() { echo "R6' VIOLATION: $*" >&2; fails=$((fails+1)); }
ok()   { echo "  ok: $*"; }

# ── the self-test ───────────────────────────────────────────────────────────
# `MINI_DIR` is the seam: the whole body below reads `$M/src` and nothing else,
# so a fixture tree with a `src/` in it is a whole mini as far as this script is
# concerned.
self_test() {
  # Not `local`: the EXIT trap fires after the function returns and `set -u`
  # would find a local unbound by then.
  TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
  local sfails=0

  # A clean fixture: scope.rs introduces the hypotheses and closes them through
  # the fallible generaliser, ev.rs re-exports the checker's Sealed, and enough
  # ordinary modules beside them to clear the scan floor.
  mk_clean() {
    local d="$1" i; mkdir -p "$d/src"
    cat > "$d/src/scope.rs" <<'EOF'
//! The one module that names `Thm::assume`. Prose here may spell the banned
//! `Thm::gen(` and `struct Sealed` without calling anything.
pub fn open(h: &Expr) -> Thm { Thm::assume(h) }
pub fn close(h: &Expr, t: &Thm, w: u32) -> Option<Thm> {
    let imp = Thm::implies_intr(h, t);
    Thm::gen_checked(w, &imp)
}
EOF
    cat > "$d/src/ev.rs" <<'EOF'
pub use nanoda_lib::sealed::Sealed;
EOF
    for i in 1 2 3 4 5 6 7 8 9 10; do
      printf 'pub fn m%s() -> u32 { %s }\n' "$i" "$i" > "$d/src/mod$i.rs"
    done
  }

  expect() { # expect pass|fail <name> <mini dir> [env...]
    local want="$1" name="$2" d="$3"; shift 3
    local rc; env MINI_DIR="$d" "$@" "$0" >/dev/null 2>&1; rc=$?
    if [[ "$want" == pass && $rc -eq 0 ]] || [[ "$want" == fail && $rc -ne 0 ]]; then
      if [[ "$want" == fail ]]; then echo "  ok: detects $name"; else echo "  ok: accepts $name"; fi
    else
      echo "SELFTEST FAIL: '$name' expected to $want, got rc=$rc" >&2
      env MINI_DIR="$d" "$@" "$0" >&2
      sfails=$((sfails+1))
    fi
  }

  echo "self-testing $0"

  d="$TMP/clean"; mk_clean "$d"; expect pass "a clean mini" "$d"

  # ── I1, both directions.
  d="$TMP/i1_second"; mk_clean "$d"
  echo 'pub fn sneak(h: &Expr) -> Thm { Thm::assume(h) }' >> "$d/src/mod1.rs"
  expect fail "a second introduction point" "$d"

  d="$TMP/i1_intr"; mk_clean "$d"
  echo 'pub fn sneak(h: &Expr, t: &Thm) -> Thm { Thm::implies_intr(h, t) }' >> "$d/src/mod2.rs"
  expect fail "an implies_intr outside scope.rs" "$d"

  d="$TMP/i1_comment"; mk_clean "$d"
  printf '// `Thm::assume` is what scope.rs calls; this line calls nothing.\n' >> "$d/src/mod1.rs"
  expect pass "prose naming the banned primitive" "$d"

  d="$TMP/i1_vacuous"; mk_clean "$d"
  grep -v 'Thm::assume' "$TMP/clean/src/scope.rs" > "$d/src/scope.rs"
  expect fail "a scope.rs that no longer introduces anything" "$d"

  # ── I3, both directions.
  d="$TMP/i3_gen"; mk_clean "$d"
  echo 'pub fn boom(w: u32, t: &Thm) -> Thm { Thm::gen(w, t) }' >> "$d/src/mod3.rs"
  expect fail "the panicking Thm::gen(" "$d"

  d="$TMP/i3_comment"; mk_clean "$d"
  printf '// `Thm::gen(` panics on a hypothetical theorem; we do not call it.\n' >> "$d/src/mod3.rs"
  expect pass "prose naming Thm::gen(" "$d"

  # I3's partner: a mini that generalises nowhere. Every ban still passes, and
  # that is the point — "gen_checked is the only entry" is then a claim about a
  # door nobody walks through.
  d="$TMP/i3_vacuous"; mk_clean "$d"
  grep -v 'gen_checked' "$TMP/clean/src/scope.rs" > "$d/src/scope.rs"
  expect fail "a mini that calls no generaliser at all" "$d"

  # ── I4, both halves.
  d="$TMP/i4_reexport"; mk_clean "$d"; echo 'pub struct Ev;' > "$d/src/ev.rs"
  expect fail "an ev.rs that no longer re-exports Sealed" "$d"

  d="$TMP/i4_second"; mk_clean "$d"
  echo 'pub struct Sealed(Thm);' >> "$d/src/mod4.rs"
  expect fail "a second Sealed newtype" "$d"

  # ── C: the scan itself.
  # The anchors survive and every ban passes — this is a tree in which
  # `mini/src` has been emptied out from under the greps, which is what the
  # count is for. Without the floor this is a green run over two files.
  d="$TMP/c_anchors_only"; mk_clean "$d"; rm -f "$d"/src/mod*.rs
  expect fail "a src/ holding only the two anchors" "$d"

  # …and the floor is a real comparison, not a `> 0`: the clean tree fails it
  # when the bar is put above the tree.
  d="$TMP/clean"; expect fail "a clean mini under a floor it cannot clear" "$d" MIN_FILES=999

  # A `src/` that is not there at all. The anchors already catch this; the cell
  # is here so that the day they are relaxed, C is still watching.
  d="$TMP/c_gone"; mkdir -p "$d"
  expect fail "a mini whose src/ has moved away" "$d"

  echo
  if (( sfails )); then echo "$sfails self-test failure(s)" >&2; return 1; fi
  echo "mini-scope self-test OK"
}

if [[ "${1:-}" == --self-test ]]; then self_test; exit $?; fi

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

# …and the partner, so the ban is not a statement about an unused door: some
# non-comment line must actually call the fallible entry. A mini that
# generalises nowhere passes the ban above having demonstrated nothing.
gen_sites=$(grep -rInE 'Thm::gen_checked\(' --include='*.rs' "$M/src" 2>/dev/null \
  | grep -cvE '^[^:]+:[0-9]+:[[:space:]]*(//|\*)')
if (( gen_sites == 0 )); then
  fail "nothing in mini calls \`Thm::gen_checked(\` — I3 bans a spelling nobody was using, so it is now vacuous"
else
  ok "gen_checked is called ($gen_sites site(s)), so I3 bans a live alternative"
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

# ── C ────────────────────────────────────────────────────────────────────────
# The same recursion and the same `--include` the three bans use, so a change
# that blinds them blinds this too. `-I` skips anything grep would treat as
# binary, again as above; `-l -e ''` lists every file it would have searched.
scanned=$(grep -rIl --include='*.rs' -e '' "$M/src" 2>/dev/null | wc -l)
if (( scanned < MIN_FILES )); then
  fail "the scan searched $scanned file(s) under $M/src, expected at least $MIN_FILES — the bans above passed having read almost nothing"
else
  ok "C $scanned files scanned"
fi

echo
if (( fails )); then
  echo "$fails R6' violation(s)" >&2
  exit 1
fi
echo "mini hypothesis discipline OK ($scanned files scanned)"
