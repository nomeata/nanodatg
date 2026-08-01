#!/usr/bin/env bash
# Self-test for ci/check-boundary.sh.
#
# A boundary check that cannot fail provides no assurance. This builds a
# synthetic "kernel" for each rule, violates exactly that rule, and asserts the
# checker rejects it — and that the clean baseline is accepted.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CHECK="$ROOT/ci/check-boundary.sh"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fails=0

# R6' scans the *non*-kernel crates. Point every one of its inputs at a clean
# fixture for the whole self-test, so each fixture below is hermetic: whether
# `derived/` and `checker/` obey R6' is check-boundary.sh's job, not this
# script's, and a violation there must not make the self-test report the checker
# as broken. Each R6' fixture then overrides exactly the one input it violates.
mkdir -p "$TMP/no-derived"
export DERIVED_DIR="$TMP/no-derived"

# A clean `checker` fixture: an introduction module that really introduces, no
# panicking generalisation, and a closed `Sealed`.
mk_checker() {
  local d="$1"; mkdir -p "$d/src"
  cat > "$d/src/scope.rs" <<'EOF'
//! The one introduction point.
pub fn open(phi: Formula) -> Thm { Thm::assume(phi) }
pub fn close(h: &Formula, t: &Thm) -> Thm { Thm::implies_intr(h, t) }
EOF
  cat > "$d/src/sealed.rs" <<'EOF'
pub struct Sealed(Thm);
impl Sealed {
    pub fn new(t: Thm) -> Result<Sealed, Thm> {
        if t.hyps().is_empty() { Ok(Sealed(t)) } else { Err(t) }
    }
}
EOF
  cat > "$d/src/tg.rs" <<'EOF'
pub fn g(x: FreeVar, t: &Thm) -> Option<Thm> { Thm::gen_checked(x, t) }
EOF
}
mk_checker "$TMP/chk-clean"
export CHECKER_DIR="$TMP/chk-clean"

# Build a minimal well-formed kernel fixture in $1.
mk_clean() {
  local d="$1"; mkdir -p "$d/src"
  cat > "$d/Cargo.toml" <<'EOF'
[package]
name = "k"
version = "0.0.0"
edition = "2021"

[dependencies]
EOF
  cat > "$d/src/lib.rs" <<'EOF'
#![forbid(unsafe_code)]
pub struct Thm {
    concl: u32,
}
impl Thm {
    pub fn concl(&self) -> u32 { self.concl }
}
EOF
}

# expect_fail <name> <dir>; expect_pass <name> <dir>
expect_fail() {
  if KERNEL_DIR="$2" "$CHECK" >/dev/null 2>&1; then
    echo "SELFTEST FAIL: '$1' was not detected" >&2; fails=$((fails+1))
  else
    echo "  ok: detects $1"
  fi
}
expect_pass() {
  if KERNEL_DIR="$2" "$CHECK" >/dev/null 2>&1; then
    echo "  ok: accepts $1"
  else
    echo "SELFTEST FAIL: '$1' should have passed" >&2
    KERNEL_DIR="$2" "$CHECK" >&2
    fails=$((fails+1))
  fi
}

# Same two, for R6': a clean kernel, with $2.. an env assignment list naming the
# one input this fixture varies (DERIVED_DIR=..., CHECKER_DIR=..., ...).
expect_fail_out() {
  local name="$1"; shift
  if env "$@" KERNEL_DIR="$TMP/clean" "$CHECK" >/dev/null 2>&1; then
    echo "SELFTEST FAIL: '$name' was not detected" >&2; fails=$((fails+1))
  else
    echo "  ok: detects $name"
  fi
}
expect_pass_out() {
  local name="$1"; shift
  if env "$@" KERNEL_DIR="$TMP/clean" "$CHECK" >/dev/null 2>&1; then
    echo "  ok: accepts $name"
  else
    echo "SELFTEST FAIL: '$name' should have passed" >&2
    env "$@" KERNEL_DIR="$TMP/clean" "$CHECK" >&2
    fails=$((fails+1))
  fi
}

echo "self-testing $CHECK"

d="$TMP/clean"; mk_clean "$d"; expect_pass "a clean kernel" "$d"

d="$TMP/unsafe"; mk_clean "$d"
echo 'pub fn f() { unsafe { } }' >> "$d/src/lib.rs"
expect_fail "unsafe block" "$d"

d="$TMP/noforbid"; mk_clean "$d"
sed -i '/forbid(unsafe_code)/d' "$d/src/lib.rs"
expect_fail "missing #![forbid(unsafe_code)]" "$d"

d="$TMP/dep"; mk_clean "$d"
echo 'rand = "0.8"' >> "$d/Cargo.toml"
expect_fail "external dependency" "$d"

# The sanctioned bignum exception is only allowed when documented in README.md.
d="$TMP/bignum_undoc"; mk_clean "$d"
echo 'num-bigint = "0.4"' >> "$d/Cargo.toml"
expect_fail "undocumented sanctioned dependency" "$d"

d="$TMP/bignum_doc"; mk_clean "$d"
echo 'num-bigint = "0.4"' >> "$d/Cargo.toml"
echo 'TCB entry: num-bigint is vetted and pinned.' > "$d/README.md"
expect_pass "documented sanctioned dependency" "$d"

d="$TMP/pubfield"; mk_clean "$d"
sed -i 's/    concl: u32,/    pub concl: u32,/' "$d/src/lib.rs"
expect_fail "public field on Thm" "$d"

d="$TMP/ctor"; mk_clean "$d"
cat >> "$d/src/lib.rs" <<'EOF'
impl Thm {
    pub fn new(c: u32) -> Self { Thm { concl: c } }
}
EOF
expect_fail "escape-hatch constructor in impl Thm" "$d"

d="$TMP/ctor2"; mk_clean "$d"
echo 'pub fn from_parts(c: u32) -> Thm { Thm { concl: c } }' >> "$d/src/lib.rs"
expect_fail "free function returning Thm" "$d"

d="$TMP/io"; mk_clean "$d"
echo 'pub fn f() { println!("derivation"); }' >> "$d/src/lib.rs"
expect_fail "printing" "$d"

d="$TMP/serde"; mk_clean "$d"
echo '#[derive(Serialize)] pub struct S;' >> "$d/src/lib.rs"
expect_fail "serialization" "$d"

d="$TMP/big"; mk_clean "$d"
for i in $(seq 1 1100); do echo "pub fn f$i() {}" >> "$d/src/lib.rs"; done
expect_fail "size budget overrun" "$d"

# A comment mentioning `unsafe` must NOT trip the check (regression: it did).
d="$TMP/comment"; mk_clean "$d"
echo '// this module must never contain unsafe code' >> "$d/src/lib.rs"
echo '/// nor `unsafe` in a doc comment' >> "$d/src/lib.rs"
expect_pass "comments mentioning unsafe" "$d"

# ── R6': the hypothesis discipline outside the kernel ───────────────────────
# The baseline: a clean `derived` (nothing) and the clean `checker` fixture.
expect_pass_out "a clean derived/ and checker/" DERIVED_DIR="$TMP/no-derived"

# ── I1, derived/: a ban over shipped code, with the test exemptions ─────────
mk_derived() { mkdir -p "$1/src"; echo 'pub fn f() { let _ = Thm::eq_refl(x); }' > "$1/src/lib.rs"; }

o="$TMP/der_clean"; mk_derived "$o"
expect_pass_out "a derived/ that builds no hypothesis" DERIVED_DIR="$o"

o="$TMP/der_assume"; mk_derived "$o"
echo 'pub fn g(p: Formula) -> Thm { Thm::assume(p) }' >> "$o/src/lib.rs"
expect_fail_out "Thm::assume in shipped derived/ code" DERIVED_DIR="$o"

o="$TMP/der_intr"; mk_derived "$o"
echo 'pub fn g(p: &Formula, t: &Thm) -> Thm { Thm::implies_intr(p, t) }' >> "$o/src/lib.rs"
expect_fail_out "Thm::implies_intr in shipped derived/ code" DERIVED_DIR="$o"

# A nested module is still shipped code — the rule must not be fooled by depth.
o="$TMP/der_nested"; mk_derived "$o"; mkdir -p "$o/src/deep"
echo 'pub fn g(p: Formula) -> Thm { Thm::assume(p) }' > "$o/src/deep/mod.rs"
expect_fail_out "Thm::assume in a nested derived/ module" DERIVED_DIR="$o"

# Exempt: a mention in a comment calls nothing.
o="$TMP/der_comment"; mk_derived "$o"
echo '/// Never call `Thm::assume` here; see kernel/README.md.' >> "$o/src/lib.rs"
echo '// nor Thm::implies_intr' >> "$o/src/lib.rs"
expect_pass_out "derived/ mentioning the rules only in comments" DERIVED_DIR="$o"

# Exempt: `#[cfg(test)]` items, which is how derived/'s consumer-side guards are
# pinned. The item after the skipped one must still be scanned, or the exemption
# swallows the file.
o="$TMP/der_cfgtest"; mk_derived "$o"
cat >> "$o/src/lib.rs" <<'EOF'
#[cfg(test)]
mod tests {
    #[test]
    fn a_hypothetical_theorem_is_visible() {
        assert!(!Thm::assume(p).hyps().is_empty());
    }
}
pub fn after(p: Formula) -> Thm { Thm::eq_refl(p) }
EOF
expect_pass_out "derived/ building a hypothesis under #[cfg(test)]" DERIVED_DIR="$o"

o="$TMP/der_cfgtest_then_ship"; mk_derived "$o"
cat >> "$o/src/lib.rs" <<'EOF'
#[cfg(test)]
mod tests {
    #[test]
    fn t() { let _ = 1; }
}
pub fn shipped(p: Formula) -> Thm { Thm::assume(p) }
EOF
expect_fail_out "shipped Thm::assume after a #[cfg(test)] module" DERIVED_DIR="$o"

# Exempt: integration tests, which live under a `tests/` directory.
o="$TMP/der_testdir"; mk_derived "$o"; mkdir -p "$o/tests"
echo 'fn t(p: Formula) { assert!(!Thm::assume(p).hyps().is_empty()); }' > "$o/tests/hyp.rs"
expect_pass_out "derived/ building a hypothesis in tests/" DERIVED_DIR="$o"

# ── I1, checker/: one introduction module, and it must not be vacuous ───────
o="$TMP/chk_elsewhere"; mk_checker "$o"
echo 'pub fn g(p: Formula) -> Thm { Thm::assume(p) }' >> "$o/src/tg.rs"
expect_fail_out "Thm::assume outside checker/src/scope.rs" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

# Unlike derived/, checker/ gets *no* test exemption: `scope::test_support` is
# the sanctioned way for a test to obtain a hypothetical theorem, so a bare
# `Thm::assume` under `#[cfg(test)]` is still a violation there.
o="$TMP/chk_cfgtest"; mk_checker "$o"
cat >> "$o/src/tg.rs" <<'EOF'
#[cfg(test)]
mod tests {
    #[test]
    fn t() { let _ = Thm::assume(p); }
}
EOF
expect_fail_out "Thm::assume under #[cfg(test)] in checker/" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

o="$TMP/chk_testdir"; mk_checker "$o"; mkdir -p "$o/tests"
echo 'fn t(p: Formula) { let _ = Thm::assume(p); }' > "$o/tests/hyp.rs"
expect_fail_out "Thm::assume in checker/tests/" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

o="$TMP/chk_vacuous"; mk_checker "$o"
echo '//! nothing is introduced here any more' > "$o/src/scope.rs"
expect_fail_out "an allowlisted scope.rs that no longer assumes" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

# ── I3, checker/: no panicking generalisation ──────────────────────────────
o="$TMP/chk_gen"; mk_checker "$o"
echo 'pub fn h(x: FreeVar, t: &Thm) -> Thm { Thm::gen(x, t) }' >> "$o/src/tg.rs"
expect_fail_out "Thm::gen( in checker/" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

# Test code is not exempt from I3 either: a panic in a test is still a panic,
# and the token is what the rule bans.
o="$TMP/chk_gen_test"; mk_checker "$o"; mkdir -p "$o/tests"
echo 'fn t(x: FreeVar, u: &Thm) { let _ = Thm::gen(x, u); }' > "$o/tests/g.rs"
expect_fail_out "Thm::gen( in checker/tests/" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

# `gen_checked` is a different token and must not trip the `Thm::gen(` scan.
o="$TMP/chk_genchecked"; mk_checker "$o"
echo 'pub fn h(x: FreeVar, t: &Thm) -> Option<Thm> { Thm::gen_checked(x, t) }' >> "$o/src/tg.rs"
expect_pass_out "gen_checked in checker/" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

# ── I4, checker/: the persistence funnel ───────────────────────────────────
o="$TMP/chk_nosealed"; mk_checker "$o"; rm "$o/src/sealed.rs"
expect_fail_out "a missing Sealed funnel" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

o="$TMP/chk_pubfield"; mk_checker "$o"
sed -i 's/pub struct Sealed(Thm);/pub struct Sealed(pub Thm);/' "$o/src/sealed.rs"
expect_fail_out "a public field on Sealed" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

o="$TMP/chk_twoctors"; mk_checker "$o"
echo '    pub fn new_unchecked(t: Thm) -> Sealed { Sealed(t) }' >> "$o/src/sealed.rs"
sed -i 's/pub fn new_unchecked/pub fn new/' "$o/src/sealed.rs"
expect_fail_out "a second Sealed constructor" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

o="$TMP/chk_unchecked"; mk_checker "$o"
sed -i 's/if t.hyps().is_empty() { Ok(Sealed(t)) } else { Err(t) }/Ok(Sealed(t))/' "$o/src/sealed.rs"
expect_fail_out "a Sealed constructor that does not read hyps()" CHECKER_DIR="$o" SEALED_FILE="$o/src/sealed.rs"

# ── Coverage: no workspace member may go unscanned ─────────────────────────
# This is the rule that would have caught rule 6 going stale six hours after it
# was written, so it is self-tested the same way as the rest.
cat > "$TMP/ws-uncovered.toml" <<'EOF'
[workspace]
members = ["kernel", "derived", "checker", "mini", "newcrate"]
EOF
expect_fail_out "a workspace member no check scans" WS_MANIFEST="$TMP/ws-uncovered.toml"

cat > "$TMP/ws-ok.toml" <<'EOF'
[workspace]
members = ["kernel", "derived", "checker", "mini"]
EOF
expect_pass_out "a fully covered workspace" WS_MANIFEST="$TMP/ws-ok.toml"

# Delegation is only coverage if the delegate is actually run.
echo '#!/bin/sh' > "$TMP/empty-check.sh"; chmod +x "$TMP/empty-check.sh"
expect_fail_out "a delegate ci/check.sh never runs" CHECK_SH="$TMP/empty-check.sh"

echo
if (( fails )); then echo "$fails self-test failure(s)" >&2; exit 1; fi
echo "boundary self-test OK"
