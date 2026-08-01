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

# Rule 6 scans the *non*-kernel crates. Point it at an empty directory for the
# whole self-test so every fixture below is hermetic: whether `derived/` and
# `checker/` obey the rule is check-boundary.sh's job, not this script's, and a
# violation there must not make the self-test report the checker as broken.
export HYP_SCAN_DIRS="$TMP/no-outside"
mkdir -p "$HYP_SCAN_DIRS"

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

# Same two, for rule 6: a clean kernel with the outside-crate scan pointed at $2.
expect_fail_out() {
  if HYP_SCAN_DIRS="$2" KERNEL_DIR="$TMP/clean" "$CHECK" >/dev/null 2>&1; then
    echo "SELFTEST FAIL: '$1' was not detected" >&2; fails=$((fails+1))
  else
    echo "  ok: detects $1"
  fi
}
expect_pass_out() {
  if HYP_SCAN_DIRS="$2" KERNEL_DIR="$TMP/clean" "$CHECK" >/dev/null 2>&1; then
    echo "  ok: accepts $1"
  else
    echo "SELFTEST FAIL: '$1' should have passed" >&2
    HYP_SCAN_DIRS="$2" KERNEL_DIR="$TMP/clean" "$CHECK" >&2
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

# ── Rule 6: no hypothetical `Thm` in shipped code outside the kernel ─────────
# The fixtures are non-kernel crates: a `src/` that is shipped, plus the two
# kinds of test code the rule deliberately exempts.
mk_outside() { mkdir -p "$1/src"; echo 'pub fn f() { let _ = Thm::eq_refl(x); }' > "$1/src/lib.rs"; }

o="$TMP/out_clean"; mk_outside "$o"
expect_pass_out "an outside crate that builds no hypothesis" "$o"

o="$TMP/out_assume"; mk_outside "$o"
echo 'pub fn g(p: Formula) -> Thm { Thm::assume(p) }' >> "$o/src/lib.rs"
expect_fail_out "Thm::assume in shipped code outside the kernel" "$o"

o="$TMP/out_intr"; mk_outside "$o"
echo 'pub fn g(p: &Formula, t: &Thm) -> Thm { Thm::implies_intr(p, t) }' >> "$o/src/lib.rs"
expect_fail_out "Thm::implies_intr in shipped code outside the kernel" "$o"

# A nested module is still shipped code — the rule must not be fooled by depth.
o="$TMP/out_nested"; mk_outside "$o"; mkdir -p "$o/src/deep"
echo 'pub fn g(p: Formula) -> Thm { Thm::assume(p) }' > "$o/src/deep/mod.rs"
expect_fail_out "Thm::assume in a nested module" "$o"

# Exempt: a mention in a comment calls nothing.
o="$TMP/out_comment"; mk_outside "$o"
echo '/// Never call `Thm::assume` here; see kernel/README.md.' >> "$o/src/lib.rs"
echo '// nor Thm::implies_intr' >> "$o/src/lib.rs"
expect_pass_out "outside crate mentioning the rules only in comments" "$o"

# Exempt: `#[cfg(test)]` items, which is how the guards are pinned. The item
# after the skipped one must still be scanned, or the exemption swallows the file.
o="$TMP/out_cfgtest"; mk_outside "$o"
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
expect_pass_out "outside crate building a hypothesis under #[cfg(test)]" "$o"

o="$TMP/out_cfgtest_then_ship"; mk_outside "$o"
cat >> "$o/src/lib.rs" <<'EOF'
#[cfg(test)]
mod tests {
    #[test]
    fn t() { let _ = 1; }
}
pub fn shipped(p: Formula) -> Thm { Thm::assume(p) }
EOF
expect_fail_out "shipped Thm::assume after a #[cfg(test)] module" "$o"

# Exempt: integration tests, which live under a `tests/` directory.
o="$TMP/out_testdir"; mk_outside "$o"; mkdir -p "$o/tests"
echo 'fn t(p: Formula) { assert!(!Thm::assume(p).hyps().is_empty()); }' > "$o/tests/hyp.rs"
expect_pass_out "outside crate building a hypothesis in tests/" "$o"

echo
if (( fails )); then echo "$fails self-test failure(s)" >&2; exit 1; fi
echo "boundary self-test OK"
