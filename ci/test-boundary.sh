#!/usr/bin/env bash
# Self-test for ci/check-boundary.sh.
#
# A boundary check that cannot fail provides no assurance. This builds a
# synthetic "kernel" for each rule, violates exactly that rule, and asserts the
# checker rejects it — and that the clean baseline is accepted.
#
# The last section — "the scans must find something to scan" — is about a
# different failure mode from all the rest. Those cells feed the checker a
# *wrong* input and require a red. Those cells feed it *no* input and require a
# red, because a scan over an absent or empty directory used to print `ok:` and
# exit 0. Each of them pins the message as well as the exit status: an absent
# `checker/` already reds for three unrelated reasons, so a cell that only
# looked at `$?` would stay green with the guard it is testing deleted. That is
# the trap the corpus seat hit at `4b463f1` — a cell that exits earlier for
# another reason cannot fail.

set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Overridable so a falsifier run can point this self-test at a deliberately
# broken copy of the checker and confirm the cells go red. Each guard in the
# last section names the edit that reds its cell; the recipe is to copy
# `ci/check-boundary.sh`, remove that guard, and re-run with BOUNDARY_CHECK set
# to the copy. Every one of them was watched failing that way.
CHECK="${BOUNDARY_CHECK:-$ROOT/ci/check-boundary.sh}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fails=0

# A clean `derived` fixture: one shipped file, plus the sanctioned introduction
# module that really introduces. Defined up here because it is also the
# baseline: R6' scans the *non*-kernel crates, and every one of its inputs is
# pointed at a clean fixture for the whole self-test, so each fixture below is
# hermetic. Whether the real `derived/` and `checker/` obey R6' is
# check-boundary.sh's job, not this script's, and a violation there must not
# make the self-test report the checker as broken. Each R6' fixture then
# overrides exactly the one input it violates.
#
# This baseline used to be an empty directory. That was only viable while an
# empty `derived/` was a pass, which is the defect this file now tests for.
mk_derived() {
  mkdir -p "$1/src"
  echo 'pub fn f() { let _ = Thm::eq_refl(x); }' > "$1/src/lib.rs"
  echo 'pub fn assuming(p: Formula) -> Thm { Thm::assume(p) }' > "$1/src/discharge.rs"
}
mk_derived "$TMP/der-base"
export DERIVED_DIR="$TMP/der-base"

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

# A red is not enough when the input is *absent*: an absent crate trips several
# unrelated rules, so a cell that only reads `$?` passes with the guard it is
# meant to test deleted. This one requires the run to fail **and** to say why.
# `KERNEL_DIR` is first so a caller can override it; `env` takes the last
# assignment of a name.
expect_fail_because() { # expect_fail_because <name> <message-substring> [env...]
  local name="$1" want="$2"; shift 2
  local out rc
  out="$(env KERNEL_DIR="$TMP/clean" "$@" "$CHECK" 2>&1)"; rc=$?
  if (( rc == 0 )); then
    echo "SELFTEST FAIL: '$name' was not detected at all" >&2; fails=$((fails+1))
  elif ! grep -qF -- "$want" <<<"$out"; then
    echo "SELFTEST FAIL: '$name' failed, but for the wrong reason" >&2
    echo "        wanted a message containing: $want" >&2
    printf '        got:\n%s\n' "$out" | head -30 >&2
    fails=$((fails+1))
  else
    echo "  ok: detects $name"
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
expect_pass_out "a clean derived/ and checker/" DERIVED_DIR="$TMP/der-base"

# ── I1, derived/: a ban over shipped code, with the test exemptions ─────────
# A `derived/` fixture comes with its sanctioned introduction module (see
# `mk_derived` at the top), exactly as `mk_checker` comes with `src/scope.rs` —
# without one the non-vacuity half of I1 fires and every fixture below would
# report the wrong violation.
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

# …and the allowlist must not be vacuous, the same way checker/'s must not.
o="$TMP/der_vacuous"; mk_derived "$o"
echo '//! nothing is introduced here any more' > "$o/src/discharge.rs"
expect_fail_out "an allowlisted discharge.rs that no longer assumes" DERIVED_DIR="$o"

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

# ── The scans must find something to scan ──────────────────────────────────
# Every cell above hands the checker a wrong input. These hand it *no* input,
# which is the failure mode that produced five incidents on this project and is
# the one a green tick is least distinguishable from. Two shapes per scan: the
# directory is absent, and the directory is there but the scan matches no files.
#
# All of them are message-pinned via `expect_fail_because`, and each names the
# guard whose deletion reds it. The falsifier recipe is at the top of this file.

# derived/, absent. Before the fix this printed
# `ok: derived/ introduces hypotheses only in src/discharge.rs` and exited 0 —
# `derived_scan` opened with `[[ -d "$D" ]] || return 0`.
# Falsifier: restore that line, or delete the `[[ ! -d "$D" ]]` branch.
expect_fail_because "an absent derived/ (the scan has nothing to scan)" \
  "does not exist — I1's scan would have nothing to scan" \
  DERIVED_DIR="$TMP/no-such-derived"

# derived/, present and empty. A `-d` test alone does not catch this one.
# Falsifier: delete the `derived_files -print | wc -l` branch.
mkdir -p "$TMP/der_empty"
expect_fail_because "an empty derived/ (the scan matches no files)" \
  "I1's scan matched no .rs files" \
  DERIVED_DIR="$TMP/der_empty"

# derived/, present and non-empty, holding *only* the allowlisted introduction
# module. The directory exists, the crate looks real, `src/lib.rs`-shaped
# guards would be satisfied, and the scan still reads zero files because
# `$DERIVED_SCOPE` is excluded from it. Same falsifier as the cell above.
mkdir -p "$TMP/der_only_scope/src"
echo 'pub fn assuming(p: Formula) -> Thm { Thm::assume(p) }' > "$TMP/der_only_scope/src/discharge.rs"
expect_fail_because "a derived/ holding only the allowlisted module" \
  "I1's scan matched no .rs files" \
  DERIVED_DIR="$TMP/der_only_scope"

# kernel/src, absent. This one *did* red before the fix — via the
# `#![forbid(unsafe_code)]` grep — while five of the six kernel rules printed
# `ok:` over nothing. Hence the message pin: without it this cell is green with
# the guard removed, and proves nothing.
# Falsifier: delete the `[[ ! -d "$K/src" ]]` branch of rule 0; the run still
# fails on the missing forbid, and this cell then reports the wrong reason.
# The substring is the *absent* half of rule 0 and not a prefix of the empty
# half — deleting the `-d` branch leaves the count branch, whose message would
# otherwise satisfy this pin and leave the cell green with its guard gone.
expect_fail_because "an absent kernel/src (rules 1-5 scan nothing)" \
  "does not exist — rules 1-5 would scan nothing" \
  KERNEL_DIR="$TMP/no-such-kernel"

# kernel/src, present with no .rs files. Same pin, same reasoning.
# Falsifier: delete the `kernel_files < 1` branch.
d="$TMP/kern_empty"; mk_clean "$d"; rm "$d/src"/*.rs
expect_fail_because "a kernel/src with no sources" \
  "rules 1-5 would scan nothing and report ok" \
  KERNEL_DIR="$d"

# The dependency scan needs the `[dependencies]` header to find anything, so a
# manifest it cannot parse used to read as "no external dependencies".
# Falsifier: delete the `grep -q '^\[dependencies\]'` branch of rule 2.
d="$TMP/kern_nodeps"; mk_clean "$d"
sed -i '/^\[dependencies\]/d' "$d/Cargo.toml"
expect_fail_because "a kernel manifest with no [dependencies] table" \
  "the dependency scan would parse nothing" \
  KERNEL_DIR="$d"

# checker/, present and empty. `crate_scan` fails closed on an *absent*
# directory, so the empty case is the one it cannot see: the greps are silent
# and I1/I3 print `ok:`.
# Falsifier: delete the `checker_files < 1` branch.
mkdir -p "$TMP/chk_empty/src"
expect_fail_because "an empty checker/ (I1 and I3 scan no files)" \
  "I1 and I3 would scan nothing" \
  CHECKER_DIR="$TMP/chk_empty" SEALED_FILE="$TMP/chk_empty/src/sealed.rs"

# checker/, absent. Fails closed already, but it used to say `Thm::assume
# outside checker/src/scope.rs` over an empty hit list — a red for a reason
# that is not true. The count guard is what makes the diagnostic honest.
# Falsifier: same as the cell above.
expect_fail_because "an absent checker/ says so, rather than naming a phantom violation" \
  "I1 and I3 would scan nothing" \
  CHECKER_DIR="$TMP/no-such-checker" SEALED_FILE="$TMP/no-such-checker/src/sealed.rs"

# Rule 3 was wrapped in "if a `Thm` type exists at all", so a kernel that
# declares none skipped the public-field and tuple-struct checks in silence.
# Measured before the fix: a kernel whose type is called `Sequent` exited 0 with
# no mention of rule 3.
# Falsifier: restore the `if grep … Thm … ; then` wrapper in place of the
# negated form, and this cell is not detected at all.
d="$TMP/kern_nothm"; mk_clean "$d"
sed -i 's/pub struct Thm {/pub struct Sequent {/' "$d/src/lib.rs"
expect_fail_because "a kernel that declares no Thm at all" \
  "rule 3 would check nothing" \
  KERNEL_DIR="$d"

# …and rules 3 and 5 read a file *list*, which was the glob `"$K/src"/*.rs` —
# top level only — while rules 1 and 4 beside them use `grep -r` and recurse.
# This is not a vacuous scan but a scan that reads less than its name says, and
# it was a real hole: measured, `pub struct Thm { pub leak: u32 }` in
# `src/sub/hidden.rs` printed `ok: Thm has no public fields` and exited 0.
# Falsifier: put the glob back in `kernel_srcs`' place at rule 3.
d="$TMP/kern_subdir"; mk_clean "$d"; mkdir -p "$d/src/sub"
# Spelled over three lines, as `mk_clean`'s is: the rule matches a field
# declaration on a line of its own, which is what rustfmt produces. A one-line
# `pub struct Thm { pub leak: u32 }` is missed by the *regex*, recursion or no,
# and a fixture built that way tests nothing about the file list.
cat > "$d/src/sub/hidden.rs" <<'EOF'
pub struct Thm {
    pub leak: u32,
}
EOF
expect_fail_because "a public field on Thm in a kernel subdirectory" \
  "Thm has public field(s)" \
  KERNEL_DIR="$d"

# The same list feeds the size budget, so a subdirectory used to be free of it.
# Falsifier: put the glob back in `kernel_srcs`' place at rule 5.
d="$TMP/kern_subdir_big"; mk_clean "$d"; mkdir -p "$d/src/sub"
for i in $(seq 1 1100); do echo "pub fn f$i() {}" >> "$d/src/sub/bulk.rs"; done
expect_fail_because "a size-budget overrun hidden in a kernel subdirectory" \
  "exceeds 700 non-comment lines" \
  KERNEL_DIR="$d"

# The coverage loop is the rule that exists *because* rule 6 silently stopped
# covering a crate — and it enumerated `members` with an awk whose silence read
# as a fully covered workspace. Measured before the fix: exit 0, "kernel
# boundary OK", not one `ok: workspace member` line printed.
# Falsifier: delete the `-z "${members//[[:space:]]/}"` branch.
printf '[workspace]\nmembers_none = 1\n' > "$TMP/ws-unparsed.toml"
expect_fail_because "a workspace manifest whose members do not parse" \
  "the coverage check would enumerate nothing" \
  WS_MANIFEST="$TMP/ws-unparsed.toml"

# Falsifier: delete the `[[ ! -f "$WS_MANIFEST" ]]` branch — the `-z` branch
# below it still reds, so this cell is pinned on the *missing-file* message
# specifically.
expect_fail_because "a missing workspace manifest" \
  "is missing — the coverage check would enumerate nothing" \
  WS_MANIFEST="$TMP/no-such-manifest.toml"

echo
if (( fails )); then echo "$fails self-test failure(s)" >&2; exit 1; fi
echo "boundary self-test OK"
