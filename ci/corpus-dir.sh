#!/usr/bin/env bash
# Where the arena corpus is — from a git worktree as well as from the main
# checkout. Prints one path; exit 0 means it is there, 1 means it is not.
#
# # The defect this exists for
#
# `vendor/` is gitignored (`.gitignore:3` — the corpus is 17 MB, 12 MB of it
# performance data), so `git worktree add` does not populate it. Every seat on
# this project works in a worktree, and three CI steps defaulted their corpus to
# `$ROOT/vendor/arena-tests` with `$ROOT` being *that worktree*. Measured in a
# fresh worktree on 2026-08-09, `ci/check.sh` produced three SKIPs — the arena
# corpus, mini-vs-nanoda, and the corpus-dependent Rust suites — plus one FAIL,
# because `ci/check-test-inputs.sh`'s own self-test hard-coded
# `CORPUS_DIR="$ROOT/vendor/arena-tests"` for a cell that needs a *present*
# corpus, and got a SKIP where it wanted a BROKEN.
#
# Two seats hit that independently in one day and both filed it as
# environmental. A step that cannot see its input in the exact environment
# every seat works in is `DECISIONS.md`'s 2026-08-08 "SKIP is not PASS" wearing
# a different hat, and the second-order cost is worse than the first: it trains
# a reader to discount a red.
#
# # How it finds it
#
#   1. `$ROOT/vendor/arena-tests` if it is there. `-d` follows symlinks, so a
#      seat who linked it by hand keeps working and nothing about the existing
#      path changes.
#   2. Otherwise the same relative path under the *main checkout*.
#      `git rev-parse --git-common-dir` names the shared `.git` from inside a
#      worktree as well as from the main checkout, and its parent is the main
#      checkout. One 17 MB copy serves every worktree.
#   3. Otherwise `$ROOT/vendor/arena-tests` again, with exit 1 — absent, but
#      still named as the *local* path, because that is the path the caller's
#      "fetch it like this" message is about.
#
# # `--link`, and why discovery alone is not enough
#
# The shell steps take a corpus path, so discovery is all they need. The Rust
# suites do not: `checker/tests/{corpus,tg_tutorial}.rs` and
# `mini/tests/{tutorial,dump,mutual}.rs` build the path from
# `CARGO_MANIFEST_DIR`, so they can only ever see a corpus at the *worktree's*
# `vendor/arena-tests`. Handing them a discovered path would need an env seam in
# five test files in two other seats' regions.
#
# So `--link` puts a symlink at `$ROOT/vendor/arena-tests` pointing at the main
# checkout's copy, and says so on stderr. It is what the two seats did by hand,
# minus the copy: both reached for `cp -al`, and a hardlink tree is not needed —
# a symlink is enough for every consumer (measured: `scripts/arena.sh` globs
# `$CORPUS/good` and `$CORPUS/bad`, which resolve through it, and the Rust
# suites use ordinary path resolution). The one consumer a symlink was *not*
# enough for was `find` without `-L`, which does not descend a symlink named on
# its command line and reported 0 where `find -L` reported 157; that is fixed at
# the call site in `ci/check-test-inputs.sh`.
#
# `--link` never overwrites: if anything already occupies the path it leaves it
# alone. `NANODATG_NO_CORPUS_LINK=1` turns it off entirely, in which case a
# worktree simply SKIPs the corpus steps the way an unequipped machine does.
#
# # Testing
#
# `--self-test` builds a throwaway repository *and a real `git worktree` of it*
# and drives the discovery through it, because the worktree is the whole defect
# and a self-test that does not create one cannot see it. Falsifiers are noted
# per cell. It writes under `target/` rather than `$TMPDIR`: `/tmp` here is
# tmpfs, and this project's rule is that no worktree of any kind lives there.
#
# Env: CORPUS_ROOT (pretend this is the checkout), CORPUS_REL (the relative
# path), NANODATG_NO_CORPUS_LINK.

set -uo pipefail

SELF_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="${CORPUS_ROOT:-$(cd "$SELF_DIR/.." && pwd)}"
REL="${CORPUS_REL:-vendor/arena-tests}"
LOCAL="$ROOT/$REL"

# The main checkout of whatever repository $ROOT belongs to, or nothing.
# `--git-common-dir` is the shared `.git`: `/repo/.git` from `/repo/wt/foo` as
# well as from `/repo`. It is relative when the answer is the cwd's own `.git`,
# so both spellings are handled.
main_checkout() {
  local gcd
  gcd="$(git -C "$ROOT" rev-parse --git-common-dir 2>/dev/null)" || return 1
  [[ -n "$gcd" ]] || return 1
  [[ "$gcd" == /* ]] || gcd="$ROOT/$gcd"
  [[ -d "$gcd" ]] || return 1
  ( cd "$gcd/.." 2>/dev/null && pwd -P ) || return 1
}

# Echoes the path; 0 = present, 1 = absent.
discover() {
  if [[ -d "$LOCAL" ]]; then echo "$LOCAL"; return 0; fi
  local m
  if m="$(main_checkout)" && [[ -n "$m" && -d "$m/$REL" ]]; then
    echo "$m/$REL"; return 0
  fi
  echo "$LOCAL"; return 1
}

# Discover, and if the answer is somewhere else, put a symlink at the local path
# so the Rust suites — which cannot be told a path — see it too. Never
# destructive: an existing local path is returned untouched, and a failure to
# link is not an error, just the un-linked path.
link_local() {
  local p rc
  p="$(discover)"; rc=$?
  if (( rc != 0 )) || [[ "$p" == "$LOCAL" ]]; then echo "$p"; return $rc; fi
  if [[ -n "${NANODATG_NO_CORPUS_LINK:-}" && "${NANODATG_NO_CORPUS_LINK}" != "0" ]]; then
    echo "$p"; return 0
  fi
  if [[ -e "$LOCAL" || -L "$LOCAL" ]]; then echo "$p"; return 0; fi
  mkdir -p "$(dirname "$LOCAL")" 2>/dev/null
  if ln -s "$p" "$LOCAL" 2>/dev/null; then
    echo "  corpus: linked $LOCAL -> $p (this is a worktree; vendor/ is gitignored)" >&2
    echo "$LOCAL"; return 0
  fi
  echo "$p"; return 0
}

# ── self-test ───────────────────────────────────────────────────────────────
self_test() {
  # `tmp` is deliberately not `local`: the EXIT trap below runs after this
  # function has returned, and a local would be out of scope by then.
  local base bad=0
  base="$(cd "$SELF_DIR/.." && pwd)/target"
  mkdir -p "$base" || { echo "cannot create $base" >&2; return 1; }
  tmp="$(mktemp -d "$base/corpus-selftest.XXXXXX")" || return 1
  trap 'git -C "$tmp/main" worktree remove --force "$tmp/wt" >/dev/null 2>&1; rm -rf "$tmp"' EXIT

  cell() { # cell <want-rc> <want-path> <name> [env...]
    local wrc="$1" wpath="$2" name="$3"; shift 3
    local got rc
    got="$(env -u GIT_DIR -u GIT_WORK_TREE "$@" "$0" 2>/dev/null)"; rc=$?
    if [[ $rc -eq $wrc && "$got" == "$wpath" ]]; then
      echo "  ok: $name"
    else
      echo "SELFTEST FAIL: $name" >&2
      echo "        wanted rc=$wrc path=$wpath" >&2
      echo "        got    rc=$rc path=$got" >&2
      bad=$((bad+1))
    fi
  }

  echo "self-testing $0"

  # A repository with a corpus, and a real worktree of it with none — the
  # defect, reproduced rather than described.
  mkdir -p "$tmp/main/vendor/arena-tests/good"
  : > "$tmp/main/vendor/arena-tests/good/x.ndjson"
  ( cd "$tmp/main" \
    && git init -q -b main \
    && git -c user.email=ci@example -c user.name=ci commit -q --allow-empty -m init \
    && git worktree add -q --detach "$tmp/wt" HEAD ) >/dev/null 2>&1
  if [[ ! -d "$tmp/wt" ]]; then
    echo "SELFTEST FAIL: could not build a git worktree to test against" >&2
    return 1
  fi
  if [[ -e "$tmp/wt/vendor" ]]; then
    echo "SELFTEST FAIL: the worktree has a vendor/ — the premise of this file" >&2
    echo "        is that git does not carry a gitignored directory into one." >&2
    return 1
  fi

  # 1. The existing path, unchanged: a corpus in the checkout wins outright and
  #    no git command has to succeed for it to.
  cell 0 "$tmp/main/vendor/arena-tests" "a corpus in the checkout is found" \
       CORPUS_ROOT="$tmp/main"
  # 2. **The gap.** From a worktree with no vendor/, the main checkout's copy.
  #    Falsifier: delete the `main_checkout` branch of `discover` and this cell
  #    returns rc=1 with the worktree's own path — which is exactly what every
  #    seat saw before this file existed.
  cell 0 "$tmp/main/vendor/arena-tests" "a worktree falls back to the main checkout" \
       CORPUS_ROOT="$tmp/wt"
  # 3. Nothing anywhere is still an absence, not an error, and it names the
  #    *local* path, because that is where the caller tells you to unpack it.
  cell 1 "$tmp/wt/vendor/nope" "absent everywhere is rc=1 at the local path" \
       CORPUS_ROOT="$tmp/wt" CORPUS_REL="vendor/nope"
  # 4. A directory that is not a git repository at all must not blow up. The
  #    ceiling is what makes it one: this scratch lives under `target/`, so
  #    without it `git` walks up and finds the very repository being tested.
  mkdir -p "$tmp/plain"
  cell 1 "$tmp/plain/vendor/arena-tests" "a non-repository is rc=1, not a crash" \
       CORPUS_ROOT="$tmp/plain" GIT_CEILING_DIRECTORIES="$tmp"
  # 5. Precedence: a local corpus wins over the main checkout's, so a seat who
  #    unpacked their own is not silently redirected to someone else's.
  mkdir -p "$tmp/wt/vendor/arena-tests"
  cell 0 "$tmp/wt/vendor/arena-tests" "a local corpus wins over the main checkout" \
       CORPUS_ROOT="$tmp/wt"
  rm -rf "$tmp/wt/vendor"

  # 6. --link materialises the path the Rust suites hard-code, and the link
  #    actually resolves to the corpus. Falsifier: drop the `ln -s` and the
  #    `-d` below fails.
  local out
  out="$(env -u GIT_DIR -u GIT_WORK_TREE CORPUS_ROOT="$tmp/wt" "$0" --link 2>/dev/null)"
  if [[ "$out" == "$tmp/wt/vendor/arena-tests" && -L "$tmp/wt/vendor/arena-tests" \
        && -d "$tmp/wt/vendor/arena-tests/good" ]]; then
    echo "  ok: --link puts a working symlink at the local path"
  else
    echo "SELFTEST FAIL: --link did not produce a resolvable local path (got '$out')" >&2
    bad=$((bad+1))
  fi
  # 7. …and a `find` over that link counts the exports. This is the second half
  #    of the defect and the reason `ci/check-test-inputs.sh` says `find -L`:
  #    without it this is 0, and a step reports a reachable corpus as empty.
  local nL nP
  nL=$(find -L "$tmp/wt/vendor/arena-tests" -name '*.ndjson' -type f 2>/dev/null | wc -l)
  nP=$(find    "$tmp/wt/vendor/arena-tests" -name '*.ndjson' -type f 2>/dev/null | wc -l)
  if (( nL == 1 )); then
    echo "  ok: find -L counts through the link ($nL; plain find sees $nP)"
  else
    echo "SELFTEST FAIL: find -L over the linked corpus counted $nL, wanted 1" >&2
    bad=$((bad+1))
  fi
  if (( nP != 0 )); then
    echo "  note: plain find descended the link on this system ($nP) — the -L in" >&2
    echo "        ci/check-test-inputs.sh is then belt and braces, not the fix." >&2
  fi
  # 8. --link is not destructive. The case that reaches the guard is a local
  #    path that exists but is not a directory — a dangling link to a corpus
  #    that moved, or a stray file. Discovery declines it and falls back, and
  #    the link step must not delete it to make room. Falsifier: replace the
  #    `-e || -L` guard with an `rm -rf` and this cell reports the loss.
  rm -rf "$tmp/wt/vendor"
  mkdir -p "$tmp/wt/vendor"
  echo "not a corpus" > "$tmp/wt/vendor/arena-tests"
  out="$(env -u GIT_DIR -u GIT_WORK_TREE CORPUS_ROOT="$tmp/wt" "$0" --link 2>/dev/null)"
  if [[ -f "$tmp/wt/vendor/arena-tests" && "$out" == "$tmp/main/vendor/arena-tests" ]]; then
    echo "  ok: --link leaves an occupied local path alone and reports the real one"
  else
    echo "SELFTEST FAIL: --link clobbered or mis-reported an occupied vendor/arena-tests" >&2
    echo "        file still there: $([[ -f $tmp/wt/vendor/arena-tests ]] && echo yes || echo NO)" >&2
    echo "        reported: $out" >&2
    bad=$((bad+1))
  fi
  # 9. …and it can be turned off, for a machine where the link is unwanted.
  rm -rf "$tmp/wt/vendor"
  env -u GIT_DIR -u GIT_WORK_TREE CORPUS_ROOT="$tmp/wt" NANODATG_NO_CORPUS_LINK=1 \
      "$0" --link >/dev/null 2>&1
  if [[ ! -e "$tmp/wt/vendor/arena-tests" ]]; then
    echo "  ok: NANODATG_NO_CORPUS_LINK=1 suppresses the link"
  else
    echo "SELFTEST FAIL: NANODATG_NO_CORPUS_LINK=1 linked anyway" >&2
    bad=$((bad+1))
  fi

  echo
  if (( bad )); then echo "$bad corpus-discovery self-test failure(s)" >&2; return 1; fi
  echo "corpus-discovery self-test OK"
  return 0
}

case "${1:-}" in
  --self-test) self_test; exit $? ;;
  --link)      link_local; exit $? ;;
  "")          discover; exit $? ;;
  *)           echo "usage: $0 [--link|--self-test]" >&2; exit 2 ;;
esac
