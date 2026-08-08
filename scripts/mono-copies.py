#!/usr/bin/env python3
"""Copies-per-group, by name, from a `monomorph` output `.ndjson`.

`monomorph` itself prints the copies-per-group *histogram* (`rep.hist`), which
is the authoritative distribution.  It does not print *which* groups the tail
belongs to, and on a Mathlib-scale input that is the interesting half.  This
script recovers it from the output file alone, by inverting the naming scheme
of `MONOMORPH.md` §1.2 property 3:

    strip a trailing `._elim.<w>`; if the **root** component is the
    `Name.str` `_at`, the next component is `k = |σ|`, the `k` after that
    are σ, and everything remaining is the input's name.

so the *owner* is what follows the marker and the copy count of a group is the
number of distinct σ its owner is seen at.  Reading `k` rather than taking
trailing numerals greedily is not a nicety: it is why the marker carries a
length at all (§1.1), and a declaration whose own root component is numeric is
mis-split without it.

**This counts owners, not groups.**  Two things follow and neither is a defect
in the script, only a difference in what is being counted.

* A monomorphic declaration has an empty σ and so carries no `_at` at all; it is
  a group with one copy this cannot see, and the `1` bucket is short by exactly
  that many.
* An inductive block's type, constructors and recursors are **one** group and
  several owners, all at the same σ set, so every bucket from 2 up is *inflated*
  by the extra names.  On `init-prelude`: `2 → 144, 3 → 17, 4 → 1, 5 → 1`
  against `rep.hist`'s `2 → 138, 3 → 9, 4 → 1, 5 → 1`.

A mutual `def` block, by contrast, is not a divergence: `MONOMORPH.md` §2.1
makes every record its own group, so its members *are* separate groups and one
owner is one group.

**What is exact is the extreme and the name attached to it** — on `init-prelude`
this names `Eq.ndrec` at five, which is what `rep.hist`'s `5 → 1` is — and that
is what this is for.  Quote `rep.hist` for the distribution and this for the
names.

Streams the file: the name table is kept as a parent-index array plus one
component each, and only the declaration names are ever materialised.

    scripts/mono-copies.py OUT.ndjson [--top N]
"""

import argparse
import collections
import re
import sys
from array import array

DECL_KEYS = ('"axiom":', '"def":', '"thm":', '"opaque":', '"quot":', '"inductive":')
NAME_RE = re.compile(rb'"name":(\d+)')
IN_STR_RE = re.compile(rb'^\{"in":(\d+),"str":\{"pre":(\d+),"str":(".*")\}\}$')
IN_NUM_RE = re.compile(rb'^\{"in":(\d+),"num":\{"i":(\d+),"pre":(\d+)\}\}$')


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--top", type=int, default=25)
    args = ap.parse_args()

    # Name table.  `pre[i]` is the parent index; `part[i]` is a `str` for a
    # `Name.str` component and an `int` for a `Name.num` one.  Index 0 is
    # `Name.anonymous`.
    pre = array("l", [0])
    part: list = [None]

    def grow(i: int, p: int, c) -> None:
        while len(part) <= i:
            pre.append(0)
            part.append(None)
        pre[i] = p
        part[i] = c

    decl_names: list[int] = []
    lines = 0
    with open(args.path, "rb") as f:
        for line in f:
            lines += 1
            if line.startswith(b'{"in":'):
                m = IN_STR_RE.match(line.rstrip())
                if m:
                    grow(int(m.group(1)), int(m.group(2)),
                         sys.intern(m.group(3).decode()[1:-1]))
                    continue
                m = IN_NUM_RE.match(line.rstrip())
                if m:
                    grow(int(m.group(1)), int(m.group(3)), int(m.group(2)))
                    continue
                raise SystemExit(f"line {lines}: unparsed name record: {line[:120]!r}")
            if line.startswith(b'{"ie":') or line.startswith(b'{"il":') \
               or line.startswith(b'{"meta"'):
                continue
            if any(line.startswith(b"{" + k) for k in
                   (b'"axiom":', b'"def":', b'"thm":', b'"opaque":',
                    b'"quot":', b'"inductive":')):
                decl_names.extend(int(x) for x in NAME_RE.findall(line))
                continue
            raise SystemExit(f"line {lines}: unrecognised record: {line[:120]!r}")

    def components(i: int) -> list:
        out = []
        while i != 0:
            out.append(part[i])
            i = pre[i]
        out.reverse()
        return out

    # owner -> set of σ.  The marker is a **root** prefix: `_at`, then `|σ|`,
    # then σ, then the input's own name.  A name whose root is not `_at` is
    # monomorphic (§1.1: "σ empty is the identity") and is not a copy of
    # anything.
    sigmas: dict[str, set] = collections.defaultdict(set)
    monomorphic = 0
    elim_only = 0
    for ni in decl_names:
        cs = components(ni)
        # strip a trailing `._elim.<w>` (mode B)
        if len(cs) >= 2 and cs[-2] == "_elim" and isinstance(cs[-1], int):
            cs = cs[:-2]
            elim_only += 1
        if not cs or cs[0] != "_at":
            monomorphic += 1
            continue
        if len(cs) < 2 or not isinstance(cs[1], int):
            raise SystemExit(f"marker with no length: {'.'.join(map(str, cs))}")
        k = cs[1]
        sig = cs[2:2 + k]
        owner = ".".join(str(c) for c in cs[2 + k:])
        sigmas[owner].add(tuple(sig))

    hist = collections.Counter(len(v) for v in sigmas.values())
    total_owners = len(sigmas)
    total_copies = sum(len(v) for v in sigmas.values())

    print(f"{args.path}: {lines} lines, {len(decl_names)} declaration names, "
          f"{len(part)} name records")
    print(f"  {monomorphic} names with no `_at` (monomorphic, carried, or "
          f"built-in); {elim_only} carried a `._elim` suffix")
    print(f"  {total_owners} owners, {total_copies} owner-copies")
    print("  copies per owner: " +
          ", ".join(f"{k} -> {hist[k]}" for k in sorted(hist)))
    one = hist[1]
    if total_owners:
        print(f"  at exactly one instantiation: {one}/{total_owners} = "
              f"{100.0 * one / total_owners:.1f}%")
    print(f"  worst {args.top}:")
    for owner, sig in sorted(sigmas.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:args.top]:
        shown = sorted(sig)[:8]
        more = "" if len(sig) <= 8 else f", +{len(sig) - 8} more"
        print(f"    {len(sig):4d}  {owner}   "
              f"{' '.join('[' + ','.join(map(str, s)) + ']' for s in shown)}{more}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
