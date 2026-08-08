#!/usr/bin/env python3
"""Copies-per-group, by name, from a `monomorph` output `.ndjson`.

`monomorph` itself prints the copies-per-group *histogram* (`rep.hist`), which
is the authoritative distribution.  It does not print *which* groups the tail
belongs to, and on a Mathlib-scale input that is the interesting half.  This
script recovers it from the output file alone, by inverting the naming scheme
of `MONOMORPH.md` §1.2 property 3:

    strip a trailing `._elim.<w>`; find the unique `_at` component; the
    `Name.num` components immediately after it are σ, and deleting them
    gives the input's name.

so the *owner* is everything before `_at` and the copy count of a group is the
number of distinct σ its owner is seen at.

**This counts owners, not groups, and its `1` bucket is not `rep.hist`'s.**  A
monomorphic declaration has an empty σ and so carries no `_at` at all; it is a
group with one copy that this script cannot see, and the `1` bucket is short by
exactly that many.  Going the other way, the members of a *mutual `def`* block
are each their own owner, so one group can show up as several owners sharing one
σ set.  **The tail — every bucket from 2 up — is exact**, which is what this is
for: on `init-prelude` it reproduces `rep.hist`'s `2 → 138, 3 → 9, 4 → 1, 5 → 1`
and names `Eq.ndrec` as the group at five.  Quote `rep.hist` for the
distribution and this for the names.

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

    # owner -> set of σ.  σ is the tuple of `Name.num` components right after
    # the `_at`; a name with no `_at` is monomorphic (§1.1: "σ empty is the
    # identity") and is not a copy of anything.
    sigmas: dict[str, set] = collections.defaultdict(set)
    monomorphic = 0
    elim_only = 0
    for ni in decl_names:
        cs = components(ni)
        # strip a trailing `._elim.<w>` (mode B)
        if len(cs) >= 2 and cs[-2] == "_elim" and isinstance(cs[-1], int):
            cs = cs[:-2]
            elim_only += 1
        try:
            at = cs.index("_at")
        except ValueError:
            monomorphic += 1
            continue
        k = at + 1
        sig = []
        while k < len(cs) and isinstance(cs[k], int):
            sig.append(cs[k])
            k += 1
        owner = ".".join(str(c) for c in cs[:at])
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
