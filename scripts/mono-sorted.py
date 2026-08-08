#!/usr/bin/env python3
"""Topological-sortedness violations in a raw `lean4export` `.ndjson`.

`MONOMORPH.md` §2 asserts that an export is topologically sorted — that a
declaration only mentions declarations appearing before it — and `monomorph`
refuses a file that is not.  The assertion is a claim about `lean4export`, not
about the format, so it wants measuring on a real input.  `monomorph` refuses at
the *first* violation it finds and so reports exactly one; this enumerates all
of them.

The grouping matches `Modelgen.Mono`: an inductive block (its types, its
constructors and its recursors) is one node, a mutual block is the node its
`all` field names, and everything else is a singleton.  A violation is a group
whose declarations mention a name that a *later* group declares.

Two passes.  The first builds the name table, the groups and each group's root
expressions; the second folds, over the expression DAG, the largest group
ordinal each node reaches.  A subterm always has a lower record index than the
term containing it, so one forward sweep suffices.

    scripts/mono-sorted.py EXPORT.ndjson [--top N]
"""

import argparse
import json
import re
import sys
from array import array

NUM = re.compile(rb'":(\d+)')
IN_STR = re.compile(rb'^\{"in":(\d+),"str":\{"pre":(\d+),"str":"(.*)"\}\}$')
IN_NUM = re.compile(rb'^\{"in":(\d+),"num":\{"i":(\d+),"pre":(\d+)\}\}$')
DECL = (b'{"axiom":', b'{"def":', b'{"inductive":', b'{"opaque":', b'{"quot":', b'{"thm":')


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--top", type=int, default=20)
    args = ap.parse_args()

    pre = array("l", [0])
    part: list = [None]

    def grow(i, p, c):
        while len(part) <= i:
            pre.append(0)
            part.append(None)
        pre[i] = p
        part[i] = c

    def full(i):
        out = []
        while i:
            out.append(part[i])
            i = pre[i]
        return ".".join(str(c) for c in reversed(out))

    # ── Pass 1: the name table, the groups, and each group's roots.
    group_of_name: dict[int, int] = {}
    group_names: list[list[int]] = []
    group_roots: list[list[int]] = []
    all_to_group: dict[int, int] = {}
    nlines = 0

    with open(args.path, "rb") as f:
        for line in f:
            nlines += 1
            if line.startswith(b'{"in":'):
                s = line.rstrip()
                m = IN_STR.match(s)
                if m:
                    grow(int(m.group(1)), int(m.group(2)),
                         sys.intern(m.group(3).decode("unicode_escape")))
                    continue
                m = IN_NUM.match(s)
                if m:
                    grow(int(m.group(1)), int(m.group(3)), int(m.group(2)))
                    continue
                raise SystemExit(f"unparsed name record: {s[:150]!r}")
            if not line.startswith(DECL):
                continue
            o = json.loads(line)
            kind = next(iter(o))
            b = o[kind]
            if kind == "inductive":
                names = ([t["name"] for t in b["types"]] + [c["name"] for c in b["ctors"]]
                         + [r["name"] for r in b["recs"]])
                roots = ([t["type"] for t in b["types"]] + [c["type"] for c in b["ctors"]]
                         + [r["type"] for r in b["recs"]]
                         + [rule["rhs"] for r in b["recs"] for rule in r["rules"]])
                alls: list[int] = []
            else:
                names = [b["name"]]
                roots = [b["type"]] + ([b["value"]] if "value" in b else [])
                alls = b.get("all", [])
            g = next((all_to_group[a] for a in alls if a in all_to_group), None)
            if g is None:
                g = len(group_names)
                group_names.append([])
                group_roots.append([])
            for a in alls:
                all_to_group.setdefault(a, g)
            for n in names:
                group_of_name[n] = g
                group_names[g].append(n)
            group_roots[g].extend(roots)

    ngroups = len(group_names)
    print(f"{args.path}: {nlines} lines, {ngroups} groups, "
          f"{len(group_of_name)} declared names")

    # ── Pass 2: fold the largest group ordinal each expression reaches.
    # `-1` is "reaches no declared constant"; 0xffffffff is -1 as int32.
    reach = array("i", b"\xff\xff\xff\xff" * (nlines + 2))

    with open(args.path, "rb") as f:
        for line in f:
            if line.startswith((b'{"in":', b'{"il":', b'{"meta"')) or line.startswith(DECL):
                continue
            nums = [int(x) for x in NUM.findall(line)]
            if line.startswith(b'{"app":'):
                reach[nums[2]] = max(reach[nums[0]], reach[nums[1]])
            elif line.startswith(b'{"const":'):
                reach[nums[-1]] = group_of_name.get(nums[0], -1)
            elif line.startswith(b'{"forallE":'):
                reach[nums[3]] = max(reach[nums[0]], reach[nums[2]])
            elif line.startswith(b'{"bvar":'):
                reach[nums[-1]] = -1
            elif line.startswith(b'{"ie":'):
                i = nums[0]
                if b'"lam":' in line:
                    reach[i] = max(reach[nums[1]], reach[nums[3]])
                elif b'"letE":' in line:
                    reach[i] = max(reach[nums[1]], reach[nums[3]], reach[nums[4]])
                elif b'"proj":' in line:
                    # `idx`, `struct`, `typeName` — the structure is a reference too.
                    reach[i] = max(reach[nums[2]], group_of_name.get(nums[3], -1))
                elif b'"sort":' in line or b'"natVal":' in line or b'"strVal":' in line:
                    reach[i] = -1
                else:
                    raise SystemExit(f"unrecognised expr record: {line[:150]!r}")
            else:
                raise SystemExit(f"unrecognised record: {line[:150]!r}")

    violations = []
    for g in range(ngroups):
        worst = max((reach[r] for r in group_roots[g]), default=-1)
        if worst > g:
            violations.append((g, worst))

    print(f"  topological-sortedness violations: {len(violations)} of {ngroups} groups "
          f"mention a name that a later group declares")
    for g, worst in sorted(violations, key=lambda x: -(x[1] - x[0]))[:args.top]:
        print(f"    group {g} ({full(group_names[g][0])})\n"
              f"      -> group {worst} ({full(group_names[worst][0])})"
              f"   forward by {worst - g}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
