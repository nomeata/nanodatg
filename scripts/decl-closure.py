#!/usr/bin/env python3
"""The **backward dependency closure** of named declarations, as a valid export.

    python3 scripts/decl-closure.py IN.ndjson OUT.ndjson NAME [NAME ...]

Given one or more declaration names, emit an export containing exactly those
declarations and everything they transitively refer to under `const`, in the
input's own order. Nothing else — so a declaration deep in a file can be
type-checked and interpreted **without paying for the declarations in front of
it that it does not need**.

# Why this exists

`scripts/nat-reach.py` answers "what would still be here if the literals were
representable" by closing *forward*. This closes *backward*, and the question it
answers is the complementary one: `init-prelude`'s interpretation pass has never
got past declaration 231, so every question about declaration 555 is
unanswerable from a run of the file. Cutting 555's closure out makes it
answerable in minutes.

That is how `PRELUDE-COST.md` §4.2 established that `List.get.match_1` is a
second wall and not merely a large declaration: its closure is 71 declarations
and 1.1 M conversions, and then the declaration itself does not finish in twenty
minutes. It is also how §4.1's acceptance-cost proxy was validated out of
sample — the `BitVec` closure interprets residue declarations 427–431 on its way
to `BitVec`, and their measured cost can be compared against the prediction.

# What it does not renumber

Like `nat-reach.py --write`, this **drops whole declaration lines and keeps the
expression pool intact**, because the pool is addressed by index and renumbering
it would be a second thing that could be wrong. An expression no surviving
declaration reaches simply becomes unreachable. The output is therefore larger
on disk than it needs to be and exactly as correct as the input.

A closure is over `const` references only. An inductive is atomic: asking for
one constructor keeps the whole declaration, with its types, constructors and
recursors, because the export has no way to split it.
"""

import importlib.util
import json
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "nat_reach", Path(__file__).resolve().parent / "nat-reach.py"
)
nr = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(nr)


def main():
    if len(sys.argv) < 4:
        print(__doc__.strip().splitlines()[2].strip(), file=sys.stderr)
        return 2
    src, out, targets = sys.argv[1], sys.argv[2], sys.argv[3:]

    raw = [json.loads(l) for l in open(src)]
    names, exprs, decls = {}, {}, []
    for i, o in enumerate(raw):
        if "in" in o:
            names[o["in"]] = o
        elif "ie" in o:
            exprs[o["ie"]] = o
        elif "il" in o:
            pass
        else:
            for k in nr.KINDS:
                if k in o:
                    decls.append((i, k, o[k]))
                    break
    res = nr.resolver(names)
    # `analyse`'s literal cap is irrelevant here; only its `consts` half is read.
    _over, consts = nr.analyse(exprs, 10**9)

    owner = {}
    for li, k, b in decls:
        for n in nr.declaration_names(k, b):
            owner[res(n)] = li
    needs = {
        li: {res(c) for e in nr.declaration_exprs(k, b) for c in consts[e]}
        for li, k, b in decls
    }

    keep, stack = set(), []
    for t in targets:
        if t in owner:
            stack.append(owner[t])
        else:
            print(f"  !! target not in export: {t}", file=sys.stderr)
    while stack:
        li = stack.pop()
        if li in keep:
            continue
        keep.add(li)
        stack.extend(owner[n] for n in needs[li] if n in owner and owner[n] not in keep)

    drop = {li for li, _, _ in decls} - keep
    with open(out, "w") as f:
        for i, l in enumerate(open(src)):
            if i not in drop:
                f.write(l)
    print(f"{out}: {len(keep)} of {len(decls)} declarations kept")
    return 0


if __name__ == "__main__":
    sys.exit(main())
