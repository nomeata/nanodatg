#!/usr/bin/env python3
"""Drop the expression-pool lines no declaration reaches, and renumber.

    python3 scripts/prune-pool.py IN.ndjson OUT.ndjson

# Why this exists

`scripts/decl-closure.py` and `scripts/nat-reach.py --write` both **drop whole
declaration lines and keep the expression pool intact**, deliberately: the pool
is addressed by index and renumbering it would be a second thing that could be
wrong. That is invisible to `mini` and to `nanoda`, which index the pool lazily
and never look at an entry nothing reaches.

It is *not* invisible to a checker that validates every pool line as it parses.
`lean-mini-kernel` declines every closure cut out of `init-prelude` with

    Declinig to handle due to parse error:
    The mini kernel does not support nat literals larger than 10

on a `natVal` of `18446744073709551616` that **no surviving declaration
mentions**. So a comparison against an external checker — `MATCHER-WALL.md`,
which is why this exists — cannot use a closure until the dead pool is gone.

Dropping the unreachable lines is not enough on its own either: nanoda's parser
requires the back-references to be continuous —

    Declined: Expr back-reference mismatch, expected Ie(272), found Ie(282).
    Back-refs must be continuous.

— so the survivors are renumbered densely in file order and every reference is
rewritten.

# What it does not touch

**Names and levels.** Nothing needed them pruned and touching them would be a
second thing that could be wrong. Unused name and level entries are what the
pool tools already leave behind, and every checker in the corpus tolerates
them.

# How it is checked

Not by an assertion here. The pruned file must draw the **same verdict, the
same declaration count and the same conversion count** as the unpruned one:
`MATCHER-WALL.md` §1.1 runs both through `nanoda_bin` (84 / 64 / 72
declarations, unchanged) and through `mini` (5 555 200 and 11 631 170
conversions, identical to the digit).
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


def declaration_body(o):
    """`(kind, body)` if this line is a declaration, else `None`."""
    for k in nr.KINDS:
        if k in o:
            return k, o[k]
    return None


def fix_expr(o, remap):
    o["ie"] = remap[o["ie"]]
    for key, fields in (
        ("app", ("fn", "arg")),
        ("lam", ("type", "body")),
        ("forallE", ("type", "body")),
        ("letE", ("type", "value", "body")),
        ("proj", ("struct",)),
    ):
        if key in o:
            for f in fields:
                o[key][f] = remap[o[key][f]]


def fix_decl(kind, b, remap):
    if kind != "inductive":
        b["type"] = remap[b["type"]]
        if "value" in b:
            b["value"] = remap[b["value"]]
        return
    for t in b["types"]:
        t["type"] = remap[t["type"]]
    for c in b["ctors"]:
        c["type"] = remap[c["type"]]
    for r in b["recs"]:
        r["type"] = remap[r["type"]]
        for rule in r.get("rules", ()):
            rule["rhs"] = remap[rule["rhs"]]


def main():
    if len(sys.argv) != 3:
        print(__doc__.strip().splitlines()[2].strip(), file=sys.stderr)
        return 2
    src, out = sys.argv[1], sys.argv[2]

    raw = [json.loads(l) for l in open(src)]
    exprs, decls = {}, []
    for o in raw:
        if "ie" in o:
            exprs[o["ie"]] = o
        elif "in" in o or "il" in o:
            pass
        else:
            d = declaration_body(o)
            if d:
                decls.append(d)

    # Reachability, iteratively: `init-prelude`'s pool is a DAG deep enough to
    # overflow the interpreter's stack recursively, which is why
    # `nat-reach.analyse` is iterative too.
    live, stack = set(), []
    for k, b in decls:
        stack.extend(nr.declaration_exprs(k, b))
    while stack:
        i = stack.pop()
        if i in live:
            continue
        live.add(i)
        stack.extend(nr.kids(exprs[i]))

    remap, nxt = {}, 0
    for o in raw:
        if "ie" in o and o["ie"] in live:
            remap[o["ie"]] = nxt
            nxt += 1

    kept = dropped = 0
    with open(out, "w") as f:
        for o in raw:
            if "ie" in o:
                if o["ie"] not in live:
                    dropped += 1
                    continue
                fix_expr(o, remap)
            elif "in" not in o and "il" not in o:
                d = declaration_body(o)
                if d:
                    fix_decl(d[0], d[1], remap)
            kept += 1
            f.write(json.dumps(o, separators=(",", ":")) + "\n")

    print(
        f"{out}: kept {kept} lines, dropped {dropped} unreachable pool exprs "
        f"({len(live)} of {len(exprs)} exprs live)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
