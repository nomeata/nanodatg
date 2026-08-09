#!/usr/bin/env python3
"""How much of an export is behind the `Nat` blocker — the dependency closure.

`mini` declines `init-prelude.ndjson` in 0.037 s at `convert::load`, on the
first nat literal above 10. That decline is *at load*, so every other question
about the file — which inductive shapes it wants, what its recursors demand,
where the checker would stop next — is unanswerable from a run. The verdict
line even reports `natLits=0`, which means "conversion aborted", not "no
literals".

This script answers the part that does not need a run: **which declarations
would still be there if the literals were representable.** It reads the export
JSON, finds every declaration whose type or value reaches a `natVal` above the
cap, closes that set forward under `const` references, and reports the split.
It never runs the checker.

The two numbers it exists to produce, on `good/init-prelude.ndjson`:

    1777 declarations, 77 carry a literal above 10 directly,
    529 (29.8%) fall once the closure is taken.

The 77 are the seeds and they are worth reading: they are `UInt8/16/32/64`,
`Char`, `String.utf8EncodeChar`, `System.Platform.numBits`, `Lean.Name.hash`
and their `noConfusion`/`decEq`/`casesOn` retinue — the machine-word layer,
not the logic. The other 1248 declarations are reachable today in principle,
which is why `--write` exists: it emits the closure's complement as a valid
export so the *next* blocker can be measured before the `Nat` bridge lands.

`--write` drops whole declaration lines and keeps the expression pool intact,
because the pool is addressed by index and renumbering it would be a second
thing that could be wrong. A dropped `natVal` node simply becomes unreachable.

What the residue bought the first time it was run: `mini` got 1 459 declarations
and 3 078 scheduled pairs into `convert::load` — against `declars=0` on the
unfiltered file — and stopped on `non-standard axiom: sorryAx`. So the blocker
after `Nat` was not nesting; it was a one-line policy decline on an axiom that
**nothing in the file uses** (`sorryAx` is a leaf: removing it drops exactly one
declaration of 1 248).

**That blocker is gone (`#121`).** `mini/src/unused_axiom.rs` narrows the rule
to axioms something in the file refers to, and it computes the leaf reading
above rather than taking it on trust: on the residue it reports `used = []`,
`unused = ["sorryAx"]`. Mini ignores the declaration, names it on the verdict
line, and carries on into the interpretation pass — where the wall is `Nat`
again, and is cost rather than a decline (`MEASUREMENTS.md`). Nesting is behind
that, and it is one declaration (`Lean.Syntax`, `numNested = 2`) by
`scripts/arm-coverage.py`.

Usage:
    python3 scripts/nat-reach.py [export.ndjson]        # default: init-prelude
    python3 scripts/nat-reach.py FILE --write OUT       # also emit the residue
    python3 scripts/nat-reach.py FILE --cap 10          # mini's cap, the default
"""

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

DEFAULT = Path("vendor/arena-tests/good/init-prelude.ndjson")
KINDS = ("def", "thm", "axiom", "opaque", "quot", "inductive")


def kids(node):
    """The expression indices a node points at. Leaves have none."""
    if "app" in node:
        return (node["app"]["fn"], node["app"]["arg"])
    if "lam" in node:
        return (node["lam"]["type"], node["lam"]["body"])
    if "forallE" in node:
        return (node["forallE"]["type"], node["forallE"]["body"])
    if "letE" in node:
        e = node["letE"]
        return (e["type"], e["value"], e["body"])
    if "proj" in node:
        return (node["proj"]["struct"],)
    return ()


def resolver(names):
    """The export's name table, as dotted strings."""
    memo = {0: ""}

    def res(i):
        if i in memo:
            return memo[i]
        d = names[i]
        part = d["str"] if "str" in d else d["num"]
        pre = res(part["pre"])
        tail = part["str"] if "str" in d else str(part["i"])
        memo[i] = f"{pre}.{tail}" if pre else tail
        return memo[i]

    return res


def analyse(exprs, cap):
    """`(over_cap, consts)` per expression index, over the whole pool.

    Iterative rather than recursive: the pool is a DAG tens of thousands of
    nodes deep in places, and `init-prelude` overflows the interpreter's stack
    on the recursive form.
    """
    over, consts = {}, {}
    for root in exprs:
        if root in over:
            continue
        stack = [(root, False)]
        while stack:
            i, done = stack.pop()
            if i in over:
                continue
            node = exprs[i]
            if not done:
                stack.append((i, True))
                stack.extend((k, False) for k in kids(node) if k not in over)
                continue
            big = "natVal" in node and int(node["natVal"]) > cap
            cs = {node["const"]["name"]} if "const" in node else set()
            for k in kids(node):
                big = big or over[k]
                cs = cs | consts[k]
            over[i], consts[i] = big, cs
    return over, consts


def declaration_exprs(kind, body):
    if kind != "inductive":
        return [body["type"]] + ([body["value"]] if "value" in body else [])
    out = [t["type"] for t in body["types"]]
    out += [c["type"] for c in body["ctors"]]
    for r in body["recs"]:
        out.append(r["type"])
        out += [rule["rhs"] for rule in r.get("rules", ())]
    return out


def declaration_names(kind, body):
    if kind != "inductive":
        return [body["name"]]
    return (
        [t["name"] for t in body["types"]]
        + [c["name"] for c in body["ctors"]]
        + [r["name"] for r in body["recs"]]
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("export", nargs="?", type=Path, default=DEFAULT)
    ap.add_argument("--cap", type=int, default=10, help="mini's literal cap (default 10)")
    ap.add_argument("--write", type=Path, help="emit the surviving declarations as an export")
    args = ap.parse_args()

    if not args.export.is_file():
        sys.exit(f"no such export: {args.export} (the corpus is gitignored for size)")

    raw = args.export.read_text().splitlines(keepends=True)
    records = [json.loads(line) for line in raw]
    exprs = {d["ie"]: d for d in records if "ie" in d}
    names = {d["in"]: d for d in records if "in" in d}
    name_of = resolver(names)
    over, consts = analyse(exprs, args.cap)

    decls, owner = [], {}
    for lineno, d in enumerate(records):
        for kind in KINDS:
            if kind not in d:
                continue
            body = d[kind]
            reach = declaration_exprs(kind, body)
            decls.append(
                {
                    "line": lineno,
                    "kind": kind,
                    "names": declaration_names(kind, body),
                    "over": any(over[e] for e in reach),
                    "consts": set().union(*(consts[e] for e in reach)) if reach else set(),
                }
            )
    for i, d in enumerate(decls):
        for n in d["names"]:
            owner[n] = i

    seeds = [i for i, d in enumerate(decls) if d["over"]]
    fallen = set(seeds)
    changed = True
    while changed:
        changed = False
        for i, d in enumerate(decls):
            if i in fallen:
                continue
            if any(owner.get(c) in fallen for c in d["consts"]):
                fallen.add(i)
                changed = True

    total = len(decls)
    print(f"{args.export.name}: {total} declarations, literal cap {args.cap}")
    print(f"  carrying a literal above the cap directly: {len(seeds)}")
    print(f"  lost once the closure is taken:            {len(fallen)}"
          f"  ({100 * len(fallen) / total:.1f}%)")
    print(f"  reachable if the literals were:            {total - len(fallen)}")
    by_kind = Counter(decls[i]["kind"] for i in fallen)
    print("  the closure by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_kind.items())))
    print("\n  the seeds, which are the machine-word layer:")
    for i in seeds:
        print(f"    {decls[i]['kind']:<10} {name_of(decls[i]['names'][0])}")

    if args.write:
        drop = {decls[i]["line"] for i in fallen}
        args.write.write_text("".join(l for n, l in enumerate(raw) if n not in drop))
        print(f"\n  wrote {args.write}: {len(raw) - len(drop)} of {len(raw)} lines")


if __name__ == "__main__":
    main()
