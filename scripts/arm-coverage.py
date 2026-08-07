#!/usr/bin/env python3
"""Arm coverage: which translation arms can any corpus declaration actually reach?

`ci/check.sh` tells you the corpus is green. It does not tell you which code the
corpus *exercises* — and on this project that gap has cost five rounds. The
indexed function-typed recursive-argument row took five successive fixes, each a
real defect, and an audit later measured that **zero of 102** corpus inductives
can reach the arm they were in: "corpus green" there meant "no declaration can
see this code". Every one of those defects was found by a surviving mutation
*after* the work rather than a coverage figure *before* it.

So this script answers, per arm, how many declarations reach it. A **zero** is
the interesting number: it says corpus-green is vacuous there and only a
designed fixture can speak. A **one** is nearly as interesting, because a single
witness cannot distinguish an axis from the identity on it — the reason a test
that pins a position needs three elements.

It reads the export JSON directly and never runs the checker, so it is cheap and
has no memory footprint worth the name.

Usage:
    python3 scripts/arm-coverage.py [dir-or-file ...]     # default: the corpus
"""

import json
import sys
from collections import Counter
from pathlib import Path

CORPUS = Path("vendor/arena-tests/good/tutorial")


def names_of(records):
    """Resolve the export's name table to dotted strings."""
    tbl = {}
    for d in records:
        if "in" in d and "str" in d:
            tbl[d["in"]] = (d["str"]["pre"], d["str"]["str"])

    def res(i, depth=0):
        if i == 0 or depth > 25:
            return ""
        pre, s = tbl.get(i, (0, "?"))
        parent = res(pre, depth + 1)
        return f"{parent}.{s}" if parent else s

    return res


def arms_of_inductive(ind, res):
    """Yield (arm, declaration-name) for each arm this declaration reaches.

    Arm names mirror the branches the translation actually distinguishes, so a
    zero here maps onto a specific piece of unreachable code rather than onto a
    vague shape.
    """
    types = ind.get("types", [])
    block = "mutual" if len(types) > 1 else "single"
    for t in types:
        name = res(t["name"])
        ni = t.get("numIndices", 0)
        np = t.get("numParams", 0)
        nested = t.get("numNested", 0)

        yield f"block:{block}", name
        yield ("indexed" if ni else "unindexed"), name
        yield (f"params:{'0' if np == 0 else '1+'}"), name
        if nested:
            yield f"nested:numNested={min(nested, 2)}{'+' if nested > 2 else ''}", name
        # Combinations, because an axis can be the identity on a population
        # even when both of its ends are well represented. The corpus has 35
        # indexed declarations and 35 indexed-with-parameters: `indexed ∧ np=0`
        # is empty, so nothing there distinguishes a parameter frame from an
        # index frame — which is the shape three of the five defects on the
        # indexed row wore.
        yield (f"indexed+params:{'1+' if np else '0'}" if ni else
               f"unindexed+params:{'1+' if np else '0'}"), name
        if t.get("isReflexive"):
            yield "reflexive", name

    for r in ind.get("recs", []):
        if r.get("k"):
            yield "recursor:k-like", res(r["name"])
        if len(r.get("all", [])) > 1:
            yield "recursor:cross-member", res(r["name"])
        if r.get("numMotives", 1) > 1:
            yield "recursor:multi-motive", res(r["name"])


def scan(path):
    records = []
    with open(path) as fh:
        for line in fh:
            try:
                records.append(json.loads(line))
            except ValueError:
                continue
    res = names_of(records)
    hits = []
    inductives = 0
    for d in records:
        if "inductive" in d:
            inductives += len(d["inductive"].get("types", []))
            hits.extend(arms_of_inductive(d["inductive"], res))
    return inductives, hits


def main(argv):
    targets = []
    for a in argv or [str(CORPUS)]:
        p = Path(a)
        targets.extend(sorted(p.glob("*.ndjson")) if p.is_dir() else [p])
    if not targets:
        sys.exit("no .ndjson found — run from the repo root")

    counts = Counter()
    witnesses = {}
    total = 0
    for t in targets:
        n, hits = scan(t)
        total += n
        for arm, decl in hits:
            counts[arm] += 1
            witnesses.setdefault(arm, []).append(f"{decl} ({t.stem})")

    print(f"{len(targets)} exports, {total} inductive declarations\n")
    print(f"{'arm':34} {'count':>6}  witnesses")
    print("-" * 78)
    for arm in sorted(counts, key=lambda a: (counts[a], a)):
        n = counts[arm]
        w = ", ".join(witnesses[arm][:2])
        flag = "  <-- SINGLE WITNESS" if n == 1 else ""
        print(f"{arm:34} {n:>6}  {w[:34]}{flag}")

    # An arm the translation has code for but that nothing here reaches is the
    # finding this script exists for, so name the ones we know are branched on.
    known = {
        "block:mutual", "indexed", "unindexed", "params:0", "params:1+",
        "reflexive", "recursor:k-like",
        "recursor:cross-member", "recursor:multi-motive",
        "nested:numNested=1", "nested:numNested=2",
        "indexed+params:0", "indexed+params:1+",
        "unindexed+params:0", "unindexed+params:1+",
    }
    unreached = sorted(known - set(counts))
    if unreached:
        print(f"\nUNREACHED by this population ({len(unreached)}):")
        for a in unreached:
            print(f"  {a}  — corpus-green says nothing here; only a fixture can")


if __name__ == "__main__":
    main(sys.argv[1:])
