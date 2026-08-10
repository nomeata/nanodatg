#!/usr/bin/env python3
"""Is the declaration-typing goal a **frontier** or a **wall**?

    NANODATG_DUMP_DECLS=decls.tsv nanoda_bin cfg.json    # build with `stepcount`
    python3 scripts/decl-frontier.py decls.tsv

# The question

`⊢ ⟦c⟧ ∈ ⟦T_c⟧` is the theorem the project exists to produce, and it stands at
26 of 2 891 value-carrying (declaration, σ) pairs. The application rule needs
the head constant's own typing, so the recursion is topological — which invites
the reading that the goal is a *bootstrapping* problem: a base too small for the
cascade to start.

**That reading is testable, and this script is the test.** If it is right, the
declarations that fail should be blocked by *other declarations*, and sealing a
few heavily-named ones should unblock many. If it is wrong, there should be
declarations with nothing blocking them that fail anyway — and their number is
the size of the real obstacle.

The aggregate counters cannot answer it: they say how many fail, not which, and
"is the next failure blocked by the last one" is a question about individual
declarations in walk order. Hence the dump.

# What counts as a blocker

A dependency blocks only if it is **itself a value-carrying declaration that is
not sealed**. A reference to an inductive type, a constructor or a recursor is
not a blocker: those are served by `derived`'s own theorems (`CtorRule` and the
ι rules), which is exactly why `HtClause::CtorApp` fires 3 291 times a run while
`has_type_app` manages 492. Counting them as blockers is the easy mistake and it
inflates the frontier to near-nothing; the first cut of this analysis made it.

# The answer, on `init-prelude` at 2026-08-10

**A wall.** 1 040 of the 2 865 unsealed declarations — 36 % — have *no* unsealed
value-carrying dependency at all, and fail anyway, every one of them tagged
`ty_premise_missing`. Sealing the ten most-named blockers moves the ready set
from 1 040 to 1 126. The dependency graph is not the constraint.
"""
import collections
import sys


def load(path):
    rows = []
    for line in open(path):
        p = (line.rstrip("\n").split("\t") + [""] * 5)[:5]
        rows.append((int(p[0]), p[1], p[2], p[3], [d for d in p[4].split(",") if d]))
    return sorted(rows)


def main(path):
    rows = load(path)
    value_carrying = {n for _, _, _, n, _ in rows}
    sealed = {n for _, o, _, n, _ in rows if o == "derived"}
    unsealed = [r for r in rows if r[1] != "derived"]

    def blockers(deps):
        return {d for d in deps if d in value_carrying and d not in sealed}

    print(f"pairs with a value: {len(rows)}  {collections.Counter(o for _, o, _, _, _ in rows)}")
    print(f"distinct sealed names: {len(sealed)}")
    print(f"gap tags: {collections.Counter(w for _, o, w, _, _ in rows if o == 'gap')}")

    nb = collections.Counter(len(blockers(r[4])) for r in unsealed)
    print("\nunsealed by number of blocking declarations:")
    for k in range(6):
        print(f"  {k}: {nb[k]}")
    print(f"  6+: {sum(v for k, v in nb.items() if k >= 6)}")

    ready = [r for r in unsealed if not blockers(r[4])]
    print(f"\nREADY BUT FAILING: {len(ready)} ({100 * len(ready) // max(1, len(unsealed))}%)")
    print("  first 15, in walk order:")
    for r in ready[:15]:
        print(f"    {r[0]:>5} {r[1]:<12} {r[2]:<20} {r[3][:44]}")

    cnt = collections.Counter()
    for r in unsealed:
        for b in blockers(r[4]):
            cnt[b] += 1
    print("\ntop blockers, by unsealed declarations naming them:")
    for n, c in cnt.most_common(10):
        print(f"  {c:>5}  {n}")

    s2 = set(sealed)
    print("\ncascade — seal the most-named blocker, repeat; how many become ready:")
    for i in range(10):
        c = collections.Counter()
        for r in unsealed:
            if r[3] in s2:
                continue
            for d in r[4]:
                if d in value_carrying and d not in s2:
                    c[d] += 1
        if not c:
            break
        b = c.most_common(1)[0][0]
        s2.add(b)
        n = sum(
            1
            for r in unsealed
            if r[3] not in s2 and not {d for d in r[4] if d in value_carrying and d not in s2}
        )
        print(f"  +{i + 1:>2} {b[:40]:<40} ready={n}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    main(sys.argv[1])
