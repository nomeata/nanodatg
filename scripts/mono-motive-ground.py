#!/usr/bin/env python3
"""Is a recursor's motive universe ever *non-ground* at a use site?

This is the one measurement that decides `monomorph`'s recursor mode
(MONOMORPH.md §4).  Mode A leaves exactly one level parameter on a recursor —
the eliminating (motive) universe — and folds everything else into the name.
The claim that mode A costs a consuming checker nothing new rests on every use
site supplying a *ground* level for that parameter, so that the surviving level
work is "substitute one closed level", never "unify two open ones".  If some
use site instantiates a recursor at a level that still mentions a parameter,
the claim is false and mode B (`--mono-recursors`, no levels at all) is the
better target.

Run over a `monomorph` **output** file:

    scripts/mono-motive-ground.py OUT.ndjson [OUT.ndjson ...]

## What is counted

* **recursors** — every `recs[]` entry of every `inductive` record.
* **level-carrying declarations** — every declaration in the output with a
  non-empty `levelParams`.  Under mode A these are the recursors, the
  `_model.rec_k` / `_model.iota_k_j` shapes §4.1 keeps a parameter on, and the
  **carried built-ins** (§3), which are passed through with their polymorphism
  intact and are therefore the population most likely to hold a non-ground use.
* **motive instantiations** — for each `const` node naming a recursor, the
  level argument at position 0.  §4.1 asserts motive-first and `monomorph`
  refuses a file where that is not so, so position 0 *is* the motive universe.
  Distinct instantiations are counted by their printed form.
* A level is **ground** when no `param` node is reachable from it.

A use site is attributed to a declaration by reachability over the expression
table, which is interned and shared — so one `const` node can belong to several
declarations, and the per-declaration list names every owner.

Prints a verdict line per file: `motive instantiations: N distinct, K
non-ground`.  `K = 0` is mode A's precondition holding.
"""

import json
import sys
from collections import defaultdict


def load(path):
    names = {0: ""}
    levels = {}
    exprs = {}
    decls = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            o = json.loads(line)
            if "meta" in o:
                continue
            if "in" in o:
                i = o["in"]
                if "str" in o:
                    p = o["str"]["pre"]
                    names[i] = (names[p] + "." if p else "") + o["str"]["str"]
                else:
                    p = o["num"]["pre"]
                    names[i] = (names[p] + "." if p else "") + str(o["num"]["i"])
            elif "il" in o:
                levels[o["il"]] = {k: v for k, v in o.items() if k != "il"}
            elif "ie" in o:
                exprs[o["ie"]] = {k: v for k, v in o.items() if k != "ie"}
            else:
                decls.append(o)
    return names, levels, exprs, decls


def level_info(levels, names):
    """(printed form, is_ground) per level index.  Index 0 is `zero`."""
    show = {}
    ground = {}

    def go(i):
        if i in show:
            return
        if i == 0 or i not in levels:
            show[i], ground[i] = "0", True
            return
        n = levels[i]
        if "param" in n:
            show[i], ground[i] = names[n["param"]], False
        elif "succ" in n:
            go(n["succ"])
            s = show[n["succ"]]
            if s.isdigit():
                show[i] = str(int(s) + 1)
            else:
                show[i] = s + "+1"
            ground[i] = ground[n["succ"]]
        else:
            k = "max" if "max" in n else "imax"
            a, b = n[k]["lhs"], n[k]["rhs"]
            go(a)
            go(b)
            show[i] = "%s(%s,%s)" % (k, show[a], show[b])
            ground[i] = ground[a] and ground[b]

    for i in list(levels) + [0]:
        go(i)
    return show, ground


CHILD_KEYS = {
    "app": ("fn", "arg"),
    "lam": ("type", "body"),
    "forallE": ("type", "body"),
    "letE": ("type", "value", "body"),
    "proj": ("struct",),
    "mdata": ("expr",),
}


def children(node):
    for k, sub in node.items():
        if k in CHILD_KEYS:
            for f in CHILD_KEYS[k]:
                if f in sub:
                    yield sub[f]


def decl_entries(d):
    """(kind, name, levelParams, [root expr indices]) for every declaration in a record."""
    out = []
    for kind, body in d.items():
        if kind == "inductive":
            for t in body.get("types", []):
                out.append(("inductive", t["name"], t.get("levelParams", []), [t["type"]]))
            for c in body.get("ctors", []):
                out.append(("ctor", c["name"], c.get("levelParams", []), [c["type"]]))
            for r in body.get("recs", []):
                roots = [r["type"]] + [rule["rhs"] for rule in r.get("rules", [])]
                out.append(("recursor", r["name"], r.get("levelParams", []), roots))
        else:
            roots = [body["type"]]
            if "value" in body:
                roots.append(body["value"])
            out.append((kind, body["name"], body.get("levelParams", []), roots))
    return out


def report(path):
    names, levels, exprs, decls = load(path)
    show, ground = level_info(levels, names)

    entries = []
    for d in decls:
        entries.extend(decl_entries(d))

    recursors = {names[n] for (k, n, _, _) in entries if k == "recursor"}
    poly = [(k, names[n], [names[p] for p in lps]) for (k, n, lps, _) in entries if lps]

    # reachability: expr node -> declarations owning it
    owners = defaultdict(set)
    for kind, n, lps, roots in entries:
        stack = list(roots)
        seen = set()
        while stack:
            e = stack.pop()
            if e in seen or e not in exprs:
                continue
            seen.add(e)
            owners[e].add(names[n])
            stack.extend(children(exprs[e]))

    # every const use site
    inst = defaultdict(set)          # recursor name -> {printed motive level}
    nonground = defaultdict(set)     # recursor name -> {(level, owners)}
    other_nonground = defaultdict(set)
    n_uses = 0
    for e, node in exprs.items():
        if "const" not in node:
            continue
        c = node["const"]
        nm = names[c["name"]]
        us = c.get("us", [])
        if nm in recursors:
            n_uses += 1
            if not us:
                inst[nm].add("<none>")
                continue
            m = us[0]
            inst[nm].add(show[m])
            if not ground[m]:
                nonground[nm].add((show[m], tuple(sorted(owners[e]))))
        else:
            for u in us:
                if not ground[u]:
                    other_nonground[nm].add((show[u], tuple(sorted(owners[e]))))

    distinct = sum(len(v) for v in inst.values())
    ng = sum(len(v) for v in nonground.values())
    polynames = {n for (_, n, _) in poly}
    head_param = {n: lps[0] for (_, n, lps) in poly}
    inside_poly = 0
    outside_poly = 0
    self_motive = 0
    for nm in nonground:
        for lvl, own in nonground[nm]:
            if own and all(o in polynames for o in own):
                inside_poly += 1
                # is it the *owner's own* motive parameter, at position 0?
                if all(head_param[o] == lvl for o in own):
                    self_motive += 1
            else:
                outside_poly += 1

    print("== %s" % path)
    print("   declarations:            %d" % len(entries))
    print("   recursors:               %d" % len(recursors))
    print("   recursors with a level param: %d"
          % len([1 for (k, n, lps, _) in entries if k == "recursor" and lps]))
    print("   level-carrying decls:    %d" % len(poly))
    print("   recursor use sites:      %d const nodes" % n_uses)
    print("   motive instantiations:   %d distinct, %d NON-GROUND" % (distinct, ng))
    print("     of the non-ground: %d confined to level-carrying declarations,"
          " %d reached from a ground declaration" % (inside_poly, outside_poly))
    print("     of those confined: %d are the *owner's own* motive parameter"
          " (a self/sibling reference the owner's own sigma grounds)" % self_motive)
    if ng:
        for nm in sorted(nonground):
            for lvl, own in sorted(nonground[nm]):
                print("      %s at %s   in %s" % (nm, lvl, ", ".join(own)))
    if other_nonground:
        tot = sum(len(v) for v in other_nonground.values())
        print("   non-recursor const uses at a non-ground level: %d" % tot)
        for nm in sorted(other_nonground):
            for lvl, own in sorted(other_nonground[nm]):
                print("      %s at %s   in %s" % (nm, lvl, ", ".join(own)))
    if poly:
        print("   level-carrying declarations:")
        for k, n, lps in sorted(poly):
            print("      %-10s %-40s {%s}" % (k, n, ", ".join(lps)))


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    for p in sys.argv[1:]:
        report(p)
