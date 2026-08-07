#!/usr/bin/env python3
"""Application-site statistics over a lean4export 3.1 ndjson file.

The export is a DAG: each expression node appears once and is referenced by
index. Two countings are reported:

- DAG: each node counted once.
- sites: each *reference* to an app node from a non-fn edge (arg edge, binder
  type/body edge, declaration root, letE parts, proj struct, mdata) counts as
  one application spine site. This is the DAG-level proxy for "how many spines
  the corpus writes down"; tree expansion would weight shared spines by their
  use count and can blow up, so it is not attempted here.

For each spine site: length (number of app nodes on the fn chain), head kind
(const/bvar/lam/other), head name for consts, and saturation against the head
constant's Pi-telescope length (syntactic foralls of its declared type; a type
that only *reduces* to a Pi under-counts the telescope, which over-counts
"over-applied" and never fakes saturation).
"""
import json, sys
from collections import Counter, defaultdict

path = sys.argv[1]

names = {0: ""}          # name idx -> dotted string
exprs = {}               # expr idx -> node dict (tag, fields)
decls = []               # (kind, name idx, type expr idx, value expr idx or None, ctor type idxs...)

def name_str(i):
    return names.get(i, f"?{i}")

root_refs = []           # expr idxs referenced from declarations
decl_kinds = Counter()

for line in open(path):
    j = json.loads(line)
    if "meta" in j: continue
    if "in" in j:
        if "str" in j:
            s = j["str"]
            pre = name_str(s["pre"])
            names[j["in"]] = (pre + "." + s["str"]) if pre else s["str"]
        elif "num" in j:
            s = j["num"]
            pre = name_str(s["pre"])
            part = str(s.get("num", s.get("i", "?")))
            names[j["in"]] = (pre + "." + part) if pre else part
        continue
    if "il" in j:  # level
        continue
    if "ie" in j:
        idx = j["ie"]
        tag = [k for k in j if k not in ("ie",)]
        assert len(tag) == 1, j
        t = tag[0]
        exprs[idx] = (t, j[t])
        continue
    # declaration lines: axiom, def, thm, opaque, quot, ind, ctor, rec ...
    for k in ("axiom","def","thm","opaque","quot","ind","ctor","rec","defn","theorem"):
        if k in j:
            d = j[k]
            decl_kinds[k] += 1
            for fld in ("type","value"):
                if isinstance(d, dict) and fld in d and isinstance(d[fld], int):
                    root_refs.append(d[fld])
            # inductive: ctors carried inside? format 3.1: ind has "ctors" list of name idxs; types come as separate ctor decls
            break
    else:
        decl_kinds["other-line"] += 1

# --- per-node census -------------------------------------------------------
tags = Counter(t for (t, _) in exprs.values())

# fn-edges: app idx -> fn idx
fn_edge_targets = set()
for idx, (t, d) in exprs.items():
    if t == "app":
        fn_edge_targets.add(d["fn"])

def spine(idx):
    """walk fn chain from an app node; return (length, head idx)."""
    n = 0
    cur = idx
    while exprs[cur][0] == "app":
        n += 1
        cur = exprs[cur][1]["fn"]
    return n, cur

# telescope length of a const's declared type (syntactic foralls)
decl_type = {}   # name idx -> type expr idx
for line in open(path):
    j = json.loads(line)
    for k in ("axiom","def","thm","opaque","quot"):
        if k in j and isinstance(j[k], dict) and "name" in j[k] and "type" in j[k]:
            decl_type[j[k]["name"]] = j[k]["type"]
    if "inductive" in j:
        d = j["inductive"]
        for grp in ("ctors", "recs", "types", "inducts"):
            for e in d.get(grp, []):
                if isinstance(e, dict) and "name" in e and "type" in e:
                    decl_type[e["name"]] = e["type"]
        # the inductive types themselves
        if "name" in d and "type" in d:
            decl_type[d["name"]] = d["type"]

def telescope(tyidx):
    n = 0
    cur = tyidx
    while cur in exprs and exprs[cur][0] == "forallE":
        n += 1
        cur = exprs[cur][1]["body"]
    return n

# --- spine sites -----------------------------------------------------------
# non-fn references to app nodes
site_lengths = Counter()
head_kinds = Counter()
head_names = Counter()
saturation = Counter()   # 'saturated' / 'partial' / 'over' / 'unknown-head'
partial_by_missing = Counter()

def note_site(idx):
    L, head = spine(idx)
    site_lengths[L] += 1
    ht, hd = exprs[head]
    head_kinds[ht] += 1
    if ht == "const":
        nm = name_str(hd["name"])
        head_names[nm] += 1
        tyidx = decl_type.get(hd["name"])
        if tyidx is None:
            saturation["no-decl-type"] += 1
        else:
            k = telescope(tyidx)
            if L == k: saturation["saturated"] += 1
            elif L < k:
                saturation["partial"] += 1
                partial_by_missing[k - L] += 1
            else: saturation["over-applied(head type reduces further)"] += 1
    else:
        saturation["non-const-head"] += 1

for idx, (t, d) in exprs.items():
    refs = []
    if t == "app":
        refs = [("arg", d["arg"])]
    elif t == "forallE" or t == "lam":
        refs = [("type", d["type"]), ("body", d["body"])]
    elif t == "letE":
        refs = [("type", d["type"]), ("value", d["value"]), ("body", d["body"])]
    elif t == "proj":
        refs = [("struct", d["struct"])]
    elif t == "mdata":
        refs = [("expr", d["expr"])]
    for _, r in refs:
        if r in exprs and exprs[r][0] == "app":
            note_site(r)
for r in root_refs:
    if r in exprs and exprs[r][0] == "app":
        note_site(r)

total_nodes = len(exprs)
napp = tags["app"]
nsites = sum(site_lengths.values())

print(f"file: {path}")
print(f"declaration lines: {sum(decl_kinds.values())} {dict(decl_kinds)}")
print(f"expression DAG nodes: {total_nodes}")
print("node tags:", dict(tags.most_common()))
print(f"app nodes: {napp} ({100*napp/total_nodes:.1f}% of DAG nodes)")
print(f"spine sites (non-fn refs to app nodes): {nsites}")
wsum = sum(l*c for l, c in site_lengths.items())
print(f"mean spine length: {wsum/nsites:.2f}")
print("spine length distribution:")
cum = 0
for L in sorted(site_lengths):
    c = site_lengths[L]
    cum += c
    print(f"  len {L:2d}: {c:6d}  ({100*c/nsites:5.1f}%)  cum {100*cum/nsites:5.1f}%")
print("head kinds:", dict(head_kinds.most_common()))
print("top 25 const heads:")
for nm, c in head_names.most_common(25):
    print(f"  {c:6d}  {nm}")
print("saturation of const-headed sites:", dict(saturation.most_common()))
print("partial sites, by number of missing args:", dict(sorted(partial_by_missing.items())))
eq = head_names.get("Eq", 0)
print(f"Eq-headed sites: {eq} ({100*eq/nsites:.1f}% of sites)")
