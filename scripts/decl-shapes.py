#!/usr/bin/env python3
"""Corpus declaration shapes, at the grain `derived::inductive::DeclSpec` has.

`scripts/arm-coverage.py` answers "which translation arms does a declaration
reach", off the inductive *record* alone. That record does not say which of a
constructor's fields are recursive, so it cannot see the axes a `DeclSpec`
turns on: `k` and `m` per constructor, the interleaved field mask, a
function-typed recursive argument and its telescope depth, and whether any
constructor is nullary. This script walks each constructor's **type** past the
parameter binders and classifies every remaining binder — plain, recursive,
recursive-and-function-typed, or a self-mention the spec cannot express — so
those axes can be counted.

It exists because a sweep of `derived/tests/` on 2026-08-11 found the fixtures
and the corpus disagreeing on three of them at once (no-nullary, `np >= 3`,
`ctors >= 6`), and the finding was only visible with the corpus side counted.
A suite agreeing on an incidental detail is the give-away; this is how to see
what the corpus actually presents. See MEASUREMENTS.md, "The fixtures and the
corpus, counted on the same axes".

Reads the export JSON directly and never runs the checker.

Usage:
    python3 scripts/decl-shapes.py vendor/arena-tests/good
"""
import json, sys, collections
from pathlib import Path


def load(path):
    recs = []
    for l in open(path):
        l = l.strip()
        if l.startswith('{'):
            try:
                recs.append(json.loads(l))
            except ValueError:
                pass
    return recs


def tables(recs):
    names = {}
    exprs = {}
    for d in recs:
        if 'in' in d and 'str' in d:
            names[d['in']] = (d['str']['pre'], d['str']['str'])
        if 'ie' in d:
            k = next((x for x in d if x != 'ie'), None)
            exprs[d['ie']] = (k, d[k])
    def res(i, depth=0):
        if i == 0 or depth > 30:
            return ''
        pre, s = names.get(i, (0, '?'))
        par = res(pre, depth + 1)
        return f'{par}.{s}' if par else s
    return res, exprs


def head_const(exprs, i, budget=200):
    """Name-index of the head constant of an application spine, or None."""
    while budget:
        budget -= 1
        k, v = exprs.get(i, (None, None))
        if k == 'app':
            i = v['fn']
        elif k == 'const':
            return v['name']
        else:
            return None
    return None


def strip_pis(exprs, i, budget=200):
    """Peel leading foralls; return (depth, core)."""
    d = 0
    while budget:
        budget -= 1
        k, v = exprs.get(i, (None, None))
        if k == 'forallE':
            d += 1
            i = v['body']
        else:
            return d, i
    return d, i


def mentions(exprs, i, target, budget=4000, seen=None):
    if seen is None:
        seen = set()
    stack = [i]
    while stack and budget:
        budget -= 1
        j = stack.pop()
        if j in seen:
            continue
        seen.add(j)
        k, v = exprs.get(j, (None, None))
        if k == 'const':
            if v['name'] == target:
                return True
        elif k == 'app':
            stack += [v['fn'], v['arg']]
        elif k in ('forallE', 'lam'):
            stack += [v['type'], v['body']]
        elif k == 'letE':
            stack += [x for x in (v.get('type'), v.get('val'), v.get('body')) if x is not None]
        elif k == 'proj':
            stack.append(v['struct'] if 'struct' in v else v.get('structure', 0))
    return False


def ctor_shape(exprs, ctor, ind_name, np):
    """[(kind, dom_depth)] per field: kind in {'plain','rec','recfun','self'}."""
    i = ctor['type']
    for _ in range(np):
        k, v = exprs.get(i, (None, None))
        if k != 'forallE':
            return None
        i = v['body']
    out = []
    while True:
        k, v = exprs.get(i, (None, None))
        if k != 'forallE':
            break
        dom = v['type']
        d, core = strip_pis(exprs, dom)
        h = head_const(exprs, core)
        if h == ind_name:
            out.append(('recfun' if d else 'rec', d))
        elif mentions(exprs, dom, ind_name):
            out.append(('self', d))
        else:
            out.append(('plain', d))
        i = v['body']
    return out


def scan(path):
    recs = load(path)
    res, exprs = tables(recs)
    ctors = {}
    for d in recs:
        if 'inductive' in d:
            for c in d['inductive'].get('ctors', []):
                ctors[c['name']] = c
    rows = []
    for d in recs:
        if 'inductive' not in d:
            continue
        ind = d['inductive']
        for t in ind['types']:
            np = t['numParams']
            shapes = []
            for cn in t['ctors']:
                s = ctor_shape(exprs, ctors[cn], t['name'], np)
                shapes.append(s if s is not None else [])
            rows.append(dict(
                name=res(t['name']), np=np, ni=t['numIndices'], nest=t['numNested'],
                mutual=len(t['all']) > 1, isrec=t['isRec'], refl=bool(t.get('isReflexive')),
                shapes=shapes, file=Path(path).stem,
                recs=[r for r in ind.get('recs', []) if r['all'] == t['all']],
                resnames=res,
            ))
    return rows


def main(argv):
    targets = []
    for a in argv:
        p = Path(a)
        targets += sorted(p.rglob('*.ndjson')) if p.is_dir() else [p]
    rows = []
    for t in targets:
        rows += scan(t)
    print(f'{len(targets)} exports, {len(rows)} inductive declarations\n')

    def bucket(r):
        n = len(r['shapes'])
        ms = [sum(1 for k, _ in s if k in ('rec', 'recfun')) for s in r['shapes']]
        ks = [sum(1 for k, _ in s if k == 'plain') for s in r['shapes']]
        return n, ms, ks

    c = collections.Counter()
    wit = {}
    for r in rows:
        n, ms, ks = bucket(r)
        m = max(ms) if ms else 0
        feats = []
        feats.append(f'ctors={"0" if n==0 else "1" if n==1 else "2" if n==2 else "3-5" if n<=5 else "6+"}')
        feats.append(f'np={"0" if r["np"]==0 else "1" if r["np"]==1 else "2+"}')
        feats.append('indexed' if r['ni'] else 'unindexed')
        if r['mutual']: feats.append('mutual')
        if r['nest']: feats.append('nested')
        feats.append(f'maxrecs={"0" if m==0 else "1" if m==1 else "2" if m==2 else "3+"}')
        nullary = any(len(s) == 0 for s in r['shapes'])
        feats.append('has-nullary' if nullary else 'no-nullary')
        if any(k == 'recfun' for s in r['shapes'] for k, _ in s):
            feats.append('fun-typed-rec')
        if any(d > 1 for s in r['shapes'] for k, d in s if k == 'recfun'):
            feats.append('rec-dom-depth>=2')
        if any(k == 'self' for s in r['shapes'] for k, _ in s):
            feats.append('self-mention')
        # interleaved: a rec slot before a later plain slot
        inter = False
        for s in r['shapes']:
            kinds = [k for k, _ in s]
            for i, k in enumerate(kinds):
                if k in ('rec', 'recfun') and 'plain' in kinds[i + 1:]:
                    inter = True
        if inter: feats.append('interleaved-mask')
        for f in feats:
            c[f] += 1
            wit.setdefault(f, []).append(r['name'])
    print(f'{"axis":24} {"count":>6}  witnesses')
    print('-' * 90)
    for k in sorted(c, key=lambda a: (a.split('=')[0], -c[a])):
        w = ', '.join(sorted(set(wit[k]))[:3])
        print(f'{k:24} {c[k]:>6}  {w[:60]}')
    return rows


if __name__ == '__main__':
    main(sys.argv[1:])
