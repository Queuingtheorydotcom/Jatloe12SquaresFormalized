#!/usr/bin/env python3
"""Tiny exact ownership/point diagnostic; not a Lean replay or proof acceptance."""
import hashlib
import itertools
import json
from pathlib import Path
import re
import resource
import signal

resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
signal.alarm(8)
ROOT = Path(__file__).resolve().parents[1]
raw = (ROOT / 'source/S12/DomainSpecData.lean').read_text()

def spec(n):
    line = re.search(r'^def combinedSpec' + str(n) + r' :.*$', raw, re.M).group()
    return [frozenset(map(int, x.split(',')))
            for x in re.findall(r'\{([\d,]+)\}', line)
            if sum(int(i) < 10 for i in x.split(',')) == 1]

perm = [8,9,6,7,4,5,2,3,0,1,18,19,15,16,17,12,13,14,10,11]
def reflect(ds):
    return [frozenset(perm[x] for x in d) for d in ds]

domains = {1:spec(1), 2:spec(3), 4:reflect(spec(1)), 8:reflect(spec(3)),
           1024:reflect(spec(13)), 2048:spec(13), 4096:spec(17),
           16384:spec(21), 32768:spec(24), 8192:spec(19),
           8196:[frozenset([6,15])] +
                [frozenset([6,15,x+10]) for x in range(10) if x != 5]}
# Integer coordinates in thousandths: all comparisons below are exact.
markers = [(1000,914),(914,1000),(3000,914),(3086,1000),
           (3000,3086),(3086,3000),(1000,3086),(914,3000),
           (1650,1650),(2350,1650),(2350,2350),(1650,2350),
           (914,2000),(2000,914),(3086,2000),(2000,3086)]
aux = [(1000,1740),(1000,2260),(1600,1000),(1600,3000),
       (2000,1740),(2000,2260),(2400,1000),(2400,3000),
       (3000,1740),(3000,2260),(1000,1600),(1000,2400),
       (1740,1000),(1740,2000),(1740,3000),(2260,1000),
       (2260,2000),(2260,3000),(3000,1600),(3000,2400)]
def inside(mask, owned):
    return {p for i,p in enumerate(markers) if mask & (1<<i)} | {aux[i] for i in owned}
def outside(mask, owned):
    return {p for i,p in enumerate(markers) if not mask & (1<<i)} | {p for i,p in enumerate(aux) if i not in owned}

def check_points(recipe):
    kind,a,b,l,r = recipe
    masks = [1024,2048,4096,16384]
    owners = [a,b,l,r]
    if kind % 2:
        masks = [2048,1024,16384,4096]
        owners = [b,a,r,l]
    transform = (lambda p:(4000-p[0],p[1])) if kind % 2 else (lambda p:p)
    positives = [[(2000,2260),(2260,2000),(2350,2350)],
                 [(1650,2350),(1600,3000),(1740,3000)] if kind < 2 else
                 [(1650,2350),(1740,2000),(1600,3000)],
                 [(914,2000),(1000,2400)],[(3086,2000),(3000,2400)]]
    negatives = [[(1650,1650),(2350,1650)],
                 [(1000,3086),(2000,3086)] if kind < 2 else [],
                 [(1650,1650)] if kind < 2 else [(1000,1740)],
                 [] if kind < 2 else [(3000,1740)]]
    for mask, owned, pos, neg in zip(masks,owners,positives,negatives):
        assert all(transform(p) in inside(mask,owned) for p in pos), (recipe,mask,'inside')
        assert all(transform(p) in outside(mask,owned) for p in neg), (recipe,mask,'outside')
    # The old-template singleton barriers are unchanged from Case567/576.
    return True

recipes = set()
report = {'validation':'exact diagnostic only; Lean source not compiled', 'cases':{}}
for case, masks in [(71,[1,2,4,8,4096,16384,32768,1024,2048]),
                    (80,[1,2,4,8,4096,16384,32768,1024,2048]),
                    (589,[1,2,8,4096,8192,16384,32768,1024,2048]),
                    (590,[1,2,8,4096,8196,16384,32768,1024,2048])]:
    vectors = []
    nodes = [0]
    def search(i, used, vector):
        nodes[0] += 1
        if i == len(masks):
            vectors.append(vector)
            return
        for d in domains[masks[i]]:
            if not used & d:
                search(i+1, used|d, vector+[d])
    search(0,frozenset(),[])
    counts = [0]*4
    for vector in vectors:
        x = dict(zip(masks,vector))
        a,b = x[1024],x[2048]
        kind = (0 if {5,16} <= a and {3,14} <= b else
                1 if {7,17} <= a and {5,13} <= b else
                2 if {5,16} <= a and {3,13} <= b else
                3 if {7,16} <= a and {5,13} <= b else None)
        assert kind is not None, (case,x)
        counts[kind] += 1
        recipe = (kind, *(tuple(sorted(x[m])) for m in [1024,2048,4096,16384]))
        assert check_points(recipe)
        recipes.add(recipe)
    report['cases'][str(case)] = {'owner_masks':masks,
        'domain_sizes':[len(domains[m]) for m in masks],
        'search_nodes':nodes[0], 'complete_vectors':len(vectors),
        'four_pattern_counts':counts, 'uncovered':0}
rows = (ROOT/'source/S12/CoverData.lean').read_text()
ordered = re.findall(r'⟨(\d+),\{([\d,]+)\},\[',rows)
assert len(ordered) == 577
report['original_rows'] = {cid:{'position':i,'family':list(map(int,fam.split(',')))}
                         for i,(cid,fam) in enumerate(ordered) if cid in report['cases']}
report['exact_bindings'] = [list(r) for r in sorted(recipes)]
report['symbolic_patterns'] = 4
report['source_sha256'] = {name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                          for name in ['source/S12/DomainSpecData.lean','source/S12/CoverData.lean',
                          'Compact/Bridge/FourSquareCase.lean','Compact/Bridge/MidpointCase.lean',
                          'Compact/Cases/MergedLower/Recipes.lean']}
target = ROOT/'evidence/merged-lower-exact-audit.json'
target.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['exact_bindings','source_sha256']},indent=2))
