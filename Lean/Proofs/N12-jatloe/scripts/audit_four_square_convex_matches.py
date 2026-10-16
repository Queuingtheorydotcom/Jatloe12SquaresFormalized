#!/usr/bin/env python3
"""Exact point-pattern inventory, not a geometric solver or Lean replay."""
import functools
import hashlib
import itertools
import json
from pathlib import Path
from provenance_source import read_bytes, exists
import resource
import signal
import sys
import time
from fractions import Fraction as F

signal.alarm(10)
ROOT = Path(__file__).resolve().parents[1]
started = time.monotonic()
coverage = json.loads((ROOT/'evidence/numeric-input-coverage.json').read_text())
old = {28, 537, 556, 565, 567, 569, 570, 575, 576, 1085, 1086, 1087}
new = {405, 424, 985, 990, 993, 994, 999, 1063, 1064, 1069, 1070}
ids = sorted(set(coverage['shortcut59'])-old-new | set(coverage['baseline_other40']))

def scale(p):
    q = [F(x)*1000 for x in p]
    return tuple(int(x) if x.denominator == 1 else x for x in q)

inside = [[(2000,2260),(2260,2000),(2350,2350)],
          [(1650,2350),(1600,3000),(1740,3000)],
          [(914,2000),(1000,2400)], [(3000,2400),(3086,2000)]]
negative = [[(1650,1650),(2350,1650)], [(1000,3086),(2000,3086)],
            [(1650,1650),(760,1870)], []]
# ExactMarkers excludes every marker outside this owner's mask, even when a
# marker is globally unused and absent from the archived foreign-point list.
markers = [(1000,914),(914,1000),(3000,914),(3086,1000),
           (3000,3086),(3086,3000),(1000,3086),(914,3000),
           (1650,1650),(2350,1650),(2350,2350),(1650,2350),
           (914,2000),(2000,914),(3086,2000),(2000,3086)]
lower_right = '--lower-right' in sys.argv
if lower_right:
    inside[3][0] = (3000,2260)

def trans(p, tf):
    x, y = p
    swap, rx, ry = tf
    if swap:
        x, y = y, x
    return (4000-x if rx else x, 4000-y if ry else y)

def cross(a, b):
    return a[0]*b[1]-a[1]*b[0]

def sub(a, b):
    return (a[0]-b[0], a[1]-b[1])

@functools.lru_cache(maxsize=20000)
def witness(poly, p):
    if p in poly:
        return [(poly.index(p), '1')]
    for i, j in itertools.combinations(range(len(poly)), 2):
        a, b = poly[i], poly[j]
        if a == b:
            continue
        if cross(sub(b,a),sub(p,a)) == 0 and all(
                min(a[k],b[k]) <= p[k] <= max(a[k],b[k]) for k in [0,1]):
            k = 0 if a[0] != b[0] else 1
            t = F(p[k]-a[k], b[k]-a[k])
            return [(i,str(1-t)),(j,str(t))]
    for i, j, k in itertools.combinations(range(len(poly)), 3):
        a, b, c = poly[i], poly[j], poly[k]
        det = cross(sub(b,a),sub(c,a))
        if det == 0:
            continue
        v = F(cross(sub(p,a),sub(c,a)),det)
        w = F(cross(sub(b,a),sub(p,a)),det)
        u = 1-v-w
        if min(u,v,w) >= 0:
            assert tuple(u*a[t]+v*b[t]+w*c[t] for t in [0,1]) == p
            return [(i,str(u)),(j,str(v)),(k,str(w))]
    return None

matches, near, positive_near, missing, input_files = [], [], [], [], []
for case in ids:
    path = ROOT/f'evidence/historical/data/case{case}-input.json'
    if not exists(path):
        missing.append(case)
        continue
    raw = read_bytes(path)
    data = json.loads(raw)
    if 'hulls' not in data:
        missing.append(case)
        continue
    input_files.append({'path': str(path.relative_to(ROOT)),
                        'sha256': hashlib.sha256(raw).hexdigest()})
    hulls = [tuple(scale(p) for p in h) for h in data['hulls']]
    outside = {int(i): set(scale(p) for p in ps)
               for i,ps in data.get('extraOutside',{}).items()}
    for owner, group in enumerate(data['row']['groups']):
        outside.setdefault(owner, set()).update(
            p for i, p in enumerate(markers) if i not in group)

    def absent(owner, p):
        return p in outside.get(owner,set()) or any(
            j != owner and witness(h,p) is not None for j,h in enumerate(hulls))

    best, bestscore = None, 999
    closest, closest_score = None, (999,999)
    for tf in itertools.product([False,True], repeat=3):
        pos = [tuple(trans(p,tf) for p in role) for role in inside]
        neg = [tuple(trans(p,tf) for p in role) for role in negative]
        choices = [[o for o,h in enumerate(hulls)
                    if all(witness(h,p) is not None for p in role)] for role in pos]
        if not all(choices):
            deficits = [[sum(witness(h,p) is None for p in role) for h in hulls]
                        for role in pos]
            minima = [min(ds) for ds in deficits]
            if sum(minima) <= 2:
                partial = [[i for i,n in enumerate(ds) if n == m]
                           for ds,m in zip(deficits,minima)]
                for owners in itertools.product(*partial):
                    if len(set(owners)) < 4:
                        continue
                    ng = [{'role':'ABLR'[r], 'point':p} for r,o in enumerate(owners)
                          for p in neg[r] if not absent(o,p)]
                    if not (absent(owners[3],trans((3240,1870),tf)) or
                            absent(owners[3],trans((3000,1740),tf))):
                        ng.append({'role':'R','point':trans((3240,1870),tf),
                                   'alternative':trans((3000,1740),tf)})
                    score = (sum(minima),len(ng))
                    if score < closest_score:
                        closest_score = score
                        closest = {'case':case,'transform':tf,'owners':owners,
                            'negative_gaps':ng,'positive_gaps':[
                                {'role':'ABLR'[r],'point':p,'hull':hulls[o]}
                                for r,o in enumerate(owners) for p in pos[r]
                                if witness(hulls[o],p) is None]}
            continue
        for owners in itertools.product(*choices):
            if len(set(owners)) < 4:
                continue
            gaps = [{'role':'ABLR'[r], 'point':p} for r,o in enumerate(owners)
                    for p in neg[r] if not absent(o,p)]
            ow = not lower_right and absent(owners[3],trans((3240,1870),tf))
            nw = absent(owners[3],trans((3000,1740),tf))
            if not (ow or nw):
                gaps.append({'role':'R', 'point':trans((3240,1870),tf),
                             'alternative':trans((3000,1740),tf)})
            if len(gaps) < bestscore:
                bestscore = len(gaps)
                best = {'case':case, 'transform':tf, 'owners':owners,
                        'right_barrier':'old' if ow else 'lower' if nw else 'missing',
                        'gaps':gaps, 'interpolated_positive':[
                            {'role':'ABLR'[r], 'point':p, 'hull':hulls[o],
                             'weights':witness(hulls[o],p)}
                            for r,o in enumerate(owners) for p in pos[r]
                            if p not in hulls[o]]}
    if best:
        (matches if bestscore == 0 else near).append(best)
    elif closest:
        positive_near.append(closest)

peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
assert peak < 30*1024*1024, peak
report = {'scope':'Exact rational point matching only. Recorded hull and outside facts still '
                 'require their original packing entrance proofs. No numerical propagation '
                 'or Lean compilation is performed.',
          'coordinate_scale':1000, 'seconds':round(time.monotonic()-started,3),
          'right_anchor_height':'113/50' if lower_right else '12/5',
          'peak_rss_bytes_macos':peak, 'requested_cases':len(ids),
          'missing_inputs':missing, 'matches':matches, 'near':near,
          'positive_near':positive_near,
          'input_files':input_files}
(ROOT/('evidence/four-square-lower-anchor-matches.json' if lower_right else
       'evidence/four-square-convex-matches.json')).write_text(
    json.dumps(report,indent=2,default=str)+'\n')
print(json.dumps({k:v for k,v in report.items() if k != 'input_files'},indent=2,default=str))
