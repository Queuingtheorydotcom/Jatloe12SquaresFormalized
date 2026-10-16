#!/usr/bin/env python3
"""Bounded exact Step04 common-polygon/point-hull proposal, never Lean.

Parent-only execution: --run,128MiB,120seconds,8MiBoutput. Keeps the earlier
family-envelope evidence unchanged. A successful proposal still requires a
checked reference-containment/convexity bridge and every stated support check.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import resource
import signal
import sys
import time

from audit_c898_family_margins import clip, ratio

ROOT = Path(__file__).resolve().parents[1]


def cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def hull(points):
    points = sorted(set(points))
    if len(points) <= 1:
        return points
    lower, upper = [], []
    for ordered, target in [(points, lower), (reversed(points), upper)]:
        for point in ordered:
            while len(target) >= 2 and cross(target[-2], target[-1], point) <= 0:
                target.pop()
            target.append(point)
    return lower[:-1]+upper[:-1]


def weights(point, vertices):
    if len(vertices) == 1:
        assert point == vertices[0]
        return [(0, Fraction(1))]
    if len(vertices) == 2:
        a, b = vertices
        coordinate = 0 if a[0] != b[0] else 1
        t = (point[coordinate]-a[coordinate])/(b[coordinate]-a[coordinate])
        result = [(0, 1-t), (1, t)]
    else:
        result = None
        for j in range(1, len(vertices)-1):
            a, b, c = vertices[0], vertices[j], vertices[j+1]
            determinant = cross(a, b, c)
            assert determinant > 0
            wb, wc = cross(a, point, c)/determinant, cross(a, b, point)/determinant
            wa = 1-wb-wc
            if min(wa, wb, wc) >= 0:
                result = [(0, wa), (j, wb), (j+1, wc)]
                break
        assert result is not None, ('point outside constructed hull', point)
    assert all(w >= 0 for _, w in result) and sum(w for _, w in result) == 1
    assert all(sum(w*vertices[i][coordinate] for i, w in result) == point[coordinate]
               for coordinate in range(2))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('source prepared only; parent must schedule --run')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic()-started > 120 or rss > 128*1024**2:
            raise RuntimeError('common polygon audit reached128MiB/120seconds')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.2, 0.2)
    path = ROOT/'evidence/c898-step04-family-margins.json'
    data = json.loads(path.read_text())
    datums = data['datums']
    sources, neighbors = data['source_routes'], data['neighbor_routes']
    assert len(sources) == 7 and len(neighbors) == 64 and data['pairs'] == 448
    own = {ident: [] for ident in sources+neighbors}
    for index in data['common_point_probe']['own_axis_supports']:
        own[datums[index]['route']].append(index)
    assert all(len(indices) == 4 for indices in own.values())
    margins = {i: Fraction(*d['margin']) for i, d in enumerate(datums)}
    counts = {'point_support_inequalities_examined': 0, 'clipping_constraints': 0,
              'candidate_polygons': 0, 'grid_candidates': 0}

    def slack(point, index):
        counts['point_support_inequalities_examined'] += 1
        x, y = datums[index]['direction']
        return -margins[index]-x*point[0]-y*point[1]

    def valid(point, indices):
        for index in indices:
            s = slack(point, index)
            if s < 0 or (s == 0 and not datums[index]['strict']):
                return False
        return True

    def intersect(polygon, indices):
        for index in indices:
            counts['clipping_constraints'] += 1
            x, y = datums[index]['direction']
            polygon = clip(polygon, x, y, -margins[index])
            if not polygon:
                break
        return polygon

    def candidate(polygon, indices):
        if not polygon:
            return None
        center = (sum(x for x, _ in polygon)/len(polygon),
                  sum(y for _, y in polygon)/len(polygon))
        if not valid(center, indices):
            return None
        # Simple decimal rationals often replace unwieldy clipping fractions.
        for scale in [1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000]:
            nearest = [((v.numerator*scale*2+v.denominator)//(2*v.denominator)) for v in center]
            for dx, dy in [(0,0),(-1,0),(1,0),(0,-1),(0,1)]:
                counts['grid_candidates'] += 1
                point = (Fraction(nearest[0]+dx, scale), Fraction(nearest[1]+dy, scale))
                if valid(point, indices):
                    return point
        return center

    neighbor_indices = [i for ident in neighbors for i in own[ident]]
    square = [(Fraction(-16),Fraction(-16)), (Fraction(16),Fraction(-16)),
              (Fraction(16),Fraction(16)), (Fraction(-16),Fraction(16))]
    common = intersect(square, neighbor_indices)
    subsets = {(ident,) for ident in sources}
    subsets.update(tuple(sources[i:j]) for i in range(len(sources))
                   for j in range(i+2, len(sources)+1) if i == 0 or j == len(sources))
    subsets.update((sources[i],sources[j]) for i in range(len(sources)) for j in range(i+1,len(sources)))
    assert len(subsets) <= 42
    candidates, by_mask, failed = [], {}, []
    for selected in sorted(subsets, key=lambda s:(-len(s),s)):
        indices = [i for ident in selected for i in own[ident]]
        counts['candidate_polygons'] += 1
        polygon = intersect(common, indices)
        point = candidate(polygon, neighbor_indices+indices)
        if point is None:
            failed.append(list(selected))
            continue
        mask = sum(1 << i for i, ident in enumerate(sources) if valid(point, own[ident]))
        assert mask and valid(point, neighbor_indices)
        if mask not in by_mask:
            by_mask[mask] = len(candidates)
            candidates.append({'point':point,'mask':mask,'seed_sources':list(selected)})
    # Seven source groups: a tiny exact set-cover search over candidate masks.
    best = {0: []}
    for index, item in enumerate(candidates):
        for covered, chosen in list(best.items()):
            union = covered | item['mask']
            proposal = chosen+[index]
            if union not in best or len(proposal) < len(best[union]):
                best[union] = proposal
    complete = (1 << len(sources))-1
    selected_indices = best.get(complete)
    report = {'scope':'exact untrusted whole Step04 common-polygon proposal; no Lean acceptance',
              'source_routes':sources,'neighbor_routes':neighbors,'original_pairs':448,
              'original_axis_checks':3584,'neighbor_common_polygon':[
                  [ratio(x),ratio(y)] for x,y in common],
              'candidate_count':len(candidates),'candidate_subsets':len(subsets),
              'failed_candidate_subsets':failed,'counts':counts,'success':False,
              'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    if selected_indices is not None:
        points = [candidates[i]['point'] for i in selected_indices]
        vertices = hull(points)
        bindings = []
        source_checks = []
        for ident in sources:
            point = next(p for p in points if valid(p, own[ident]))
            combination = weights(point, vertices)
            bindings.append({'source':ident,'point':[ratio(v) for v in point],
                             'convex_weights':[[i,ratio(w)] for i,w in combination]})
            for support in own[ident]:
                s = slack(point,support)
                assert s >= 0 and (s > 0 or datums[support]['strict'])
                source_checks.append({'support':support,'slack':ratio(s)})
        neighbor_checks = []
        for vertex, point in enumerate(vertices):
            for support in neighbor_indices:
                s = slack(point,support)
                assert s >= 0 and (s > 0 or datums[support]['strict'])
                neighbor_checks.append({'vertex':vertex,'support':support,'slack':ratio(s)})
        report.update({'success':True,'selected_points':len(points),'hull_vertices':[
            [ratio(x),ratio(y)] for x,y in vertices],'bindings':bindings,
            'source_checks':source_checks,'neighbor_checks':neighbor_checks,
            'proof_obligations':{'unique_directional_supports':284,
                                 'source_point_inequalities':len(source_checks),
                                 'neighbor_hull_inequalities':len(neighbor_checks),
                                 'convex_combinations':len(bindings),
                                 'convex_weight_terms':sum(len(b['convex_weights']) for b in bindings),
                                 'all_original_pairs_covered':448}})
    report['elapsed_seconds'] = time.monotonic()-started
    target = ROOT/'evidence/c898-step04-common-polygon.json'
    encoded = json.dumps(report,separators=(',',':'))+'\n'
    assert len(encoded.encode()) < 8*1024**2
    temporary = target.with_suffix('.json.tmp')
    try:
        temporary.write_text(encoded)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps({key:report[key] for key in ['success','candidate_count','candidate_subsets',
                                                'counts','elapsed_seconds']} |
                     {'proof_obligations':report.get('proof_obligations')}))


if __name__ == '__main__':
    main()
