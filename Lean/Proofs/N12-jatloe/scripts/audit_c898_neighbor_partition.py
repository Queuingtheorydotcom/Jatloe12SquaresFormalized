#!/usr/bin/env python3
"""Bounded exact Step04 neighbor partition with explicit numeric fallbacks.

Parent-only --run;128MiB/120seconds/8MiBoutput. At most63 neighbor intervals
are considered. Every selected group covers all seven source contexts and
every neighbor occurs in exactly one group. No Lean, external data, or active
source edits. Earlier failed whole-neighbor common-polygon evidence is kept.
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
from audit_c898_common_polygon import hull, weights

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--max-depth', type=int, default=5, choices=range(6))
    args = parser.parse_args()
    if not args.run:
        parser.error('prepared only; parent must schedule --run')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic()-started > 120 or rss > 128*1024**2:
            raise RuntimeError('partition audit reached128MiB/120seconds')

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
    margins = {i: Fraction(*d['margin']) for i,d in enumerate(datums)}
    costs = {'intervals_examined':0,'candidate_polygons':0,'clipping_constraints':0,
             'point_inequalities_examined':0}
    attempts = []

    def slack(point,index):
        costs['point_inequalities_examined'] += 1
        x,y = datums[index]['direction']
        return -margins[index]-x*point[0]-y*point[1]

    def valid(point,indices):
        for index in indices:
            s = slack(point,index)
            if s < 0 or (s == 0 and not datums[index]['strict']):
                return False
        return True

    def intersect(polygon,indices):
        for index in indices:
            costs['clipping_constraints'] += 1
            x,y = datums[index]['direction']
            polygon = clip(polygon,x,y,-margins[index])
            if not polygon:
                break
        return polygon

    def point_in(polygon,indices):
        if not polygon:
            return None
        point = (sum(x for x,_ in polygon)/len(polygon),sum(y for _,y in polygon)/len(polygon))
        if not valid(point,indices):
            return None
        for scale in [1000,10000,100000,1000000,10000000,100000000]:
            rounded = tuple(Fraction((v.numerator*scale*2+v.denominator)//(2*v.denominator),scale)
                            for v in point)
            if valid(rounded,indices):
                return rounded
        return point

    subsets = {(ident,) for ident in sources}
    subsets.update(tuple(sources[i:j]) for i in range(len(sources))
                   for j in range(i+2,len(sources)+1) if i == 0 or j == len(sources))
    subsets.update((sources[i],sources[j]) for i in range(len(sources)) for j in range(i+1,len(sources)))
    assert len(subsets) <= 42
    ordered_subsets = sorted(subsets,key=lambda s:(len(s),s))

    def geometric(lo,hi):
        selected_neighbors = neighbors[lo:hi]
        neighbor_supports = [i for ident in selected_neighbors for i in own[ident]]
        polygon = [(Fraction(-16),Fraction(-16)),(Fraction(16),Fraction(-16)),
                   (Fraction(16),Fraction(16)),(Fraction(-16),Fraction(16))]
        common = intersect(polygon,neighbor_supports)
        if not common:
            return None,'empty_neighbor_core'
        candidates, seen = [],set()
        for selected in ordered_subsets:
            source_supports = [i for ident in selected for i in own[ident]]
            costs['candidate_polygons'] += 1
            point = point_in(intersect(common,source_supports),neighbor_supports+source_supports)
            if point is None:
                if len(selected) == 1:
                    return None,f'no_common_point_for_source_{selected[0]}'
                continue
            mask = sum(1 << i for i,ident in enumerate(sources) if valid(point,own[ident]))
            if mask not in seen:
                seen.add(mask)
                candidates.append((point,mask))
        best = {0:[]}
        for index,(_,mask) in enumerate(candidates):
            for covered,chosen in list(best.items()):
                union = covered | mask
                proposal = chosen+[index]
                if union not in best or len(proposal) < len(best[union]):
                    best[union] = proposal
        chosen = best.get((1 << len(sources))-1)
        if chosen is None:
            return None,'candidate_cover_failed'
        points = [candidates[i][0] for i in chosen]
        vertices = hull(points)
        bindings,source_checks,neighbor_checks = [],[],[]
        for ident in sources:
            point = next(p for p in points if valid(p,own[ident]))
            combination = weights(point,vertices)
            bindings.append({'source':ident,'point':[ratio(v) for v in point],
                             'convex_weights':[[i,ratio(w)] for i,w in combination]})
            for index in own[ident]:
                s = slack(point,index)
                assert s >= 0 and (s > 0 or datums[index]['strict'])
                source_checks.append({'support':index,'slack':ratio(s)})
        for vertex,point in enumerate(vertices):
            for index in neighbor_supports:
                s = slack(point,index)
                assert s >= 0 and (s > 0 or datums[index]['strict'])
                neighbor_checks.append({'vertex':vertex,'support':index,'slack':ratio(s)})
        obligations = {'source_point_inequalities':len(source_checks),
                       'neighbor_hull_inequalities':len(neighbor_checks),
                       'convex_combinations':len(bindings),
                       'convex_weight_terms':sum(len(b['convex_weights']) for b in bindings)}
        return {'kind':'common_hull','lo':lo,'hi':hi,'neighbors':selected_neighbors,
                'represented_pairs':len(sources)*len(selected_neighbors),
                'hull_vertices':[[ratio(x),ratio(y)] for x,y in vertices],
                'bindings':bindings,'source_checks':source_checks,'neighbor_checks':neighbor_checks,
                'support_ids':sorted(set(neighbor_supports+[i for ident in sources for i in own[ident]])),
                'obligations':obligations,
                'comparison_cost':len(source_checks)+len(neighbor_checks)},None

    def solve(lo,hi,depth):
        costs['intervals_examined'] += 1
        assert costs['intervals_examined'] <= 63
        proof,reason = geometric(lo,hi)
        fallback = {'kind':'original_pair_axes','lo':lo,'hi':hi,'neighbors':neighbors[lo:hi],
                    'represented_pairs':7*(hi-lo),'comparison_cost':8*7*(hi-lo)}
        best = [proof] if proof and proof['comparison_cost'] < fallback['comparison_cost'] else [fallback]
        attempts.append({'lo':lo,'hi':hi,'success':proof is not None,'failure':reason,
                         'hull_vertices':len(proof['hull_vertices']) if proof else None,
                         'comparison_cost':proof['comparison_cost'] if proof else None})
        if depth < args.max_depth and hi-lo > 1:
            middle = (lo+hi)//2
            split = solve(lo,middle,depth+1)+solve(middle,hi,depth+1)
            if sum(p['comparison_cost'] for p in split) < sum(p['comparison_cost'] for p in best):
                best = split
        return best

    partition = solve(0,len(neighbors),0)
    assert [n for group in partition for n in group['neighbors']] == neighbors
    assert sum(group['represented_pairs'] for group in partition) == 448
    geometric_groups = [g for g in partition if g['kind'] == 'common_hull']
    fallback_groups = [g for g in partition if g['kind'] != 'common_hull']
    supports = sorted({i for g in geometric_groups for i in g['support_ids']})
    obligations = {'geometric_groups':len(geometric_groups),'fallback_groups':len(fallback_groups),
                   'geometrically_covered_pairs':sum(g['represented_pairs'] for g in geometric_groups),
                   'fallback_pairs':sum(g['represented_pairs'] for g in fallback_groups),
                   'fallback_axis_checks':sum(g['comparison_cost'] for g in fallback_groups),
                   'unique_own_axis_supports':len(supports),
                   'source_point_inequalities':sum(g['obligations']['source_point_inequalities'] for g in geometric_groups),
                   'neighbor_hull_inequalities':sum(g['obligations']['neighbor_hull_inequalities'] for g in geometric_groups),
                   'convex_combinations':sum(g['obligations']['convex_combinations'] for g in geometric_groups),
                   'convex_weight_terms':sum(g['obligations']['convex_weight_terms'] for g in geometric_groups),
                   'scalar_comparisons_including_fallback':sum(g['comparison_cost'] for g in partition)}
    report = {'scope':'untrusted whole Step04 partition proposal; no Lean acceptance',
              'sources':sources,'neighbors':neighbors,'all_original_pairs':448,'original_axis_checks':3584,
              'partition':partition,'own_support_ids':supports,'proof_obligations':obligations,
              'attempts':attempts,'search_costs':costs,'max_depth':args.max_depth,
              'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
              'elapsed_seconds':time.monotonic()-started}
    target = ROOT/'evidence/c898-step04-neighbor-partition.json'
    encoded = json.dumps(report,separators=(',',':'))+'\n'
    assert len(encoded.encode()) < 8*1024**2
    temporary = target.with_suffix('.json.tmp')
    try:
        temporary.write_text(encoded)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps({'proof_obligations':obligations,'search_costs':costs,
                      'elapsed_seconds':report['elapsed_seconds']}))


if __name__ == '__main__':
    main()
