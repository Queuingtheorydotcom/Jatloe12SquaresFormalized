#!/usr/bin/env python3
"""Prepare exact common-point rectangles for every original C898 pair stage.

Parent-only --run, 192MiB/120seconds, <=8MiB output. No Lean, archives, active
source changes, or subprocesses. Each stage is partitioned into <=100 Cartesian
rectangles, each either checked at one common point or explicitly preserving
its old pair records. Candidate search failure never implies exclusion.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import re
import resource
import signal
import sys
import time

from audit_c898_family_margins import clip, ratio, sha
from build_c898_pair_fan_pilot import cramer, direction

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--groups', type=int, default=100)
    args = parser.parse_args()
    if not args.run:
        parser.error('prepared only; the coordinator must schedule --run')
    if not 1 <= args.groups <= 100:
        parser.error('each stage must have at most 100 groups')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic()-started > 120 or rss > 192*1024**2:
            raise RuntimeError('all-stage point audit reached192MiB/120seconds')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.2, 0.2)
    paths = {key: ROOT/value for key, value in {
        'poses':'evidence/c898-shared-pose-map.json',
        'fans':'evidence/c898-support-fan-counts.json',
        'records':'evidence/c898-pair-record-map.json',
        'plans':'evidence/c898-pair-pruning-plan-map.json',
        'domains':'evidence/c898-domain-map.json',
        'routes':'evidence/c898-all-cached-pairs.json',
        'references':'Compact/Cases/C898/References.lean'}.items()}
    shared, fans, record_doc, plan_doc, domains, old_routes = [
        json.loads(paths[key].read_text())
        for key in ['poses','fans','records','plans','domains','routes']]
    assert sha(paths['poses']) == fans['source_pose_map_sha256']
    assert sha(paths['poses']) == old_routes['input_sha256']['poses']
    refs = [tuple(map(int, values)) for values in re.findall(
        r'⟨(-?\d+), (-?\d+), (\d+), (-?\d+), (\d+)⟩,', paths['references'].read_text())]
    assert len(refs) == 64
    assert all(c*c+s*s == d*d and d > 0 and sd > 0 for c,s,d,_,sd in refs)
    contexts = {tuple(c['rows']):c for c in fans['contexts']}
    routes, route_ids, support_pool, own = [], {}, [], {}
    costs = {'cone_candidates':0,'candidate_rectangles':0,
             'clipping_constraints':0,'point_inequalities_examined':0}

    def route(pose, block):
        key = (pose, block)
        if key in route_ids:
            return route_ids[key]
        ident = len(routes)
        route_ids[key] = ident
        inputs = ([] if block is None else shared['blocks'][block]['rows']) + shared['poses'][pose]['rows']
        context = contexts[tuple(sorted(set(inputs)))]
        angle = shared['poses'][pose]['angle']
        routes.append({'pose':pose,'block':block,'angle':angle,'context':context['id'],'inputs':inputs})
        indices = []
        for quadrant in [0,2,1,3]:
            key = quadrant*64+angle
            x,y = direction(key,refs)
            choices = []
            for first,second in context['bases']:
                costs['cone_candidates'] += 1
                value = cramer(shared['rows'][first],shared['rows'][second],x,y)
                if value is not None:
                    choices.append((Fraction(value[3],value[2]),not value[4],first,second,value))
            assert choices, (pose,block,key,'missing inherited own-axis support')
            bound,_,first,second,value = min(choices)
            assert first in inputs and second in inputs
            c,s,d,side,sd = refs[angle]
            radius = Fraction(d*side,2*sd)
            margin = bound-radius
            indices.append(len(support_pool))
            support_pool.append({'route':ident,'key':key,'direction':[x,y],
                                 'basis':[first,second],'bound':ratio(bound),
                                 'margin':ratio(margin),'strict':value[4]})
        own[ident] = indices
        return ident

    # Preserve existing nonterminal route IDs before adding the accepted
    # terminal stage's contexts. No original active map is edited.
    for item in old_routes['routes']:
        ident = route(item['pose'],item['block'])
        assert routes[ident] == item
    margins = {}

    def valid(point, indices):
        for index in indices:
            costs['point_inequalities_examined'] += 1
            datum = support_pool[index]
            if index not in margins:
                margins[index] = Fraction(*datum['margin'])
            x,y = datum['direction']
            slack = -margins[index]-x*point[0]-y*point[1]
            if slack < 0 or (slack == 0 and not datum['strict']):
                return False
        return True

    stages = []
    for step in sorted(map(int,domains['pair_steps'])):
        source_domain,neighbor_domain,target_domain = domains['pair_steps'][str(step)]
        plans = sorted([p for p in plan_doc['plans'] if p['step'] == step], key=lambda p:p['pose'])
        blocked = [p for p in plans if p['block'] is not None]
        sources = [route(p['source'],p['block']) for p in blocked]
        neighbors = [route(p,None) for p in domains['domains'][neighbor_domain]]
        assert [p['source'] for p in plans] == domains['domains'][source_domain]
        assert all(p['neighbors_name'] == neighbor_domain for p in plans)
        records = sorted([r for r in record_doc['records'] if r['step'] == step],key=lambda r:r['index'])
        expected = [(p['source'],n,p['block']) for p in blocked
                    for n in domains['domains'][neighbor_domain]]
        assert [(r['source'],r['neighbor'],r['block']) for r in records] == expected
        assert len(records) == len(sources)*len(neighbors)
        cache, attempts = {}, []

        def candidate(box):
            if box in cache:
                return cache[box]
            costs['candidate_rectangles'] += 1
            assert len(cache) < 500
            al,ah,bl,bh = box
            selected = sources[al:ah]+neighbors[bl:bh]
            indices = [i for ident in selected for i in own[ident]]
            polygon = [(Fraction(-16),Fraction(-16)),(Fraction(16),Fraction(-16)),
                       (Fraction(16),Fraction(16)),(Fraction(-16),Fraction(16))]
            for index in indices:
                datum = support_pool[index]
                if index not in margins:
                    margins[index] = Fraction(*datum['margin'])
                x,y = datum['direction']
                costs['clipping_constraints'] += 1
                polygon = clip(polygon,x,y,-margins[index])
                if not polygon:
                    break
            point = None
            if polygon:
                center = tuple(sum(p[c] for p in polygon)/len(polygon) for c in range(2))
                if valid(center,indices):
                    point = center
                    for scale in [1000,10000,100000,1000000,10000000,100000000]:
                        rounded = tuple(Fraction((v.numerator*scale*2+v.denominator)//(2*v.denominator),scale)
                                        for v in center)
                        if valid(rounded,indices):
                            point = rounded
                            break
            pairs = (ah-al)*(bh-bl)
            fallback_cost = 8*pairs
            point_cost = 4*(ah-al+bh-bl)
            if point is not None and point_cost < fallback_cost:
                result = {'kind':'common_point','bounds':list(box),
                          'point':[ratio(v) for v in point],'pairs':pairs,
                          'point_checks':ah-al+bh-bl,'scalar_comparisons':point_cost}
            else:
                result = {'kind':'original_pair_axes','bounds':list(box),'pairs':pairs,
                          'point_checks':0,'scalar_comparisons':fallback_cost}
            cache[box] = result
            attempts.append({'bounds':list(box),'common_point_found':point is not None,
                             'selected_kind':result['kind']})
            return result

        def solve(box, budget):
            base = candidate(box)
            if base['kind'] == 'common_point' or budget == 1:
                return [base]
            al,ah,bl,bh = box
            splits = []
            if bh-bl > 1:
                mid = (bl+bh)//2
                splits.append(('neighbor',(al,ah,bl,mid),(al,ah,mid,bh)))
            if ah-al > 1:
                mid = (al+ah)//2
                splits.append(('source',(al,mid,bl,bh),(mid,ah,bl,bh)))
            if not splits:
                return [base]
            scored = []
            for label,left,right in splits:
                immediate = candidate(left)['scalar_comparisons']+candidate(right)['scalar_comparisons']
                # Equal failed lookahead prefers the larger geometric range;
                # it never changes acceptance or original pair coverage.
                width = bh-bl if label == 'neighbor' else ah-al
                scored.append((immediate,-width,label,left,right))
            _,_,_,left,right = min(scored)
            partition = solve(left,budget//2)+solve(right,budget-budget//2)
            return partition if sum(g['scalar_comparisons'] for g in partition) < base['scalar_comparisons'] else [base]

        partition = solve((0,len(sources),0,len(neighbors)),args.groups)
        assert len(partition) <= args.groups
        seen, used_supports, point_memberships, fallback_ids = set(),set(),0,[]
        for group in partition:
            al,ah,bl,bh = group['bounds']
            for i in range(al,ah):
                for j in range(bl,bh):
                    index = i*len(neighbors)+j
                    assert index not in seen
                    seen.add(index)
                    if group['kind'] == 'original_pair_axes':
                        fallback_ids.append(records[index]['index'])
            if group['kind'] == 'common_point':
                selected = sources[al:ah]+neighbors[bl:bh]
                indices = [k for ident in selected for k in own[ident]]
                point = tuple(Fraction(*v) for v in group['point'])
                assert valid(point,indices)
                used_supports.update(indices)
                point_memberships += len(indices)
        assert seen == set(range(len(records)))
        geometric = [g for g in partition if g['kind'] == 'common_point']
        stages.append({'step':step,'source_domain':source_domain,'neighbor_domain':neighbor_domain,
                       'target_domain':target_domain,'sources':sources,'neighbors':neighbors,
                       'original_pairs':len(records),'original_axes':8*len(records),
                       'partition':partition,'attempts':attempts,
                       'geometric_pairs':sum(g['pairs'] for g in geometric),
                       'fallback_pairs':len(fallback_ids),'fallback_original_record_indices':fallback_ids,
                       'fallback_numeric_rechecked':False,
                       'unique_own_supports':len(used_supports),
                       'point_inequalities':point_memberships,
                       'point_checks':sum(g['point_checks'] for g in partition),
                       'scalar_comparisons':sum(g['scalar_comparisons'] for g in partition)})
    totals = {key:sum(stage[key] for stage in stages) for key in [
        'original_pairs','original_axes','geometric_pairs','fallback_pairs',
        'unique_own_supports','point_inequalities','point_checks','scalar_comparisons']}
    assert totals['original_pairs'] == 25843
    assert totals['geometric_pairs']+totals['fallback_pairs'] == 25843
    report = {'scope':'exact untrusted 13-stage point proposal; all original fallback records retained, no Lean acceptance',
              'routes':routes,'own_supports':support_pool,'stages':stages,'totals':totals,
              'max_groups_per_stage':args.groups,'costs':costs,
              'fallback_boundary':'Original pair records are bound by exact source/block/full-neighbor identity; no new numeric acceptance claim for them.',
              'input_sha256':{key:sha(path) for key,path in paths.items()},
              'elapsed_seconds':time.monotonic()-started}
    target = ROOT/'evidence/c898-all-common-points.json'
    encoded = json.dumps(report,separators=(',',':'))+'\n'
    assert len(encoded.encode()) < 8*1024**2
    temporary = target.with_suffix('.json.tmp')
    try:
        temporary.write_text(encoded)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps({'totals':totals,'groups':[len(s['partition']) for s in stages],
                      'costs':costs,'elapsed_seconds':report['elapsed_seconds']}))


if __name__ == '__main__':
    main()
