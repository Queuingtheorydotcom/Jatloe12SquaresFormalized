#!/usr/bin/env python3
"""Exact common-point compression audit of all six historical pair graphs.

Prepared source only: the coordinator runs --run in one serial 256 MiB / 180 s
slot. No Lean, subprocess, archives, active-source edits, or Cartesian lists.
Each original stage has at most 100 rectangular groups. A group either proves
all pairs by a checked shared point or retains and rechecks all eight original
axes. Actual empty contexts require their explicit strict Farkas certificates.
Output (<=16 MiB) is candidate evidence, never a Lean acceptance receipt.
"""
from bisect import bisect_right
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path
import argparse
import hashlib
import json
import resource
import shutil
import signal
import sys
import time

from audit_c898_family_margins import clip
from audit_historical_bank_reachability import JSONStream

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
FANS = ROOT / 'evidence/historical-fans-701-713-717-973-978-979-cycles'
CASES = (701, 713, 717, 973, 978, 979)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--groups', type=int, default=100)
    parser.add_argument('--output', default='evidence/historical-common-points')
    args = parser.parse_args()
    need(args.run, 'prepared only; parent must schedule --run')
    need(1 <= args.groups <= 100, 'group bound must be between 1 and 100')
    out = (ROOT / args.output).resolve()
    need(out.is_relative_to(ROOT / 'evidence'), 'output must be under evidence')
    staging = out.with_name(out.name + '.staging')
    need(not out.exists() and not staging.exists(), 'refusing existing output')
    started = time.monotonic()
    provenance, costs, unsupported = {}, Counter(), []
    written = 0

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        rss *= 1 if sys.platform == 'darwin' else 1024
        need(rss < 256 * 1024**2, '256 MiB RSS guard')
        need(time.monotonic() - started < 175, '175-second working deadline')

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    def authenticate(path, expected=None):
        h = hashlib.sha256()
        with path.open('rb') as source:
            for chunk in iter(lambda: source.read(65536), b''):
                guard()
                h.update(chunk)
        digest = h.hexdigest()
        need(expected is None or digest == expected, 'source hash mismatch: ' + str(path))
        provenance[str(path.relative_to(ROOT))] = digest
        return digest

    def load(path, expected=None):
        authenticate(path, expected)
        with path.open() as source:
            return json.load(source)

    def records(path, expected=None):
        authenticate(path, expected)
        stream = JSONStream(path, guard)
        try:
            yield from stream.array()
            need(stream.peek() is None, 'trailing JSON content')
        finally:
            stream.file.close()

    def write(name, value):
        nonlocal written
        path = staging / name
        with path.open('w') as target:
            for chunk in json.JSONEncoder(separators=(',', ':')).iterencode(value):
                written += len(chunk.encode())
                need(written <= 16 * 1024**2, '16 MiB aggregate output guard')
                target.write(chunk)
            target.write('\n')
        return {'path':name, 'bytes':path.stat().st_size,
                'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

    try:
        staging.mkdir(parents=True)
        manifest = load(BASE / 'manifest.json')
        fan_manifest = load(FANS / 'manifest.json')
        need(fan_manifest['all_selected_pairs_pass'], 'incomplete original fan audit')
        need(fan_manifest['requested_pairs'] == 639066, 'unexpected original occurrence count')
        hashes = fan_manifest['sources']

        def expected(name):
            return hashes[str((BASE / name).relative_to(ROOT))]

        rows = []
        for r in records(BASE / 'rows.json', expected('rows.json')):
            need(r['index'] == len(rows), 'row ID order')
            rows.append((*r['integers'], bool(r['strict'])))
        poses = []
        for p in records(BASE / 'poses.json', expected('poses.json')):
            need(p['index'] == len(poses), 'pose ID order')
            poses.append((p['angle'], tuple(p['rows'])))
        blocks = []
        for b in records(BASE / 'blocks.json', expected('blocks.json')):
            need(b['index'] == len(blocks), 'block ID order')
            blocks.append(tuple(b['rows']))
        contexts = []
        for c in records(BASE / 'contexts.json', expected('contexts.json')):
            need(c['index'] == len(contexts), 'context ID order')
            contexts.append((c['angle'], tuple(c['inputs'])))
        context_ids = {c:i for i,c in enumerate(contexts)}
        need(len(context_ids) == len(contexts), 'duplicate context IDs')
        refs = load(BASE / 'references.json', expected('references.json'))
        need(len(refs) == 192, 'original reference count')
        for r in refs:
            need(r['denominator'] > 0 and r['sideDenominator'] > 0 and
                 r['sideNumerator'] > 0 and
                 r['c']**2 + r['s']**2 == r['denominator']**2,
                 'invalid original unit reference')
        data = {case:load(BASE / f'C{case}.json', expected(f'C{case}.json')) for case in CASES}

        def context(pose, block=None):
            angle, inputs = poses[pose]
            return context_ids[(angle, (() if block is None else blocks[block]) + inputs)]

        expected_plans, canonical, stage_plans = {}, {}, defaultdict(list)
        occurrence_count = 0
        for case in CASES:
            for p in data[case]['plans']:
                stage_plans[case, p['step']].append(p)
                if p['block'] is None:
                    need(p['historical_pair_count'] == 0, 'unblocked plan has pair declarations')
                    continue
                neighbors = data[case]['domains'][p['neighbors_name']]
                need(len(neighbors) == p['historical_pair_count'], 'original neighbor count')
                identity = (case, p['step'], p['name'])
                need(identity not in expected_plans, 'duplicate plan use')
                expected_plans[identity] = p
                signature = (p['source'], p['block'], tuple(neighbors))
                origin = p['origin']
                if origin in canonical:
                    need(canonical[origin] == signature, 'reused declaration changed its context')
                else:
                    canonical[origin] = signature
                occurrence_count += len(neighbors)
        unique_count = sum(len(signature[2]) for signature in canonical.values())
        need(unique_count == manifest['counts']['covered_pair_declarations'] == 635162,
             'canonical declaration coverage differs from authenticated extraction')
        need(occurrence_count == 639066, 'original occurrence coverage differs')
        need(len(stage_plans) == 113, 'original pair-stage count differs')

        # Stream the largest fan document; never retain its Cartesian neighbor copies.
        fans, starts, empty, order, seen_plans = {}, {}, {}, None, set()
        fan_hash = next(f['sha256'] for f in fan_manifest['files'] if f['path'] == 'fans.json')
        authenticate(FANS / 'fans.json', fan_hash)
        stream = JSONStream(FANS / 'fans.json', guard)
        try:
            stream.punctuation('{')
            seen_keys = set()
            while stream.peek() != '}':
                if seen_keys:
                    stream.punctuation(',')
                key = stream.value()
                need(key not in seen_keys, 'duplicate fan field')
                seen_keys.add(key)
                stream.punctuation(':')
                if key == 'context_records':
                    for record in stream.array():
                        cid = record['context']
                        need(cid not in fans, 'duplicate fan context')
                        entries = tuple(tuple(e) for e in record['entries'])
                        indices = tuple(e[0] for e in entries)
                        # BoundaryFan.cycleEntries adds a wrap entry at zero;
                        # the first actual edge can also start at zero. Several
                        # adjacent normals may map to the same discrete key.
                        # Preserve these ties: bisect_right, like the existing
                        # fan selector, chooses the final qualifying entry.
                        need(indices and indices[0] == 0 and
                             all(0 <= k <= 768 for k in indices) and
                             all(a <= b for a,b in zip(indices, indices[1:])),
                             f'invalid fan start keys for context {cid}')
                        inputs = contexts[cid][1]
                        for _,i,j,X,Y,D in entries:
                            a,b = rows[i],rows[j]
                            need(i in inputs and j in inputs and D > 0, 'invalid basis membership')
                            need(a[0]*b[1]-a[1]*b[0] != 0 and
                                 a[0]*X+a[1]*Y+a[2]*D == 0 and
                                 b[0]*X+b[1]*Y+b[2]*D == 0, 'invalid exact fan vertex')
                            costs['fan_basis_checks'] += 1
                        fans[cid], starts[cid] = entries, indices
                elif key == 'empty_contexts':
                    empty = {int(k):v for k,v in stream.value().items()}
                elif key == 'angle_order':
                    order = stream.value()
                elif key == 'plans':
                    for actual in stream.array():
                        identity = (actual['case'], actual['step'], actual['name'])
                        need(identity in expected_plans and identity not in seen_plans, 'unknown/repeated fan plan')
                        seen_plans.add(identity)
                        p = expected_plans[identity]
                        need(actual['source_pose'] == p['source'] and actual['block'] == p['block'] and
                             actual['source'] == context(p['source'], p['block']), 'fan source binding changed')
                        neighbors = data[actual['case']]['domains'][p['neighbors_name']]
                        need(len(actual['neighbors']) == len(neighbors) and
                             all(cid == context(pid) for cid,pid in zip(actual['neighbors'], neighbors)),
                             'fan neighbor binding changed')
                else:
                    raise ValueError('unknown fan field: ' + key)
            stream.punctuation('}')
            need(stream.peek() is None, 'trailing fan data')
        finally:
            stream.file.close()
        need(seen_plans == set(expected_plans), 'incomplete fan plan coverage')
        need(sorted(order) == list(range(192)), 'angle order is not a permutation')
        need(len(empty) == fan_manifest['empty_context_count'] == 1, 'empty context count differs')
        for cid, witness in empty.items():
            ids, weights = witness['rows'], witness['weights']
            need(len(ids) == len(weights) and all(i in contexts[cid][1] for i in ids), 'empty input membership')
            need(all(w >= 0 for w in weights) and any(weights), 'empty certificate weights')
            totals = [sum(w*rows[i][k] for i,w in zip(ids,weights)) for k in range(3)]
            strict = any(w > 0 and rows[i][3] for i,w in zip(ids,weights))
            need(totals[:2] == [0,0] and (totals[2] < 0 or totals[2] == 0 and strict), 'invalid empty certificate')
            need(totals[2] == witness['constant'] and strict == witness['strict'], 'empty metadata changed')
            costs['empty_certificate_checks'] += 1

        rank = {angle:i for i,angle in enumerate(order)}
        directions = []
        for quadrant in range(4):
            for angle in order:
                c,s = refs[angle]['c'],refs[angle]['s']
                directions.append(((c,s),(-s,c),(-c,-s),(s,-c))[quadrant])

        def keys(angle):
            return tuple(q*192+rank[angle] for q in range(4))

        @lru_cache(maxsize=32768)
        def support(cid, key):
            need(cid in fans and cid not in empty, 'no nonempty fan for requested context')
            entry_index = bisect_right(starts[cid], key)-1
            _,i,j,X,Y,D = fans[cid][entry_index]
            x,y = directions[key]
            a,b = rows[i],rows[j]
            det = a[0]*b[1]-a[1]*b[0]
            sign = 1 if det > 0 else -1
            u = sign*(x*b[1]-y*b[0])
            v = sign*(a[0]*y-a[1]*x)
            need(u >= 0 and v >= 0, 'selected support direction outside its exact cone')
            strict = (u > 0 and a[3]) or (v > 0 and b[3])
            costs['support_cone_checks'] += 1
            return (-x*X-y*Y, D, strict, entry_index)

        own = {}

        def own_supports(cid):
            if cid in own:
                return own[cid]
            need(cid not in empty, 'empty context does not need point supports')
            ref = refs[contexts[cid][0]]
            radius = Q(ref['denominator']*ref['sideNumerator'], 2*ref['sideDenominator'])
            result = []
            # Match CommonPoint.ownDirection, not the cyclic fan's quadrant order.
            for quadrant in (0,2,1,3):
                key = quadrant*192+rank[contexts[cid][0]]
                constant,D,strict,entry = support(cid,key)
                x,y = directions[key]
                g = gcd(abs(x),abs(y))
                ceiling = (radius-Q(constant,D))/g
                result.append((x//g,y//g,ceiling,strict,entry))
            own[cid] = tuple(result)
            costs['distinct_own_support_checks'] += 4
            return own[cid]

        def point_value(values):
            D = lcm(values[0].denominator, values[1].denominator)
            return (int(values[0]*D), int(values[1]*D), D)

        def valid(point, selected, counter):
            X,Y,D = point
            need(D > 0, 'nonpositive point denominator')
            for cid in selected:
                for x,y,ceiling,strict,_ in own_supports(cid):
                    costs[counter] += 1
                    lhs = (x*X+y*Y)*ceiling.denominator
                    rhs = ceiling.numerator*D
                    if lhs > rhs or lhs == rhs and not strict:
                        return False
            return True

        @lru_cache(maxsize=8192)
        def axis_target(a,b,key):
            A,B = refs[a],refs[b]
            x,y = directions[key]
            scale = 2*A['denominator']*A['sideDenominator']*B['denominator']*B['sideDenominator']
            ar = A['sideNumerator']*(abs(x*A['c']+y*A['s'])+abs(-x*A['s']+y*A['c']))
            br = B['sideNumerator']*(abs(x*B['c']+y*B['s'])+abs(-x*B['s']+y*B['c']))
            return scale,ar*B['denominator']*B['sideDenominator']+br*A['denominator']*A['sideDenominator']

        def pair_check(a,b):
            aa,ba = contexts[a][0],contexts[b][0]
            for key in keys(aa)+keys(ba):
                ac,ad,astrict,_ = support(a,key)
                bc,bd,bstrict,_ = support(b,(key+384)%768)
                scale,radius = axis_target(aa,ba,key)
                lhs,rhs = scale*(bd*ac+ad*bc),ad*bd*radius
                costs['fallback_axis_checks'] += 1
                need(lhs < rhs or lhs == rhs and (astrict or bstrict),
                     f'fallback axis failed for contexts {a},{b}, key {key}')

        summaries, final_point_contexts = [], set()
        for case in CASES:
            for step_text, domain_names in sorted(data[case]['pair_steps'].items(), key=lambda p:int(p[0])):
                guard()
                step = int(step_text)
                plans = stage_plans[case,step]
                src_domain,neighbor_domain,target_domain = domain_names
                need([p['source'] for p in plans] == data[case]['domains'][src_domain], 'source plan coverage')
                neighbor_poses = data[case]['domains'][neighbor_domain]
                need(all(data[case]['domains'][p['neighbors_name']] == neighbor_poses for p in plans), 'neighbor domain coverage')
                blocked = [p for p in plans if p['block'] is not None]
                sources = [context(p['source'],p['block']) for p in blocked]
                neighbors = [context(p) for p in neighbor_poses]
                need(sources and neighbors, f'unsupported empty Cartesian stage {case}/{step}')
                cache = {}

                def candidate(box):
                    if box in cache:
                        return cache[box]
                    costs['candidate_rectangles'] += 1
                    al,ah,bl,bh = box
                    selected = sources[al:ah]+neighbors[bl:bh]
                    nonempty = [cid for cid in selected if cid not in empty]
                    ea = sum(cid in empty for cid in sources[al:ah])
                    eb = sum(cid in empty for cid in neighbors[bl:bh])
                    empty_pairs = ea*(bh-bl)+(ah-al-ea)*eb
                    pairs = (ah-al)*(bh-bl)
                    fallback_cost = 8*(pairs-empty_pairs)
                    point_cost = 4*len(nonempty)
                    result = {'kind':'original_pair_axes','bounds':list(box),'pairs':pairs,
                              'empty_pairs':empty_pairs,'scalar_comparisons':fallback_cost}
                    # The budget controls discovery only. Every remaining pair is
                    # still checked, and a timed-out candidate never proves geometry.
                    if fallback_cost > point_cost and len(cache) < 500 and time.monotonic()-started < 108:
                        constraints = {}
                        for cid in nonempty:
                            for x,y,ceiling,strict,_ in own_supports(cid):
                                old = constraints.get((x,y))
                                if old is None or ceiling < old[0]:
                                    constraints[x,y] = (ceiling,strict)
                                elif ceiling == old[0]:
                                    constraints[x,y] = (ceiling,strict and old[1])
                        polygon = [(Q(-16),Q(-16)),(Q(16),Q(-16)),(Q(16),Q(16)),(Q(-16),Q(16))]
                        for (x,y),(ceiling,_) in constraints.items():
                            costs['discovery_clipping_constraints'] += 1
                            polygon = clip(polygon,x,y,ceiling)
                            if not polygon:
                                break
                        if polygon:
                            center = tuple(sum(p[c] for p in polygon)/len(polygon) for c in range(2))
                            point = point_value(center)
                            if valid(point,nonempty,'discovery_point_axis_checks'):
                                for scale in (1000,10000,100000,1000000,10000000,100000000):
                                    rounded = tuple(Q((v.numerator*scale*2+v.denominator)//(2*v.denominator),scale) for v in center)
                                    proposed = point_value(rounded)
                                    if valid(proposed,nonempty,'discovery_point_axis_checks'):
                                        point = proposed
                                        break
                                result.update(kind='common_point', point=list(point),
                                              point_checks=len(nonempty), scalar_comparisons=point_cost)
                    cache[box] = result
                    return result

                def solve(box,budget):
                    base = candidate(box)
                    if base['kind'] == 'common_point' or budget == 1 or base['scalar_comparisons'] == 0:
                        return [base]
                    al,ah,bl,bh = box
                    choices = []
                    if bh-bl > 1:
                        mid = (bl+bh)//2
                        choices.append((bh-bl,(al,ah,bl,mid),(al,ah,mid,bh)))
                    if ah-al > 1:
                        mid = (al+ah)//2
                        choices.append((ah-al,(al,mid,bl,bh),(mid,ah,bl,bh)))
                    if not choices:
                        return [base]
                    _,_,left,right = min((candidate(a)['scalar_comparisons']+candidate(b)['scalar_comparisons'],
                                         -width,a,b) for width,a,b in choices)
                    partition = solve(left,budget//2)+solve(right,budget-budget//2)
                    return partition if sum(p['scalar_comparisons'] for p in partition) < base['scalar_comparisons'] else [base]

                partition = solve((0,len(sources),0,len(neighbors)),args.groups)
                need(len(partition) <= args.groups, 'too many groups')
                # Exact cover by disjoint intervals in each source row. This is
                # linear in rows*groups, never a materialized Cartesian product.
                for i in range(len(sources)):
                    intervals = sorted((g['bounds'][2],g['bounds'][3]) for g in partition if g['bounds'][0] <= i < g['bounds'][1])
                    cursor = 0
                    for lo,hi in intervals:
                        need(lo == cursor and lo < hi <= len(neighbors), 'rectangle gap or overlap')
                        cursor = hi
                    need(cursor == len(neighbors), 'incomplete rectangular coverage')
                point_pairs = fallback_pairs = empty_pairs = point_checks = 0
                for group in partition:
                    al,ah,bl,bh = group['bounds']
                    need(0 <= al < ah <= len(sources) and 0 <= bl < bh <= len(neighbors), 'group outside original stage')
                    empty_pairs += group['empty_pairs']
                    if group['kind'] == 'common_point':
                        selected = [cid for cid in sources[al:ah]+neighbors[bl:bh] if cid not in empty]
                        need(valid(group['point'],selected,'final_point_axis_checks'), 'selected common point failed')
                        final_point_contexts.update(selected)
                        point_checks += len(selected)
                        point_pairs += group['pairs']-group['empty_pairs']
                    else:
                        for a in sources[al:ah]:
                            for b in neighbors[bl:bh]:
                                if a in empty or b in empty:
                                    continue
                                pair_check(a,b)
                                fallback_pairs += 1
                original_pairs = len(sources)*len(neighbors)
                need(point_pairs+fallback_pairs+empty_pairs == original_pairs, 'stage occurrence accounting')
                summaries.append({'case':case,'step':step,'domains':domain_names,
                                  'source_plans':[p['origin'] for p in blocked],
                                  'source_contexts':sources,'neighbor_contexts':neighbors,
                                  'original_pairs':original_pairs,'common_point_pairs':point_pairs,
                                  'fallback_pairs':fallback_pairs,'empty_pairs':empty_pairs,
                                  'point_checks':point_checks,'point_axis_checks':4*point_checks,
                                  'fallback_axis_checks':8*fallback_pairs,
                                  'groups':partition,'candidate_rectangles':len(cache)})
            print(json.dumps({'case':case,'stages':sum(s['case'] == case for s in summaries),
                              'elapsed_seconds':round(time.monotonic()-started,3)}),flush=True)

        totals = {key:sum(s[key] for s in summaries) for key in
                  ('original_pairs','common_point_pairs','fallback_pairs','empty_pairs',
                   'point_checks','point_axis_checks','fallback_axis_checks')}
        need(len(summaries) == 113 and totals['original_pairs'] == 639066, 'final graph occurrence mismatch')
        need(totals['empty_pairs'] == fan_manifest['pairs_closed_by_empty_certificate'] == 21, 'true empty closures changed')
        need(totals['point_axis_checks'] == costs['final_point_axis_checks'] and
             totals['fallback_axis_checks'] == costs['fallback_axis_checks'], 'actual scalar-check accounting differs')
        totals.update(unique_original_pair_declarations=unique_count,
                      reused_declaration_occurrences=occurrence_count-unique_count,
                      original_axis_checks_without_empty=8*(occurrence_count-totals['empty_pairs']),
                      candidate_scalar_checks=totals['point_axis_checks']+totals['fallback_axis_checks'],
                      selected_distinct_own_support_checks=4*len(final_point_contexts),
                      groups=sum(len(s['groups']) for s in summaries),
                      max_groups_per_stage=max(len(s['groups']) for s in summaries))
        files = [write('stages.json', summaries),
                 write('own-support-selection.json', {str(cid):[e[4] for e in support_rows] for cid,support_rows in own.items()}),
                 write('empty-certificates.json', empty)]
        report = {'status':'complete exact mathematical audit; Lean emission and replay pending',
                  'lean_checked':False,'whole_cases_proved':False,'all_original_occurrences_accounted':True,
                  'all_fallback_axes_rechecked':True,'cases':CASES,'pair_stages':113,
                  'totals':totals,'actual_work':dict(costs),'unsupported':unsupported,
                  'sources':provenance,'files':files,'elapsed_seconds':time.monotonic()-started,
                  'limits':{'rss_mib':256,'working_seconds':175,'output_mib':16,'groups_per_stage':args.groups},
                  'record_identity':'source_plans[i] without final Plan, followed by Overlap<j>; i,j are original row/neighbor offsets',
                  'group_semantics':'Half-open Cartesian ranges; remove explicit empty contexts, then shared-point checks or every eight-axis fallback.',
                  'remaining':['Translate exact partitions and original graph bindings into Lean.',
                               'Kernel-check own supports, all selected point memberships, empty certificates and remaining pair axes.',
                               'Prove all retained pruning, relaxation, chord and original-entry obligations.']}
        write('manifest.json',report)
        staging.rename(out)
        print(json.dumps({'output':str(out),'status':report['status'],'totals':totals,
                          'elapsed_seconds':report['elapsed_seconds']}),flush=True)
    except BaseException as error:
        shutil.rmtree(staging,ignore_errors=True)
        print(json.dumps({'status':'stopped; staging output removed','unsupported':[str(error)],
                          'elapsed_seconds':time.monotonic()-started}),file=sys.stderr,flush=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)


if __name__ == '__main__':
    main()
