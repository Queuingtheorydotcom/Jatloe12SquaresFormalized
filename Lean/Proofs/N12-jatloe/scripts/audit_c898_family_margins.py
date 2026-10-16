#!/usr/bin/env python3
"""Exact Step04 support-margin envelopes; candidate evidence, never Lean.

Run only in the coordinator's serial 192-MiB/120-second slot with --run.
Reads existing authenticated dictionaries and accepted-stage metadata. Writes
at most8MiB, no archives, subprocesses, generated Lean, or active source edits.
The report counts all envelope memberships, strict ties and comparisons; it
does not mistake Python acceptance for a formal proof or hide pair work.
"""
from collections import defaultdict
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

from build_c898_pair_fan_pilot import cramer, direction, axis_key

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            h.update(block)
    return h.hexdigest()


def ratio(value):
    return [value.numerator, value.denominator]


def radius(reference, x, y):
    c, s, denominator, side, side_denominator = reference
    assert denominator > 0 and side_denominator > 0
    return Fraction(side * (abs(x*c+y*s) + abs(-x*s+y*c)),
                    2*denominator*side_denominator)


def clip(polygon, x, y, ceiling):
    if not polygon:
        return []
    result = []
    previous = polygon[-1]
    before = ceiling-x*previous[0]-y*previous[1]
    for current in polygon:
        after = ceiling-x*current[0]-y*current[1]
        if (before < 0) != (after < 0):
            t = before/(before-after)
            cross = (previous[0]+t*(current[0]-previous[0]),
                     previous[1]+t*(current[1]-previous[1]))
            if not result or result[-1] != cross:
                result.append(cross)
        if after >= 0 and (not result or result[-1] != current):
            result.append(current)
        previous, before = current, after
    if len(result) > 1 and result[0] == result[-1]:
        result.pop()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('prepared only; the coordinating worker must schedule --run')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic()-started > 120 or rss > 192*1024**2:
            raise RuntimeError('family audit reached its 120-second/192-MiB cap')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.2, 0.2)
    paths = {name: ROOT/path for name, path in {
        'poses': 'evidence/c898-shared-pose-map.json',
        'fans': 'evidence/c898-support-fan-counts.json',
        'stages': 'evidence/c898-all-cached-pairs.json',
        'references': 'Compact/Cases/C898/References.lean',
    }.items()}
    shared = json.loads(paths['poses'].read_text())
    audit = json.loads(paths['fans'].read_text())
    stages = json.loads(paths['stages'].read_text())
    assert sha(paths['poses']) == audit['source_pose_map_sha256']
    assert sha(paths['poses']) == stages['input_sha256']['poses']
    assert sha(paths['references']) == stages['references_sha256']
    refs = [tuple(map(int, match)) for match in re.findall(
        r'⟨(-?\d+), (-?\d+), (\d+), (-?\d+), (\d+)⟩,', paths['references'].read_text())]
    assert len(refs) == 64
    stage = next(s for s in stages['stages'] if s['step'] == 4)
    sources, neighbors = stage['source_routes'], stage['neighbor_routes']
    assert len(sources) == 7 and len(neighbors) == 64 and stage['implied_pairs'] == 448
    routes, rows = stages['routes'], shared['rows']
    contexts = {c['id']: c for c in audit['contexts']}
    requests = defaultdict(set)
    source_axes, neighbor_axes = defaultdict(list), defaultdict(list)
    for role, selected, scopes in [('source', sources, source_axes),
                                    ('neighbor', neighbors, neighbor_axes)]:
        for ident in selected:
            angle = routes[ident]['angle']
            for quadrant in range(4):
                scopes[quadrant*64+angle].append(ident)
    for a in sources:
        for b in neighbors:
            for axis in range(8):
                key = axis_key(routes[a]['angle'], routes[b]['angle'], axis)
                requests[a].add(key)
                requests[b].add((key+128)%256)
    datums, values, by_key = [], {}, {}
    cone_attempts = 0
    for ident, keys in sorted(requests.items()):
        route = routes[ident]
        for key in sorted(keys):
            x, y = direction(key, refs)
            candidates = []
            for first, second in contexts[route['context']]['bases']:
                cone_attempts += 1
                weights = cramer(rows[first], rows[second], x, y)
                if weights is not None:
                    bound = Fraction(weights[3], weights[2])
                    candidates.append((bound, not weights[4], first, second, weights))
            assert candidates, (ident, key, 'missing inherited support')
            bound, _, first, second, weights = min(candidates)
            assert first in route['inputs'] and second in route['inputs']
            own_radius = radius(refs[route['angle']], x, y)
            margin = bound-own_radius
            index = len(datums)
            by_key[ident, key] = index
            values[index] = margin
            datums.append({'route': ident, 'key': key, 'direction': [x, y],
                           'basis': [first, second], 'bound': ratio(bound),
                           'radius': ratio(own_radius), 'margin': ratio(margin),
                           'strict': bool(weights[4])})
    # Check exactly the same pair/axis product before any aggregation.
    pair_axes = 0
    for a in sources:
        for b in neighbors:
            for axis in range(8):
                key = axis_key(routes[a]['angle'], routes[b]['angle'], axis)
                ai, bi = by_key[a, key], by_key[b, (key+128)%256]
                av, bv = values[ai], values[bi]
                assert av+bv <= 0 and (av+bv < 0 or datums[ai]['strict'] or datums[bi]['strict'])
                pair_axes += 1
    envelopes, envelope_ids = [], {}

    def envelope(key, members):
        fingerprint = (key, tuple(members))
        if fingerprint in envelope_ids:
            return envelope_ids[fingerprint]
        member_ids = [by_key[ident, key] for ident in members]
        maximum = max(values[i] for i in member_ids)
        attainers = [i for i in member_ids if values[i] == maximum]
        strict = all(datums[i]['strict'] for i in attainers)
        assert all(values[i] <= maximum and
                   (not strict or values[i] < maximum or datums[i]['strict']) for i in member_ids)
        index = len(envelopes)
        envelopes.append({'key': key, 'direction': list(direction(key, refs)),
                          'members': member_ids, 'maximum': ratio(maximum),
                          'attainers': attainers, 'winner': attainers[0], 'strict': strict})
        envelope_ids[fingerprint] = index
        return index

    comparisons = []
    for role, scopes in [('source_axis', source_axes), ('neighbor_axis', neighbor_axes)]:
        for key, restricted in sorted(scopes.items()):
            aa = restricted if role == 'source_axis' else sources
            bb = neighbors if role == 'source_axis' else restricted
            ae, be = envelope(key, aa), envelope((key+128)%256, bb)
            A, B = envelopes[ae], envelopes[be]
            total = Fraction(*A['maximum'])+Fraction(*B['maximum'])
            assert total <= 0 and (total < 0 or A['strict'] or B['strict'])
            comparisons.append({'role': role, 'key': key, 'source_envelope': ae,
                                'neighbor_envelope': be, 'slack': ratio(-total),
                                'represented_pairs': len(aa)*len(bb)})
    assert sum(c['represented_pairs'] for c in comparisons) == pair_axes == 3584
    assert len(source_axes) == 28 and len(neighbor_axes) == 256
    # Stronger optional shortcut: a single point in every reference square
    # for all admitted centers. A candidate is verified against every own-axis
    # bound with strict support propagated exactly. Empty clipping means only
    # that this probe found no certificate, not an exclusion theorem.
    own_supports = []
    for ident in sources+neighbors:
        for quadrant in range(4):
            own_supports.append(by_key[ident, quadrant*64+routes[ident]['angle']])
    polygon = [(Fraction(-16), Fraction(-16)), (Fraction(16), Fraction(-16)),
               (Fraction(16), Fraction(16)), (Fraction(-16), Fraction(16))]
    for index in own_supports:
        x, y = datums[index]['direction']
        polygon = clip(polygon, x, y, -values[index])
    point_probe = {'scope': 'candidate common point only; no Lean acceptance',
                   'own_axis_supports': own_supports, 'own_axis_count': len(own_supports),
                   'closed_polygon_vertices': [[ratio(x), ratio(y)] for x, y in polygon],
                   'found': False}
    if polygon:
        point = (sum(x for x, _ in polygon)/len(polygon),
                 sum(y for _, y in polygon)/len(polygon))
        slacks = [-values[i]-datums[i]['direction'][0]*point[0]-
                  datums[i]['direction'][1]*point[1] for i in own_supports]
        point_probe.update({'point': [ratio(v) for v in point],
                            'found': all(s >= 0 and (s > 0 or datums[i]['strict'])
                                         for i, s in zip(own_supports, slacks)),
                            'slacks': [ratio(s) for s in slacks]})
    report = {
        'scope': 'exact untrusted Step04 margin proposal; no new Lean proof acceptance',
        'source_routes': sources, 'neighbor_routes': neighbors,
        'pairs': 448, 'original_axis_checks': pair_axes, 'datums': datums,
        'envelopes': envelopes, 'comparisons': comparisons, 'common_point_probe': point_probe,
        'costs': {'unique_context_direction_supports': len(datums),
                  'two_row_basis_candidates_examined': cone_attempts,
                  'envelopes': len(envelopes), 'nontrivial_envelopes': sum(len(e['members']) > 1 for e in envelopes),
                  'all_member_checks': sum(len(e['members']) for e in envelopes),
                  'nontrivial_member_checks': sum(len(e['members']) for e in envelopes if len(e['members']) > 1),
                  'singleton_identity_checks': sum(len(e['members']) == 1 for e in envelopes),
                  'max_selection_comparisons': sum(len(e['members'])-1 for e in envelopes),
                  'strict_attainer_checks': sum(len(e['attainers']) for e in envelopes),
                  'envelope_pair_comparisons': len(comparisons),
                  'common_point_numeric_checks': len(own_supports)},
        'input_sha256': {name: sha(path) for name, path in paths.items()},
        'elapsed_seconds': time.monotonic()-started,
    }
    target = ROOT/'evidence/c898-step04-family-margins.json'
    encoded = json.dumps(report, separators=(',', ':'))+'\n'
    assert len(encoded.encode()) < 8*1024**2
    temporary = target.with_suffix('.json.tmp')
    try:
        temporary.write_text(encoded)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps({'costs': report['costs'], 'common_point_found': point_probe['found'],
                      'elapsed_seconds': report['elapsed_seconds']}))


if __name__ == '__main__':
    main()
