#!/usr/bin/env python3
"""Exact boundary-intersection pilot for replacing C898 initial forests.

Only audits the closed compulsory-point relaxation against original reduced
poses. No theorem is asserted, no sources generated, no Lean process started.
The arrangement-vertex soundness theorem is a separate required obligation.
Default owner0, all64 angles; --all selects all11 owners. Resource caps are
120seconds/256MiB RSS, output8MiB. Explicit --run required.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import math
import re
import resource
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def point_forms(c, s, side, point):
    x, y = map(Q, point)
    return [(-c, -s, side/2+c*x+s*y),
            (c, s, side/2-c*x-s*y),
            (s, -c, side/2-s*x+c*y),
            (-s, c, side/2+s*x-c*y)]


def primitive_normal(row):
    x, y, constant = row
    den = math.lcm(x.denominator, y.denominator)
    ix, iy = int(x * den), int(y * den)
    gcd = math.gcd(ix, iy)
    if not gcd:
        return (0, 0, constant)
    return ix//gcd, iy//gcd, constant * den / gcd


def strongest_parallel(rows):
    by_normal = {}
    for row in rows:
        x, y, constant = primitive_normal(row)
        key = (x, y)
        if key not in by_normal or constant < by_normal[key]:
            by_normal[key] = constant
    return [(x, y, constant) for (x, y), constant in by_normal.items()]


def evaluate(row, point):
    return row[0] * point[0] + row[1] * point[1] + row[2]


def intersection(a, b):
    det = a[0]*b[1]-a[1]*b[0]
    if not det:
        return None
    return ((a[1]*b[2]-a[2]*b[1])/det, (a[2]*b[0]-a[0]*b[2])/det)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--all', action='store_true')
    parser.add_argument('--owner', type=int, default=0)
    args = parser.parse_args()
    if not args.run:
        parser.error('Prepared only; explicit --run required in a scheduled compute slot.')
    started = time.monotonic()
    stats, cases, failures = Counter(), [], []

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic() - started > 120 or rss > 256*1024**2:
            raise RuntimeError('120-second/256-MiB pilot cap reached')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .1, .1)
    paths = {k: ROOT / v for k, v in {
        'geometry': 'evidence/C898/raw/data/region898.json',
        'poses': 'evidence/c898-shared-pose-map.json',
        'angles': 'vendor/S12/AngleData.lean',
    }.items()}
    raw_owners = json.loads(paths['geometry'].read_text())
    owners = [{k: owner[k] for k in ['owner', 'inside', 'outside']} for owner in raw_owners]
    del raw_owners
    if not args.all:
        owners = [owner for owner in owners if owner['owner'] == args.owner]
    assert owners
    angles = {int(i): [Q(t.strip().strip('()')) for t in values.split(',')]
              for i, values in re.findall(r'def angle64_(\d+) : AngleEnclosure := ⟨([^⟩]+)⟩',
                                          paths['angles'].read_text())}
    assert len(angles) == 64
    pose_map = json.loads(paths['poses'].read_text())
    reduced = {}
    for pose in pose_map['poses']:
        match = re.fullmatch(r'continuousScout898Initial(\d+)_(\d+)', pose['name'])
        if match:
            key = int(match[1]), pose['angle']
            assert key not in reduced
            reduced[key] = pose
    for owner in owners:
        owner_id = owner['owner']
        for angle_id in range(64):
            _, _, c, s, outer, inner, wall = angles[angle_id]
            inside = [row for point in owner['inside']
                      for row in point_forms(c, s, Q(1001,1000)*outer, point)]
            base = strongest_parallel(inside + [(Q(1),Q(0),-wall/2),
                (Q(-1),Q(0),4-wall/2), (Q(0),Q(1),-wall/2), (Q(0),Q(-1),4-wall/2)])
            forbidden = [[primitive_normal(row) for row in point_forms(c, s, inner, point)]
                         for point in owner['outside']]
            lines = sorted(set(base + list(itertools.chain.from_iterable(forbidden))))
            points = set()
            pair_count = 0
            for first, second in itertools.combinations(lines, 2):
                p = intersection(first, second)
                if p is None:
                    continue
                pair_count += 1
                if all(evaluate(row,p) >= 0 for row in base) and all(
                        any(evaluate(row,p) <= 0 for row in block) for block in forbidden):
                    points.add(p)
            pose = reduced.get((owner_id, angle_id))
            targets = [] if pose is None else list({tuple(pose_map['rows'][i]['integers'])
                                                    for i in pose['rows']})
            if pose is not None:
                assert all(not pose_map['rows'][i]['strict'] or
                           pose_map['rows'][i]['integers'] == [0,0,1] for i in pose['rows'])
            bad = [(p, target, evaluate(target,p)) for p in points for target in targets
                   if evaluate(target,p) < 0]
            strict_points = sum(all(evaluate(row,p)>0 for row in inside) for p in points)
            missing_nonempty = pose is None and bool(points)
            case = {'owner':owner_id, 'angle':angle_id, 'inside_points':len(owner['inside']),
                    'forbidden_rectangles':len(forbidden), 'base_planes':len(base),
                    'boundary_planes':len(lines), 'nonparallel_pairs':pair_count,
                    'feasible_vertices':len(points), 'strict_input_feasible_vertices':strict_points,
                    'target_pose':None if pose is None else pose['name'],
                    'unique_target_rows':len(targets), 'target_failures':len(bad),
                    'closed_empty':not points, 'missing_pose_closed_nonempty':missing_nonempty}
            cases.append(case)
            stats['owner_angles'] += 1
            stats['boundary_planes'] += len(lines)
            stats['nonparallel_pairs'] += pair_count
            stats['feasible_vertices'] += len(points)
            stats['target_vertex_checks'] += len(points)*len(targets)
            stats['target_failures'] += len(bad)
            stats['absent_pose_angles'] += pose is None
            stats['closed_empty_angles'] += not points
            stats['absent_pose_closed_nonempty'] += missing_nonempty
            if bad or missing_nonempty:
                failures.append({'owner':owner_id,'angle':angle_id,
                                 'target_examples':[[list(map(str,p)),list(target),str(value)]
                                                    for p,target,value in bad[:4]],
                                 'empty_root_examples':[list(map(str,p)) for p in sorted(points)[:4]]
                                 if missing_nonempty else []})
    signal.setitimer(signal.ITIMER_REAL,0)
    report = {'scope':'Exact finite audit of all boundary intersections for listed owner-angles; generic vertex soundness not yet accepted.',
              'counts':dict(stats), 'cases':cases, 'failures':failures,
              'input_sha256':{name:digest(path) for name,path in paths.items()},
              'elapsed_seconds':time.monotonic()-started,
              'strict_boundary_policy':'Forbidden rectangles are OPEN (all>0); their boundaries remain feasible. Compulsory inputs are CLOSED only for this proposed stronger coverage check. Strict-filtered vertex counts cannot prove emptiness.'}
    output = ROOT/'evidence'/('c898-direct-cover-all.json' if args.all else f'c898-direct-cover-owner{args.owner}.json')
    with output.open('w') as f:
        json.dump(report,f,separators=(',',':'))
        f.write('\n')
    assert output.stat().st_size < 8*1024**2
    print(json.dumps({'counts':dict(stats),'failed_owner_angles':len(failures),
                      'elapsed_seconds':report['elapsed_seconds'],'output':str(output.relative_to(ROOT))}))


if __name__ == '__main__':
    main()
