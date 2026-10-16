#!/usr/bin/env python3
"""Prepare exact whole-line exclusions for C898's direct initial cover.

Explicit --run is required; --all audits all 704 roots, otherwise owner0's64.
Optional --emit writes only per-boundary hints, never per-pair witnesses.
Original root indices and input hashes must match the existing emitter.
Every retained active intersection is checked with exact integer arithmetic.
No Lean, subprocess, network, old region tree, or geometric search is run.
Limits: 120 seconds, 256 MiB RSS, 8 MiB combined new output, atomic writes.
Run only through the parent's external serial resource guard.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import math
import os
import re
import resource
import signal
import sys
import time

sys.dont_write_bytecode = True
from audit_c898_direct_cover import point_forms
from build_c898_direct_initial import strongest_original_indices

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def encode(row, strict):
    """Exact DirectPoseForms.Form.encode row, with strictness retained."""
    row = tuple(map(Q, row))
    den = math.lcm(*(q.denominator for q in row))
    return tuple(q.numerator * (den // q.denominator) for q in row) + (strict,)


def dedup_last(rows):
    """Mathlib List.dedup retains the last occurrence, including strict bit."""
    seen, reverse = set(), []
    for row in reversed(rows):
        if row not in seen:
            seen.add(row)
            reverse.append(row)
    return list(reversed(reverse))


def direction(row):
    x, y = row[:2]
    g = math.gcd(x, y)
    assert g, 'Unexpected constant-only boundary'
    x, y = x // g, y // g
    return (x, y) if x > 0 or (x == 0 and y > 0) else (-x, -y)


def nonparallel_pairs(rows):
    sizes = Counter(direction(row) for row in rows)
    return (len(rows) ** 2 - sum(n*n for n in sizes.values())) // 2


def line_hint(boundary, base):
    """One exact parallel compulsory bound excludes an entire zero line."""
    coordinate = 0 if boundary[0] else 1
    pivot = boundary[coordinate]
    assert pivot
    for index, row in enumerate(base):
        scale = abs(pivot)
        multiple = (1 if pivot > 0 else -1) * row[coordinate]
        if scale*row[0] != multiple*boundary[0] or scale*row[1] != multiple*boundary[1]:
            continue
        if scale*row[2] < multiple*boundary[2]:
            # Reduce the witness integers; every checked identity is preserved.
            g = math.gcd(scale, multiple)
            return [index, scale // g, multiple // g]
    return None


def validate_hint(boundary, base, hint):
    if hint is None:
        return
    index, scale, multiple = hint
    assert 0 <= index < len(base) and scale > 0
    row = base[index]
    assert scale*row[0] == multiple*boundary[0]
    assert scale*row[1] == multiple*boundary[1]
    assert scale*row[2] < multiple*boundary[2]


def vertex(a, b):
    d = a[0]*b[1]-a[1]*b[0]
    if not d:
        return None
    x, y = a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2]
    if d < 0:
        x, y, d = -x, -y, -d
    return x, y, d


def evaluate(row, v):
    return row[0]*v[0]+row[1]*v[1]+row[2]*v[2]


def check_active(base, forbidden, targets, active):
    points, checked_pairs, target_tests = set(), 0, 0
    for a, b in itertools.combinations(active, 2):
        v = vertex(a, b)
        if v is None:
            continue
        checked_pairs += 1
        if any(evaluate(row, v) < 0 for row in base):
            continue
        if any(all(evaluate(row, v) > 0 for row in block) for block in forbidden):
            continue
        for target in targets:
            assert evaluate(target, v) >= 0, f'Failed retained target at {v}'
            target_tests += 1
        gcd = math.gcd(*v)
        points.add(tuple(x // gcd for x in v))
    return points, checked_pairs, target_tests


def lean_source(owner, cases):
    lines = ['import Compact.Core.PlanarBoundaryFilter\n\n',
             '/-! Exact line-exclusion hints only. Every hint still requires Lean checking. -/\n',
             'namespace N12Compact.C898BoundaryHints\n',
             'open PlanarBoundaryFilter\n\n']
    for case in cases:
        if case['owner'] != owner:
            continue
        lines.append(f'def hints{owner}_{case["angle"]} : List (Option LineExclusion) := [\n')
        for hint in case['plan']:
            lines.append('  none,\n' if hint is None else
                         f'  some ⟨{hint[0]}, {hint[1]}, {hint[2]}⟩,\n')
        lines.append(']\n\n')
    lines.append('end N12Compact.C898BoundaryHints\n')
    return ''.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--all', action='store_true')
    parser.add_argument('--owner', type=int, default=0)
    parser.add_argument('--emit', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('Prepared only; explicit --run requires the parent serial compute slot.')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic()-started > 120 or rss > 256*1024**2:
            raise RuntimeError('Boundary-filter audit exceeded 120 seconds or 256 MiB RSS')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.1, 0.1)
    temporary = []
    try:
        paths = {name: ROOT/path for name, path in {
            'geometry': 'evidence/C898/raw/data/region898.json',
            'poses': 'evidence/c898-shared-pose-map.json',
            'angles': 'vendor/S12/AngleData.lean',
        }.items()}
        audit_path = ROOT/'evidence/c898-direct-cover-all.json'
        emitter_path = ROOT/'evidence/c898-direct-initial-source.json'
        audit, emitted = (json.loads(p.read_text()) for p in (audit_path, emitter_path))
        hashes = {name: digest(path) for name, path in paths.items()}
        assert hashes == audit['input_sha256'] == emitted['input_sha256']
        assert audit['counts']['owner_angles'] == emitted['counts']['root_certificates'] == 704
        assert audit['counts']['absent_pose_angles'] == emitted['empty_angle_count'] == 74
        assert not audit['failures'] and not audit['counts']['target_failures']
        assert not audit['counts']['absent_pose_closed_nonempty']
        saved_roots = {(x['owner'], x['angle']): x for x in emitted['roots']}
        audited_roots = {(x['owner'], x['angle']): x for x in audit['cases']}
        assert len(saved_roots) == len(audited_roots) == 704
        raw = json.loads(paths['geometry'].read_text())
        owners = {o['owner']: {k: o[k] for k in ('inside', 'outside')} for o in raw}
        del raw
        selected = sorted(owners) if args.all else [args.owner]
        assert all(owner in owners for owner in selected)
        angles = {int(i): [Q(x.strip().strip('()')) for x in text.split(',')]
                  for i, text in re.findall(r'def angle64_(\d+) : AngleEnclosure := ⟨([^⟩]+)⟩',
                                            paths['angles'].read_text())}
        assert set(angles) == set(range(64))
        pose_map = json.loads(paths['poses'].read_text())
        poses = {p['name']: p for p in pose_map['poses']}
        counts, cases = Counter(), []
        for owner in selected:
            for angle in range(64):
                _, _, c, s, outer, inner, wall = angles[angle]
                original = [row for p in owners[owner]['inside']
                            for row in point_forms(c, s, Q(1001, 1000)*outer, p)]
                wall_start = len(original)
                original += [(Q(1), Q(0), -wall/2), (Q(-1), Q(0), 4-wall/2),
                             (Q(0), Q(1), -wall/2), (Q(0), Q(-1), 4-wall/2)]
                saved = saved_roots[owner, angle]
                indices = strongest_original_indices(original)
                assert indices == saved['input_indices']
                base = [encode(original[i], i < wall_start) for i in indices]
                forbidden = [[encode(row, True) for row in point_forms(c, s, inner, p)]
                             for p in owners[owner]['outside']]
                boundaries = dedup_last(base+list(itertools.chain.from_iterable(forbidden)))
                plan = [line_hint(row, base) for row in boundaries]
                for row, hint in zip(boundaries, plan):
                    validate_hint(row, base, hint)
                active = [row for row, hint in zip(boundaries, plan) if hint is None]
                target_name = saved['target_name']
                targets = [(0, 0, -1, False)] if target_name is None else [
                    tuple(pose_map['rows'][i]['integers'])+(pose_map['rows'][i]['strict'],)
                    for i in poses[target_name]['rows']]
                points, active_pairs, target_tests = check_active(base, forbidden, targets, active)
                assert active_pairs == nonparallel_pairs(active)
                assert len(points) == audited_roots[owner, angle]['feasible_vertices']
                assert target_name is not None or not points
                n, m = len(boundaries), len(active)
                item = {'owner': owner, 'angle': angle, 'target_name': target_name,
                        'original_boundaries': n, 'active_boundaries': m,
                        'discarded_boundaries': n-m, 'original_ordered_pairs': n*n,
                        'original_unordered_pairs': n*(n-1)//2,
                        'active_unordered_pairs': m*(m-1)//2,
                        'original_nonparallel_pairs': nonparallel_pairs(boundaries),
                        'active_nonparallel_pairs': active_pairs,
                        'feasible_vertices': len(points), 'target_vertex_checks': target_tests,
                        'empty_target': target_name is None, 'input_indices': indices, 'plan': plan}
                cases.append(item)
                for key in ('original_boundaries', 'active_boundaries', 'discarded_boundaries',
                            'original_ordered_pairs', 'original_unordered_pairs',
                            'active_unordered_pairs', 'original_nonparallel_pairs',
                            'active_nonparallel_pairs', 'feasible_vertices', 'target_vertex_checks'):
                    counts[key] += item[key]
                counts['roots'] += 1
                counts['empty_target_roots'] += target_name is None
        assert counts['roots'] == (704 if args.all else 64)
        if args.all:
            assert counts['empty_target_roots'] == 74
        sources = {ROOT/f'Compact/Cases/C898/BoundaryHints/Owner{o:02d}.lean': lean_source(o, cases)
                   for o in selected}
        source_bytes = sum(len(s.encode()) for s in sources.values())
        source_lines = sum(s.count('\n') for s in sources.values())
        report = {'scope': 'Exact C898 whole-line exclusion audit; concrete Lean checks still required.',
                  'counts': dict(counts), 'cases': cases, 'input_sha256': hashes,
                  'direct_audit_sha256': digest(audit_path), 'emitter_sha256': digest(emitter_path),
                  'source_script_sha256': digest(Path(__file__)),
                  'hint_lean_lines': source_lines, 'hint_lean_bytes': source_bytes,
                  'hint_modules': len(sources), 'emitted_lean': args.emit,
                  'all_roots_pass': True, 'elapsed_seconds': time.monotonic()-started,
                  'strict_boundary_policy': 'Base closed; forbidden open; line exclusions strictly negative.',
                  'ordering': 'Exact integer Form.encode rows; List.dedup keeps last occurrence including strictness.',
                  'historical_scope': 'C898 only: all74 of the312 seven-case absent target intervals retained.'}
        suffix = 'all' if args.all else f'owner{args.owner}'
        report_path = ROOT/f'evidence/c898-boundary-filter-{suffix}.json'
        text = json.dumps(report, separators=(',', ':'))+'\n'
        outputs = {report_path: text}
        if args.emit:
            outputs.update(sources)
        assert sum(len(t.encode()) for t in outputs.values()) < 8*1024**2
        guard()
        for path, text in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            temp = path.with_suffix(path.suffix+'.tmp')
            temporary.append(temp)
            temp.write_text(text)
            os.replace(temp, path)
        print(json.dumps({k: report[k] for k in ('scope', 'counts', 'hint_lean_lines',
              'hint_lean_bytes', 'emitted_lean', 'elapsed_seconds')}))
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        for temp in temporary:
            if temp.exists():
                temp.unlink()


if __name__ == '__main__':
    main()
