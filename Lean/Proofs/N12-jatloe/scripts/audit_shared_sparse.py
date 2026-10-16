#!/usr/bin/env python3
"""Bounded exact provenance check for the sparse-integer Lean pilots.

No solver, compilation, source generation, network, or child process. The
output distinguishes exact rational identities from Lean replay validation.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import math
import re
import resource
import signal
import time

signal.alarm(15)
resource.setrlimit(resource.RLIMIT_CPU, (15, 15))
ROOT = Path(__file__).resolve().parents[1]
OLD = Path(__import__('os').environ.get('N12_LEGACY_PROJECT', str(ROOT.parent / 'n12-jatloe419'))) / 'Completion/Cases/C696/RootOneStep000Data.lean'
started = time.monotonic()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def integer_relation(rows, target, indices):
    a, b = (rows[i] for i in indices[:2])
    determinant = a[0]*b[1] - a[1]*b[0]
    weights = [Q(target[0]*b[1] - b[0]*target[1], determinant),
               Q(a[0]*target[1] - target[0]*a[1], determinant)]
    slack = target[2] - weights[0]*a[2] - weights[1]*b[2]
    if len(indices) == 3:
        assert rows[indices[2]][:3] == (0, 0, 1)
        weights.append(slack)
    else:
        assert slack == 0
    assert all(w >= 0 for w in weights)
    scale = math.lcm(*(w.denominator for w in weights))
    weights = [int(w*scale) for w in weights]
    assert all(sum(w*rows[i][j] for w, i in zip(weights, indices)) ==
               scale*target[j] for j in range(3))
    return {'terms': list(zip(weights, indices)), 'scale': scale}


text = OLD.read_text()
rows = [(int(x), int(y), int(c), int(d), s == 'true') for x, y, c, d, s in
        re.findall(r'⟨(-?\d+),(-?\d+),(-?\d+),(\d+),(true|false)⟩',
                   text.split('def rawRows')[1].split('\n]', 1)[0])]
poses = [(int(angle), [int(i) for i in indices.split(',')]) for angle, indices in
         re.findall(r'⟨(\d+),\[([^]]*)\]⟩',
                    text.split('def rawPoses')[1].split('\n]', 1)[0])]
assert poses[0] == (0, [0, 1, 2, 3, 4, 5, 6, 6, 7, 1, 3, 8])
assert poses[117] == (0, [0, 1, 2, 3, 4, 802, 803, 804, 805, 6, 6, 7, 1, 3, 8])
relations = {str(i): integer_relation(rows, rows[i], sources) for i, sources in
             [(802, [4, 5]), (803, [4, 5, 8]), (804, [4, 5, 8]), (805, [5, 6])]}
selected = list(range(9)) + list(range(802, 806))
fixture = (ROOT/'Compact/Core/C696Pose117.lean').read_text()
literal = [(int(x), int(y), int(c), s == 'true') for x, y, c, s in re.findall(
    r'⟨(-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(true|false)⟩', fixture)]
assert literal == [(rows[i][0], rows[i][1], rows[i][2], rows[i][4]) for i in selected]
den_literal = [int(i) for i in re.findall(r'\d+', fixture.split('def denominators')[1]
               .split('![', 1)[1].split(']', 1)[0])]
assert den_literal == [rows[i][3] for i in selected]
for original_id, relation in relations.items():
    match = re.search(r'def certificate'+original_id+
                      r'.*?⟨\[(.*?)\],\s*(\d+)⟩', fixture, re.S)
    assert match
    terms = [(int(w), int(i)) for w, i in re.findall(r'\((\d+),\s*(\d+)\)', match[1])]
    assert terms == relation['terms'] and int(match[2]) == relation['scale']

c898 = ROOT/'evidence/C898/raw/data/region898.json'
owners = json.loads(c898.read_text())
owner = next(o for o in owners if o['owner'] == 0)
node = owner['roots'][0]
for branch in 'YYYNYYN':
    node = node['yes' if branch == 'Y' else 'no']
assert node['kind'] == 'empty' and len(node['terms']) == 4
assert [sum((Q(row[0][j])*Q(w) for row, w in node['terms']), Q(0))
        for j in range(3)] == [0, 0, 0]
leaf_rows, cleared = [], []
for row, weight in node['terms']:
    coeff = [Q(x) for x in row[0]]
    den = math.lcm(*(x.denominator for x in coeff))
    leaf_rows.append([*[int(x*den) for x in coeff], den, row[1]])
    cleared.append(Q(weight)/den)
common = math.lcm(*(x.denominator for x in cleared))
leaf_weights = [int(x*common) for x in cleared]
assert all(w >= 0 for w in leaf_weights)
assert any(w > 0 and row[4] for w, row in zip(leaf_weights, leaf_rows))
assert all(sum(w*row[j] for w, row in zip(leaf_weights, leaf_rows)) == 0
           for j in range(3))
leaf_fixture = (ROOT/'Compact/Core/C898EmptyLeaf.lean').read_text()
leaf_literal = [(int(x), int(y), int(c), s == 'true') for x, y, c, s in re.findall(
    r'⟨(-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(true|false)⟩',
    leaf_fixture.split('def denominators')[0])]
assert leaf_literal == [(r[0], r[1], r[2], r[4]) for r in leaf_rows]
leaf_den_literal = [int(i) for i in re.findall(r'\d+',
    leaf_fixture.split('def denominators')[1].split('![', 1)[1].split(']', 1)[0])]
assert leaf_den_literal == [r[3] for r in leaf_rows]
leaf_terms_literal = [(int(w), int(i)) for w, i in re.findall(r'\((\d+),\s*(\d+)\)',
    leaf_fixture.split('def certificate')[1].split('theorem checked')[0])]
assert leaf_terms_literal == list(zip(leaf_weights, range(4)))

report = {
    'scope': 'One complete C696 pose-row implication and one complete C898 empty leaf',
    'validation': 'Exact Python integer/rational identities; Lean replay is separate',
    'c696': {
        'source': str(OLD), 'sha256': sha(OLD), 'source_pose': 0, 'target_pose': 117,
        'angle_unchanged': 0, 'source_row_occurrences': poses[0][1],
        'target_row_occurrences': poses[117][1],
        'distinct_source_rows': 9, 'new_target_rows': 4,
        'shared_row_dictionary_entries': 13,
        'old_support_records': 15, 'new_numerical_checks': 4,
        'eliminated_alias_checks': 11,
        'check_count_reduction_fraction': '11/15',
        'old_support_term_occurrences': 21, 'new_weighted_term_occurrences': 10,
        'relations': relations,
        'important_limit': 'The old rawRows already shared these 13 literal rows. '
          'Measured improvement is elimination of 11 redundant support checks and '
          'rational Cramer reconstruction, not a claim of a smaller original row table.'},
    'c898': {'source': str(c898.relative_to(ROOT)), 'sha256': sha(c898),
        'owner': 0, 'angular_root': 0, 'branch_path': 'YYYNYYN',
        'rows': leaf_rows, 'weights': leaf_weights,
        'integer_sum': [0, 0, 0], 'strict_positive_source': True,
        'important_limit': 'Only the identified empty leaf is migrated. Its initial '
          'ancestry and 15 later propagation rounds are not established by this pilot.'},
    'runtime_seconds': time.monotonic() - started,
    'max_rss_bytes_macos': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
}
(ROOT/'evidence/shared-sparse-pilots.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: report[k] for k in ['scope', 'runtime_seconds', 'max_rss_bytes_macos']}))
