#!/usr/bin/env python3
"""Read-only exact arithmetic experiment; never a Lean acceptance receipt."""
from provenance_source import read_bytes, read_text, text_stream
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import hashlib
import json
import re
from itertools import combinations

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(r'^(?:noncomputable )?(?:def|theorem) ([A-Za-z0-9_]+)', re.M)
leaves = {}
certificates = []
files = []
for number in range(66):
    path = ROOT / f'vendor/S12/Push898Chunk{number}.lean'
    raw = read_bytes(path)
    files.append({'path': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(raw).hexdigest()})
    text = raw.decode()
    matches = list(DECL.finditer(text))
    for j, match in enumerate(matches):
        end = matches[j + 1].start() if j + 1 < len(matches) else len(text)
        name = match.group(1)
        declaration = text[match.start():end]
        if re.search(r' : PoseLeaf :=', declaration[:200]):
            rows = re.search(r'regionConstraintsFromText "([^"\n]*)"', declaration)
            if rows:
                leaves[name] = rows.group(1)
        if re.fullmatch(r'continuousScout898Step14Pose\d+Overlap\d+', name):
            certificates.append((name, declaration))

angles = {}
angle_path = ROOT / 'vendor/S12/AngleData.lean'
for line in angle_path.read_text().splitlines():
    match = re.match(r'def angle64_(\d+) : AngleEnclosure := ⟨(.*)⟩$', line)
    if match:
        values = [F(x.replace('(', '').replace(')', '')) for x in match[2].split(',')]
        angles[int(match[1])] = (values[2], values[3], values[5])

def parse_rows(text):
    return [tuple([F(t) for t in row.split(',')[:3]] + [row.split(',')[3] == '1'])
            for row in text.split(';')] if text else []

def radius(angle, x, y):
    c, s, side = angle
    return side / 2 * (abs(x*c + y*s) + abs(-x*s + y*c))

def solve_two(rows, direction):
    (x1, y1, _, _), (x2, y2, _, _) = rows
    x, y = direction
    determinant = x1*y2 - y1*x2
    if not determinant:
        return None
    return [(x*y2-y*x2)/determinant, (x1*y-y1*x)/determinant]

def best_two(rows, active, direction):
    options = []
    for indices in combinations(active, 2):
        selected = [rows[i] for i in indices]
        weights = solve_two(selected, direction)
        if weights is not None and all(w >= 0 for w in weights):
            options.append((sum(w*r[2] for w,r in zip(weights,selected)), indices, weights))
    if not options:
        return None
    return min(options, key=lambda x:x[0])

summary = Counter()
patterns = Counter()
failures = []
encoded = []
old_bytes = 0
for name, declaration in certificates:
    a, b = [angles[int(n)] for n in re.findall(r'let [ab] : .*?angle64_(\d+)\.reference', declaration)]
    source = re.search(r'let ia := \w+BlockRows\+\+(\w+)\.inputs', declaration)[1]
    neighbor = re.search(r'let ib := (\w+)\.inputs', declaration)[1]
    # Every terminal Step14 block is [] in the original source.
    source_rows, neighbor_rows = parse_rows(leaves[source]), parse_rows(leaves[neighbor])
    rows = [(x, y, F(0), F(0), z, strict) for x,y,z,strict in source_rows]
    rows += [(F(0), F(0), x, y, z, strict) for x,y,z,strict in neighbor_rows]
    proof_text = re.search(r'\(axisOverlapForms a.val b.val\) "([^"\n]*)"', declaration)[1]
    old_bytes += len(proof_text)
    proofs = proof_text.split(';')
    axes = [(a[0],a[1]),(-a[1],a[0]),(b[0],b[1]),(-b[1],b[0])]
    axes = [v for x,y in axes for v in [(x,y),(-x,-y)]]
    assert len(proofs) == len(axes) == 8
    for number, (proof, (nx,ny)) in enumerate(zip(proofs, axes)):
        weights = [(F(term.split(':')[0]),int(term.split(':')[1])) for term in proof.split(',')]
        target_constant = radius(a,nx,ny)+radius(b,nx,ny)
        opposite = (-nx,-ny,nx,ny,-target_constant,False)
        allrows = [opposite] + rows
        combination = [sum(w*allrows[i][k] for w,i in weights) for k in range(5)]
        assert all(v == 0 for v in combination)
        assert all(w >= 0 and i < len(allrows) for w,i in weights)
        assert any(w > 0 and allrows[i][5] for w,i in weights)
        summary['original_exact_checks_passed'] += 1
        active_a = sorted({i-1 for w,i in weights if w and 0 < i <= len(source_rows)
                           and (source_rows[i-1][0] or source_rows[i-1][1])})
        active_b = sorted({i-1-len(source_rows) for w,i in weights if w and i > len(source_rows)
                           and (neighbor_rows[i-1-len(source_rows)][0] or neighbor_rows[i-1-len(source_rows)][1])})
        patterns[f'{len(active_a)}+{len(active_b)}'] += 1
        best_a = best_two(source_rows, active_a, (nx,ny))
        best_b = best_two(neighbor_rows, active_b, (-nx,-ny))
        if best_a is None or best_b is None:
            failures.append([name,number,'no independent nonnegative support pair']);continue
        _, active_a, wa = best_a
        _, active_b, wb = best_b
        selected_a = [source_rows[i] for i in active_a]
        selected_b = [neighbor_rows[i] for i in active_b]
        constant = -target_constant + sum(w*r[2] for w,r in zip(wa,selected_a)) + sum(w*r[2] for w,r in zip(wb,selected_b))
        strict = constant < 0 or any(w > 0 and r[3] for w,r in zip(wa+wb,selected_a+selected_b))
        if any(w < 0 for w in wa+wb) or constant > 0 or not strict:
            failures.append([name,number,'sign or strictness']);continue
        summary['reconstructed_from_four_indices'] += 1
        encoded.append([name,number,*active_a,*active_b])

result = {
    'scope': 'All424 terminal Step14 overlap certificates,3392 axis implications. Exact Python rational audit only; no Lean compilation or theorem acceptance.',
    'source_files': files,
    'angle_source_sha256': hashlib.sha256(angle_path.read_bytes()).hexdigest(),
    'counts': dict(summary), 'support_patterns': dict(patterns), 'failures': failures,
    'old_weight_text_bytes': old_bytes,
    'four_indices_u16_payload_bytes': 8*summary['reconstructed_from_four_indices'],
    'method': 'Retain two source-row indices and two neighbor-row indices. Among original positive support rows, select a nonnegative independent pair with smallest weighted constant. Compute weights by two2x2 Cramer solves for axis direction and its negative. Compute constant slack against exact overlap radius. Require strictness, nonnegative slack, and actual input membership. An eventual Lean checker must verify these conditions; Python result is evidence of compressibility only.'
}
(ROOT/'audit/c898-support-reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'evidence/c898-step14-four-index-witnesses.json').write_text(json.dumps(encoded,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['source_files','failures']},indent=2))
print('failed implications:',len(failures))
