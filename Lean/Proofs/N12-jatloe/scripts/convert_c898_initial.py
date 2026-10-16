#!/usr/bin/env python3
"""Convert all authenticated C898 initial trees to direct integer region DAGs.

This is a deterministic encoder, not a solver or a trusted proof step. Lean
checks every cut, complement, sparse sum, context use, and geometric binding.
CPU/wall time are bounded; output is a readable row/context/node table.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import math
import re
import resource
import signal
import time

signal.alarm(60)
resource.setrlimit(resource.RLIMIT_CPU, (55, 55))
ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'evidence/C898/raw/data/region898.json'
OUT = ROOT/'Compact/Cases/C898/Initial'
OUT.mkdir(parents=True, exist_ok=True)
started = time.monotonic()


def canonical(raw):
    coeff, strict = raw
    return tuple(Q(x) for x in coeff) + (bool(strict),)


def negate(row):
    return tuple(-x for x in row[:3]) + (not row[3],)


def point_forms(c, s, side, point):
    x, y = map(Q, point)
    return [(-c, -s, side/2+c*x+s*y, True),
            (c, s, side/2-c*x-s*y, True),
            (s, -c, side/2-s*x+c*y, True),
            (-s, c, side/2+s*x-c*y, True)]


def rational(q):
    q = Q(q)
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'


def points(ps):
    return '['+', '.join(f'({rational(x)}, {rational(y)})' for x, y in ps)+']'


def list_nat(xs):
    return '['+', '.join(map(str, xs))+']'


def output(path, text):
    path.write_text(text)
    return {'file': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size,
            'lines': text.count('\n')}


angle_text = (ROOT/'vendor/S12/AngleData.lean').read_text()
angles = {}
for index, fields in re.findall(r'def angle64_(\d+) : AngleEnclosure := ⟨([^⟩]+)⟩', angle_text):
    angles[int(index)] = [Q(x.strip().strip('()')) for x in fields.split(',')]
assert len(angles) == 64
owners = json.loads(SOURCE.read_text())
assert len(owners) == 11
files = []
stats = Counter()
root_stats = []

header = 'import Compact.Bridge.RegionOwner\nimport Compact.Cases.C898.Initial.Angles\n\n'
header += 'namespace N12Compact.C898Initial\nopen S12 IntegerSupport SparseInteger RegionDAG RegionOwner\n\n'
input_text = header
for owner in owners:
    i = owner['owner']
    input_text += f'def inside{i} : List (ℚ × ℚ) := {points(owner["inside"])}\n'
    input_text += f'def outside{i} : List (ℚ × ℚ) := {points(owner["outside"])}\n'
input_text += '\nend N12Compact.C898Initial\n'
files.append(output(OUT/'Inputs.lean', input_text))

angle_names = ', '.join(f'angle64_{i}' for i in range(64))
files.append(output(OUT/'Angles.lean', 'import S12.AngleData64\n\nnamespace N12Compact.C898Initial\nopen S12\n\n'
    '/-- Ordinary kernel proof of complete closed-interval coverage. -/\n'
    'theorem angles64_cover_kernel : CoversInterval 0 1 (angles64.map Subtype.val) := by\n'
    '  norm_num [angles64, CoversInterval, '+angle_names+']\n\n'
    '#print axioms angles64_cover_kernel\nend N12Compact.C898Initial\n'))


def geometry_rows(owner, angular_index):
    lo, hi, c, s, outer, inner, wall = angles[angular_index]
    initial = [row for p in owner['inside'] for row in point_forms(c, s, Q(1001, 1000)*outer, p)]
    initial += [(Q(1), Q(0), -wall/2, False), (Q(-1), Q(0), 4-wall/2, False),
                (Q(0), Q(1), -wall/2, False), (Q(0), Q(-1), 4-wall/2, False),
                (Q(0), Q(0), Q(1), True)]
    forbidden = [point_forms(c, s, inner, p) for p in owner['outside']]
    return initial, forbidden


def encode(owner, angular_index, tree, pool):
    owner_index = owner['owner']
    lo, hi, *_ = angles[angular_index]
    initial, forbidden = geometry_rows(owner, angular_index)
    row_ids, rows, raw_rows = pool
    original_size = len(rows)

    def intern(row):
        if row not in row_ids:
            row_ids[row] = len(rows)
            rows.append(row)
            den = math.lcm(*(x.denominator for x in row[:3]))
            raw_rows.append(tuple(int(x*den) for x in row[:3]) + (row[3], den))
        return row_ids[row]

    initial_ids = [intern(row) for row in initial]
    forbidden_ids = [[intern(row) for row in block] for block in forbidden]
    contexts = [(0, 0, 0)]
    context_rows = [()]

    def push(parent, row):
        index = len(contexts)
        contexts.append((parent, row, contexts[parent][2]+1))
        context_rows.append((row,)+context_rows[parent])
        return index

    initial_context = 0
    for row in reversed(initial_ids):
        initial_context = push(initial_context, row)
    assert context_rows[initial_context] == tuple(initial_ids)
    nodes, leaves, leaf_original_indices = [], [], []
    counts = Counter()

    def visit(tree, context):
        kind = tree['kind']
        counts[kind] += 1
        incoming = set(context_rows[context])
        if kind == 'cut':
            test = canonical(tree['test'])
            test_id, opposite_id = intern(test), intern(negate(test))
            yes = visit(tree['yes'], push(context, test_id))
            no = visit(tree['no'], push(context, opposite_id))
            result = f'.cut {test_id} {opposite_id} {yes} {no}'
        elif kind == 'forbidden':
            block = [canonical(row) for row in tree['block']]
            b = forbidden.index(block)
            assert set(forbidden_ids[b]) <= incoming
            counts['discarded_tautological_implications'] += len(tree['proofs'])
            result = f'.forbidden {b}'
        elif kind == 'leaf':
            old_index = tree['index']
            saved = owner['leaves'][old_index]
            assert saved['angle'] == angular_index
            saved_rows = tuple(intern(canonical(row)) for row in saved['inputs'])
            assert saved_rows == context_rows[context], (owner_index, angular_index, old_index)
            result = f'.leaf {len(leaves)}'
            leaves.append(context)
            leaf_original_indices.append(old_index)
        elif kind == 'empty':
            indices, fractional_weights = [], []
            for row, weight in tree['terms']:
                index = intern(canonical(row))
                assert index in incoming
                indices.append(index)
                fractional_weights.append(Q(weight)/raw_rows[index][4])
            common = math.lcm(*(w.denominator for w in fractional_weights))
            weights = [int(w*common) for w in fractional_weights]
            gcd = math.gcd(*weights)
            weights = [w//gcd for w in weights]
            assert all(w >= 0 for w in weights)
            assert any(w > 0 and raw_rows[i][3] for w, i in zip(weights, indices))
            assert all(sum(w*raw_rows[i][j] for w, i in zip(weights, indices)) == 0
                       for j in range(3))
            terms = ', '.join(f'({w}, {i})' for w, i in zip(weights, indices))
            result = f'.empty ⟨[{terms}], 1⟩'
            counts['weighted_terms'] += len(weights)
        else:
            raise AssertionError(kind)
        index = len(nodes)
        nodes.append(f'  ⟨{context}, {result}⟩')
        return index

    root_node = visit(tree, initial_context)
    prefix = f'r{owner_index}_{angular_index}'
    size = len(rows)
    assert size == original_size, 'shared dictionary prepass omitted a required row'
    lines = [f'/- Owner {owner_index}, half-angle interval [{lo}, {hi}]. -/',
             f'def {prefix}_contexts : Array (Context {size}) := #[']
    lines += ['  ⟨'+f'{parent}, {row}, {depth}'+'⟩'+(',' if i+1 < len(contexts) else '')
              for i, (parent, row, depth) in enumerate(contexts)]
    lines += [']', f'def {prefix}_nodes : Array (Node {size}) := #[', ',\n'.join(nodes), ']']
    lines += [f'def {prefix}_leafContexts : Array Nat := #{list_nat(leaves)}',
              f'def {prefix}_forbidden : Array (List (Fin {size})) := #[',
              ',\n'.join('  '+list_nat(block) for block in forbidden_ids), ']']
    lines += [f'def {prefix}_program : Program {size} where',
              f'  rows := shared{angular_index}_rows',
              f'  denominators := shared{angular_index}_denominators',
              f'  contexts i := ({prefix}_contexts[i]?).getD ⟨0, 0, 0⟩',
              f'  nodes i := ({prefix}_nodes[i]?).getD ⟨0, .leaf 0⟩',
              f'  nodeCount := {len(nodes)}',
              f'  leaves i := contextRows (fun j => ({prefix}_contexts[j]?).getD ⟨0, 0, 0⟩)',
              f'    (({prefix}_leafContexts[i]?).getD 0)',
              f'  leafCount := {len(leaves)}',
              f'  forbidden i := ({prefix}_forbidden[i]?).getD []',
              f'  forbiddenCount := {len(forbidden)}',
              f'def {prefix} : Root := ⟨{size}, {prefix}_program, {root_node},',
              f'  ⟨angle64_{angular_index}, angle64_{angular_index}_checked⟩⟩',
              f'theorem {prefix}_checked : {prefix}.Check inside{owner_index} outside{owner_index} := by',
              f'  refine ⟨?_, shared{angular_index}_positive, ?_, ?_, ?_⟩',
              '  all_goals decide +kernel', '']
    stats.update(counts)
    stats['contexts'] += len(contexts)
    stats['nodes'] += len(nodes)
    stats['roots'] += 1
    root_stats.append({'owner': owner_index, 'angle': angular_index, 'rows': size,
        'contexts': len(contexts), 'nodes': len(nodes), 'leaves': len(leaves),
        'max_context_depth': max(c[2] for c in contexts),
        'original_leaf_indices': leaf_original_indices})
    return '\n'.join(lines)


for owner in owners:
    i = owner['owner']
    assert owner['N'] == 64 and len(owner['roots']) == 64
    for part in range(4):
        text = 'import Compact.Cases.C898.Initial.Inputs\n\n'
        text += f'import Compact.Cases.C898.Initial.Shared{part}\n\n'
        text += 'namespace N12Compact.C898Initial\n'
        text += 'open S12 IntegerSupport SparseInteger RegionDAG RegionOwner\n'
        text += 'set_option maxRecDepth 4096\n\n'
        (OUT/f'Owner{i:02d}Part{part}.lean').write_text(text)

for part in range(4):
    (OUT/f'Shared{part}.lean').write_text('import Compact.Core.SparseInteger\n\n'
        'namespace N12Compact.C898Initial\nopen IntegerSupport\n\n')

for angular_index in range(64):
    row_ids, rows, raw_rows = {}, [], []

    def gather(row):
        if row not in row_ids:
            row_ids[row] = len(rows)
            rows.append(row)
            den = math.lcm(*(x.denominator for x in row[:3]))
            raw_rows.append(tuple(int(x*den) for x in row[:3])+(row[3], den))

    def gather_tree(tree):
        if tree['kind'] == 'cut':
            row = canonical(tree['test'])
            gather(row)
            gather(negate(row))
            gather_tree(tree['yes'])
            gather_tree(tree['no'])
        elif tree['kind'] == 'empty':
            for row, _ in tree['terms']:
                gather(canonical(row))
        elif tree['kind'] == 'forbidden':
            for row in tree['block']:
                gather(canonical(row))

    for owner in owners:
        initial, forbidden = geometry_rows(owner, angular_index)
        for row in initial:
            gather(row)
        for block in forbidden:
            for row in block:
                gather(row)
        gather_tree(owner['roots'][angular_index])
    size = len(rows)
    shared = [f'/- Angle {angular_index}: numerical rows shared across all 11 owners. -/',
              f'def shared{angular_index}_data : Array (Row × Nat) := #[']
    shared += ['  ⟨⟨'+f'{x}, {y}, {z}, {str(strict).lower()}'+'⟩, '+str(den)+'⟩'+
              (',' if i+1 < size else '') for i, (x, y, z, strict, den) in enumerate(raw_rows)]
    shared += [']', f'def shared{angular_index}_rows (i : Fin {size}) : Row :=',
               f'  ((shared{angular_index}_data[i.val]?).getD (⟨0, 0, 0, false⟩, 1)).1',
               f'def shared{angular_index}_denominators (i : Fin {size}) : Nat :=',
               f'  ((shared{angular_index}_data[i.val]?).getD (⟨0, 0, 0, false⟩, 1)).2',
               f'theorem shared{angular_index}_positive : ∀ i, 0 < shared{angular_index}_denominators i := by',
               '  decide +kernel', '']
    with (OUT/f'Shared{angular_index//16}.lean').open('a') as stream:
        stream.write('\n'.join(shared)+'\n')
    stats['rows'] += size
    for owner in owners:
        text = encode(owner, angular_index, owner['roots'][angular_index], (row_ids, rows, raw_rows))
        with (OUT/f'Owner{owner["owner"]:02d}Part{angular_index//16}.lean').open('a') as stream:
            stream.write(text+'\n')

for path in sorted(OUT.glob('*Part*.lean'))+sorted(OUT.glob('Shared*.lean')):
    with path.open('a') as stream:
        stream.write('\nend N12Compact.C898Initial\n')
    text = path.read_text()
    files.append({'file': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size,
                  'lines': text.count('\n')})

for owner in owners:
    i = owner['owner']
    assembly = ''.join(f'import Compact.Cases.C898.Initial.Owner{i:02d}Part{part}\n' for part in range(4))
    assembly += '\nnamespace N12Compact.C898Initial\nopen S12 RegionOwner\n\n'
    assembly += f'def owner{i} : Owner := ⟨inside{i}, outside{i}, [\n'
    assembly += ',\n'.join(f'  ⟨r{i}_{j}, r{i}_{j}_checked⟩' for j in range(64))+'\n]⟩\n\n'
    assembly += f'theorem owner{i}_checked : owner{i}.Check := by\n'
    assembly += '  change CoversInterval 0 1 (angles64.map Subtype.val)\n'
    assembly += '  exact angles64_cover_kernel\n\n'
    assembly += f'theorem owner{i}_oriented_cover (q : OpenSquare)\n'
    assembly += '    (ha : 1 < q.side) (hs : q.side ≤ 1001 / 1000) (hb : InsideContainer q)\n'
    assembly += f'    (hi : ∀ P ∈ inside{i}, q.Inside P.1 P.2)\n'
    assembly += f'    (ho : ∀ P ∈ outside{i}, ¬q.Inside P.1 P.2) :\n'
    assembly += f'    OrientedPoseCovered owner{i}.leaves q :=\n'
    assembly += f'  owner{i}.oriented_sound owner{i}_checked q ha hs hb hi ho\n\n'
    assembly += f'#print axioms owner{i}_oriented_cover\nend N12Compact.C898Initial\n'
    files.append(output(OUT/f'Owner{i:02d}.lean', assembly))
files.append(output(OUT/'All.lean', ''.join(f'import Compact.Cases.C898.Initial.Owner{o["owner"]:02d}\n' for o in owners)))
for owner in owners:
    indices = [index for item in root_stats if item['owner'] == owner['owner']
               for index in item['original_leaf_indices']]
    assert indices == list(range(len(owner['leaves']))), 'Original owner leaf order changed'
assert stats['roots'] == 704 and stats['cut'] == 14088 and stats['empty'] == 10149
assert stats['forbidden'] == 3522 and stats['leaf'] == 1121
assert stats['discarded_tautological_implications'] == 14088
report = {'source': str(SOURCE.relative_to(ROOT)),
          'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
          'scope': 'All 704 C898 initial roots and all 11 original-model owner covers; later propagation separate',
          'validation': 'Exact encoder invariants checked; generated Lean awaits root-worker replay',
          'counts': dict(stats), 'files': files, 'roots': root_stats,
          'total_lean_bytes': sum(f['bytes'] for f in files),
          'total_lean_lines': sum(f['lines'] for f in files),
          'modules': len(files), 'runtime_seconds': time.monotonic()-started,
          'max_rss_bytes_macos': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(ROOT/'evidence/c898-initial-conversion.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: report[k] for k in ['counts', 'total_lean_bytes', 'total_lean_lines', 'modules',
                                      'runtime_seconds', 'max_rss_bytes_macos']}))
