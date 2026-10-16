#!/usr/bin/env python3
"""Prepare the complete step14 shared-support-fan pilot, never run Lean.

All candidate bases come from authenticated existing four-index witnesses.
Select the strongest exact rational directional support per requested key,
then merge equal supports on consecutive keys. Lean binary lookup remains
untrusted: every selected basis is checked against its actual axis and rows.
Explicit --run,120 seconds,192MiB RSS,8MiB output; no active files modified.
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

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def cramer(first, second, x, y):
    ax, ay, ac = first['integers']
    bx, by, bc = second['integers']
    det = ax * by - ay * bx
    sign = 1 if det >= 0 else -1
    u, v, scale = sign * (x * by - y * bx), sign * (ax * y - ay * x), sign * det
    if u < 0 or v < 0 or scale <= 0:
        return None
    assert u * ax + v * bx == scale * x and u * ay + v * by == scale * y
    return u, v, scale, u * ac + v * bc, (u > 0 and first['strict']) or (v > 0 and second['strict'])


def direction(key, refs):
    quadrant, angle = divmod(key, 64)
    c, s = refs[angle][:2]
    return [(c, s), (-s, c), (-c, -s), (s, -c)][quadrant]


def axis_key(a, b, axis):
    return [0, 2, 1, 3][axis % 4] * 64 + (a if axis < 4 else b)


def target_constant(a, b, x, y):
    ac, ass, ad, aside, asd = a
    bc, bs, bd, bside, bsd = b
    aradius = aside * (abs(x * ac + y * ass) + abs(-x * ass + y * ac))
    bradius = bside * (abs(x * bc + y * bs) + abs(-x * bs + y * bc))
    return 2 * ad * asd * bd * bsd, aradius * bd * bsd + bradius * ad * asd


def check_sources(count):
    blocks = (count+3)//4
    header = ['import Compact.Cases.C898.PairStep14FanData', '',
              'set_option Elab.async false', '', 'namespace N12Compact.C898Shared', '']
    diagnostic = header + ['theorem fanStep14_first4 : fanStep14BlockCheck 0 := by',
                           '  decide +kernel', '', '#print axioms fanStep14_first4', '',
                           'end N12Compact.C898Shared', '']
    proof = list(header)
    for i in range(blocks):
        proof += [f'theorem fanStep14_block{i} : fanStep14BlockCheck {i} := by',
                  '  decide +kernel', '']
    proof += [f'theorem fanStep14_blocks (i : Fin {blocks}) : fanStep14BlockCheck i.val := by',
              '  fin_cases i']
    proof += [f'  · exact fanStep14_block{i}' for i in range(blocks)]
    proof += ['', f'theorem fanStep14_checked (i : Fin {count}) :',
              '    (fanStep14Record i).Check step14Fans := by',
              f'  let b : Fin {blocks} := ⟨i.val / 4, by omega⟩',
              '  let j : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩',
              '  have he : b.val * 4 + j.val = i.val := by dsimp [b, j]; omega',
              f'  have hl : b.val * 4 + j.val < {count} := by rw [he]; exact i.isLt',
              '  have h := fanStep14_blocks b j hl',
              f'  have hi : (⟨b.val * 4 + j.val, hl⟩ : Fin {count}) = i := Fin.ext he',
              '  simpa only [hi] using h', '', '#print axioms fanStep14_checked', '',
              'end N12Compact.C898Shared', '']
    return '\n'.join(proof), '\n'.join(diagnostic)


def block_definition(count):
    return [f'noncomputable def fanStep14BlockCheck (block : Nat) : Prop :=',
            f'  ∀ offset : Fin 4, ∀ h : block * 4 + offset.val < {count},',
            '    (fanStep14Record ⟨block * 4 + offset.val, h⟩).Check step14Fans', '',
            'noncomputable instance (block : Nat) : Decidable (fanStep14BlockCheck block) :=',
            '  inferInstanceAs (Decidable (∀ offset : Fin 4, ∀ h : _, _))', '',
            'end N12Compact.C898Shared', '']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('Prepared only; pass --run in one scheduled bounded compute slot.')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic() - started > 120 or rss > 192 * 1024**2:
            raise RuntimeError('120-second/192-MiB pilot cap reached')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.1, 0.1)
    paths = {name: ROOT / path for name, path in {
        'poses': 'evidence/c898-shared-pose-map.json',
        'fans': 'evidence/c898-support-fan-counts.json',
        'witnesses': 'evidence/c898-all-pair-four-index-witnesses.jsonl',
        'records': 'evidence/c898-pair-record-map.json',
        'references': 'Compact/Cases/C898/References.lean',
    }.items()}
    data = json.loads(paths['poses'].read_text())
    fan_audit = json.loads(paths['fans'].read_text())
    assert digest(paths['poses']) == fan_audit['source_pose_map_sha256']
    assert digest(paths['witnesses']) == fan_audit['witness_jsonl_sha256']
    rows = data['rows']
    poses = {p['name']: p for p in data['poses']}
    blocks = {b['name']: b for b in data['blocks']}
    contexts = {tuple(c['rows']): c for c in fan_audit['contexts']}
    expected = [r for r in json.loads(paths['records'].read_text())['records'] if r['step'] == 14]
    expected.sort(key=lambda r: r['index'])
    refs = [tuple(map(int, values)) for values in re.findall(
        r'⟨(-?\d+), (-?\d+), (\d+), (-?\d+), (\d+)⟩,', paths['references'].read_text())]
    assert len(refs) == 64 and len(expected) == 424
    selected = []
    requests = defaultdict(set)
    used_contexts = {}
    with paths['witnesses'].open() as f:
        for line in f:
            record = json.loads(line)
            if not re.search(r'Step14Pose\d+Overlap', record['name']):
                continue
            assert not record['fallbacks']
            source, neighbor, block = poses[record['source']], poses[record['neighbor']], blocks[record['block']]
            arows, brows = block['rows'] + source['rows'], neighbor['rows']
            ac = contexts[tuple(sorted(set(arows)))]
            bc = contexts[tuple(sorted(set(brows)))]
            for context in [ac, bc]:
                used_contexts[context['id']] = context
            for axis in range(8):
                key = axis_key(source['angle'], neighbor['angle'], axis)
                requests[ac['id']].add(key)
                requests[bc['id']].add((key + 128) % 256)
            selected.append({'name': record['name'], 'source': source['index'],
                             'neighbor': neighbor['index'], 'block': block['index'],
                             'source_context': ac['id'], 'neighbor_context': bc['id'],
                             'angles': [source['angle'], neighbor['angle']]})
    by_name = {r['name']: r for r in selected}
    assert len(by_name) == len(selected) == len(expected)
    records = [by_name[r['name']] for r in expected]
    for i, record in enumerate(records):
        assert all(record[k] == expected[i][k] for k in ['name', 'source', 'neighbor', 'block'])
    choices, fan_entries = {}, {}
    for cid, keys in sorted(requests.items()):
        context = used_contexts[cid]
        choices[cid] = {}
        for key in sorted(keys):
            x, y = direction(key, refs)
            candidates = []
            for first, second in context['bases']:
                assert first in context['rows'] and second in context['rows']
                result = cramer(rows[first], rows[second], x, y)
                if result is not None:
                    _, _, scale, constant, strict = result
                    candidates.append((Fraction(constant, scale), not strict, first, second, result))
            assert candidates, (cid, key, 'no valid directional support')
            _, _, first, second, result = min(candidates)
            choices[cid][key] = ((first, second), result)
        entries = []
        for key, (basis, _) in sorted(choices[cid].items()):
            if not entries or entries[-1][1:] != basis:
                entries.append((key if entries else 0, *basis))
        fan_entries[cid] = entries
    # Validate exactly the finite checker arithmetic and every lookup, not just
    # that a best support has a plausible numerical value.
    axes = 0
    for record in records:
        ai, bi = record['angles']
        for axis in range(8):
            key = axis_key(ai, bi, axis)
            opposite = (key + 128) % 256
            achoice, a = choices[record['source_context']][key]
            bchoice, b = choices[record['neighbor_context']][opposite]
            for cid, k, expected_basis in [(record['source_context'], key, achoice),
                                           (record['neighbor_context'], opposite, bchoice)]:
                entries = fan_entries[cid]
                lo, hi, best = 0, len(entries), (0, 0)
                for _ in range(16):
                    if lo >= hi:
                        break
                    mid = (lo + hi) // 2
                    start, first, second = entries[mid]
                    if start <= k:
                        lo, best = mid + 1, (first, second)
                    else:
                        hi = mid
                assert best == expected_basis
            x, y = direction(key, refs)
            scale, constant = target_constant(refs[ai], refs[bi], x, y)
            combined = a[3] * b[2] + b[3] * a[2]
            total_scale = a[2] * b[2]
            assert scale > 0 and scale * combined <= total_scale * constant
            assert scale * combined < total_scale * constant or a[4] or b[4]
            axes += 1
    context_order = sorted(fan_entries)
    local = {cid: i for i, cid in enumerate(context_order)}
    lines = ['import Compact.Cases.C898.PairFanSyntax', '',
             'set_option Elab.async false', 'set_option linter.unnecessarySeqFocus false', '',
             'namespace N12Compact.C898Shared', '',
             '/-- Separate whole-step pilot; no original pair obligation is omitted. -/']
    for cid in context_order:
        lines += [f'noncomputable def step14Fan{local[cid]} : Array (SupportFan.Entry rowCount) :=',
                  f'  fan_entries% {data["row_count"]} "']
        lines += [f'{key},{a},{b}' for key, a, b in fan_entries[cid]]
        lines += ['"', '']
    lines += ['noncomputable def step14Fans : Nat → Array (SupportFan.Entry rowCount)',
              *[f'  | {local[cid]} => step14Fan{local[cid]}' for cid in context_order],
              '  | _ => #[]', '']
    chunks = [records[i:i+128] for i in range(0, len(records), 128)]
    for i, chunk in enumerate(chunks):
        lines += [f'noncomputable def fanStep14Chunk{i} : Array FanRecord :=',
                  f'  fan_records% {data["pose_count"]} "']
        lines += [f'{r["source"]},{r["neighbor"]},{r["block"]},'
                  f'{local[r["source_context"]]},{local[r["neighbor_context"]]}' for r in chunk]
        lines += ['"', '']
    lines += ['noncomputable def fanStep14Records : Array (Array FanRecord) := #[',
              ',\n'.join(f'  fanStep14Chunk{i}' for i in range(len(chunks))), ']', '',
              f'noncomputable def fanStep14Record (i : Fin {len(records)}) : FanRecord :=',
              '  (((fanStep14Records[i.val / 128]?).getD #[])[i.val % 128]?).getD ⟨0, 0, 0, 0, 0⟩', '']
    lines += block_definition(len(records))
    payload = '\n'.join(lines)
    assert len(payload.encode()) < 8 * 1024**2
    output = ROOT / 'Compact/Cases/C898/PairStep14FanData.lean'
    output.write_text(payload)
    proof, diagnostic = check_sources(len(records))
    proof_output = ROOT / 'Compact/Cases/C898/PairStep14FanPilot.lean'
    proof_output.write_text(proof)
    diagnostic_output = ROOT / 'Compact/Cases/C898/PairStep14FanFirst4.lean'
    diagnostic_output.write_text(diagnostic)
    report = {
        'scope': 'Exact integer audit and separate assembled source; no Lean acceptance.',
        'records': len(records), 'axes': axes, 'context_count': len(context_order),
        'requested_context_directions': sum(map(len, requests.values())),
        'fan_entries': sum(map(len, fan_entries.values())),
        'max_fan_entries': max(map(len, fan_entries.values())),
        'old_support_row_indices': len(records) * 8 * 4,
        'new_fan_row_indices': 2 * sum(map(len, fan_entries.values())),
        'new_record_natural_fields': len(records) * 5,
        'source_lines': len(lines), 'source_bytes': len(payload.encode()),
        'input_sha256': {name: digest(path) for name, path in paths.items()},
        'output': str(output.relative_to(ROOT)), 'output_sha256': digest(output),
        'whole_step_proof': str(proof_output.relative_to(ROOT)),
        'whole_step_proof_sha256': digest(proof_output),
        'diagnostic': str(diagnostic_output.relative_to(ROOT)),
        'diagnostic_sha256': digest(diagnostic_output),
        'proof_block_size':4, 'proof_block_count':(len(records)+3)//4,
        'elapsed_seconds': time.monotonic() - started,
        'record_map': records,
        'contexts': [{'original_context': cid, 'local_fan': local[cid],
                      'entries': fan_entries[cid]} for cid in context_order],
        'semantic_boundary': [
            'No optimality claim is trusted; all eight actual targets are checked.',
            'Every original step14 record, source, neighbor, block and order is preserved.',
            'Membership and strict boundary information remain explicit checks.',
            'Full-step plan/coverage integration is separate from this424-record pilot.',
        ],
    }
    report_path = ROOT / 'evidence/c898-step14-support-fan-pilot.json'
    with report_path.open('w') as f:
        json.dump(report, f, separators=(',', ':'))
        f.write('\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({k: v for k, v in report.items() if k not in ['record_map', 'contexts', 'input_sha256']}))


if __name__ == '__main__':
    main()
