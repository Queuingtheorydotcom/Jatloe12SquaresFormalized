#!/usr/bin/env python3
"""Parent-only exact box-recipe re-emission of the inactive direct bank.

The four original IDs stay in each box record. The Lean decoder materializes
the same balanced literal row tree, with no extra index table. Only boxes
contained in one existing bounded leaf are grouped; crossing boxes stay raw.
All positive denominators/coefficients/strict bits are reconstructed exactly.
No active edits, semantic row removals, Lean runs or numerical search.
Serial200MiB/60s; transactional output16MiB. Root owns activation and replay.
"""
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

ROOT = Path(__file__).resolve().parents[1]
BANK = ROOT / 'evidence/historical-direct-bank'
REDUNDANCY = ROOT / 'evidence/historical-polygon-redundancy'


def need(test, message):
    if not test:
        raise ValueError(message)


def payload(source):
    before, sep, rest = source.partition('sparse_rows% "\n')
    need(bool(sep), 'expected an original sparse row literal')
    text, sep, after = rest.partition('\n"')
    need(bool(sep), 'unterminated sparse row literal')
    rows = {}
    for line in text.splitlines():
        key, rest = line.split(':', 1)
        key = int(key)
        fields = rest.split(',')
        need(len(fields) == 5 and fields[3] in ('true', 'false'), 'invalid original row')
        value = tuple(map(int, fields[:3])) + (fields[3] == 'true', int(fields[4]))
        need(key not in rows, 'duplicate original row ID')
        rows[key] = (line, value)
    need(list(rows) == sorted(rows), 'original leaf is not sorted')
    return before, after, rows


def encoded_box(ids, rows):
    bounds = []
    mask = 0
    for face, rid in enumerate(ids):
        _, (x, y, c, strict, pred) = rows[rid]
        den = pred + 1
        need(den > 0, 'nonpositive original denominator')
        normal = ((den, 0), (-den, 0), (0, den), (0, -den))[face]
        need((x, y) == normal, 'box face has a non-unit normalized axis')
        numerator = -c if face in (0, 2) else c
        bounds.append(f'{numerator},{pred}')
        mask |= int(strict) << face
    return 'B:' + ','.join(map(str, ids)) + ';' + '|'.join(bounds) + ';' + str(mask)


def decode_line(line):
    key, body = line.split(':', 1)
    if key != 'B':
        fields = body.split(',')
        return {int(key): tuple(map(int, fields[:3])) + (fields[3] == 'true', int(fields[4]))}
    keys, bound_text, mask = body.split(';')
    ids = list(map(int, keys.split(',')))
    bounds = [tuple(map(int, s.split(','))) for s in bound_text.split('|')]
    mask = int(mask)
    need(len(ids) == len(bounds) == 4 and mask < 16, 'invalid box recipe arity')
    result = {}
    for face, (rid, (n, pred)) in enumerate(zip(ids, bounds)):
        den = pred+1
        x, y = ((den, 0), (-den, 0), (0, den), (0, -den))[face]
        result[rid] = (x, y, -n if face in (0, 2) else n, bool(mask & (1 << face)), pred)
    return result


def rewrite(source, boxes):
    before, after, rows = payload(source)
    available = set(rows)
    chosen = [ids for ids in boxes if set(ids) <= available]
    used = set()
    starters = {}
    for ids in chosen:
        need(not used.intersection(ids), 'overlapping audited box groups')
        used.update(ids)
        starters[min(ids)] = encoded_box(ids, rows)
    if not chosen:
        return source, [], 0
    lines = []
    for rid, (line, _) in rows.items():
        if rid in starters:
            lines.append(starters[rid])
        elif rid not in used:
            lines.append(line)
    # Compare every decoded original integer coefficient, strictness and
    # denominator before reporting source savings. No numerical tolerance.
    decoded = {}
    for line in lines:
        for rid, value in decode_line(line).items():
            need(rid not in decoded, 'duplicate decoded key')
            decoded[rid] = value
    need(decoded == {key: value for key, (_, value) in rows.items()}, 'exact decoded rows differ')
    result = before.replace('import Compact.Core.SparseLiteral', 'import Compact.Core.BoxRowSyntax') + \
        'boxed_sparse_rows% "\n' + '\n'.join(lines) + '\n"' + after
    return result, [rid for ids in chosen for rid in ids], len(chosen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--output', default='evidence/historical-box-bank')
    args = parser.parse_args()
    need(args.run, 'parent serial slot and --run required')
    dest = (ROOT / args.output).resolve()
    need(dest.is_relative_to(ROOT / 'evidence'), 'output must be under evidence')
    stage = dest.with_name(dest.name + '.staging')
    need(not dest.exists() and not stage.exists(), 'refusing existing proposal')
    started = time.monotonic()
    sources = {}
    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 190*1024**2 and time.monotonic()-started < 55, '190MiB/55second working limit')
    def stop(*_):
        raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    def read(path, expected=None):
        raw = path.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        need(expected is None or digest == expected, 'source hash mismatch: '+str(path))
        sources[str(path.relative_to(ROOT))] = digest
        guard()
        return raw.decode()
    stage.mkdir(parents=True)
    try:
        bank = json.loads(read(BANK/'manifest.json'))
        audit = json.loads(read(REDUNDANCY/'manifest.json'))
        records = json.loads(read(REDUNDANCY/'boxes.json'))
        need(audit['status'].startswith('complete exact local') and bank['proposal']['emitted'],
             'required exact audits missing')
        need(len(records) == audit['cooccurring_boxes']['disjoint_four_row_groups'], 'box scope differs')
        boxes = [ids for _, ids in records]
        all_box_ids = [rid for ids in boxes for rid in ids]
        need(len(set(all_box_ids)) == len(all_box_ids), 'audit boxes are not disjoint')
        poses = json.loads(read(ROOT/'evidence/historical-compact-data/poses.json',
            bank['sources']['evidence/historical-compact-data/poses.json']))
        for pid, ids in records:
            need(len(ids) == 4 and all(rid in poses[pid]['rows'] for rid in ids),
                 'box faces do not co-occur in the actual original pose')
        del poses
        changed = []
        decoded_ids = set()
        count = 0
        lines = size = written = 0
        output_hashes = {}
        for name, digest in bank['proposal']['sha256'].items():
            source = read(BANK/'proposal'/name, digest)
            if '/RowsChunks/' in name:
                source, ids, n = rewrite(source, boxes)
                need(not decoded_ids.intersection(ids), 'same box emitted in multiple leaves')
                decoded_ids.update(ids)
                count += n
                if n:
                    changed.append({'path': name, 'boxes': n})
            raw = source.encode()
            lines += source.count('\n')
            size += len(raw)
            written += len(raw)
            need(written <= 16*1024**2, '16MiB output cap')
            path = stage/'proposal'/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            output_hashes[name] = hashlib.sha256(raw).hexdigest()
            guard()
        # One genuinely original leaf, rather than a equality against a second
        # reconstructed copy. Its name and source hash are pinned in the report.
        original_path = ROOT/'Compact/HistoricalData/RowsChunks/Part000000.lean'
        original = read(original_path)
        boxed, pilot_ids, pilot_count = rewrite(original, boxes)
        need(pilot_count > 0, 'no complete pilot box in active original first leaf')
        marker = 'boxed_sparse_rows% "\n'
        literal = boxed.split(marker, 1)[1].split('\n"', 1)[0]
        pilot = '''import Compact.Core.BoxRowSyntax
import Compact.HistoricalData.RowsChunks.Part000000

namespace N12Compact.HistoricalBoxPilot
open IntegerSupport SparseLiteral
set_option Elab.async false
noncomputable def boxed : SparseLiteral.Tree (Row × Nat) := boxed_sparse_rows% "
''' + literal + '''
"
theorem exact_original : boxed = HistoricalData.RowsChunks.part000000 := rfl
end N12Compact.HistoricalBoxPilot
#print axioms N12Compact.HistoricalBoxPilot.exact_original
'''
        ppath = stage/'pilot/Compact/HistoricalData/BoxPilot.lean'
        ppath.parent.mkdir(parents=True, exist_ok=True)
        ppath.write_text(pilot)
        written += len(pilot.encode())
        report = {
            'status': 'exact source proposal, every row reconstructed; Lean box decoder/pilot and activation pending',
            'sources': sources, 'outputs': output_hashes,
            'original_row_count': bank['direct_route']['rows'],
            'original_pose_count': bank['direct_route']['poses'],
            'grouped_boxes': count, 'grouped_row_records': len(decoded_ids),
            'cross_leaf_or_separator_boxes_retained_raw': len(boxes)-count,
            'record_lines_saved': 3*count, 'source_lines': lines, 'source_bytes': size,
            'source_modules': len(output_hashes),
            'prior_source_lines': bank['proposal']['lines'],
            'prior_source_bytes': bank['proposal']['bytes'],
            'actual_lines_saved': bank['proposal']['lines']-lines,
            'actual_bytes_saved': bank['proposal']['bytes']-size,
            'changed_leaves': changed,
            'pilot': {'path':'pilot/Compact/HistoricalData/BoxPilot.lean',
                'original':str(original_path.relative_to(ROOT)), 'boxes':pilot_count,
                'source_lines':pilot.count('\n'),'sha256':hashlib.sha256(pilot.encode()).hexdigest()},
            'kernel_representation': 'Same ordinary balanced tree with the same literal integer Rows and Nat denominators. No extra lookup structure or arithmetic on lookup.',
            'preservation': 'Every original global ID, coefficient, strictness and denominator unchanged. No geometric redundancy deletion was applied.',
            'required_before_activation': [
                'Accept BoxRowRecipe/BoxRowSyntax and the exact-original pilot under the same compiler resource limits.',
                'Accept all complete direct-pruning replacements before removing pair-only bank IDs, exactly as required by historical-direct-bank.',
                'Verify all emitted source hashes, replay dependent imported roots, and measure the full retained source closure including the two new generic modules.'
            ],
            'seconds':time.monotonic()-started,
        }
        blob = (json.dumps(report, indent=2)+'\n').encode()
        written += len(blob)
        need(written <= 16*1024**2, '16MiB output cap')
        (stage/'manifest.json').write_bytes(blob)
        guard()
        stage.rename(dest)
        print(json.dumps({key:report[key] for key in ('status','grouped_boxes',
            'grouped_row_records','cross_leaf_or_separator_boxes_retained_raw',
            'source_lines','source_bytes','source_modules','actual_lines_saved',
            'actual_bytes_saved','pilot','seconds')}, indent=2))
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
