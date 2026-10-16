#!/usr/bin/env python3
"""Exact, bounded follow-up to the direct-bank audit. No source activation.

Counts computable normal families and genuine co-occurring box recipes, then
checks strictness-preserving halfplane redundancy in every retained original
pose and in every fan context. This is a proposed geometric re-emission, not
compatibility of old fan IDs: all downstream checks must be regenerated.
Parent-only --run; serial200MiB/60s, output8MiB. No search over configurations.
"""
from collections import Counter
from math import gcd
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

from audit_historical_bank_reachability import JSONStream
from audit_historical_outside_coverage import Context

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
BANK = ROOT / 'evidence/historical-direct-bank'
FANS = ROOT / 'evidence/historical-fans-701-713-717-973-978-979-cycles'


def need(test, message):
    if not test:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--output', default='evidence/historical-polygon-redundancy')
    args = parser.parse_args()
    need(args.run, 'parent serial slot and --run required')
    dest = (ROOT / args.output).resolve()
    need(dest.is_relative_to(ROOT / 'evidence'), 'output must be under evidence')
    staging = dest.with_name(dest.name + '.staging')
    need(not dest.exists() and not staging.exists(), 'refusing existing output')
    started = time.monotonic()
    sources = {}
    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 190 * 1024**2 and time.monotonic() - started < 55, '190MiB/55second working guard')
    def stopped(*_):
        raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stopped)
    signal.signal(signal.SIGINT, stopped)
    def authenticate(path, expected=None):
        h = hashlib.sha256()
        with path.open('rb') as file:
            for block in iter(lambda: file.read(65536), b''):
                h.update(block)
                guard()
        digest = h.hexdigest()
        need(expected is None or digest == expected, 'hash mismatch: ' + str(path))
        sources[str(path.relative_to(ROOT))] = digest
        return digest
    def load(path, expected=None):
        authenticate(path, expected)
        need(path.stat().st_size < 16 * 1024**2, 'oversized metadata load')
        with path.open() as file:
            result = json.load(file)
        guard()
        return result
    def streamed_array(path):
        stream = JSONStream(path, guard)
        try:
            yield from stream.array()
            need(stream.peek() is None, 'trailing JSON array')
        finally:
            stream.file.close()
    staging.mkdir(parents=True)
    try:
        bank = load(BANK / 'manifest.json')
        selection = load(BANK / 'selection.json')
        need(bank['status'].startswith('complete conditional') and bank['outside_contexts'] == 16896
             and bank['direct_plans'] == 9166,
             'direct bank audit missing')
        manifest = load(BASE / 'manifest.json')
        expected = {x['path']: x['sha256'] for x in manifest['output_files']}
        poses = load(BASE / 'poses.json', expected['poses.json'])
        contexts = load(BASE / 'contexts.json', expected['contexts.json'])
        blocks = load(BASE / 'blocks.json', expected['blocks.json'])
        live = set(selection['row_ids'])
        rows = [None] * manifest['unique_objects']['row']
        denominators = [0] * len(rows)
        record_sizes = [0] * len(rows)
        normal_shapes, directions = Counter(), Counter()
        axis = Counter()
        row_stats = Counter()
        authenticate(BASE / 'rows.json', expected['rows.json'])
        for i, record in enumerate(streamed_array(BASE / 'rows.json')):
            need(record['index'] == i and record['denominator'] > 0, 'invalid original row')
            if i not in live:
                continue
            x, y, c = record['integers']
            strict, den = record['strict'], record['denominator']
            rows[i] = (x, y, c, strict)
            denominators[i] = den
            record_sizes[i] = len((f'{i}:{x},{y},{c},{str(strict).lower()},{den-1}\n').encode())
            normal_shapes[(x, y, den)] += 1
            g = gcd(abs(x), abs(y)) or 1
            directions[(x//g, y//g)] += 1
            row_stats['strict' if strict else 'nonstrict'] += 1
            if den == max(abs(x), abs(y)):
                row_stats['denominator_is_max_normal'] += 1
            if x == 0 and y == 0:
                row_stats['constant'] += 1
            elif x == 0 or y == 0:
                key = 'x_lower' if x > 0 else 'x_upper' if x < 0 else 'y_lower' if y > 0 else 'y_upper'
                axis[key] += 1
                if abs(x or y) == den:
                    row_stats['unit_axis_normalized'] += 1
            if den == max(abs(x), abs(y)) and c * 100000000 % den == 0:
                row_stats['offset_on_1e8_grid'] += 1
        need(i+1 == len(rows) and sum(r is not None for r in rows) == len(live), 'row coverage differs')
        families = {'exact_normal_denominator_families': len(normal_shapes),
                    'primitive_oriented_directions': len(directions),
                    'top_exact_normal_multiplicities': normal_shapes.most_common(12),
                    'top_direction_multiplicities': directions.most_common(12),
                    'axis_rows': dict(axis), 'row_properties': dict(row_stats)}
        del normal_shapes, directions
        reductions = []
        reduced_pose_rows = set()
        pose_lengths = Counter()
        original_pose_occurrences = reduced_pose_occurrences = removal_count = 0
        # Each deletion is justified from the then-remaining rows. Reversing the
        # logged deletions gives a proof of equivalence, preserving strictness.
        def reduce_ids(ids):
            current = list(dict.fromkeys(ids))
            removed = []
            position = 0
            while position < len(current):
                rid = current[position]
                rest = current[:position] + current[position+1:]
                hint = Context(tuple(rows[r] for r in rest)).hint(rows[rid])
                if hint is None:
                    position += 1
                else:
                    used = [] if hint[0] == 0 else [rest[j] for j in hint[1:]]
                    removed.append([rid, hint[0], *used])
                    current = rest
            return current, removed
        boxes = []
        box_used = set()
        full_box_poses = 0
        for pid in selection['pose_ids']:
            guard()
            p = poses[pid]
            need(p['index'] == pid and all(r in live for r in p['rows']), 'pose references omitted row')
            kept, removed = reduce_ids(p['rows'])
            reductions.append([pid, kept, removed])
            reduced_pose_rows.update(kept)
            original_pose_occurrences += len(p['rows'])
            reduced_pose_occurrences += len(kept)
            removal_count += len(removed)
            pose_lengths[len(kept)] += 1
            oriented = {}
            for rid in kept:
                x, y, _, strict = rows[rid]
                if strict or not (x == 0 or y == 0) or (x == 0 and y == 0):
                    continue
                if abs(x or y) != denominators[rid]:
                    continue
                direction = 0 if x > 0 else 1 if x < 0 else 2 if y > 0 else 3
                if direction not in oriented:
                    oriented[direction] = rid
            if len(oriented) == 4:
                full_box_poses += 1
                ids = [oriented[i] for i in range(4)]
                # Only disjoint groups of four ACTUALLY co-occurring bounds:
                # no arbitrary packing of unrelated rows is called a box.
                if not box_used.intersection(ids):
                    boxes.append([pid, ids])
                    box_used.update(ids)
        fan_manifest = load(FANS / 'manifest.json')
        fan_entry = next(x for x in fan_manifest['files'] if x['path'] == 'fans.json')
        authenticate(FANS / 'fans.json', fan_entry['sha256'])
        fan_rows = set()
        fan_records = []
        seen_contexts = set()
        fan_stats = Counter()
        stream = JSONStream(FANS / 'fans.json', guard)
        try:
            stream.punctuation('{')
            keys = set()
            while stream.peek() != '}':
                if keys:
                    stream.punctuation(',')
                key = stream.value()
                need(key not in keys, 'duplicate fan key')
                keys.add(key)
                stream.punctuation(':')
                if key == 'context_records':
                    for record in stream.array():
                        guard()
                        cid = record['context']
                        need(cid not in seen_contexts, 'duplicate fan context')
                        seen_contexts.add(cid)
                        original = contexts[cid]['inputs']
                        need(all(r in live for r in original), 'fan references omitted original row')
                        cycle = list(dict.fromkeys(record['boundary_cycle'] or []))
                        need(cycle and all(r in original and r in live for r in cycle), 'missing/invalid cycle')
                        ctx = Context(tuple(rows[r] for r in cycle))
                        kept = cycle.copy()
                        omitted = []
                        for rid in original:
                            if rid in kept:
                                continue
                            hint = ctx.hint(rows[rid])
                            if hint is None:
                                kept.append(rid)
                                fan_stats['residual_strict' if rows[rid][3] else 'residual_nonstrict'] += 1
                            else:
                                used = [] if hint[0] == 0 else [cycle[j] for j in hint[1:]]
                                omitted.append([rid, hint[0], *used])
                        fan_rows.update(kept)
                        fan_records.append([cid, kept, omitted])
                        fan_stats['original_occurrences'] += len(original)
                        fan_stats['retained_occurrences'] += len(kept)
                        fan_stats['omitted_occurrences'] += len(omitted)
                        fan_stats['cycle_only_contexts'] += int(len(kept) == len(cycle))
                elif key == 'empty_contexts':
                    for cid, witness in stream.value().items():
                        cid = int(cid)
                        need(cid not in seen_contexts, 'duplicate empty context')
                        seen_contexts.add(cid)
                        # Preserve its exact explicit emptiness inputs, not a
                        # default empty polygon or a missing fan record.
                        kept = contexts[cid]['inputs']
                        fan_rows.update(kept)
                        fan_records.append([cid, kept, []])
                        fan_stats['empty_contexts'] += 1
                elif key == 'plans':
                    for _ in stream.array():
                        pass
                elif key == 'angle_order':
                    stream.value()
                else:
                    raise ValueError('unknown fan key ' + str(key))
            stream.punctuation('}')
            need(stream.peek() is None, 'trailing fan object')
        finally:
            stream.file.close()
        need(seen_contexts == set(selection['context_ids']), 'full selected fan coverage differs')
        blocked_rows = {rid for bid in selection['block_ids'] for rid in blocks[bid]['rows']}
        candidate = reduced_pose_rows | fan_rows | blocked_rows
        need(candidate <= live, 'new row outside authenticated selected bank')
        removed_global = sorted(live - candidate)
        # Global data rows still used by a block cannot be removed merely because
        # every ordinary pose occurrence was redundant.
        report = {
            'status': 'complete exact local equivalence audit; no source emitted or activated',
            'sources': sources, 'families': families,
            'pose_count': len(reductions), 'original_pose_row_occurrences': original_pose_occurrences,
            'retained_pose_row_occurrences': reduced_pose_occurrences,
            'deleted_pose_occurrences_with_explicit_hints': removal_count,
            'retained_pose_length_histogram': dict(pose_lengths),
            'fan_contexts': len(seen_contexts), 'fans': dict(fan_stats),
            'global_rows_before': len(live), 'global_rows_after_candidate': len(candidate),
            'global_row_records_saved': len(removed_global),
            'global_row_record_bytes_saved': sum(record_sizes[i] for i in removed_global),
            'removed_global_ids': removed_global,
            'cooccurring_boxes': {'poses_with_four_nonstrict_axis_faces': full_box_poses,
                'disjoint_four_row_groups': len(boxes), 'axis_rows_in_groups': len(box_used),
                'four_rows_to_one_recipe_record_saving': 3*len(boxes),
                'scope': 'Actual co-occurring irredundant axis bounds; positive denominators and exact original numerator scaling preserved.'},
            'activation_gates': [
                'All local equivalences must become ordinary Lean proofs or be discharged by a complete fresh original-model chain.',
                'Rewrite original pose/target lists and direct context positions coherently; old hints and metadata equalities are not compatible automatically.',
                'Regenerate support fans from reduced inputs, preserving every strict support and all original point/axis comparisons.',
                'Rerun initial covers, direct pruning, all retained chord contracts and all final original-case roots.',
                'Box recipes need their exact decoder and a measured compile/source comparison; recipe record savings are not emitted Lean line savings.'
            ],
            'interpretation': 'Normal-family counts measure sharing, not a reduction in mathematical cases or unique offsets. Only omitted implied inequalities reduce geometric data.',
            'seconds': time.monotonic()-started,
        }
        written = 0
        for name, value in [('manifest.json', report), ('pose-reductions.json', reductions),
                            ('fan-reductions.json', fan_records), ('boxes.json', boxes)]:
            blob = (json.dumps(value, separators=(',', ':')) + '\n').encode()
            written += len(blob)
            need(written <= 8*1024**2, '8MiB output cap')
            (staging/name).write_bytes(blob)
        guard()
        staging.rename(dest)
        print(json.dumps({key:report[key] for key in ('status','families','pose_count',
            'original_pose_row_occurrences','retained_pose_row_occurrences','fans',
            'global_rows_before','global_rows_after_candidate','global_row_records_saved',
            'global_row_record_bytes_saved','cooccurring_boxes','seconds')}, indent=2))
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
