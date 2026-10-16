#!/usr/bin/env python3
"""Audit whole-target contrapositives for all 9,166 original pruning plans.

Coordinator-only exact arithmetic: 200 MiB / 55 seconds / 4 MiB output.
No Lean execution or source activation. Strict complements, original source
and target rows, and complete original blocks are retained. An unsupported
rule is reported, never weakened or replaced with an assumed empty region.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import resource
import shutil
import signal
import sys
import time

from audit_historical_outside_coverage import Context, opposite
from prepare_c713_direct_pruning import ROOT, BASE, AUDIT, need, digest

PREVIOUS = ROOT / 'evidence/proposals/HistoricalDirectPruningStages'
DEST = ROOT / 'evidence/historical-blocked-targets'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    need(args.run, 'coordinator serial slot and --run required')
    stage = DEST.with_name(DEST.name + '.staging')
    need(not DEST.exists() and not stage.exists(), 'refusing existing audit')
    started, provenance = time.monotonic(), {}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 200 * 1024**2 and time.monotonic() - started < 55, '200 MiB / 55 second limit')

    def authenticate(path, expected=None):
        guard()
        actual = digest(path)
        need(expected is None or actual == expected, 'source hash mismatch: ' + str(path))
        provenance[str(path.relative_to(ROOT))] = actual

    def load(path, expected=None):
        authenticate(path, expected)
        need(path.stat().st_size < 16 * 1024**2, 'oversized metadata')
        return json.loads(path.read_text())

    def records(path, expected):
        authenticate(path, expected)
        with path.open() as stream:
            for line in stream:
                line = line.strip().rstrip(',')
                if line not in ('[', ']', ''):
                    yield json.loads(line)

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    stage.mkdir(parents=True)
    try:
        previous = load(PREVIOUS / 'manifest.json')
        need(previous['original_plans'] == 9166 and previous['direct_outside_contexts'] == 16896,
             'incomplete original plan scope')
        plans = previous['records']
        del previous
        old = load(AUDIT / 'manifest.json')
        manifest = load(BASE / 'manifest.json', old['input_sha256']['evidence/historical-compact-data/manifest.json'])
        expected = {r['path']: r['sha256'] for r in manifest['output_files']}
        wanted = {p['source'] for p in plans}
        wanted.update(target for p in plans for target in p['direct_targets'])
        poses = {p['index']: p for p in records(BASE / 'poses.json', expected['poses.json']) if p['index'] in wanted}
        need(set(poses) == wanted, 'original pose missing')
        needed_rows = {row for p in poses.values() for row in p['rows']}
        needed_rows.update(row for p in plans for row in (p['block_rows'] or []))
        rows = {r['index']: (*r['integers'], bool(r['strict']))
                for r in records(BASE / 'rows.json', expected['rows.json']) if r['index'] in needed_rows}
        need(set(rows) == needed_rows, 'original row missing')
        counts, per_case, per_stage, failures = Counter(), {}, {}, []
        output = stage / 'rules.jsonl'
        written = 0
        with output.open('w') as stream:
            for plan in plans:
                guard()
                case, ordinal, step = plan['case'], plan['ordinal'], plan['step']
                stats = Counter(plans=1)
                targets = plan['direct_targets']
                block_ids = plan['block_rows']
                need(len(targets) == (1 if block_ids is None else len(block_ids)), 'original face coverage changed')
                stats['old_outside_contexts'] = len(targets)
                stats['old_target_row_checks'] = sum(len(poses[t]['rows']) for t in targets)
                original = [rows[r] for r in poses[plan['source']]['rows']]
                if not targets:
                    need(block_ids == [], 'zero output without excluded empty conjunction')
                    stats['empty_block_exclusion_plans'] = 1
                    record = [case, ordinal, 0]
                elif len(set(targets)) != 1:
                    stats['nonuniform_target_plans'] = 1
                    record = [case, ordinal, 3, sorted(set(targets))]
                    failures.append({'case': case, 'ordinal': ordinal, 'reason': 'multiple original final targets'})
                else:
                    target_id = targets[0]
                    target = [rows[r] for r in poses[target_id]['rows']]
                    block = [rows[r] for r in (block_ids or [])]
                    need(poses[target_id]['angle'] == poses[plan['source']]['angle'], 'target angle changed')
                    context, rules, unsupported = Context(original), [], []
                    cache = {}
                    for position, row in enumerate(target):
                        if row in cache:
                            rule = cache[row]
                            stats['duplicate_target_row_occurrences'] += 1
                        else:
                            direct = context.hint(row)
                            if direct is not None:
                                rule = [0, direct]
                            else:
                                violation = Context([opposite(row)] + original)
                                hints, bad = violation.cover(block) if block_ids is not None else (None, -1)
                                if hints is not None:
                                    rule = [1, hints]
                                else:
                                    empty = violation.empty()
                                    rule = [2, empty] if empty is not None else [3, bad]
                            cache[row] = rule
                            stats['unique_target_rules'] += 1
                        rules.append(rule)
                        if rule[0] == 0:
                            stats['direct_target_rows'] += 1
                            stats['new_integer_hint_checks'] += 1
                        elif rule[0] == 1:
                            stats['contrapositive_target_rows'] += 1
                            stats['new_integer_hint_checks'] += len(block)
                        elif rule[0] == 2:
                            stats['empty_violation_target_rows'] += 1
                            stats['new_empty_checks'] += 1
                        else:
                            unsupported.append(position)
                    stats['uniform_target_plans'] = 1
                    if unsupported:
                        stats['unsupported_plans'] = 1
                        failures.append({'case': case, 'ordinal': ordinal, 'target': target_id,
                                         'target_row_positions': unsupported})
                    else:
                        stats['supported_uniform_target_plans'] = 1
                        if all(rule[0] in (0, 2) for rule in rules):
                            stats['target_independent_of_block_plans'] = 1
                    record = [case, ordinal, 1, target_id, rules]
                counts.update(stats)
                per_case.setdefault(str(case), Counter()).update(stats)
                per_stage.setdefault(f'{case}:{step}', Counter()).update(stats)
                encoded = json.dumps(record, separators=(',', ':')) + '\n'
                written += len(encoded.encode())
                need(written < 4 * 1024**2, '4 MiB certificate cap')
                stream.write(encoded)
        need(counts['plans'] == 9166 and counts['old_outside_contexts'] == 16896, 'incomplete whole-scope pass')
        report = {'status': 'complete exact audit; no Lean acceptance or source activation',
                  'counts': dict(counts), 'per_case': per_case, 'per_stage': per_stage,
                  'unsupported': failures, 'all_plans_visited': True,
                  'all_plans_supported': not failures, 'source_sha256': provenance,
                  'rules_sha256': digest(output), 'rules_bytes': written,
                  'interpretation': 'The same final target and every strict block/source/target row are retained. Empty blocks are excluded by actual overlap, not an empty-center claim. New support counts are arithmetic witness costs, not emitted source-line or replay-time bounds.',
                  'elapsed_seconds': time.monotonic() - started}
        (stage / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        stage.rename(DEST)
        print(json.dumps({'counts': dict(counts), 'all_plans_supported': not failures,
                          'rules_bytes': written, 'elapsed_seconds': report['elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
