#!/usr/bin/env python3
"""Reuse the exact outside audit's witnesses instead of searching in Lean.

Coordinator-only source preparation, 256 MiB / 115 seconds / 16 MiB output.
Default pilot compares the first C713 stage-0/stage-1 batches in new namespaces.
--all-batches emits the selected cases' batch replacements as an isolated
proposal. No source activation, certificate search, or Lean execution occurs.
"""
from collections import Counter, defaultdict
from pathlib import Path
import argparse
import hashlib
import json
import resource
import shutil
import signal
import sys
import time

from prepare_c713_direct_pruning import ROOT, BASE, AUDIT, need, digest, header, footer, literal

PREVIOUS = ROOT / 'evidence/proposals/HistoricalDirectPruningStages'
CASES = (701, 713, 717, 973, 978, 979)


def render(namespace, plans):
    text = header(['Compact.Bridge.DirectPruningHintSyntax',
                   'Compact.Cases.C713.SharedDictionary'], namespace)
    for plan in plans:
        block = 'none' if plan['block_rows'] is None else '(some ' + literal(plan['block_rows']) + ')'
        text += f'checked_direct_plan_hints plan{plan["ordinal"]} (dictionary,{plan["source"]},{block})'
        text += literal(plan['direct_targets']) + ' using [\n'
        text += ',\n'.join('  [' + ', '.join(hints) + ']' for hints in plan['full_hints'])
        text += ']\n'
    text += '\ndef plans : List (Plan HistoricalData.rowCount HistoricalData.poseCount) :=\n  '
    text += '[' + ','.join('plan' + str(plan['ordinal']) for plan in plans) + ']\n\n'
    text += '''theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  simp only [plans, List.forall_mem_cons]
  exact ⟨''' + ', '.join('plan' + str(plan['ordinal']) + '_checked' for plan in plans)
    text += ', by simp⟩\n'
    return text + footer(namespace)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--all-batches', action='store_true')
    parser.add_argument('--cases', default='713')
    args = parser.parse_args()
    need(args.run, 'coordinator serial slot and --run required')
    cases = CASES if args.cases == 'all' else tuple(map(int, args.cases.split(',')))
    need(cases and set(cases) <= set(CASES) and len(cases) == len(set(cases)), 'bad case selection')
    need(args.all_batches or cases == (713,), 'comparison pilot is specifically C713')
    suffix = 'All' if cases == CASES else '_'.join(map(str, cases))
    dest = ROOT / ('evidence/proposals/DirectPruningHints' + (suffix if args.all_batches else 'Pilot'))
    staging = dest.with_name(dest.name + '.staging')
    need(not dest.exists() and not staging.exists(), 'refusing existing proposal')
    started, hashes = time.monotonic(), {}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 256 * 1024**2 and time.monotonic() - started < 115, '256 MiB / 115 second limit')

    def authenticate(path, expected=None):
        guard()
        actual = digest(path)
        need(expected is None or actual == expected, 'input hash mismatch: ' + str(path))
        hashes[str(path.relative_to(ROOT))] = actual

    def load(path, expected=None):
        authenticate(path, expected)
        need(path.stat().st_size < 16 * 1024**2, 'oversized metadata input')
        return json.loads(path.read_text())

    def records(path, expected):
        authenticate(path, expected)
        with path.open() as stream:
            for line in stream:
                line = line.strip().rstrip(',')
                if line in ('[', ']', ''):
                    continue
                yield json.loads(line)

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    staging.mkdir(parents=True)
    try:
        previous = load(PREVIOUS / 'manifest.json')
        need(previous['shared_stage_theorem'] and previous['original_plans'] == 9166,
             'not the complete reviewed direct-plan proposal')
        audit = load(AUDIT / 'manifest.json')
        need(audit['all_outside_contexts_visited'] and audit['counts'].get('unsupported_branches', 0) == 0,
             'outside audit is incomplete')
        manifest = load(BASE / 'manifest.json',
                        audit['input_sha256']['evidence/historical-compact-data/manifest.json'])
        expected = {item['path']: item['sha256'] for item in manifest['output_files']}
        grouped = defaultdict(list)
        for plan in previous['records']:
            if plan['case'] in cases:
                grouped[(plan['case'], plan['step'])].append(plan)
        batches = []
        for (case, step), plans in sorted(grouped.items()):
            for start in range(0, len(plans), 16):
                if not args.all_batches and (step not in (0, 1) or start != 0):
                    continue
                batches.append((case, step, start // 16, plans[start:start + 16]))
        selected = {(p['case'], p['ordinal']): p for *_, plans in batches for p in plans}
        wanted_poses = {p['source'] for p in selected.values()}
        wanted_poses.update(target for p in selected.values() for target in p['direct_targets'])
        poses = {p['index']: p for p in records(BASE / 'poses.json', expected['poses.json'])
                 if p['index'] in wanted_poses}
        need(set(poses) == wanted_poses, 'missing original pose')
        wanted_rows = {row for p in poses.values() for row in p['rows']}
        wanted_rows.update(row for p in selected.values() for row in (p['block_rows'] or []))
        rows = {r['index']: (*r['integers'], bool(r['strict']))
                for r in records(BASE / 'rows.json', expected['rows.json']) if r['index'] in wanted_rows}
        need(set(rows) == wanted_rows, 'missing original row')
        del previous, grouped
        branches = {}
        authenticate(AUDIT / 'branches.jsonl', audit['branches_sha256'])
        with (AUDIT / 'branches.jsonl').open() as stream:
            for line in stream:
                record = json.loads(line)
                if tuple(record[:2]) in selected:
                    need(record[3] == 0, 'explicit close outcome requires its own witness syntax')
                    key = tuple(record[:3])
                    need(key not in branches, 'duplicate audited context')
                    branches[key] = record
        used, reports, outputs = set(), [], []
        for case, step, batch, plans in batches:
            guard()
            stats = Counter()
            input_sizes, target_sizes = [], []
            for plan in plans:
                inputs = [rows[row] for row in poses[plan['source']]['rows']]
                block = plan['block_rows']
                need(len(plan['direct_targets']) == (1 if block is None else len(block)),
                     'original outside branch count differs')
                contexts = []
                if block is None:
                    contexts = [inputs]
                else:
                    for index in block:
                        row = rows[index]
                        contexts.append([(-row[0], -row[1], -row[2], not row[3])] + inputs)
                        inputs = [row] + inputs
                plan['full_hints'] = []
                for face, (context, target_id) in enumerate(zip(contexts, plan['direct_targets'])):
                    key = (case, plan['ordinal'], face)
                    need(key in branches, 'missing audited branch')
                    record = branches[key]
                    need(record[4] == target_id, 'changed final original target')
                    used.add(key)
                    target = [rows[row] for row in poses[target_id]['rows']]
                    need(poses[target_id]['angle'] == poses[plan['source']]['angle'], 'angle changed')
                    sparse = {item[0]: item[1:] for item in record[5]}
                    need(len(sparse) == len(record[5]) and set(sparse) <= set(range(len(target))),
                         'malformed sparse hint positions')
                    full = []
                    for position, row in enumerate(target):
                        if position not in sparse:
                            need(row in context, 'omitted witness is not an exact copied row')
                            full.append('.copy ' + str(context.index(row)))
                            stats['copy_hints'] += 1
                            continue
                        witness = sparse[position]
                        if witness == [0]:
                            full.append('.constant')
                            stats['constant_hints'] += 1
                        elif len(witness) == 2 and witness[0] == 1:
                            need(0 <= witness[1] < len(context), 'invalid single-row position')
                            full.append('.single ' + str(witness[1]))
                            stats['single_hints'] += 1
                        else:
                            need(len(witness) == 3 and witness[0] == 2 and
                                 all(0 <= i < len(context) for i in witness[1:]), 'invalid pair positions')
                            full.append('.pair ' + str(witness[1]) + ' ' + str(witness[2]))
                            stats['pair_hints'] += 1
                    plan['full_hints'].append(full)
                    stats['outside_contexts'] += 1
                    stats['input_row_occurrences'] += len(context)
                    stats['target_row_occurrences'] += len(target)
                    stats['old_search_candidate_upper_bound'] += len(target) * (
                        1 + 2 * len(context) + len(context) * (len(context) - 1) // 2)
                    input_sizes.append(len(context))
                    target_sizes.append(len(target))
            folder = 'DirectPruning' if args.all_batches else 'DirectPruningHintPilot'
            namespace = f'N12Compact.C{case}DirectPruning.Step{step:02}Batch{batch:02}'
            if not args.all_batches:
                namespace = f'N12Compact.C{case}DirectPruningHintPilot.Step{step:02}Batch{batch:02}'
            relative = f'Compact/Cases/C{case}/{folder}/Step{step:02}Batch{batch:02}.lean'
            text = render(namespace, plans)
            path = staging / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            outputs.append({'path': relative, 'sha256': hashlib.sha256(text.encode()).hexdigest(),
                            'lines': text.count('\n'), 'bytes': len(text.encode())})
            reports.append({'case': case, 'step': step, 'batch': batch, 'plans': len(plans),
                            'statistics': dict(stats), 'input_row_range': [min(input_sizes, default=0), max(input_sizes, default=0)],
                            'target_row_range': [min(target_sizes, default=0), max(target_sizes, default=0)]})
        need(used == set(branches), 'unused audited context')
        report = {'status': 'explicit audited hints; source only, unchanged Plan.Check requires replay',
                  'pilot_only': not args.all_batches, 'cases': list(cases),
                  'input_sha256': hashes, 'batches': reports, 'outputs': outputs,
                  'lean_modules': len(outputs), 'lean_lines': sum(p['lines'] for p in outputs),
                  'lean_bytes': sum(p['bytes'] for p in outputs),
                  'remaining_lean_searches': 0, 'elapsed_seconds': time.monotonic() - started}
        need(report['lean_bytes'] < 16 * 1024**2, '16 MiB source output cap')
        (staging / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        staging.rename(dest)
        print(json.dumps({key: report[key] for key in
              ['status', 'lean_modules', 'lean_lines', 'lean_bytes', 'elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(staging)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
