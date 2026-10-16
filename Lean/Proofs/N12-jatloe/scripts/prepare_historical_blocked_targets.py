#!/usr/bin/env python3
"""Emit all113 whole-target stages, or two independent authentic pilots.

Coordinator-only256MiB/115second/12MiB source producer. Reuses the completed
exact contrapositive audit, never searches for witnesses or runs Lean. Keeps
all original sources, blocks, final targets, neighbors and case compositions.
"""
from collections import defaultdict
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

from prepare_c713_direct_pruning import ROOT, BASE, need, digest, literal

PREVIOUS = ROOT / 'evidence/proposals/HistoricalDirectPruningStages'
AUDIT = ROOT / 'evidence/historical-blocked-targets'
CASES = (701, 713, 717, 973, 978, 979)


def local_hint(hint):
    if hint[0] == 'copy': return '.copy ' + str(hint[1])
    if hint == [0] or hint == (0,): return '.constant'
    if hint[0] == 1: return '.single ' + str(hint[1])
    need(hint[0] == 2 and len(hint) == 3, 'bad local support hint')
    return '.pair ' + str(hint[1]) + ' ' + str(hint[2])


def full_block_hints(inputs, blocked, sparse):
    selected = {r[0]: r[1:] for r in sparse}
    need(len(selected) == len(sparse) and set(selected) <= set(range(len(blocked))), 'bad block positions')
    output = []
    for position, row in enumerate(blocked):
        if position in selected:
            hint = selected[position]
            need(hint[0] == 0 or all(0 <= i < len(inputs) for i in hint[1:]), 'bad support source index')
        else:
            need(row in inputs, 'missing copied block row')
            hint = ('copy', inputs.index(row))
        output.append(local_hint(hint))
    return '[' + ', '.join(output) + ']'


def encoded_plan(plan, record, poses, rows):
    name = 'plan' + str(plan['ordinal'])
    if record[2] == 0:
        need(plan['block_rows'] == [] and not plan['direct_targets'], 'invalid excluded empty conjunction')
        return f'{name} empty({plan["source"]})'
    need(record[2] == 1 and set(plan['direct_targets']) == {record[3]}, 'target changed')
    inputs = [rows[r] for r in poses[plan['source']]['rows']]
    target = [rows[r] for r in poses[record[3]]['rows']]
    blocked = [rows[r] for r in (plan['block_rows'] or [])]
    need(len(target) == len(record[4]), 'target row omitted')
    rules = []
    for row, rule in zip(target, record[4]):
        if rule[0] == 0:
            hint = rule[1]
            need(hint[0] == 0 or all(0 <= i < len(inputs) for i in hint[1:]), 'invalid direct source index')
            rules.append('.direct (' + local_hint(hint) + ')')
        elif rule[0] == 1:
            need(plan['block_rows'] is not None, 'unblocked source cannot assume exclusion')
            opposite = (-row[0], -row[1], -row[2], not row[3])
            rules.append('.block ' + full_block_hints([opposite] + inputs, blocked, rule[1]))
        else:
            need(rule[0] == 2 and rule[1], 'unproved target rule')
            indices = [i for i, w in rule[1]]
            need(all(0 <= i <= len(inputs) and w > 0 for i, w in rule[1]), 'invalid empty witness')
            terms = '[' + ','.join(f'({w},{i})' for i, w in rule[1]) + ']'
            rules.append('.impossible ⟨' + literal(indices) + ',' + terms + '⟩')
    block = 'none' if plan['block_rows'] is None else '(some ' + literal(plan['block_rows']) + ')'
    return f'{name} ({plan["source"]},{block},{record[3]}) [' + ', '.join(rules) + ']'


def batch_source(namespace, plans, records, poses, rows):
    return '''import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

''' + f'checked_blocked_batch {namespace} (N12Compact.C713Shared.dictionary) [\n' + \
        ',\n'.join('  ' + encoded_plan(p, records[(p['case'], p['ordinal'])], poses, rows) for p in plans) + ']\n'


def stage_source(case, step, domain_names, batches):
    source, neighbor, target = domain_names
    namespace = f'N12Compact.C{case}DirectPruning.Step{step:02}'
    module = f'Compact.Cases.C{case}.DirectPruning'
    imports = [module + '.' + name for name in batches]
    imports += ['Compact.Cases.C713.SharedDomains' if case == 713 else f'Compact.Preservation.C{case}']
    imports += ['Compact.Bridge.IndexedBlockedTarget']
    text = '\n'.join('import ' + name for name in imports) + f'''

namespace {namespace}
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
'''
    if case != 713: text += f'open N12Compact.Preservation.C{case}\n'
    text += '\ndef plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=\n  '
    text += ' ++ '.join(f'N12Compact.C{case}DirectPruning.{batch}.plans' for batch in batches) + '\n\n'
    proofs = [f'N12Compact.C{case}DirectPruning.{batch}.plans_checked' for batch in batches]
    text += 'theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by\n  unfold plans\n'
    if len(batches) > 1:
        text += '  simp only [List.forall_mem_append, and_assoc]\n'
    text += '  exact ' + (proofs[0] if len(proofs) == 1 else '⟨' + ', '.join(proofs) + '⟩') + '\n\n'
    text += f'''theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = {source}Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans {target}Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨{source}Ids, {neighbor}Ids, {target}Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered {source} q)
    (neighbors : OrientedPoseCovered {neighbor} t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered {target} q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end {namespace}
'''
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--pilot', action='store_true')
    args = parser.parse_args()
    need(args.run, 'coordinator serial slot and --run required')
    dest = ROOT / ('evidence/proposals/HistoricalBlockedTargets' + ('Pilot' if args.pilot else ''))
    staging = dest.with_name(dest.name + '.staging')
    need(not dest.exists() and not staging.exists(), 'refusing existing proposal')
    started, provenance = time.monotonic(), {}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 256 * 1024**2 and time.monotonic() - started < 115, '256 MiB / 115 second cap')

    def auth(path, expected=None):
        guard()
        actual = digest(path)
        need(expected is None or expected == actual, 'source hash mismatch: ' + str(path))
        provenance[str(path.relative_to(ROOT))] = actual

    def load(path, expected=None):
        auth(path, expected)
        need(path.stat().st_size < 16 * 1024**2, 'metadata size cap')
        return json.loads(path.read_text())

    def rows_from(path, expected):
        auth(path, expected)
        with path.open() as stream:
            for line in stream:
                line = line.strip().rstrip(',')
                if line not in ('[', ']', ''): yield json.loads(line)

    def stop(*_): raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    staging.mkdir(parents=True)
    try:
        audit = load(AUDIT / 'manifest.json')
        need(audit['all_plans_visited'] and audit['all_plans_supported'] and
             audit['counts']['plans'] == 9166, 'incomplete whole-target audit')
        previous = load(PREVIOUS / 'manifest.json',
                        audit['source_sha256']['evidence/proposals/HistoricalDirectPruningStages/manifest.json'])
        original_outputs = {r['path']: r['sha256'] for r in previous['outputs']}
        manifest = load(BASE / 'manifest.json',
                        audit['source_sha256']['evidence/historical-compact-data/manifest.json'])
        expected = {r['path']: r['sha256'] for r in manifest['output_files']}
        grouped = defaultdict(list)
        for plan in previous['records']: grouped[(plan['case'], plan['step'])].append(plan)
        batches = []
        for (case, step), plans in sorted(grouped.items()):
            for start in range(0, len(plans), 16):
                if args.pilot and (case != 713 or step not in (0, 1) or start): continue
                batches.append((case, step, start // 16, plans[start:start + 16]))
        selected = {(p['case'], p['ordinal']): p for *_, plans in batches for p in plans}
        wanted_poses = {p['source'] for p in selected.values()}
        wanted_poses.update(t for p in selected.values() for t in p['direct_targets'])
        poses = {p['index']: p for p in rows_from(BASE / 'poses.json', expected['poses.json'])
                 if p['index'] in wanted_poses}
        need(set(poses) == wanted_poses, 'original pose missing')
        wanted_rows = {r for p in poses.values() for r in p['rows']}
        wanted_rows.update(r for p in selected.values() for r in (p['block_rows'] or []))
        rows = {r['index']: (*r['integers'], bool(r['strict']))
                for r in rows_from(BASE / 'rows.json', expected['rows.json']) if r['index'] in wanted_rows}
        need(set(rows) == wanted_rows, 'original row missing')
        rules = {}
        auth(AUDIT / 'rules.jsonl', audit['rules_sha256'])
        with (AUDIT / 'rules.jsonl').open() as stream:
            for line in stream:
                record = json.loads(line)
                if tuple(record[:2]) in selected:
                    need(tuple(record[:2]) not in rules, 'duplicate rule')
                    rules[tuple(record[:2])] = record
        need(set(rules) == set(selected), 'missing original plan rules')
        output, count = [], 0

        def write(relative, text):
            nonlocal count
            raw = text.encode()
            count += len(raw)
            need(count < 12 * 1024**2, '12 MiB source cap')
            path = staging / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            output.append({'path': relative, 'sha256': hashlib.sha256(raw).hexdigest(),
                           'bytes': len(raw), 'lines': text.count('\n')})

        by_step = defaultdict(list)
        for case, step, batch, plans in batches:
            guard()
            name = f'Step{step:02}Batch{batch:02}'
            folder = 'BlockedTargetPilot' if args.pilot else 'DirectPruning'
            namespace = f'N12Compact.C{case}' + ('BlockedTargetPilot' if args.pilot else 'DirectPruning') + '.' + name
            write(f'Compact/Cases/C{case}/{folder}/{name}.lean', batch_source(namespace, plans, rules, poses, rows))
            by_step[(case, step)].append(name)
        if not args.pilot:
            for case in CASES:
                data = load(BASE / f'C{case}.json', expected[f'C{case}.json'])
                need(set(map(int, data['pair_steps'])) == {step for c, step in by_step if c == case}, 'missing original stage')
                for step in sorted(map(int, data['pair_steps'])):
                    domains = data['pair_steps'][str(step)]
                    need([p['source'] for p in grouped[(case, step)]] == data['domains'][domains[0]],
                         'changed original source order')
                    write(f'Compact/Cases/C{case}/DirectPruning/Step{step:02}.lean',
                          stage_source(case, step, domains, by_step[(case, step)]))
                relative = f'Compact/Cases/C{case}/DirectPruning/All.lean'
                auth(PREVIOUS / relative, original_outputs[relative])
                assembly = (PREVIOUS / relative).read_text()
                # This namespace supplied only the retired plan type. The
                # unchanged adapters use the public StepNN interfaces alone.
                assembly = assembly.replace(
                    'open S12 S12Pilot IntegerSupport DirectPruningPlan C713Shared',
                    'open S12 S12Pilot IntegerSupport C713Shared')
                write(relative, assembly)
            relative = 'Compact/HistoricalDirectPruning.lean'
            auth(PREVIOUS / relative, original_outputs[relative])
            write(relative, (PREVIOUS / relative).read_text())
        report = {'status': 'whole-target source proposal; generic and concrete Lean acceptance required',
                  'pilot_only': args.pilot, 'original_plans': len(selected),
                  'pair_stages': len(by_step), 'source_sha256': provenance,
                  'outside_branch_records': 0, 'remaining_lean_witness_searches': 0,
                  'audit_counts': audit['counts'], 'outputs': output,
                  'lean_modules': len(output), 'lean_lines': sum(r['lines'] for r in output),
                  'lean_bytes': count, 'elapsed_seconds': time.monotonic() - started}
        (staging / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        staging.rename(dest)
        print(json.dumps({key: report[key] for key in ['status', 'original_plans', 'pair_stages',
                          'lean_modules', 'lean_lines', 'lean_bytes', 'elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(staging)
        raise
    finally: signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__': main()
