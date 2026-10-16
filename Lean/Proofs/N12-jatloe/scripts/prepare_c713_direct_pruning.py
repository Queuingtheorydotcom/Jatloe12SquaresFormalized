#!/usr/bin/env python3
"""Prepare all nine original C713 pair routes without intermediate raw poses.

Parent-only serial256MiB/120second slot. Consumes the completed authenticated
whole-outside-context audit; emits original source/block/final-target recipes,
ordinary per-plan kernel checks, and full source/neighbor/target adapters.
The only outstanding semantic premise in each stage is actual overlap for
the excluded blocks. No pair certificate is claimed or manufactured here.
Outputs an atomic <=4MiB proposal, never modifies active Lean or runs Lean.
"""
from collections import defaultdict
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
AUDIT = ROOT / 'evidence/historical-outside-coverage'
DEST = ROOT / 'evidence/proposals/C713DirectPruning'
NS = 'N12Compact.C713DirectPruning'
PREFIX = 'Compact/Cases/C713/DirectPruning'
MODULE = 'Compact.Cases.C713.DirectPruning'


def need(test, message):
    if not test:
        raise ValueError(message)


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            value.update(block)
    return value.hexdigest()


def literal(values):
    return '[' + ','.join(map(str, values)) + ']'


def header(imports, namespace):
    return '\n'.join('import ' + module for module in imports) + f'''

namespace {namespace}
open S12 S12Pilot IntegerSupport DirectPruningPlan C713Shared
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

'''


def footer(namespace):
    return '\nend\nend ' + namespace + '\n'


def batch_source(namespace, plans):
    source = header(['Compact.Bridge.DirectPruningSyntax',
                     'Compact.Cases.C713.SharedDictionary'], namespace)
    for plan in plans:
        block = 'none' if plan['block_rows'] is None else '(some ' + literal(plan['block_rows']) + ')'
        source += f'checked_direct_plan plan{plan["ordinal"]} (dictionary,{plan["source"]},{block})'
        source += literal(plan['direct_targets']) + '\n'
    source += '\ndef plans : List (Plan HistoricalData.rowCount HistoricalData.poseCount) :=\n  '
    source += '[' + ','.join('plan' + str(plan['ordinal']) for plan in plans) + ']\n\n'
    source += '''theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  simp only [plans, List.forall_mem_cons]
  exact ⟨''' + ', '.join('plan' + str(plan['ordinal']) + '_checked' for plan in plans)
    source += ', by simp⟩\n'
    return source + footer(namespace)


def stage_source(step, names, batch_names, case=713, shared_stage=False):
    case_namespace = f'N12Compact.C{case}DirectPruning'
    case_module = f'Compact.Cases.C{case}.DirectPruning'
    namespace = case_namespace + f'.Step{step:02}'
    source_name, neighbor_name, target_name = names
    domain_module = 'Compact.Cases.C713.SharedDomains' if case == 713 else f'Compact.Preservation.C{case}'
    imports = [case_module + '.' + name for name in batch_names] + [domain_module,
        'Compact.Bridge.DirectPruningStage']
    source = header(imports, namespace)
    if case != 713:
        source += f'open N12Compact.Preservation.C{case}\n\n'
    source += 'def plans : List (Plan HistoricalData.rowCount HistoricalData.poseCount) :=\n  '
    source += ' ++ '.join(case_namespace + '.' + name + '.plans' for name in batch_names) + '\n\n'
    source += 'theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by\n'
    source += '  unfold plans\n'
    if len(batch_names) > 1:
        source += '  simp only [List.forall_mem_append, and_assoc]\n'
    source += '  exact '
    proofs = [case_namespace + '.' + name + '.plans_checked' for name in batch_names]
    source += (proofs[0] if len(proofs) == 1 else '⟨' + ', '.join(proofs) + '⟩') + '\n\n'
    source += f'''theorem source_ids : plans.map Plan.source = {source_name}Ids := by
  decide +kernel

theorem target_members : ∀ plan ∈ plans, ∀ target ∈ plan.targets,
    target ∈ {target_name}Ids := by
  exact DirectPruningStage.target_members_of_values _ _ (by decide +kernel)

theorem covers : CoverCheck {source_name}Ids {target_name}Ids plans :=
  cover_of_source_map _ _ _ source_ids target_members

'''
    if shared_stage:
        source += f'''def stage : DirectPruningStage.Stage dictionary :=
  ⟨{source_name}Ids, {neighbor_name}Ids, {target_name}Ids, plans⟩

theorem stage_checked : stage.Check := ⟨covers, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered {source_name} q)
    (neighbors : OrientedPoseCovered {neighbor_name} t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered {target_name} q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
'''
        return source + footer(namespace)
    source += f'''
/-- The sole unfinished numerical premise: every actual blocked source pose
overlaps the actual neighbor square, using its complete original cover. -/
def BlockOverlap : Prop :=
  ∀ plan ∈ plans, ∀ q t : OpenSquare,
    (dictionary.pose plan.source).OrientedRealizes q →
    OrientedPoseCovered {neighbor_name} t →
    ∀ block, plan.block = some block →
      (∀ i ∈ block, (dictionary.rows i).Holds ![centerX q,centerY q]) →
      ∃ x y, q.Inside x y ∧ t.Inside x y

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered {source_name} q)
    (neighbors : OrientedPoseCovered {neighbor_name} t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered {target_name} q := by
  apply DirectPruningPlan.cover_sound dictionary HistoricalData.positive_denominators
    {source_name}Ids {target_name}Ids plans covers plans_checked q incoming
  intro plan member realizes block blocked holds
  obtain ⟨x,y,inside⟩ := overlap plan member q t realizes neighbors block blocked holds
  exact disjoint x y inside

#print axioms step_sound
'''
    return source + footer(namespace)


def assembly_source(steps):
    source = header([MODULE + f'.Step{step:02}' for step in steps] +
                    ['Compact.Cases.C713.Assembly'], NS)
    source += '/-- Exactly the nine original pair-block overlap families remain. -/\n'
    source += 'structure BlockOverlaps : Prop where\n'
    source += ''.join(f'  step{step} : Step{step:02}.BlockOverlap\n' for step in steps)
    source += '\ntheorem pair_stages (checked : BlockOverlaps) : C713Assembly.PairStages :=\n  {\n'
    source += ''.join(f'    step{step} := Step{step:02}.step_sound checked.step{step}\n' for step in steps)
    source += '  }\n\n'
    source += '''/-- Conditional original-packing conclusion. This does not supply the
remaining block-overlap fields or assert an unconditional case exclusion. -/
theorem family_impossible_of_block_overlaps (checked : BlockOverlaps)
    (p : NormalizedPacking) (family : codedMarkerFamily p = case713Family) : False :=
  C713Assembly.family_impossible_of_pair_stages (pair_stages checked) p family

#print axioms family_impossible_of_block_overlaps
'''
    return source + footer(NS)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    need(parser.parse_args().run, 'parent serial slot and --run required')
    stage = DEST.with_name(DEST.name + '.staging')
    need(not DEST.exists() and not stage.exists(), 'refusing existing proposal')
    started = time.monotonic()
    hashes = {}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 256 * 1024**2 and time.monotonic() - started < 114, '256MiB/114second limit')

    def stop(*_):
        raise RuntimeError('termination requested')

    def load(path, expected=None):
        guard()
        actual = digest(path)
        need(expected is None or expected == actual, 'input hash differs: ' + str(path))
        hashes[str(path.relative_to(ROOT))] = actual
        need(path.stat().st_size < 16 * 1024**2, 'metadata load limit')
        return json.loads(path.read_text())

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    stage.mkdir(parents=True)
    try:
        audit = load(AUDIT / 'manifest.json')
        need(audit['all_outside_contexts_visited'] and audit['all_retained_links_visited'], 'partial audit')
        need(audit['counts'].get('unsupported_branches', 0) == 0 and
             audit['counts'].get('unsupported_retained_links', 0) == 0, 'unresolved audit')
        need(audit['counts']['pair_stages'] == 113 and audit['counts']['outside_branches'] == 16896,
             'unexpected historical scope')
        manifest = load(BASE / 'manifest.json', audit['input_sha256']['evidence/historical-compact-data/manifest.json'])
        expected = {item['path']: item['sha256'] for item in manifest['output_files']}
        data = load(BASE / 'C713.json', expected['C713.json'])
        blocks = load(BASE / 'blocks.json', expected['blocks.json'])
        branch_path = AUDIT / 'branches.jsonl'
        need(digest(branch_path) == audit['branches_sha256'], 'branch audit changed')
        hashes[str(branch_path.relative_to(ROOT))] = audit['branches_sha256']
        choices = {}
        with branch_path.open() as stream:
            for line in stream:
                record = json.loads(line)
                if record[0] == 713:
                    need(record[3] == 0, 'unsupported or closed branch requires explicit adapter')
                    key = (record[1], record[2])
                    need(key not in choices, 'duplicate audited context')
                    choices[key] = record[4]
        need(len(data['plans']) == 1037 and len(choices) == 1620, 'C713 audit scope differs')
        by_step, records, used = defaultdict(list), [], set()
        for ordinal, plan in enumerate(data['plans']):
            guard()
            block = None if plan['block'] is None else blocks[plan['block']]['rows']
            count = 1 if block is None else len(block)
            targets = []
            for face in range(count):
                key = (ordinal, face)
                need(key in choices, 'missing original first-failed-face context')
                target = choices[key]
                need(target in plan['targets'], 'audited target outside original plan')
                targets.append(target)
                used.add(key)
            if not plan['pieces']:
                need(block == [], 'zero-piece plan has an unexplained nonempty outside branch')
            record = {'ordinal': ordinal, 'step': plan['step'], 'name': plan['name'],
                'source': plan['source'], 'block': plan['block'], 'block_rows': block,
                'direct_targets': targets, 'historical_origin': plan['origin']}
            records.append(record)
            by_step[plan['step']].append(record)
        need(used == set(choices), 'unused audited branch')
        steps = sorted(by_step)
        need(steps == [0,1,2,3,4,6,7,8,9], 'changed C713 stage graph')
        outputs = {}
        # Four representative genuine plans, then four more; include an empty
        # blocked conjunction and nonempty block, not only cheap unblocked ones.
        pilot = []
        for predicate in (lambda p:p['block_rows'] is None,
                          lambda p:p['block_rows'] == [],
                          lambda p:bool(p['block_rows']),
                          lambda p:len(p['direct_targets']) > 1):
            found = next((p for p in records if predicate(p) and p not in pilot), None)
            if found is not None:
                pilot.append(found)
        pilot += [p for p in records if p not in pilot][:8-len(pilot)]
        outputs[PREFIX + '/Pilot.lean'] = batch_source(NS + '.Pilot', pilot)
        for step in steps:
            names = data['pair_steps'][str(step)]
            need([p['source'] for p in by_step[step]] == data['domains'][names[0]], 'source-order coverage differs')
            batches = []
            for number, start in enumerate(range(0, len(by_step[step]), 16)):
                name = f'Step{step:02}Batch{number:02}'
                batches.append(name)
                outputs[PREFIX + '/' + name + '.lean'] = batch_source(NS + '.' + name, by_step[step][start:start+16])
            outputs[PREFIX + f'/Step{step:02}.lean'] = stage_source(step, names, batches)
        outputs[PREFIX + '/All.lean'] = assembly_source(steps)
        total = sum(len(text.encode()) for text in outputs.values())
        need(total < 4 * 1024**2, 'source proposal exceeds4MiB')
        for relative, text in outputs.items():
            path = stage / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        result = {'status': 'complete source proposal; Lean plan and stage replay pending',
            'case': 713, 'pair_stages': len(steps), 'original_plans': len(records),
            'direct_outside_contexts': len(choices), 'empty_block_conjunction_plans':
                sum(p['block_rows'] == [] for p in records),
            'intermediate_raw_pose_references': 0, 'separate_relaxation_links': 0,
            'remaining_semantic_premise': 'Actual blocked-source/complete-neighbor overlap, exactly nine original stage families.',
            'input_sha256': hashes, 'pilot_original_plan_ordinals': [p['ordinal'] for p in pilot],
            'lean_modules': len(outputs), 'lean_lines': sum(s.count('\n') for s in outputs.values()),
            'lean_bytes': total, 'maximum_plans_per_module': 16,
            'outputs': [{'path': name, 'sha256': hashlib.sha256(source.encode()).hexdigest(),
                         'lines': source.count('\n'), 'bytes': len(source.encode())}
                        for name, source in outputs.items()],
            'records': records, 'elapsed_seconds': time.monotonic() - started}
        (stage / 'manifest.json').write_text(json.dumps(result, indent=2) + '\n')
        need(sum(p.stat().st_size for p in stage.rglob('*') if p.is_file()) < 4 * 1024**2,
             'total proposal exceeds4MiB')
        stage.rename(DEST)
        print(json.dumps({k:result[k] for k in ['status','pair_stages','original_plans',
            'direct_outside_contexts','lean_modules','lean_lines','lean_bytes','elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
