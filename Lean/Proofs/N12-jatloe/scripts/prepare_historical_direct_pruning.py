#!/usr/bin/env python3
"""Prepare all113 exact pair-stage bindings, without activating any source.

Consumes the authenticated complete outside-context audit. All9,166 original
plans retain their original source, block, final targets, and stage graph;
all16,896 contexts are checked independently by ordinary Lean Plan.Check.
Five case adapters retain exactly their original entrance/chord obligations.
C713 uses its completed occupied-row height route. Actual block overlaps
remain explicit until the common-point/fallback certificates discharge them.
Parent-only256MiB/120second slot; atomic8MiB proposal; no compiler/subprocess.
"""
from collections import defaultdict
from pathlib import Path
import argparse, hashlib, json, re, resource, shutil, signal, sys, time

from prepare_c713_direct_pruning import (
    ROOT, BASE, AUDIT, need, digest, header, footer, batch_source,
    stage_source, assembly_source,
)

CASES = (701, 713, 717, 973, 978, 979)
DEST = ROOT / 'evidence/proposals/HistoricalDirectPruning'


def original_fields(text):
    block = re.search(r'^structure Pending : Prop where\n(.*?)(?=^theorem family_impossible)',
                      text, re.M | re.S)
    need(block is not None, 'original Pending interface absent')
    clean = re.sub(r'/\-.*?\-/', '', block[1], flags=re.S)
    fields = re.findall(r'^  (\w+) : (.*?)(?=^  \w+ :|\Z)', clean, re.M | re.S)
    need(fields and len(dict(fields)) == len(fields), 'ambiguous Pending fields')
    return [(name, body.rstrip()) for name, body in fields]


def case_assembly(case, data, preservation, owners):
    namespace = f'N12Compact.C{case}DirectPruning'
    module = f'Compact.Cases.C{case}.DirectPruning'
    steps = sorted(map(int, data['pair_steps']))
    if case == 713:
        return assembly_source(steps)
    fields = original_fields(preservation)
    pair_fields = {'step' + str(step) for step in steps}
    need(pair_fields <= {name for name, _ in fields}, 'missing original pair field')
    remaining = [(name, body) for name, body in fields if name not in pair_fields]
    source = header([module + f'.Step{step:02}' for step in steps] +
                    [f'Compact.Preservation.C{case}'], namespace)
    source += f'open N12Compact.Preservation.C{case} S12Completion\n\n'
    source += 'structure BlockOverlaps : Prop where\n'
    source += ''.join(f'  step{step} : Step{step:02}.BlockOverlap\n' for step in steps)
    source += '\n/-- Only the unchanged original entrance and chord obligations. -/\n'
    source += 'structure Remaining : Prop where\n'
    source += ''.join(f'  {name} : {body}\n' for name, body in remaining)
    source += '''
private theorem owner_disjoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (a b : Nat)
    (ha : a ∈ family) (hb : b ∈ family) (distinct : a ≠ b) :
    ∀ x y, ¬((p.square (ownerIndex p a)).Inside x y ∧
      (p.square (ownerIndex p b)).Inside x y) := by
  apply p.disjoint
  intro equal
  apply distinct
  have left := ownerIndex_spec p a (by rw [hf]; exact ha)
  have right := ownerIndex_spec p b (by rw [hf]; exact hb)
  exact left.symm.trans ((congrArg (markerCode p) equal).trans right)

'''
    source += f'''theorem pending_of_block_overlaps (checked : BlockOverlaps)
    (remaining : Remaining) : N12Compact.Preservation.C{case}.Pending := by
  refine {{
'''
    for name, body in fields:
        if name not in pair_fields:
            source += f'    {name} := remaining.{name}\n'
            continue
        step = int(name[4:])
        names = data['pair_steps'][str(step)]
        declarations = re.findall(r'OrientedPoseCovered (\w+)', body)
        masks = list(map(int, re.findall(r'ownerIndex p (\d+)', body)))
        need(declarations == names and len(masks) == 3 and masks[0] == masks[2],
             'pair contract differs from exact original stage')
        owner_numbers = [int(re.fullmatch(fr'continuousScout{case}Domain(\d+)_\d+', name)[1]) for name in names]
        need(masks == [owners[str(owner)] for owner in owner_numbers], 'original owner binding differs')
        left, right = masks[:2]
        need(left != right, 'pair stage has identical actual owners')
        source += f'''    {name} := by
      intro p hf incoming neighbors
      exact Step{step:02}.step_sound checked.{name}
        (p.square (ownerIndex p {left})) (p.square (ownerIndex p {right})) incoming neighbors
        (owner_disjoint p hf {left} {right}
          (by decide +kernel) (by decide +kernel) (by decide))
'''
    source += '  }\n\n'
    source += f'''/-- Conditional original-case conclusion. No remaining overlap, entrance,
or chord field is declared true by this adapter. -/
theorem excludes_case_of_remaining (checked : BlockOverlaps) (remaining : Remaining) :
    ExcludesCase {case} :=
  N12Compact.Preservation.C{case}.excludes_case (pending_of_block_overlaps checked remaining)

#print axioms excludes_case_of_remaining
'''
    return source + footer(namespace)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--shared-stage', action='store_true',
                        help='factor the113 logical composition proofs through one generic theorem')
    args = parser.parse_args()
    need(args.run, 'parent serial slot and --run required')
    destination = DEST.with_name('HistoricalDirectPruningStages') if args.shared_stage else DEST
    stage = destination.with_name(destination.name + '.staging')
    need(not destination.exists() and not stage.exists(), 'refusing existing proposal')
    started, hashes = time.monotonic(), {}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 256 * 1024**2 and time.monotonic() - started < 114, '256MiB/114second limit')

    def stop(*_):
        raise RuntimeError('termination requested')

    def read(path, expected=None, parse=True):
        guard()
        actual = digest(path)
        need(expected is None or actual == expected, 'source hash mismatch: ' + str(path))
        hashes[str(path.relative_to(ROOT))] = actual
        need(path.stat().st_size < 16 * 1024**2, 'bounded metadata read exceeded')
        raw = path.read_text()
        return json.loads(raw) if parse else raw

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    stage.mkdir(parents=True)
    try:
        audit = read(AUDIT / 'manifest.json')
        need(audit['all_outside_contexts_visited'] and audit['all_retained_links_visited'], 'partial audit')
        counts = audit['counts']
        need(counts.get('unsupported_branches', 0) == 0 and counts.get('unsupported_retained_links', 0) == 0,
             'unresolved audited branch or link')
        need((counts['pair_stages'], counts['plans'], counts['outside_branches']) == (113,9166,16896),
             'unexpected historical scope')
        manifest = read(BASE / 'manifest.json', audit['input_sha256']['evidence/historical-compact-data/manifest.json'])
        expected = {entry['path']:entry['sha256'] for entry in manifest['output_files']}
        blocks = read(BASE / 'blocks.json', expected['blocks.json'])
        angles = read(ROOT / 'evidence/historical-direct-cover-audit.json')
        owners = {case['case']:case['owner_masks'] for case in angles['cases']}
        branches = AUDIT / 'branches.jsonl'
        need(digest(branches) == audit['branches_sha256'], 'branch evidence hash mismatch')
        hashes[str(branches.relative_to(ROOT))] = audit['branches_sha256']
        choices = {}
        with branches.open() as stream:
            for line in stream:
                record = json.loads(line)
                need(record[0] in CASES and record[3] == 0, 'unsupported branch outcome')
                key = tuple(record[:3])
                need(key not in choices, 'duplicate audited original context')
                choices[key] = record[4]
        need(len(choices) == 16896, 'branch coverage truncated')
        used, outputs, records, summaries = set(), {}, [], []
        for case in CASES:
            data = read(BASE / f'C{case}.json', expected[f'C{case}.json'])
            preservation = read(ROOT / f'Compact/Preservation/C{case}.lean', parse=False)
            namespace = f'N12Compact.C{case}DirectPruning'
            prefix = f'Compact/Cases/C{case}/DirectPruning'
            by_step, local_records = defaultdict(list), []
            for ordinal, plan in enumerate(data['plans']):
                guard()
                block = None if plan['block'] is None else blocks[plan['block']]['rows']
                expected_faces = 1 if block is None else len(block)
                targets = []
                for face in range(expected_faces):
                    key = (case, ordinal, face)
                    need(key in choices, 'missing original outside context')
                    target = choices[key]
                    need(target in plan['targets'], 'audited target outside original plan')
                    used.add(key)
                    targets.append(target)
                if not plan['pieces']:
                    need(block == [], 'unexplained zero-piece branch')
                item = {'case':case,'ordinal':ordinal,'step':plan['step'],'name':plan['name'],
                        'source':plan['source'],'block':plan['block'],'block_rows':block,
                        'direct_targets':targets,'historical_origin':plan['origin']}
                by_step[plan['step']].append(item)
                local_records.append(item)
            need(set(by_step) == set(map(int,data['pair_steps'])), 'pair-stage coverage differs')
            for step in sorted(by_step):
                names = data['pair_steps'][str(step)]
                need([p['source'] for p in by_step[step]] == data['domains'][names[0]], 'original source order differs')
                batch_names = []
                for number, start in enumerate(range(0,len(by_step[step]),16)):
                    name = f'Step{step:02}Batch{number:02}'
                    batch_names.append(name)
                    outputs[prefix+'/'+name+'.lean'] = batch_source(namespace+'.'+name,by_step[step][start:start+16])
                outputs[prefix+f'/Step{step:02}.lean'] = stage_source(step,names,batch_names,case,args.shared_stage)
            outputs[prefix+'/All.lean'] = case_assembly(case,data,preservation,owners[case])
            records.extend(local_records)
            summaries.append({'case':case,'pair_stages':len(by_step),'plans':len(local_records),
                'outside_contexts':sum(len(p['direct_targets']) for p in local_records),
                'empty_block_conjunction_plans':sum(p['block_rows']==[] for p in local_records)})
        need(used == set(choices), 'unused original branch certificate')
        need(sum(s['pair_stages'] for s in summaries)==113 and len(records)==9166, 'incomplete full-stage emission')
        outputs['Compact/HistoricalDirectPruning.lean'] = '\n'.join(
            f'import Compact.Cases.C{case}.DirectPruning.All' for case in CASES) + '\n\n' + \
            '/-! All original historical pair-stage adapters; actual overlap, entrance,\n' + \
            'and remaining chord obligations are explicit. No unconditional case claim. -/\n'
        total = sum(len(value.encode()) for value in outputs.values())
        need(total < 8 * 1024**2, 'source output exceeds8MiB')
        for name, source in outputs.items():
            path = stage/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(source)
        report = {'status':'full113-stage source proposal; no activation or Lean acceptance',
            'shared_stage_theorem': args.shared_stage,
            'scope':list(CASES),'pair_stages':113,'original_plans':len(records),'direct_outside_contexts':len(choices),
            'cases':summaries,'intermediate_raw_pose_references':0,'separate_pair_relaxation_links':0,
            'remaining':'Actual common-point/fallback block overlaps; original entrance covers;20 original chord stages. C713 height is independently accepted.',
            'input_sha256':hashes,'maximum_plans_per_module':16,'lean_modules':len(outputs),
            'lean_lines':sum(source.count('\n') for source in outputs.values()),'lean_bytes':total,
            'outputs':[{'path':name,'sha256':hashlib.sha256(source.encode()).hexdigest(),
                'bytes':len(source.encode()),'lines':source.count('\n')} for name,source in outputs.items()],
            'records':records,'elapsed_seconds':time.monotonic()-started}
        (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        need(sum(p.stat().st_size for p in stage.rglob('*') if p.is_file()) < 8*1024**2,
             'complete proposal exceeds8MiB')
        stage.rename(destination)
        print(json.dumps({key:report[key] for key in ['status','pair_stages','original_plans',
            'direct_outside_contexts','lean_modules','lean_lines','lean_bytes','elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':
    main()
