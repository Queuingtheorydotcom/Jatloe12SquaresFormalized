#!/usr/bin/env python3
"""Prepare one semantic record per C898 initial angle, without activation.

Writes only evidence/proposals/C898RecipeTable and its accounting manifest.
The existing original-pose bank supplies all target row IDs and coefficients;
no owner-local target pools or per-root semantic wrappers are duplicated.
All 704 angle roots (including 74 empty roots) retain separate checked caches
and numeric theorem commands, with eight records per independent module.
The checked_recipe command supplies the reusable declaration scaffolding;
it still invokes ordinary kernel checking separately for every root. Each owner's small
assembly preserves the same original domain and coverage API.
No Lean/search/network subprocess is run.
Parent serial slot only: --run, 120 seconds, 256 MiB RSS, 4 MiB output.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json
import re
import resource
import signal
import sys
import time

from build_c898_direct_initial import ROOT, OWNERS, digest, strongest_original_indices
from audit_c898_direct_cover import point_forms

DEST = ROOT / 'evidence/proposals/C898RecipeTable'
NS = 'N12Compact.C898RecipeInitial'


def header(imports, namespace=NS):
    return '\n'.join('import ' + name for name in imports) + f'''

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace {namespace}
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

'''


def footer(namespace=NS):
    return f'\nend {namespace}\n'


def bank_source():
    return header(['Compact.Bridge.DirectRecipeDictionary',
                   'Compact.Cases.C898.SharedDictionary',
                   'Compact.Cases.C898.DirectInitial.Inputs']) + '''
noncomputable def bank : DirectRecipeTable.Bank 64 C898Shared.poseCount :=
  DirectRecipeTable.Bank.ofDictionary C898Shared.dictionary C898Shared.positive_denominators

theorem bank_pose (i : Fin C898Shared.poseCount) : bank.poses i = C898Shared.poses i :=
  C898Shared.dictionary_pose i
''' + footer()


def batch_source(owner, batch, records):
    name = f'entries{owner}_{batch}'
    source = '/-- Each record creates its own named cache and kernel-checked theorem. -/\n'
    names = []
    for record in records:
        target = 'none' if record['target'] is None else 'some ' + str(record['target'])
        indices = ', '.join(map(str, record['input_indices']))
        entry = f'entry{owner}_{record["angle"]}'
        names.append(entry)
        source += f'checked_recipe {entry} (bank, inside{owner}, outside{owner}) := '
        source += f'⟨{record["angle"]}, [{indices}], {target}⟩\n'
    source += '\n'
    source += f'noncomputable def {name} : List (DirectRecipeTable.Entry bank inside{owner} outside{owner}) :=\n'
    source += '  [' + ', '.join(names) + ']\n\n'
    source += f'theorem {name}_literal_checked :\n'
    source += f'    ∀ entry ∈ {name}, DirectRecipeCheck.LiteralCheck entry := by\n'
    source += f'  simp only [{name}, List.forall_mem_cons]\n'
    proofs = [entry + '_literal_checked' for entry in names]
    source += '  exact ⟨' + ', '.join(proofs + ['by simp']) + '⟩\n\n'
    source += f'theorem {name}_checked : ∀ entry ∈ {name}, entry.Check :=\n'
    source += f'  DirectRecipeCheck.all_checked {name} {name}_literal_checked\n\n'
    return source


def owner_source(owner, records):
    source = header([f'Compact.Cases.C898.RecipeInitial.Batch{owner:02d}_{batch:02d}'
                     for batch in range(8)])
    source += f'noncomputable def entries{owner} : List (DirectRecipeTable.Entry bank inside{owner} outside{owner}) :=\n  '
    source += ' ++\n  '.join(f'entries{owner}_{batch}' for batch in range(8)) + '\n\n'
    source += f'''theorem entries{owner}_checked : ∀ entry ∈ entries{owner}, entry.Check := by
  unfold entries{owner}
  simp only [List.forall_mem_append]
  exact ⟨'''
    source += ', '.join(f'entries{owner}_{batch}_checked' for batch in range(8)) + '⟩\n\n'
    source += f'''noncomputable def owner{owner} : Owner :=
  DirectRecipeTable.checkedOwner bank inside{owner} outside{owner} entries{owner} entries{owner}_checked

theorem owner{owner}_checked : owner{owner}.Check :=
  DirectRecipeTable.checkedOwner_check bank inside{owner} outside{owner}
    entries{owner} entries{owner}_checked C898Initial.angles64_cover_kernel
'''
    return source + footer()


def owner_bridge(owner):
    return header([f'Compact.Cases.C898.RecipeInitial.Data{owner:02d}',
                   'Compact.Cases.C898.SharedDomains']) + f'''
/-- Equality to the complete original reduced domain, including empty roots. -/
theorem owner{owner}_leaves_shared :
    owner{owner}.leaves = C898Shared.continuousScout898Domain{owner}_0 := by
  unfold owner{owner}
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

#print axioms owner{owner}_leaves_shared
''' + footer()


def entry_source():
    namespace = 'N12Compact.C898Entry'
    source = header(['Compact.Bridge.DirectOwnerFamily', 'Compact.Cases.C898.EntryPoints',
                     'Compact.Cases.C898.RecipeInitial.All'], namespace)
    source += 'open C898RecipeInitial\n\n'
    for owner, mask in OWNERS.items():
        source += f'''theorem owner{owner}_premises_checked :
    PointPremises.Check case898Domain{owner} commonPoints898 inside{owner} outside{owner} := by
  decide +kernel

noncomputable def owner{owner}_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain{owner}, owner{owner}, owner{owner}_checked, owner{owner}_premises_checked,
   C898Shared.continuousScout898Domain{owner}_0, owner{owner}_leaves_shared⟩

theorem owner{owner}_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain{owner}_0
      (p.square (ownerIndex p {mask})) :=
  owner{owner}_entry.sound p hf

'''
    return source + footer(namespace)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('Prepared only; --run requires the parent serial slot.')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic() - started > 120 or rss > 256*1024**2:
            raise RuntimeError('Spec emitter exceeded 120 seconds or 256 MiB RSS')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .1, .1)
    paths = {name: ROOT/path for name, path in {
        'geometry': 'evidence/C898/raw/data/region898.json',
        'poses': 'evidence/c898-shared-pose-map.json',
        'angles': 'vendor/S12/AngleData.lean'}.items()}
    audit_path = ROOT/'evidence/c898-direct-cover-all.json'
    audit = json.loads(audit_path.read_text())
    hashes = {name: digest(path) for name, path in paths.items()}
    assert hashes == audit['input_sha256']
    assert audit['counts']['owner_angles'] == 704 and not audit['failures']
    assert audit['counts']['target_failures'] == audit['counts']['absent_pose_closed_nonempty'] == 0
    raw = json.loads(paths['geometry'].read_text())
    owners = {r['owner']: {k: r[k] for k in ('inside', 'outside')} for r in raw}
    del raw
    assert set(owners) == set(OWNERS)
    angles = {int(i): [Q(x.strip().strip('()')) for x in values.split(',')]
              for i, values in re.findall(r'def angle64_(\d+) : AngleEnclosure := ⟨([^⟩]+)⟩',
                                          paths['angles'].read_text())}
    assert set(angles) == set(range(64))
    pose_map = json.loads(paths['poses'].read_text())
    reduced = {}
    for pose in pose_map['poses']:
        matched = re.fullmatch(r'continuousScout898Initial(\d+)_(\d+)', pose['name'])
        if matched:
            key = int(matched[1]), pose['angle']
            assert key not in reduced
            reduced[key] = pose
    assert len(reduced) == 630
    domain_path = ROOT/'evidence/c898-domain-map.json'
    domains = json.loads(domain_path.read_text())['domains']
    audited = {(item['owner'], item['angle']): item for item in audit['cases']}
    outputs, all_records, counts = {'Bank.lean': bank_source()}, [], Counter()
    for owner in OWNERS:
        records = []
        for angle in range(64):
            _, _, c, s, outer, _, wall = angles[angle]
            original = [row for point in owners[owner]['inside']
                        for row in point_forms(c, s, Q(1001, 1000)*outer, point)]
            wall_start = len(original)
            original += [(Q(1), Q(0), -wall/2), (Q(-1), Q(0), 4-wall/2),
                         (Q(0), Q(1), -wall/2), (Q(0), Q(-1), 4-wall/2)]
            indices = strongest_original_indices(original)
            assert len(indices) == 8 and all(i in indices for i in range(wall_start, wall_start+4))
            target = reduced.get((owner, angle))
            old = audited[owner, angle]
            assert old['target_pose'] == (None if target is None else target['name'])
            if target is None:
                assert old['closed_empty']
                counts['empty_angles'] += 1
            else:
                assert target['angle'] == angle
                for index in target['rows']:
                    row = pose_map['rows'][index]
                    assert row['denominator'] > 0
                    assert not row['strict'] or (row['integers'][:2] == [0, 0] and row['integers'][2] > 0)
                counts['target_angles'] += 1
            records.append({'owner': owner, 'angle': angle, 'input_indices': indices,
                            'target': None if target is None else target['index']})
        assert [r['target'] for r in records if r['target'] is not None] == domains[f'continuousScout898Domain{owner}_0']
        all_records.extend(records)
        for batch in range(8):
            source = header(['Compact.Cases.C898.RecipeInitial.Bank',
                             'Compact.Bridge.CheckedRecipeCommand'])
            source += batch_source(owner, batch, records[8*batch:8*batch+8])
            outputs[f'Batch{owner:02d}_{batch:02d}.lean'] = source + footer()
        outputs[f'Data{owner:02d}.lean'] = owner_source(owner, records)
        outputs[f'Owner{owner:02d}.lean'] = owner_bridge(owner)
    # A real single-root instance uses exactly the same representation.
    pilot = header(['Compact.Cases.C898.RecipeInitial.Bank',
                    'Compact.Bridge.CheckedRecipeCommand'])
    pilot += batch_source(0, 0, all_records[:1])
    pilot += '#print axioms entries0_0_checked\n'
    outputs['Pilot.lean'] = pilot + footer()
    outputs['All.lean'] = '\n'.join(f'import Compact.Cases.C898.RecipeInitial.Owner{i:02d}' for i in OWNERS)+'\n'
    outputs['Entry.lean'] = entry_source()
    assert len(all_records) == 704 and counts == {'empty_angles': 74, 'target_angles': 630}
    # Refactoring the declaration mechanism must not alter any original root,
    # selected premise index, optional target or root order.
    report_path = ROOT/'evidence/c898-spec-initial-proposal.json'
    previous_sha256 = None
    if report_path.exists():
        previous = json.loads(report_path.read_text())
        assert previous['semantic_records'] == 704
        assert previous['records'] == all_records
        previous_sha256 = digest(report_path)
    total = sum(len(source.encode()) for source in outputs.values())
    assert total < 4*1024**2
    guard()
    DEST.mkdir(parents=True, exist_ok=True)
    temporaries = []
    try:
        for name, source in outputs.items():
            temporary = (DEST/name).with_suffix('.lean.tmp')
            temporaries.append(temporary)
            temporary.write_text(source)
        for name, temporary in zip(outputs, temporaries):
            temporary.replace(DEST/name)
    finally:
        for temporary in temporaries:
            temporary.unlink(missing_ok=True)
    report = {'scope': 'Proposal only. Complete original C898 initial obligations; ordinary Lean checks pending.',
              'proposal_directory': str(DEST.relative_to(ROOT)), 'production_namespace': NS,
              'semantic_records': 704, 'numeric_batches': 88,
              'numeric_declaration_strategy': 'checked_recipe: separate named Entry and ordinary kernel theorem per record',
              'previous_identical_records_report_sha256': previous_sha256,
              'active_source_sha256': {name: digest(ROOT/'Compact/Cases/C898/RecipeInitial'/name)
                  if (ROOT/'Compact/Cases/C898/RecipeInitial'/name).exists() else None
                  for name in outputs},
              'maximum_roots_per_numeric_module': 8, **dict(counts),
              'lean_modules': len(outputs), 'lean_bytes': total,
              'lean_lines': sum(source.count('\n') for source in outputs.values()),
              'serialized_target_rows': 0, 'owner_target_pool_ids': 0,
              'records': all_records, 'input_sha256': hashes,
              'audit_sha256': digest(audit_path), 'domains_sha256': digest(domain_path),
              'outputs': [{'path': str((DEST/name).relative_to(ROOT)), 'sha256': digest(DEST/name),
                           'lines': source.count('\n'), 'bytes': len(source.encode())}
                          for name, source in outputs.items()],
              'seconds': time.monotonic() - started,
              'activation': 'Parent must check generic modules and pilot before replacing RecipeInitial. No active source was modified.'}
    report_path.write_text(json.dumps(report, indent=2)+'\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({k: report[k] for k in ('semantic_records', 'numeric_batches', 'empty_angles',
        'target_angles', 'lean_modules', 'lean_lines', 'lean_bytes', 'serialized_target_rows', 'seconds')}, indent=2))


if __name__ == '__main__':
    main()
