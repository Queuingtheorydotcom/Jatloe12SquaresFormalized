#!/usr/bin/env python3
"""Prepare the shared-recipe C898 initial cover in a separate source namespace.

No Lean process, search, or vertex recomputation. Each owner's exact target
rows are deduplicated into a local pool selected from the existing shared row
literal; no coefficients are copied into source. Lean materializes exact base,
forbidden and automatically retained boundary rows once per recipe, checking
each cache equality. Eight-root numeric batches inspect only integer data.
One generic checked-owner constructor replaces704 semantic proof wrappers.

Explicit --run;120seconds/256MiB RSS/4MiB output. Does not change DirectInitial
or Complete, so current replay and this comparison remain independent.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json
import os
import re
import resource
import signal
import sys
import time

from build_c898_direct_initial import ROOT, OWNERS, digest, strongest_original_indices
from audit_c898_direct_cover import point_forms

DEST = ROOT / 'Compact/Cases/C898/RecipeInitial'
NS = 'N12Compact.C898RecipeInitial'


def header(imports, namespace=NS):
    return '\n'.join('import ' + module for module in imports) + f'''

/-! Generated exact target pools and shared owner recipes.
No coefficient duplication, stored arrangement vertices, or region trees.
All numeric checks and original-domain equalities remain kernel obligations. -/
namespace {namespace}
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

'''


def footer(namespace=NS):
    return f'\nend {namespace}\n'


def pool_source(name, ids):
    # One shared row reference per source line. Typed extraction produces a
    # bounded, deduplicated local table; no runtime global-dictionary lookup.
    return f'noncomputable def {name} := row_subset% N12Compact.C898Shared.rowData "\n' + \
        ',\n'.join(map(str, ids)) + '\n"\n\n'


def recipe_source(owner, angle, indices, target, positions, pool):
    selected = '[' + ', '.join(f'⟨{i}, by decide +kernel⟩' for i in indices) + ']'
    result = 'none' if target is None else '(some (poolForms ' + pool + ' [' + \
        ', '.join(str(positions[i]) for i in target['rows']) + ']))'
    return f'  ⟨⟨angle64_{angle}, angle64_{angle}_checked⟩,\n    {selected},\n    {result}⟩'


def owner_bridge(owner):
    return f'''/-- Exact full original reduced domain, including row order and angles. -/
theorem owner{owner}_leaves_shared :
    owner{owner}.leaves = C898Shared.continuousScout898Domain{owner}_0 := by
  rfl

#print axioms owner{owner}_leaves_shared
'''


def entry_source():
    ns = 'N12Compact.C898Entry'
    source = header(['Compact.Bridge.DirectOwnerFamily', 'Compact.Cases.C898.EntryPoints',
                     'Compact.Cases.C898.RecipeInitial.All'], ns)
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
    return source + footer(ns)


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
            raise RuntimeError('Recipe emitter exceeded120seconds or256MiB RSS')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .1, .1)
    paths = {name: ROOT/path for name, path in {
        'geometry': 'evidence/C898/raw/data/region898.json',
        'poses': 'evidence/c898-shared-pose-map.json',
        'angles': 'vendor/S12/AngleData.lean'}.items()}
    audit = json.loads((ROOT/'evidence/c898-direct-cover-all.json').read_text())
    hashes = {name: digest(path) for name, path in paths.items()}
    assert hashes == audit['input_sha256']
    assert audit['counts']['owner_angles'] == 704 and not audit['failures']
    assert audit['counts']['target_failures'] == audit['counts']['absent_pose_closed_nonempty'] == 0
    raw = json.loads(paths['geometry'].read_text())
    owners = {record['owner']: {key: record[key] for key in ('inside', 'outside')} for record in raw}
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
    domains = json.loads((ROOT/'evidence/c898-domain-map.json').read_text())['domains']
    audited = {(item['owner'], item['angle']): item for item in audit['cases']}
    outputs, records, counts = {}, [], Counter()
    imports = ['Compact.Bridge.DirectCachedRecipe', 'Compact.Core.RowSubsetSyntax',
               'Compact.Cases.C898.DirectInitial.Inputs', 'Compact.Cases.C898.SharedRows']
    for owner in OWNERS:
        owner_poses = [reduced[owner, angle] for angle in range(64) if (owner, angle) in reduced]
        assert [pose['index'] for pose in owner_poses] == domains[f'continuousScout898Domain{owner}_0']
        pool_ids = list(dict.fromkeys(i for pose in owner_poses for i in pose['rows']))
        positions = {row: i for i, row in enumerate(pool_ids)}
        counts['target_occurrences'] += sum(len(pose['rows']) for pose in owner_poses)
        counts['pooled_target_rows'] += len(pool_ids)
        source = header(imports) + pool_source(f'targetPool{owner}', pool_ids)
        recipes = []
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
            else:
                assert [pool_ids[positions[i]] for i in target['rows']] == target['rows']
                for i in target['rows']:
                    row = pose_map['rows'][i]
                    assert not row['strict'] or (row['integers'][0:2] == [0, 0] and row['integers'][2] > 0)
                    assert row['denominator'] > 0
            original_name = f'recipe{owner}_{angle}'
            cached_name = f'cached{owner}_{angle}'
            source += f'noncomputable def {original_name} : Recipe inside{owner} :=\n'
            source += recipe_source(owner, angle, indices, target, positions, f'targetPool{owner}') + '\n\n'
            source += f'noncomputable def {cached_name} : CachedRecipe inside{owner} outside{owner} :=\n'
            source += f'  cache_recipe%({original_name}, outside{owner})\n\n'
            recipes.append('  ' + cached_name)
            counts['recipes'] += 1
            counts['materialized_base_caches'] += 1
            counts['materialized_forbidden_caches'] += 1
            counts['materialized_active_boundary_caches'] += 1
            if owner == angle == 0:
                pilot_ids = list(dict.fromkeys(target['rows']))
                pilot_positions = {row: i for i, row in enumerate(pilot_ids)}
                pilot = header(imports) + pool_source('pilotPool', pilot_ids)
                pilot += 'noncomputable def pilotRecipe : Recipe inside0 :=\n'
                pilot += recipe_source(0, 0, indices, target, pilot_positions, 'pilotPool') + '\n\n'
                pilot += 'noncomputable def pilotCached : CachedRecipe inside0 outside0 :=\n'
                pilot += '  cache_recipe%(pilotRecipe, outside0)\n\n'
                pilot += 'theorem pilot_checked : pilotCached.Check := by decide +kernel\n'
                pilot += 'theorem pilot_root_checked : (pilotRecipe.root outside0).Check inside0 outside0 :=\n'
                pilot += '  pilotCached.checked pilot_checked\n\n#print axioms pilot_root_checked\n'
                outputs['Pilot.lean'] = pilot + footer()
        for batch in range(8):
            name = f'recipes{owner}_{batch}'
            source += f'noncomputable def {name} : List (CachedRecipe inside{owner} outside{owner}) := [\n'
            source += ',\n'.join(recipes[8*batch:8*batch+8]) + '\n]\n\n'
            source += f'theorem {name}_checked : ∀ recipe ∈ {name}, recipe.Check := by\n'
            source += '  decide +kernel\n\n'
            counts['opaque_numeric_batches'] += 1
        source += f'noncomputable def recipes{owner} : List (CachedRecipe inside{owner} outside{owner}) :=\n  '
        source += ' ++\n  '.join(f'recipes{owner}_{batch}' for batch in range(8)) + '\n\n'
        source += f'''theorem recipes{owner}_checked : ∀ recipe ∈ recipes{owner}, recipe.Check := by
  unfold recipes{owner}
  simp only [List.forall_mem_append]
  exact ⟨'''
        source += ', '.join(f'recipes{owner}_{batch}_checked' for batch in range(8)) + '⟩\n'
        source += f'''

noncomputable def owner{owner} : Owner :=
  checkedCachedOwner inside{owner} outside{owner} recipes{owner} recipes{owner}_checked

theorem owner{owner}_checked : owner{owner}.Check :=
  C898Initial.angles64_cover_kernel
'''
        outputs[f'Data{owner:02d}.lean'] = source + footer()
        outputs[f'Owner{owner:02d}.lean'] = header([
            f'Compact.Cases.C898.RecipeInitial.Data{owner:02d}',
            'Compact.Cases.C898.SharedDomains']) + owner_bridge(owner) + footer()
        records.append({'owner': owner, 'pool_original_ids': pool_ids,
                        'target_occurrences': sum(len(pose['rows']) for pose in owner_poses)})
    outputs['All.lean'] = '\n'.join(f'import Compact.Cases.C898.RecipeInitial.Owner{i:02d}' for i in OWNERS)+'\n'
    outputs['Entry.lean'] = entry_source()
    total = sum(len(source.encode()) for source in outputs.values())
    assert total < 4*1024**2 and counts['recipes'] == 704
    guard()
    DEST.mkdir(parents=True, exist_ok=True)
    temporary = []
    try:
        for name, source in outputs.items():
            path = DEST/name
            temp = path.with_suffix('.lean.tmp')
            temporary.append(temp)
            temp.write_text(source)
            os.replace(temp, path)
        report = {'scope': 'Complete shared-recipe source, not yet replayed in Lean.',
                  'input_sha256': hashes, 'counts': dict(counts), 'pools': records,
                  'generated_lean_bytes': total, 'generated_module_count': len(outputs),
                  'generated_lean_lines': sum(source.count('\n') for source in outputs.values()),
                  'files': {str((DEST/name).relative_to(ROOT)): {
                      'sha256': digest(DEST/name), 'bytes': len(source.encode()),
                      'lines': source.count('\n')} for name, source in outputs.items()},
                  'generator_sha256': digest(Path(__file__)),
                  'elapsed_seconds': time.monotonic()-started,
                  'trust': 'Target subset extraction and input/active materialization emit ordinary constructor terms. Every cache equality, automatic line exclusion, numeric batch and exact original-domain link is kernel checked.'}
        path = ROOT/'evidence/c898-recipe-initial-source.json'
        temp = path.with_suffix('.json.tmp')
        temporary.append(temp)
        temp.write_text(json.dumps(report, separators=(',', ':'))+'\n')
        os.replace(temp, path)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        for temp in temporary:
            if temp.exists():
                temp.unlink()
    print(json.dumps({key: report[key] for key in (
        'counts', 'generated_lean_bytes', 'generated_lean_lines', 'generated_module_count', 'elapsed_seconds')}))


if __name__ == '__main__':
    main()
