#!/usr/bin/env python3
"""Prepare concise whole C898 pair-stage source using checked common points.

Parent-only --run,192MiB/120seconds,<=32MiB isolated output. No Lean, archive
access, subprocesses, or active-source changes. Preserves the accepted manual
Step04 and terminal14; eleven other stages use audited rectangle partitions.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json
import math
import re
import resource
import shutil
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'evidence/proposals/C898CommonPairs'
PREFIX = 'Compact/Cases/C898/CachedPairs/'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def header(imports):
    return [*[f'import {name}' for name in imports], '',
            'set_option Elab.async false', 'set_option maxRecDepth 10000',
            'set_option linter.unnecessarySeqFocus false', '',
            'namespace N12Compact.C898Cached.AllPairs',
            'open C898Shared S12 CommonGroups', 'noncomputable section', '']


def finish(lines):
    return '\n'.join(lines+['', 'end', 'end N12Compact.C898Cached.AllPairs', ''])


def vec(values):
    return '!['+', '.join(map(str,values))+']'


def original_wrapper(relative, prior_manifest):
    """Read the authenticated pre-activation wrapper without resetting sources."""
    active = ROOT/relative
    expected = (prior_manifest or {}).get('canonical_input_sources',
        (prior_manifest or {}).get('input_sources', {})).get(relative)
    candidates = [active]
    # Backups are candidates only: their names confer no trust. The previous
    # manifest's per-file hash must match before source is used.
    retired = ROOT/'evidence/retired/C898BeforeCommonGroups'
    if expected and retired.exists():
        candidates += sorted(retired.glob('*/'+relative))
    for candidate in candidates:
        if not candidate.is_file() or candidate.is_symlink():
            continue
        actual = sha(candidate)
        if expected and actual != expected:
            continue
        text = candidate.read_text()
        if 'have hp := step_sound ' in text:
            return text, actual, str(candidate.relative_to(ROOT))
    raise RuntimeError('No hash-authenticated original wrapper available: '+relative)


def fix_metadata(metadata, step, target_domain, target_ids):
    prefix = f'step{step}'
    metadata = metadata.replace(
        f'[{prefix}Plans, List.mem_cons, List.mem_singleton]',
        f'[{prefix}Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]')
    if f'def {prefix}LinkTargetIds :' in metadata:
        recorded = re.search(r'def '+prefix+r'LinkTargetIds[^=]*:=\s*\[(.*?)\]',metadata,re.S)
        assert recorded
        actual = [int(value.strip()) for value in recorded.group(1).split(',') if value.strip()]
        assert actual == target_ids
        assert '  have targets : ∀ i ∈ '+prefix+'Links,' not in metadata
        return metadata
    marker = f'theorem {prefix}_links_checked'
    literal = '['+', '.join(map(str,target_ids))+']'
    declarations = (f'def {prefix}LinkTargetIds : List (Fin poseCount) :=\n  {literal}\n\n'
        f'theorem {prefix}_link_targets_mem :\n'
        f'    {prefix}LinkTargetIds.all (fun target => decide (target ∈ {target_domain}Ids)) = true := by\n'
        '  decide +kernel\n\n')
    assert marker in metadata
    metadata = metadata.replace(marker,declarations+marker,1)
    pattern = r'  have targets : ∀ i ∈ '+prefix+r'Links,.*?    decide \+kernel\n'
    replacement = (f'  have exact_targets : {prefix}Links.map (fun i => (C898CompactRelaxation.links i).target) =\n'
                   f'      {prefix}LinkTargetIds := by rfl\n')
    metadata,count = re.subn(pattern,replacement,metadata,count=1,flags=re.S)
    assert count == 1, (step,'old target-membership proof not found')
    old = '  exact ⟨i, hi, he, targets i hi⟩'
    new = (f'  have target_member : (C898CompactRelaxation.links i).target ∈ {prefix}LinkTargetIds := by\n'
           '    rw [← exact_targets]\n'
           '    exact List.mem_map.mpr ⟨i, hi, rfl⟩\n'
           f'  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp {prefix}_link_targets_mem _ target_member)⟩')
    assert old in metadata
    return metadata.replace(old,new,1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('prepared only; coordinating worker must schedule --run')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic()-started > 120 or rss > 192*1024**2:
            raise RuntimeError('common-pair source producer reached192MiB/120seconds')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,0.2,0.2)
    prior_path = OUT/'manifest.json'
    prior_manifest = json.loads(prior_path.read_text()) if prior_path.exists() else None
    report_path = ROOT/'evidence/c898-all-common-points.json'
    audit = json.loads(report_path.read_text())
    routes = audit['routes']
    link_map = json.loads((ROOT/'evidence/c898-retained-relaxation-link-map.json').read_text())
    for key,relative in [('poses','evidence/c898-shared-pose-map.json'),
                         ('records','evidence/c898-pair-record-map.json'),
                         ('plans','evidence/c898-pair-pruning-plan-map.json'),
                         ('domains','evidence/c898-domain-map.json'),
                         ('references','Compact/Cases/C898/References.lean')]:
        assert sha(ROOT/relative) == audit['input_sha256'][key]
    assert audit['totals']['original_pairs'] == 25843
    all_stages = audit['stages']
    stages = [s for s in all_stages if s['step'] not in (4,14)]
    assert len(stages) == 11
    used = sorted({r for stage in stages for r in stage['sources']+stage['neighbors']})
    context_modules = {}
    for path in (ROOT/'Compact/Cases/C898/CachedPairs').glob('Contexts*.lean'):
        for route in re.findall(r'^def route(\d+)\b',path.read_text(),re.M):
            assert int(route) not in context_modules
            context_modules[int(route)] = 'Compact.Cases.C898.CachedPairs.'+path.stem
    assert all(r in context_modules for r in used)
    rendered, shard_of = {}, {}
    for start in range(0,len(used),64):
        selected = used[start:start+64]
        shard = start//64
        for route in selected:
            shard_of[route] = shard
        lines = header(sorted({context_modules[r] for r in selected})+
                       ['Compact.Core.BoundaryFanSyntax','Compact.Cases.C898.CommonPairGroups'])
        for route in selected:
            lines += [f'def commonRaw{route} : RawSupportFan.Context :=',
                      f'  materialize_raw_fan% (route{route}.context.numeric)',
                      f'theorem commonRaw{route}_exact : commonRaw{route} = route{route}.context.numeric := rfl','']
        rendered[PREFIX+f'CommonRaw{shard:02}.lean'] = finish(lines)
    output_stages, input_sources, canonical_locations = [], {}, {}
    for stage in stages:
        step = stage['step']
        stem, prefix = f'Step{step:02}', f'step{step}'
        m,n = len(stage['sources']),len(stage['neighbors'])
        original_relative = PREFIX+stem+'.lean'
        original, original_sha, original_location = original_wrapper(original_relative,prior_manifest)
        input_sources[original_relative] = original_sha
        canonical_locations[original_relative] = original_location
        marker = f'theorem pairStep{step}_sound'
        metadata, terminal = original.split(marker,1)
        assert f'import Compact.Cases.C898.CachedPairs.{stem}Pairs' in metadata
        metadata = metadata.replace(f'import Compact.Cases.C898.CachedPairs.{stem}Pairs',
                                    f'import Compact.Cases.C898.CachedPairs.{stem}Data')
        data_source = (ROOT/PREFIX/(stem+'Data.lean')).read_text()
        link_match = re.search(r'def '+prefix+r'Links[^=]*:= \[(.*?)\]',data_source)
        assert link_match
        link_ids = [int(value.strip()) for value in link_match.group(1).split(',') if value.strip()]
        metadata = fix_metadata(metadata,step,stage['target_domain'],[link_map[i]['target'] for i in link_ids])
        rendered[PREFIX+stem+'Metadata.lean'] = metadata+'end\nend N12Compact.C898Cached.AllPairs\n'
        imports = sorted({f'Compact.Cases.C898.CachedPairs.CommonRaw{shard_of[r]:02}'
                          for r in stage['sources']+stage['neighbors']})
        imports += [f'Compact.Cases.C898.CachedPairs.{stem}Data',
                    'Compact.Cases.C898.CommonPairGroups','Compact.Core.KernelMatrix']
        data = header(imports)
        for role,count,ids in [('Sources',m,stage['sources']),('Neighbors',n,stage['neighbors'])]:
            singular = 'Source' if role == 'Sources' else 'Neighbor'
            data += [f'def {prefix}CommonRaw{role} : Fin {count} → RawSupportFan.Context :=',
                     '  '+vec('commonRaw'+str(r) for r in ids),
                     f'theorem {prefix}CommonRaw{role}_exact (i : Fin {count}) :',
                     f'    {prefix}CommonRaw{role} i = ({prefix}{role} i).context.numeric := by',
                     '  fin_cases i',
                     *['  · exact commonRaw'+str(r)+'_exact' for r in ids],'',
                     f'def {prefix}Common{singular}Angles : Fin {count} → Fin 64 :=',
                     '  '+vec(routes[r]['angle'] for r in ids),
                     f'theorem {prefix}Common{singular}Angles_exact (i : Fin {count}) :',
                     f'    {prefix}Common{singular}Angles i = ({prefix}{role} i).keyAngle := by',
                     '  fin_cases i <;> rfl','']
        data += [f'theorem {prefix}CommonNeighborUnblocked : ∀ j, ({prefix}Neighbors j).block = [] := by',
                 '  intro j; fin_cases j <;> rfl','']
        rendered[PREFIX+stem+'CommonData.lean'] = finish(data)
        groups = header([f'Compact.Cases.C898.CachedPairs.{stem}CommonData'])
        names,scopes = [],[]
        for index,group in enumerate(stage['partition']):
            scope = f'{prefix}CommonScope{index}'
            name = f'{prefix}CommonGroup{index}'
            names.append(name);scopes.append(scope)
            al,ah,bl,bh = group['bounds']
            ac,bc = ah-al,bh-bl
            assert 0 <= al < ah <= m and 0 <= bl < bh <= n
            groups += [f'def {scope} : Scope := ⟨{al}, {ac}, {bl}, {bc}⟩',
                       f'theorem {scope}_valid : {scope}.Valid {m} {n} := by decide +kernel','']
            source = f'{scope}.sourceIndex {scope}_valid a'
            neighbor = f'{scope}.neighborIndex {scope}_valid b'
            shared_arguments = [f'  {prefix}Sources {prefix}Neighbors',
                f'  {prefix}CommonRawSources {prefix}CommonRawNeighbors',
                f'  {prefix}CommonRawSources_exact {prefix}CommonRawNeighbors_exact',
                f'  {prefix}CommonNeighborUnblocked {scope} {scope}_valid']
            if group['kind'] == 'common_point':
                x,y = [Fraction(*v) for v in group['point']]
                denominator = math.lcm(x.denominator,y.denominator)
                px,py = x.numerator*(denominator//x.denominator),y.numerator*(denominator//y.denominator)
                point = f'{prefix}CommonPoint{index}'
                groups += [f'def {point} : CommonPoint.Point := ⟨{px}, {py}, {denominator}⟩',
                    f'kernel_matrix {name}_sources : {ac} × 1 => (fun a _ =>',
                    f'  CommonPoint.check ({prefix}CommonRawSources ({source}))',
                    f'    (ownKeys ({prefix}CommonSourceAngles ({source}))) {point} = true)',
                    f'kernel_matrix {name}_neighbors : {bc} × 1 => (fun b _ =>',
                    f'  CommonPoint.check ({prefix}CommonRawNeighbors ({neighbor}))',
                    f'    (ownKeys ({prefix}CommonNeighborAngles ({neighbor}))) {point} = true)',
                    f'def {name} : CheckedGroup {prefix}Sources {prefix}Neighbors := pointGroup',
                    *shared_arguments,
                    f'  (fun i => ownKeys ({prefix}CommonSourceAngles i))',
                    f'  (fun j => ownKeys ({prefix}CommonNeighborAngles j)) {point}',
                    f'  (fun a => {name}_sources a 0) (fun b => {name}_neighbors b 0)','']
            else:
                assert group['kind'] == 'original_pair_axes'
                groups += [f'kernel_matrix {name}_checked : {ac} × {bc} => (fun a b =>',
                    f'  RawSupportFan.PairCheck ({prefix}CommonRawSources ({source}))',
                    f'    ({prefix}CommonRawNeighbors ({neighbor}))',
                    f'    (fanDirectionKey ({prefix}CommonSourceAngles ({source}))',
                    f'      ({prefix}CommonNeighborAngles ({neighbor}))) (fun key => (key + 128) % 256))',
                    f'def {name} : CheckedGroup {prefix}Sources {prefix}Neighbors := fallbackGroup',
                    *shared_arguments,
                    f'  {prefix}CommonSourceAngles {prefix}CommonNeighborAngles',
                    f'  {prefix}CommonSourceAngles_exact {prefix}CommonNeighborAngles_exact',
                    f'  {name}_checked','']
        groups += [f'def {prefix}CommonScopes : List Scope := [',
                   '  '+', '.join(scopes)+']',
                   f'def {prefix}CommonGroups : List (CheckedGroup {prefix}Sources {prefix}Neighbors) := [',
                   '  '+', '.join(names)+']',
                   f'theorem {prefix}CommonScopes_exact :',
                   f'    {prefix}CommonGroups.map CheckedGroup.scope = {prefix}CommonScopes := rfl',
                   f'kernel_matrix {prefix}CommonCoverage : {m} × {n} => (fun i j =>',
                   f'  ScopeCheck {prefix}CommonScopes i.val j.val)',
                   f'theorem {prefix}_geometric_overlap (i : Fin {m}) (j : Fin {n}) :',
                   f'    PairOverlaps ({prefix}Sources i) ({prefix}Neighbors j) :=',
                   f'  groups_sound {prefix}Sources {prefix}Neighbors {prefix}CommonGroups',
                   f'    {prefix}CommonScopes {prefix}CommonScopes_exact {prefix}CommonCoverage i j',
                   f'#print axioms {prefix}_geometric_overlap']
        rendered[PREFIX+stem+'CommonGroups.lean'] = finish(groups)
        # Keep every original domain, plan and outward-link hypothesis. Only
        # the complete overlap argument is replaced by checked group geometry.
        geometric = marker+terminal
        geometric = geometric.replace(f'pairStep{step}_sound',f'pairStep{step}_geometric_sound')
        geometric = geometric.replace('have hp := step_sound ', 'have hp := step_sound_of_overlap ')
        geometric = geometric.replace(f'{prefix}_neighbor_complete {prefix}_neighbor_unblocked {prefix}_pairs_checked',
                                      f'{prefix}_neighbor_complete {prefix}_geometric_overlap')
        assert f'{prefix}_pairs_checked' not in geometric
        geometric_header = header([f'Compact.Cases.C898.CachedPairs.{stem}Metadata',
                                   f'Compact.Cases.C898.CachedPairs.{stem}CommonGroups'])
        rendered[PREFIX+stem+'Geometric.lean'] = '\n'.join(geometric_header)+geometric
        wrapper = header([f'Compact.Cases.C898.CachedPairs.{stem}Geometric'])
        theorem_type = (marker+terminal).split(' := by',1)[0]
        wrapper += [theorem_type+' := by',f'  exact pairStep{step}_geometric_sound q t hq ht disjoint',
                    f'#print axioms pairStep{step}_sound']
        rendered[PREFIX+stem+'.lean'] = finish(wrapper)
        output_stages.append({'step':step,'groups':len(names),'pairs':stage['original_pairs'],
                              'point_checks':stage['point_checks'],'fallback_pairs':stage['fallback_pairs']})
    # Reuse the strictly smaller already accepted Step04 point certificate.
    step4 = (ROOT/PREFIX/'Step04.lean').read_text()
    marker = 'theorem pairStep4_sound'
    theorem_type = marker+step4.split(marker,1)[1].split(' := by',1)[0]
    wrapper = header(['Compact.Cases.C898.CachedPairs.Step04Geometric'])
    wrapper += [theorem_type+' := by','  exact pairStep4_geometric_sound q t hq ht disjoint',
                '#print axioms pairStep4_sound']
    rendered[PREFIX+'Step04.lean'] = finish(wrapper)
    input_sources[PREFIX+'Step04.lean'] = sha(ROOT/PREFIX/'Step04.lean')
    total = sum(len(value.encode()) for value in rendered.values())
    assert total < 32*1024**2
    assert sum(s['original_pairs'] for s in all_stages) == 25843
    OUT.mkdir(parents=True,exist_ok=True)
    previous_manifest, previous_backup = None, None
    old_manifest_path = OUT/'manifest.json'
    if old_manifest_path.exists():
        previous_manifest = sha(old_manifest_path)
        old_manifest = json.loads(old_manifest_path.read_text())
        for relative,entry in old_manifest['outputs'].items():
            assert sha(OUT/relative) == entry['sha256'], ('modified earlier proposal',relative)
        previous_backup = ROOT/'evidence/retired/C898CommonProposal'/previous_manifest[:16]
        previous_backup.mkdir(parents=True,exist_ok=True)
        saved_manifest = previous_backup/'manifest.json'
        if saved_manifest.exists():
            assert sha(saved_manifest) == previous_manifest
        else:
            shutil.copyfile(old_manifest_path,saved_manifest)
        for relative,value in rendered.items():
            old = OUT/relative
            if old.exists() and sha(old) != hashlib.sha256(value.encode()).hexdigest():
                saved = previous_backup/relative
                saved.parent.mkdir(parents=True,exist_ok=True)
                if saved.exists():
                    assert sha(saved) == sha(old)
                else:
                    shutil.copyfile(old,saved)
    outputs = {}
    for relative,text in rendered.items():
        target = OUT/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        temporary = target.with_suffix('.lean.tmp')
        try:
            temporary.write_text(text)
            temporary.replace(target)
        finally:
            temporary.unlink(missing_ok=True)
        outputs[relative] = {'bytes':len(text.encode()),'lines':text.count('\n'),'sha256':sha(target)}
    allowed_previous_sources = {relative:[entry['sha256']]
        for relative,entry in (prior_manifest or {}).get('outputs',{}).items()}
    report = {'scope':'source proposal for complete original C898 pair stages; no Lean acceptance',
              'stages':output_stages,'reused_stages':[4,14],'raw_contexts':len(used),
              'modules':len(outputs),'bytes':total,'lines':sum(v['lines'] for v in outputs.values()),
              'audit_sha256':sha(report_path),'input_sources':input_sources,'outputs':outputs,
              'canonical_input_sources':input_sources,'canonical_source_locations':canonical_locations,
              'allowed_previous_sources':allowed_previous_sources,
              'previous_proposal_manifest_sha256':previous_manifest,
              'previous_proposal_backup':str(previous_backup.relative_to(ROOT)) if previous_backup else None,
              'elapsed_seconds':time.monotonic()-started}
    with (OUT/'manifest.json').open('w') as stream:
        json.dump(report,stream,indent=2);stream.write('\n')
    print(json.dumps({k:report[k] for k in ['modules','bytes','lines','raw_contexts','elapsed_seconds']}))


if __name__ == '__main__':
    main()
