#!/usr/bin/env python3
"""Prepare all13 C898 pair stages with shared certified vertex fans.

No Lean or archive access. Exact original plan, block, every neighbor, every
surviving piece and every outward-relaxation link is retained. Per-pair record
lists are replaced by implied Cartesian coverage. Run only in the parent's
bounded slot after the complete Step14 cached pilot is accepted.
Suggested hard outer guard:256MiB,120sec,32MiB output.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import re
import signal
import time

from build_c898_pair_fan_pilot import cramer, direction, axis_key, target_constant
from build_c898_cached_pair_pilot import vertex, row_text, ref_text, chunk_check_lines

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'Compact/Cases/C898/CachedPairs'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def begin(imports):
    return [*[f'import {name}' for name in imports], '',
            'set_option Elab.async false', 'set_option maxRecDepth 10000',
            'set_option linter.unnecessarySeqFocus false', '',
            'namespace N12Compact.C898Cached.AllPairs',
            'open C898Shared CachedSupportFan S12', 'noncomputable section', '']


def finish(lines):
    return '\n'.join(lines+['', 'end', 'end N12Compact.C898Cached.AllPairs', ''])


def ids(values):
    return '['+', '.join(map(str,values))+']'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--raw-numeric', action='store_true',
                        help='use literal proof-free fans and bounded generic matrix acceptance')
    parser.add_argument('--recipe-contexts', action='store_true',
                        help='use the shared checked context constructor instead of repeated wrappers')
    args = parser.parse_args()
    if not args.run:
        parser.error('prepared only; explicit --run requires the coordinating worker')
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('120sec deadline')))
    signal.alarm(120)
    started = time.monotonic()
    paths = {name:ROOT/'evidence'/file for name,file in {
        'poses':'c898-shared-pose-map.json','fans':'c898-support-fan-counts.json',
        'records':'c898-pair-record-map.json','plans':'c898-pair-pruning-plan-map.json',
        'domains':'c898-domain-map.json','links':'c898-retained-relaxation-link-map.json'}.items()}
    data, audit, record_doc, plan_doc, domains_doc, links = [
        json.loads(paths[name].read_text()) for name in paths]
    rows, poses, blocks = data['rows'],data['poses'],data['blocks']
    records, plans = record_doc['records'],plan_doc['plans']
    domains = domains_doc['domains']
    stages = {int(k):v for k,v in domains_doc['pair_steps'].items()}
    assert len(records)==25843 and len(stages)==13
    assert sha(paths['poses'])==audit['source_pose_map_sha256']
    references_path = ROOT/'Compact/Cases/C898/References.lean'
    refs=[tuple(map(int,m)) for m in re.findall(
        r'⟨(-?\d+), (-?\d+), (\d+), (-?\d+), (\d+)⟩,',references_path.read_text())]
    assert len(refs)==64
    context_by_rows={tuple(c['rows']):c for c in audit['contexts']}
    contexts={c['id']:c for c in audit['contexts']}
    requests=defaultdict(set)
    route_keys={}
    route_ids={}
    routes=[]
    groups=defaultdict(list)

    def route(pose,block):
        key=(pose,block)
        if key in route_ids:
            return route_ids[key]
        actual=([] if block is None else blocks[block]['rows'])+poses[pose]['rows']
        cid=context_by_rows[tuple(sorted(set(actual)))]['id']
        index=len(routes)
        routes.append({'pose':pose,'block':block,'angle':poses[pose]['angle'],
                       'context':cid,'inputs':actual})
        route_ids[key]=index
        route_keys[index]=key
        return index

    for record in records:
        # The complete terminal transition already has an accepted standalone
        # theorem. Do not duplicate its fan data or 424 numeric pair decisions.
        if record['step'] == 14:
            continue
        ra,rb=route(record['source'],record['block']),route(record['neighbor'],None)
        record['cache_source'],record['cache_neighbor']=ra,rb
        groups[record['step']].append(record)
        a,b=routes[ra],routes[rb]
        for axis in range(8):
            key=axis_key(a['angle'],b['angle'],axis)
            requests[a['context']].add(key)
            requests[b['context']].add((key+128)%256)
    choices, fans={},{}
    for cid,keys in sorted(requests.items()):
        choices[cid]={}
        entries=[]
        for key in sorted(keys):
            x,y=direction(key,refs)
            candidates=[]
            for first,second in contexts[cid]['bases']:
                value=cramer(rows[first],rows[second],x,y)
                if value is not None:
                    candidates.append((Fraction(value[3],value[2]),not value[4],first,second,value))
            assert candidates,(cid,key,'missing support')
            _,_,first,second,value=min(candidates)
            choices[cid][key]=value
            if not entries or entries[-1][1:]!=(first,second):
                entries.append((key if entries else 0,first,second))
        fans[cid]=entries
    for record in records:
        if record['step'] == 14:
            continue
        a,b=routes[record['cache_source']],routes[record['cache_neighbor']]
        for axis in range(8):
            key=axis_key(a['angle'],b['angle'],axis)
            A,B=choices[a['context']][key],choices[b['context']][(key+128)%256]
            x,y=direction(key,refs)
            scale,constant=target_constant(refs[a['angle']],refs[b['angle']],x,y)
            lhs=scale*(A[3]*B[2]+B[3]*A[2]);rhs=A[2]*B[2]*constant
            assert lhs<=rhs and (lhs<rhs or A[4] or B[4]),record['name']
    # Group by geometric context, not pair occurrence. All role aliases of a
    # context use one small literal fan and retain their exact input list.
    by_context=defaultdict(list)
    for rid,route0 in enumerate(routes):
        by_context[route0['context']].append(rid)
    context_order=sorted(fans)
    group_of={cid:i//64 for i,cid in enumerate(context_order)}
    rendered={}
    for chunk_index in range((len(context_order)+63)//64):
        context_imports=['Compact.Cases.C898.CachedPoseRecipe' if args.recipe_contexts
                         else 'Compact.Cases.C898.CachedPairFan']
        if args.raw_numeric:
            context_imports.append('Compact.Core.BoundaryFanSyntax')
        lines=begin(context_imports)
        for cid in context_order[chunk_index*64:(chunk_index+1)*64]:
            entries=fans[cid]
            lines += [f'def fan{cid} : Array (Entry rowCount) := #[']
            for key,first,second in entries:
                x,y,d=vertex(rows[first],rows[second])
                lines.append(f'  ⟨{key},{first},{second},⟨{row_text(rows[first])},'
                             f'{row_text(rows[second])},{x},{y},{d}⟩⟩,')
            lines += [']','']
            if not args.recipe_contexts:
                lines += [f'def fan{cid}Entry (i : Fin {len(entries)}) : Entry rowCount :=',
                          f"  fan{cid}[i.val]'(by change i.val < {len(entries)}; exact i.isLt)",'']
            for rid in by_context[cid]:
                r=routes[rid];pose,block,angle=r['pose'],r['block'],r['angle']
                incoming=f'poseRows {pose}' if block is None else f'blockRows {block} ++ poseRows {pose}'
                if args.recipe_contexts:
                    optional_block='none' if block is None else f'some {block}'
                    lines += [f'def route{rid}Recipe : ContextRecipe :=',
                              f'  ⟨{pose},{optional_block},{angle},{ref_text(refs[angle])},fan{cid}⟩','',
                              f'theorem route{rid}_checked : route{rid}Recipe.Check := by',
                              '  decide +kernel','',
                              f'def route{rid} : PoseContext := route{rid}Recipe.certify route{rid}_checked','']
                else:
                    lines += [f'def route{rid}Inputs : List (Fin rowCount) := {incoming}',
                          f'def route{rid}Reference : ReferenceAxis.Reference := {ref_text(refs[angle])}', '',
                          f'theorem route{rid}_checked (i : Fin {len(entries)}) :',
                          f'    (fan{cid}Entry i).Check rows route{rid}Inputs := by',
                          '  revert i; decide +kernel','',
                          f'def route{rid}Context : Context rows :=',
                          f'  ⟨route{rid}Inputs,route{rid}Reference,',
                          f'   ⟨fan{cid}Entry 0,route{rid}_checked 0⟩,',
                          f'   Array.ofFn (fun i : Fin {len(entries)} => ⟨fan{cid}Entry i,route{rid}_checked i⟩)⟩','',
                          f'theorem route{rid}_reference : route{rid}Reference =',
                          f'    references (poseAngle {pose}) := by decide +kernel','',
                          f'def route{rid} : PoseContext where',f'  pose := {pose}',
                          '  block := '+('[]' if block is None else f'blockRows {block}'),
                          f'  keyAngle := {angle}',f'  context := route{rid}Context',
                          '  inputs_exact := by rfl',f'  reference_exact := route{rid}_reference','']
                if args.raw_numeric:
                    lines += [f'def route{rid}Raw : RawSupportFan.Context :=',
                              f'  materialize_raw_fan% (route{rid}.context.numeric)','',
                              f'theorem route{rid}Raw_exact : route{rid}Raw = route{rid}.context.numeric := rfl','']
        rendered[f'Contexts{chunk_index:02}.lean']=finish(lines)
    stage_reports=[]
    for step,(source_domain,neighbor_domain,target_domain) in sorted(stages.items()):
        if step == 14:
            terminal = begin(['Compact.Cases.C898.PairStep14Cached'])
            terminal += ['theorem pairStep14_sound (q t : S12Pilot.OpenSquare)',
                         f'    (hq : OrientedPoseCovered {source_domain} q)',
                         f'    (ht : OrientedPoseCovered {neighbor_domain} t)',
                         '    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :',
                         f'    OrientedPoseCovered {target_domain} q :=',
                         '  N12Compact.C898Cached.pairStep14_sound q t hq ht disjoint',
                         '', '#print axioms pairStep14_sound']
            rendered['Step14.lean'] = finish(terminal)
            stage_reports.append({'step':14,'source_domain':source_domain,
                                  'neighbor_domain':neighbor_domain,'target_domain':target_domain,
                                  'implied_pairs':424,'reused_accepted_terminal':True,
                                  'original_source_count':8,'original_neighbor_count':53})
            continue
        selected=sorted([p for p in plans if p['step']==step],key=lambda p:p['pose'])
        blocked=[p for p in selected if p['block'] is not None]
        source_routes=[route_ids[(p['source'],p['block'])] for p in blocked]
        neighbor_routes=[route_ids[(p,None)] for p in domains[neighbor_domain]]
        assert 0<len(source_routes)<=64 and 0<len(neighbor_routes)<=64
        expected=[(p['source'],n,p['block']) for p in blocked for n in domains[neighbor_domain]]
        actual=[(r['source'],r['neighbor'],r['block']) for r in sorted(groups[step],key=lambda r:r['index'])]
        assert expected==actual
        assert [p['source'] for p in selected]==domains[source_domain]
        assert all(p['neighbors_name']==neighbor_domain for p in selected)
        pieces=[piece for p in selected for piece in p['pieces']]
        used_links=[l for l in links if re.fullmatch(f'continuousScout898Step{step}Pose'+r'\d+Link\d+',l['name'])]
        assert sorted(l['source'] for l in used_links)==sorted(pieces)
        links_by_source={l['source']:l for l in used_links}
        assert len(links_by_source)==len(used_links), (step,'duplicate piece links')
        used_links=[links_by_source[piece] for piece in pieces]
        assert [l['source'] for l in used_links]==pieces
        assert all(l['target'] in domains[target_domain] for l in used_links)
        imports=[f'Compact.Cases.C898.CachedPairs.Contexts{i:02}' for i in sorted({
            group_of[routes[r]['context']] for r in source_routes+neighbor_routes})]
        imports+=['Compact.Cases.C898.CachedPairPlans','Compact.Cases.C898.PairComplements',
                  'Compact.Cases.C898.SharedDomains']
        lines=begin(imports)
        prefix=f'step{step}'
        for label,values in [('Sources',source_routes),('Neighbors',neighbor_routes)]:
            lines += [f'def {prefix}{label}Data : Array PoseContext := #[',
                      '  '+', '.join(f'route{r}' for r in values),']','',
                      f'def {prefix}{label} (i : Fin {len(values)}) : PoseContext :=',
                      f"  {prefix}{label}Data[i.val]'(by change i.val < {len(values)}; exact i.isLt)",'']
        lines += [f'def {prefix}SourcePoseIds : Fin {len(source_routes)} → Fin poseCount :=',
                  '  !'+ids(routes[r]['pose'] for r in source_routes),
                  f'def {prefix}SourceBlockIds : Fin {len(source_routes)} → Nat :=',
                  '  !'+ids(routes[r]['block'] for r in source_routes),
                  f'def {prefix}NeighborPoseIds : Fin {len(neighbor_routes)} → Fin poseCount :=',
                  '  !'+ids(routes[r]['pose'] for r in neighbor_routes),'']
        lines += [f'def {prefix}Plans : List Plan := [']
        for plan in selected:
            block='none' if plan['block'] is None else f'some {plan["block"]}'
            lines.append(f'  ⟨{plan["source"]},{block},{ids(plan["pieces"])}⟩,')
        lines += [']','',f'def {prefix}Pieces : List (Fin poseCount) := {ids(pieces)}',
                  f'def {prefix}Links : List (Fin 927) := {ids(l["index"] for l in used_links)}','',
                  f'def {prefix}PairCheck (i : Fin {len(source_routes)}) (j : Fin {len(neighbor_routes)}) : Prop :=',
                  f'  ({prefix}Sources i).PairCheck ({prefix}Neighbors j)','',
                  f'instance (i : Fin {len(source_routes)}) (j : Fin {len(neighbor_routes)}) :',
                  f'    Decidable ({prefix}PairCheck i j) :=',
                  f'  inferInstanceAs (Decidable (({prefix}Sources i).PairCheck _))','']
        if args.raw_numeric:
            for label,values in [('Sources',source_routes),('Neighbors',neighbor_routes)]:
                lines += [f'def {prefix}Raw{label} : Fin {len(values)} → RawSupportFan.Context :=',
                          '  !['+', '.join(f'route{r}Raw' for r in values)+']','',
                          f'def {prefix}Raw{label}Angle : Fin {len(values)} → Fin 64 :=',
                          '  !'+ids(routes[r]['angle'] for r in values),'',
                          f'theorem {prefix}Raw{label}_exact (i : Fin {len(values)}) :',
                          f'    {prefix}Raw{label} i = ({prefix}{label} i).context.numeric := by',
                          '  fin_cases i <;> rfl','',
                          f'theorem {prefix}Raw{label}Angle_exact (i : Fin {len(values)}) :',
                          f'    {prefix}Raw{label}Angle i = ({prefix}{label} i).keyAngle := by',
                          '  fin_cases i <;> rfl','']
            lines += [f'def {prefix}RawPairCheck (i : Fin {len(source_routes)})',
                      f'    (j : Fin {len(neighbor_routes)}) : Prop :=',
                      f'  RawSupportFan.PairCheck ({prefix}RawSources i) ({prefix}RawNeighbors j)',
                      f'    (fanDirectionKey ({prefix}RawSourcesAngle i) ({prefix}RawNeighborsAngle j))',
                      '    (fun key => (key + 128) % 256)','',
                      f'instance (i : Fin {len(source_routes)}) (j : Fin {len(neighbor_routes)}) :',
                      f'    Decidable ({prefix}RawPairCheck i j) :=',
                      '  inferInstanceAs (Decidable (RawSupportFan.PairCheck _ _ _ _))','']
        rendered[f'Step{step:02}Data.lean']=finish(lines)
        if args.raw_numeric:
            proof=begin([f'Compact.Cases.C898.CachedPairs.Step{step:02}Data',
                         'Compact.Core.KernelMatrix', 'Compact.Core.RawSupportFanBridge'])
            proof += [f'kernel_matrix {prefix}_raw_pairs_checked : '
                      f'{len(source_routes)} × {len(neighbor_routes)} => {prefix}RawPairCheck','',
                      f'theorem {prefix}_pairs_checked (i : Fin {len(source_routes)})',
                      f'    (j : Fin {len(neighbor_routes)}) : {prefix}PairCheck i j := by',
                      '  apply CachedSupportFan.PairCheck.of_cached_numeric',
                      f'    ({prefix}Sources i).context ({prefix}Neighbors j).context',
                      f'    ({prefix}RawSources i) ({prefix}RawNeighbors j)',
                      f'    ({prefix}RawSources_exact i) ({prefix}RawNeighbors_exact j)',
                      f'    (fanDirectionKey ({prefix}Sources i).keyAngle ({prefix}Neighbors j).keyAngle)',
                      '    (fun key => (key + 128) % 256)',
                      f'  have checked := {prefix}_raw_pairs_checked i j',
                      '  change RawSupportFan.PairCheck _ _ _ _ at checked',
                      f'  simpa only [← {prefix}RawSourcesAngle_exact i,',
                      f'    ← {prefix}RawNeighborsAngle_exact j] using checked','']
        else:
            proof=begin([f'Compact.Cases.C898.CachedPairs.Step{step:02}Data',
                         'Compact.Core.FiniteCheckChunks'])
            proof += chunk_check_lines(prefix, f'{prefix}PairCheck',
                                       len(source_routes),len(neighbor_routes))
            proof += [f'theorem {prefix}_pairs_checked (i : Fin {len(source_routes)})',
                      f'    (j : Fin {len(neighbor_routes)}) : {prefix}PairCheck i j := by','  fin_cases i']
            proof += [f'  · exact {prefix}_source{i}_checked j' for i in range(len(source_routes))]
        rendered[f'Step{step:02}Pairs.lean']=finish(proof)
        complete=begin([f'Compact.Cases.C898.CachedPairs.Step{step:02}Pairs',
                        'Compact.Cases.C898.CompactRelaxation.All'])
        complete += [f'theorem {prefix}_source_pose_exact (i : Fin {len(source_routes)}) :',
                     f'    ({prefix}Sources i).pose = {prefix}SourcePoseIds i := by fin_cases i <;> rfl','',
                     f'theorem {prefix}_source_block_exact (i : Fin {len(source_routes)}) :',
                     f'    ({prefix}Sources i).block = blockRows ({prefix}SourceBlockIds i) := by',
                     '  fin_cases i <;> rfl','',
                     f'theorem {prefix}_neighbor_pose_exact (j : Fin {len(neighbor_routes)}) :',
                     f'    ({prefix}Neighbors j).pose = {prefix}NeighborPoseIds j := by fin_cases j <;> rfl','',
                     f'theorem {prefix}_plans_checked : ∀ plan ∈ {prefix}Plans, plan.Check complement := by',
                     '  decide +kernel','',
                     f'theorem {prefix}_cover : StepCover {source_domain}Ids {prefix}Pieces {prefix}Plans := by',
                     '  decide +kernel','',f'theorem {prefix}_source_matches :',
                     f'    ∀ plan ∈ {prefix}Plans, ∀ block, plan.block = some block →',
                     f'      ∃ i, ({prefix}Sources i).pose = plan.source ∧',
                     f'        ({prefix}Sources i).block = blockRows block := by',
                     # Nat block is infinite; split finite plan list first, then
                     # inject each Option equality instead of deciding Nat∀.
                     '  intro plan member block hb',
                     f'  simp only [{prefix}Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member',
                     '  rcases member with '+ ' | '.join(['rfl']*len(selected))]
        for plan in selected:
            if plan['block'] is None:
                complete += ['  · cases hb']
            else:
                local=source_routes.index(route_ids[(plan['source'],plan['block'])])
                complete += ['  · cases hb',
                             f'    exact ⟨{local}, {prefix}_source_pose_exact {local},',
                             f'      {prefix}_source_block_exact {local}⟩']
        complete += ['',f'private theorem {prefix}_neighbor_ids_complete : ∀ pose ∈ {neighbor_domain}Ids,',
                     f'    ∃ j, {prefix}NeighborPoseIds j = pose := by',
                     f'  have exact_ids : (List.finRange {len(neighbor_routes)}).map {prefix}NeighborPoseIds =',
                     f'      {neighbor_domain}Ids := by rfl',
                     '  intro pose member', '  rw [← exact_ids] at member',
                     '  obtain ⟨j, _, hj⟩ := List.mem_map.mp member', '  exact ⟨j, hj⟩','',
                     f'theorem {prefix}_neighbor_complete : ∀ pose ∈ {neighbor_domain}Ids,',
                     f'    ∃ j, ({prefix}Neighbors j).pose = pose := by',
                     '  intro pose member',
                     f'  obtain ⟨j,hj⟩ := {prefix}_neighbor_ids_complete pose member',
                     f'  exact ⟨j,({prefix}_neighbor_pose_exact j).trans hj⟩','',
                     f'theorem {prefix}_neighbor_unblocked : ∀ j, ({prefix}Neighbors j).block = [] := by',
                     '  intro j; fin_cases j <;> rfl','',
                     f'def {prefix}LinkTargetIds : List (Fin poseCount) :=',
                     f'  {ids(link["target"] for link in used_links)}','',
                     f'theorem {prefix}_link_targets_mem :',
                     f'    {prefix}LinkTargetIds.all (fun target => decide (target ∈ {target_domain}Ids)) = true := by',
                     '  decide +kernel','',f'theorem {prefix}_links_checked :',
                     f'    ∀ piece ∈ {prefix}Pieces, ∃ i ∈ {prefix}Links,',
                     '      (C898CompactRelaxation.links i).source = piece ∧',
                     f'      (C898CompactRelaxation.links i).target ∈ {target_domain}Ids := by',
                     f'  have exact_sources : {prefix}Links.map (fun i => (C898CompactRelaxation.links i).source) =',
                     f'      {prefix}Pieces := by rfl',
                     f'  have exact_targets : {prefix}Links.map (fun i => (C898CompactRelaxation.links i).target) =',
                     f'      {prefix}LinkTargetIds := by rfl',
                     '  intro piece member', '  rw [← exact_sources] at member',
                     '  obtain ⟨i, hi, he⟩ := List.mem_map.mp member',
                     f'  have target_member : (C898CompactRelaxation.links i).target ∈ {prefix}LinkTargetIds := by',
                     '    rw [← exact_targets]',
                     '    exact List.mem_map.mpr ⟨i, hi, rfl⟩',
                     f'  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp {prefix}_link_targets_mem _ target_member)⟩','',
                     f'theorem pairStep{step}_sound (q t : S12Pilot.OpenSquare)',
                     f'    (hq : OrientedPoseCovered {source_domain} q)',
                     f'    (ht : OrientedPoseCovered {neighbor_domain} t)',
                     '    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :',
                     f'    OrientedPoseCovered {target_domain} q := by',
                     f'  have hp := step_sound {source_domain}Ids {neighbor_domain}Ids',
                     f'    {prefix}Pieces {prefix}Plans complement {prefix}Sources {prefix}Neighbors',
                     f'    {prefix}_cover {prefix}_plans_checked {prefix}_source_matches',
                     f'    {prefix}_neighbor_complete {prefix}_neighbor_unblocked {prefix}_pairs_checked',
                     '    q t hq ht disjoint',
                     '  obtain ⟨piece, member, realizes⟩ := hp',
                     '  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member',
                     f'  obtain ⟨i, _, hs, ht⟩ := {prefix}_links_checked piece in_pieces',
                     '  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩',
                     '  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)','',
                     f'#print axioms pairStep{step}_sound']
        if step == 4:
            # Both the original numeric pilot and the geometric replacement
            # consume these unchanged whole-plan/relaxation metadata facts.
            split = next(i for i, line in enumerate(complete)
                         if line.startswith('theorem pairStep4_sound'))
            metadata = complete[:split]
            metadata[0] = 'import Compact.Cases.C898.CachedPairs.Step04Data'
            rendered['Step04Metadata.lean'] = finish(metadata)
            complete = begin(['Compact.Cases.C898.CachedPairs.Step04Pairs',
                              'Compact.Cases.C898.CachedPairs.Step04Metadata']) + complete[split:]
        rendered[f'Step{step:02}.lean']=finish(complete)
        stage_reports.append({'step':step,'source_domain':source_domain,'neighbor_domain':neighbor_domain,
                              'target_domain':target_domain,'plans':len(selected),'blocked_plans':len(blocked),
                              'neighbors':len(neighbor_routes),'implied_pairs':len(expected),'pieces':len(pieces),
                              'relaxation_links':len(used_links),'source_routes':source_routes,'neighbor_routes':neighbor_routes})
    total=sum(len(value.encode()) for value in rendered.values())
    assert total<32*1024**2
    OUT.mkdir(parents=True,exist_ok=True)
    for name,value in rendered.items():
        temporary=OUT/(name+'.tmp');temporary.write_text(value);temporary.replace(OUT/name)
    report={'scope':'all13 original C898 pair transitions assembled as candidate source; no Lean acceptance',
            'raw_numeric':args.raw_numeric,'recipe_contexts':args.recipe_contexts,
            'pairs':len(records),'axes':8*len(records),'contexts':len(fans),'pose_context_routes':len(routes),
            'new_pairs':len(records)-424,'reused_terminal_pairs':424,
            'fan_entries':sum(map(len,fans.values())),'max_entries':max(map(len,fans.values())),
            'stages':stage_reports,'routes':routes,
            'input_sha256':{name:sha(path) for name,path in paths.items()},
            'references_sha256':sha(references_path),'all_old_pair_indices_removed':True,
            'all_cartesian_families_and_original_relaxation_links_verified':True,
            'outputs':{str((OUT/name).relative_to(ROOT)):{'bytes':len(value.encode()),
                       'lines':value.count('\n'),'sha256':sha(OUT/name)} for name,value in rendered.items()},
            'elapsed_seconds':time.monotonic()-started}
    with (ROOT/'evidence/c898-all-cached-pairs.json').open('w') as f:
        json.dump(report,f,separators=(',',':'));f.write('\n')
    print(json.dumps({k:report[k] for k in ['pairs','axes','contexts','pose_context_routes','fan_entries','elapsed_seconds']}))


if __name__=='__main__':
    main()
