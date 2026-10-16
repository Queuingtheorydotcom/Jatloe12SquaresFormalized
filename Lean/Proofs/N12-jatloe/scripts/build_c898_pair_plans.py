#!/usr/bin/env python3
"""Assemble complete pair transitions from authenticated source identities."""
from provenance_source import read_bytes, read_text, text_stream
from pathlib import Path
from fractions import Fraction as F
import json,re,hashlib

ROOT=Path(__file__).resolve().parents[1];out=ROOT/'Compact/Cases/C898'
m=json.loads((ROOT/'evidence/c898-shared-pose-map.json').read_text())
poses={p['name']:p for p in m['poses']}
plans=json.loads((ROOT/'evidence/c898-pair-pruning-plan-map.json').read_text())['plans']
records=json.loads((ROOT/'evidence/c898-pair-record-map.json').read_text())['records']
links=json.loads((ROOT/'evidence/c898-relaxation-link-map.json').read_text())
domains={};steps={}
for c in range(66):
    for line in read_text(ROOT/f'vendor/S12/Push898Chunk{c}.lean').splitlines():
        x=re.match(r'def (continuousScout898Domain\d+_\d+) : List PoseLeaf := \[(.*)\]$',line)
        if x:domains[x[1]]=[poses[n]['index'] for n in x[2].split(',')] if x[2] else []
        x=re.match(r'theorem continuousScout898Step(\d+)_checked : PruningCoverCheck (\w+) (\w+) (\w+) ',line)
        if x:steps[int(x[1])]=list(x.groups()[1:])
assert len(domains)==26 and len(steps)==13
lines=['import Compact.Cases.C898.SharedPoses','','namespace N12Compact.C898Shared','open S12','']
for name,ids in domains.items():
    lines += [f"def {name}Ids : List (Fin poseCount) := [{', '.join(map(str,ids))}]",
              f'noncomputable def {name} : List PoseLeaf := {name}Ids.map poses','']
lines+=['end N12Compact.C898Shared',''];(out/'SharedDomains.lean').write_text('\n'.join(lines))
(ROOT/'evidence/c898-domain-map.json').write_text(json.dumps({'domains':domains,'pair_steps':steps},separators=(',',':'))+'\n')

def key(row):return (*[F(i,row['denominator']) for i in row['integers']],row['strict'])
lookup={key(row):i for i,row in enumerate(m['rows'])}
complements=[]
for row in m['rows']:
    x,y,z,t=key(row);complements.append(lookup.get((-x,-y,-z,not t),0))
lines=['import Compact.Cases.C898.SharedRows','','namespace N12Compact.C898Shared','',
       'def complementData : Array (Fin rowCount) := #[']
for i in range(0,len(complements),256):lines.append('  '+', '.join(map(str,complements[i:i+256]))+',')
lines+= [']','def complement (i : Fin rowCount) : Fin rowCount := (complementData[i.val]?).getD 0','',
          'end N12Compact.C898Shared',''];(out/'PairComplements.lean').write_text('\n'.join(lines))

for step,(source_domain,neighbor_domain,target_domain) in sorted(steps.items()):
    selected=sorted([p for p in plans if p['step']==step],key=lambda p:p['pose'])
    source_ids=domains[source_domain];neighbor_ids=domains[neighbor_domain];target_ids=domains[target_domain]
    assert [p['source'] for p in selected]==source_ids
    for p in selected:
        assert p['neighbors_name']==neighbor_domain
        witnesses=[r for r in records if r['step']==step and r['plan']==p['pose']]
        if p['block'] is not None:
            assert [r['neighbor'] for r in witnesses]==neighbor_ids
            assert all(r['source']==p['source'] and r['block']==p['block'] for r in witnesses)
    pieces=[i for p in selected for i in p['pieces']]
    used_links=[w for w in links if re.fullmatch(f'continuousScout898Step{step}Pose'+r'\d+Link\d+',w['name'])]
    assert sorted(w['source'] for w in used_links)==sorted(pieces)
    assert all(w['target'] in target_ids for w in used_links)
    sn=f'pairStep{step}';rec=f'{sn}Records'
    lines=[f'import Compact.Cases.C898.PairStep{step:02}Records','import Compact.Cases.C898.PairPlans',
           'import Compact.Cases.C898.PairComplements','import Compact.Cases.C898.SharedDomains',
           'import Compact.Cases.C898.Relaxation.All','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
           'namespace N12Compact.C898Shared','open S12','',f'def {sn}Plans : List PairPlan := [']
    for p in selected:
        block='none' if p['block'] is None else f'(some {p["block"]})'
        witnesses=[r['index'] for r in records if r['step']==step and r['plan']==p['pose']]
        lines.append(f"  ⟨{p['source']}, {neighbor_domain}Ids, {block}, [{', '.join(map(str,p['pieces']))}], [{', '.join(map(str,witnesses))}]⟩,")
    lines += [']','',f"def {sn}Pieces : List (Fin poseCount) := [{', '.join(map(str,pieces))}]",
              f"def {sn}Links : List (Fin C898Relaxation.linksCount) := [{', '.join(str(w['index']) for w in used_links)}]",'',
              f'theorem {sn}Plans_checked : ∀ plan ∈ {sn}Plans,',
              f'    plan.Check complement (pairRecordAt {rec}) {rec}.size := by',
              '  decide +kernel','',
              f'theorem {sn}Cover_checked : PairStepCheck {source_domain}Ids',
              f'    {neighbor_domain}Ids {sn}Pieces {sn}Plans := by',
              '  decide +kernel','',
              f'theorem {sn}Links_checked : ∀ piece ∈ {sn}Pieces, ∃ i ∈ {sn}Links,',
              '    (C898Relaxation.links i).source = piece ∧',
              f'    (C898Relaxation.links i).target ∈ {target_domain}Ids := by',
              '  decide +kernel','',
              f'theorem {sn}_sound (q t : S12Pilot.OpenSquare)',
              f'    (hq : OrientedPoseCovered {source_domain} q)',
              f'    (ht : OrientedPoseCovered {neighbor_domain} t)',
              '    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :',
              f'    OrientedPoseCovered {target_domain} q := by',
              f'  have hp := pair_step_sound {source_domain}Ids {neighbor_domain}Ids',
              f'    {sn}Pieces {sn}Plans complement (pairRecordAt {rec}) {rec}.size',
              f'    {sn}Cover_checked {sn}Plans_checked',
              f'    (pairRecordAt_checked {rec} {rec}_checked) q t hq ht disjoint',
              '  obtain ⟨piece, member, realizes⟩ := hp',
              '  obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp member',
              f'  obtain ⟨i, _, hsource, htarget⟩ := {sn}Links_checked piece hpiece',
              '  refine ⟨poses (C898Relaxation.links i).target,',
              '    List.mem_map.mpr ⟨_, htarget, rfl⟩, ?_⟩',
              '  exact C898Relaxation.link_sound i q (by simpa only [hsource] using realizes)','',
              f'#print axioms {sn}_sound','end N12Compact.C898Shared','']
    (out/f'PairStep{step:02}.lean').write_text('\n'.join(lines))
paths=[out/'SharedDomains.lean',out/'PairComplements.lean']+[out/f'PairStep{i:02}.lean' for i in sorted(steps)]
proofs={'scope':'Entire13 pairwise transitions assembled, including all-source/all-neighbor coverage and exact named relaxation links. Source only until Lean replay.',
        'steps':steps,'plans':len(plans),'pieces':sum(len(p['pieces']) for p in plans),
        'files':[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'lines':p.read_bytes().count(b'\n'),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]}
(ROOT/'evidence/c898-pair-step-assembly.json').write_text(json.dumps(proofs,indent=2)+'\n')
print(json.dumps({'steps':len(steps),'plans':len(plans),'pieces':proofs['pieces'],'files':len(paths),'bytes':sum(x['bytes'] for x in proofs['files']),'lines':sum(x['lines'] for x in proofs['files'])}))
