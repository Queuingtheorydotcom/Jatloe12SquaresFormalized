#!/usr/bin/env python3
"""Assemble compact exact pair records; this does not compile or accept them."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,re,math

ROOT=Path(__file__).resolve().parents[1]
m=json.loads((ROOT/'evidence/c898-shared-pose-map.json').read_text())
poses={p['name']:p for p in m['poses']};blocks={b['name']:b for b in m['blocks']}
out=ROOT/'Compact/Cases/C898'
angles=[]
for line in (ROOT/'vendor/S12/AngleData.lean').read_text().splitlines():
    x=re.match(r'def angle64_(\d+) : AngleEnclosure := ⟨(.*)⟩$',line)
    if x:
        values=[F(t.replace('(','').replace(')','')) for t in x[2].split(',')]
        den=math.lcm(values[2].denominator,values[3].denominator)
        angles.append([int(values[2]*den),int(values[3]*den),den,values[5].numerator,values[5].denominator])
assert len(angles)==64
lines=['import Compact.Core.ReferenceAxis','import S12.AngleData64','import S12.AngleReference','',
       'namespace N12Compact.C898Shared','open S12 ReferenceAxis','',
       'def referenceData : Array Reference := #[']
lines+=['  ⟨'+', '.join(map(str,row))+'⟩,' for row in angles]
lines+= [']','',
 'def references (i : Fin 64) : Reference :=',
 '  ((referenceData[i.val]?).getD ⟨1, 0, 1, 1, 1⟩)','',
 'theorem references_valid : ∀ i : Fin 64, (references i).Valid := by',
 '  decide +kernel','',
 'theorem references_exact (i : Fin 64) : (references i).value =',
 '    ((angles64[i.val]?).getD ⟨angle64_0, angle64_0_checked⟩).val.reference 1 := by',
 '  revert i','  decide +kernel','',
 '#print axioms references_exact','end N12Compact.C898Shared','']
(out/'References.lean').write_text('\n'.join(lines))
lines=['import Compact.Core.PairPruning','import Compact.Cases.C898.SharedPoses',
       'import Compact.Cases.C898.References','',
       'namespace N12Compact.C898Shared','open S12 IntegerSupport PairPruning','',
       'def blockData : Array (List (Fin rowCount)) := #[']
for b in m['blocks']:lines.append('  ['+', '.join(map(str,b['rows']))+'],')
lines+= [']','def blockRows (i : Nat) : List (Fin rowCount) := (blockData[i]?).getD []','',
 'structure PairRecord where','  source : Fin poseCount','  neighbor : Fin poseCount',
 '  block : Nat','  supports : Array (Support rowCount)','',
 'def PairRecord.witness (record : PairRecord) (i : Fin 8) : Support rowCount :=',
 '  (record.supports[i.val]?).getD ⟨0, 0, 0, 0⟩','',
 'noncomputable def PairRecord.Check (record : PairRecord) : Prop :=',
 '  PairPruning.Check rows (blockRows record.block ++ poseRows record.source)',
 '    (poseRows record.neighbor) (references (poseAngle record.source))',
 '    (references (poseAngle record.neighbor)) record.witness','',
 'noncomputable instance (record : PairRecord) : Decidable record.Check :=',
 '  inferInstanceAs (Decidable (PairPruning.Check _ _ _ _ _ _))','',
 'theorem PairRecord.sound (record : PairRecord) (checked : record.Check)',
 '    (q t : S12Pilot.OpenSquare) (hq : (poses record.source).Realizes q)',
 '    (ht : (poses record.neighbor).Realizes t)',
 '    (hblock : ∀ i ∈ blockRows record.block, (rows i).Holds ![centerX q, centerY q]) :',
 '    ∃ x y, q.Inside x y ∧ t.Inside x y := by',
 '  exact PairPruning.actual_overlap rows denominators positive_denominators',
 '    (blockRows record.block) (poseRows record.source) (poseRows record.neighbor)',
 '    (poses record.source) (poses record.neighbor)',
 '    (references (poseAngle record.source)) (references (poseAngle record.neighbor))',
 '    (references_valid _) (references_valid _)',
 '    (references_exact _) (references_exact _) rfl rfl record.witness checked q t hq ht hblock','',
 '#print axioms PairRecord.sound','end N12Compact.C898Shared','']
(out/'PairRecords.lean').write_text('\n'.join(lines))
steps={i:[] for i in list(range(9))+list(range(11,15))};meta=[]
with (ROOT/'evidence/c898-all-pair-four-index-witnesses.jsonl').open() as f:
    for line in f:
        r=json.loads(line);source=poses[r['source']];neighbor=poses[r['neighbor']];block=blocks[r['block']]
        assert r['angles']==[source['angle'],neighbor['angle']] and not r['fallbacks']
        a=block['rows']+source['rows'];b=neighbor['rows']
        supports=[[a[i],a[j],b[k],b[l]] for i,j,k,l in r['supports']]
        match=re.fullmatch(r'continuousScout898Step(\d+)Pose(\d+)Overlap(\d+)',r['name']);step=int(match[1])
        record_index=len(steps[step]);steps[step].append((source['index'],neighbor['index'],block['index'],supports))
        meta.append({'name':r['name'],'step':step,'index':record_index,'plan':int(match[2]),'neighbor_index':int(match[3]),'source':source['index'],'neighbor':neighbor['index'],'block':block['index']})
for step,records in steps.items():
    name=f'pairStep{step}Records'
    lines=['import Compact.Cases.C898.PairRecords','',
           'set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
           'namespace N12Compact.C898Shared','',f'def {name} : Array PairRecord := #[']
    for source,neighbor,block,supports in records:
        data=', '.join('⟨'+', '.join(map(str,s))+'⟩' for s in supports)
        lines.append(f'  ⟨{source}, {neighbor}, {block}, #[{data}]⟩,')
    lines += [']','',f'theorem {name}_checked : ∀ record ∈ {name}.toList, record.Check := by',
              '  decide +kernel','',f'#print axioms {name}_checked','end N12Compact.C898Shared','']
    (out/f'PairStep{step:02}Records.lean').write_text('\n'.join(lines))
payload={'scope':'Assembled compact Lean source; no compilation or acceptance by this script.',
         'records':meta,'steps':{str(i):len(r) for i,r in steps.items()},
         'output_files':[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'lines':p.read_bytes().count(b'\n'),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in [out/'References.lean',out/'PairRecords.lean']+sorted(out.glob('PairStep*Records.lean'))]}
(ROOT/'evidence/c898-pair-record-map.json').write_text(json.dumps(payload,separators=(',',':'))+'\n')
print(json.dumps({'records':len(meta),'files':len(payload['output_files']),'lines':sum(f['lines'] for f in payload['output_files']),'bytes':sum(f['bytes'] for f in payload['output_files'])}))
