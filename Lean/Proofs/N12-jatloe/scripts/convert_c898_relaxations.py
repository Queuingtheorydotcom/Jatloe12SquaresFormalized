#!/usr/bin/env python3
"""Encode every audited relaxation using shared checked support indices."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
dest=ROOT/'Compact/Cases/C898/Relaxation';dest.mkdir(exist_ok=True)
records=json.loads((ROOT/'evidence/c898-relaxation-two-index-witnesses.json').read_text())
rules=[];rule_ids={}
for record in records:
    selected=[]
    for proof in record['proofs']:
        if proof[1]=='alias':continue
        assert proof[1]!='fallback'
        key=tuple(proof)
        if key not in rule_ids:rule_ids[key]=len(rules);rules.append(key)
        index=rule_ids[key]
        if index not in selected:selected.append(index)
    record['support_ids']=selected

def grouped(name,items,batch,ty,encode,imports,checktype,checkexpr):
    modules=[];groups=[]
    for group,start in enumerate(range(0,len(items),batch)):
        block=items[start:start+batch];mod=f'{name}{group:02d}';modules.append(mod);groups.append((start,len(block)))
        ns=f'N12Compact.C898Relaxation.{mod}'
        body='\n'.join(f'  {encode(item)},' for item in block)
        text=f'''{imports}

namespace {ns}
open S12 IntegerSupport IndexedRelaxation C898Shared
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def data : Array ({ty}) := #[
{body}
]

def get (i : Fin {len(block)}) : {ty} := data[i.val]'(by exact i.isLt)

theorem all_checked : ∀ w ∈ data.toList, {checktype} := by decide +kernel

theorem checked (i : Fin {len(block)}) : {checkexpr} :=
  all_checked (get i) (Array.getElem_mem_toList i.isLt)

end {ns}
'''
        (dest/f'{mod}.lean').write_text(text)
    return modules,groups

mods,groups=grouped('Supports',rules,1024,'Support rowCount',lambda x:'⟨'+', '.join(map(str,x))+'⟩',
    'import Compact.Cases.C898.SharedDictionary','w.Check rows','(get i).Check rows')

def combined(name,mods,groups,ty,total,check):
    imports='\n'.join('import Compact.Cases.C898.Relaxation.'+x for x in mods)
    lines=[]
    for number,((start,size),mod) in enumerate(zip(groups,mods)):
        expr=f'{mod}.get ⟨i.val - {start}, by omega⟩'
        if number+1<len(groups):lines.append(f'  if h{number} : i.val < {start+size} then {expr} else')
        else:lines.append('  '+expr)
    cases='\n'.join(f'  · exact {mod}.checked _' for mod in mods)
    text=f'''{imports}
import Lean.Elab.Tactic.Omega

namespace N12Compact.C898Relaxation
open S12 IntegerSupport IndexedRelaxation C898Shared
def {name}Count : Nat := {total}
def {name} (i : Fin {name}Count) : {ty} :=
{chr(10).join(lines)}

theorem {name}_checked (i : Fin {name}Count) : {check} := by
  unfold {name}
  split_ifs
{cases}
end N12Compact.C898Relaxation
'''
    (dest/(name.capitalize()+'.lean')).write_text(text)

combined('rules',mods,groups,'Support rowCount',len(rules),'(rules i).Check rows')
mods,groups=grouped('Links',records,128,'Link poseCount rulesCount',
    lambda r:'⟨'+str(r['source'])+', '+str(r['target'])+', ['+', '.join(map(str,r['support_ids']))+']⟩',
    'import Compact.Cases.C898.Relaxation.Rules','w.Check dictionary rules','(get i).Check dictionary rules')
combined('links',mods,groups,'Link poseCount rulesCount',len(records),'(links i).Check dictionary rules')
aliases='\n'.join(f'def {r["name"]} : Link poseCount rulesCount := links {i}' for i,r in enumerate(records))
(dest/'All.lean').write_text(f'''import Compact.Cases.C898.Relaxation.Links

namespace N12Compact.C898Relaxation
open S12 IntegerSupport IndexedRelaxation C898Shared

theorem link_sound (i : Fin linksCount) (q : S12Pilot.OpenSquare)
    (h : (poses (links i).source).OrientedRealizes q) :
    (poses (links i).target).OrientedRealizes q :=
  (links i).sound dictionary rules (links_checked i) positive_denominators rules_checked q h

{aliases}

#print axioms link_sound
end N12Compact.C898Relaxation
''')
mapping=[{'name':r['name'],'index':i,'source':r['source'],'target':r['target']} for i,r in enumerate(records)]
(ROOT/'evidence/c898-relaxation-link-map.json').write_text(json.dumps(mapping,separators=(',',':'))+'\n')
files=list(dest.glob('*.lean'))
report={'scope':'All 2048 original relaxation links; numerical and source assembly only until Lean replay.',
        'support_rules':len(rules),'links':len(records),'lean_modules':len(files),
        'lean_bytes':sum(p.stat().st_size for p in files),
        'lean_lines':sum(p.read_text().count('\n') for p in files)}
(ROOT/'evidence/c898-relaxation-conversion.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
