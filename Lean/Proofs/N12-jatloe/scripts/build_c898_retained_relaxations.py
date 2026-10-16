#!/usr/bin/env python3
"""Remove obsolete raw-leaf incoming relaxations after direct initial cover.

Retains exactly all927 subsequent pair/chord links and7086 used support
triples, using unchanged IndexedRelaxation and RowSupport soundness. Writes
new modules and copied chord callers only; never edits the active old route.
Explicit --run in parent guard:128MiB,60sec,8MiB output. Never invokes Lean.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import signal
import time

ROOT=Path(__file__).resolve().parents[1]
CASE=ROOT/'Compact/Cases/C898'
DEST=CASE/'RetainedRelaxation'
NAMESPACE='N12Compact.C898RetainedRelaxation'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def nums(values):
    return '['+', '.join(map(str,values))+']'


def header(imports,namespace):
    return [*[f'import {name}' for name in imports], '',
            'set_option Elab.async false','set_option maxRecDepth 10000',
            'set_option linter.unnecessarySeqFocus false','',
            f'namespace {namespace}',
            'open S12 IntegerSupport IndexedRelaxation C898Shared',
            'noncomputable section','']


def close(lines,namespace):
    return '\n'.join(lines+['','end',f'end {namespace}',''])


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',action='store_true')
    if not ap.parse_args().run:ap.error('prepared only; coordinating worker must pass --run')
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('60sec deadline')))
    signal.alarm(60);started=time.monotonic()
    witness=ROOT/'evidence/c898-relaxation-two-index-witnesses.json'
    original_map=ROOT/'evidence/c898-relaxation-link-map.json'
    records=json.loads(witness.read_text());old_map=json.loads(original_map.read_text())
    assert len(records)==len(old_map)==2048
    assert all((r['name'],r['source'],r['target'])==(o['name'],o['source'],o['target'])
               for r,o in zip(records,old_map))
    old_rules=set();rules=[];rule_ids={};kept=[];mapping=[]
    for old_index,record in enumerate(records):
        for proof in record['proofs']:
            if len(proof)==3:old_rules.add(tuple(proof))
        if record['name'].startswith('incoming898ToScout898'):
            assert old_index<1121
            continue
        selected=[]
        for proof in record['proofs']:
            if proof[1]=='alias':continue
            assert len(proof)==3 and all(type(x) is int for x in proof)
            triple=tuple(proof)
            if triple not in rule_ids:rule_ids[triple]=len(rules);rules.append(triple)
            ident=rule_ids[triple]
            if ident not in selected:selected.append(ident)
        index=len(kept)
        assert index==old_index-1121
        kept.append({**record,'support_ids':selected})
        mapping.append({'name':record['name'],'index':index,'old_index':old_index,
                        'source':record['source'],'target':record['target']})
    assert len(kept)==927 and len(rules)==7086 and len(old_rules)==15504
    outputs={}

    def grouped(kind,items,batch,ty,encode,imports,claim):
        groups=[]
        for group,start in enumerate(range(0,len(items),batch)):
            block=items[start:start+batch];mod=f'{kind}{group:02}';namespace=f'{NAMESPACE}.{mod}'
            lines=header(imports+['Compact.Core.FiniteCheckChunks'],namespace)
            lines += [f'def data : Array ({ty}) := #[',
                      *[f'  {encode(item)},' for item in block],']','',
                      f'def get (i : Fin {len(block)}) : {ty} :=',
                      f"  data[i.val]'(by change i.val < {len(block)}; exact i.isLt)",'',
                      f'def Claim (i : Fin {len(block)}) : Prop := {claim}','',
                      f'instance (i : Fin {len(block)}) : Decidable (Claim i) :=',
                      f'  inferInstanceAs (Decidable ({claim}))','']
            count=(len(block)+7)//8
            for i in range(count):
                lines += [f'theorem block{i} : FiniteCheckChunks.Check Claim {i} := by',
                          '  decide +kernel','']
            lines += [f'theorem checked (i : Fin {len(block)}) : {claim} := by',
                      f'  refine FiniteCheckChunks.sound Claim (count := {count}) (by decide) ?_ i',
                      '  intro part','  fin_cases part',
                      *[f'  · exact block{i}' for i in range(count)]]
            outputs[DEST/f'{mod}.lean']=close(lines,namespace)
            groups.append((mod,start,len(block)))
        return groups

    def combine(name,groups,ty,total,claim):
        lines=header([f'Compact.Cases.C898.RetainedRelaxation.{m}' for m,_,_ in groups],NAMESPACE)
        lines += [f'abbrev {name}Count : Nat := {total}',
                  f'def {name} (i : Fin {name}Count) : {ty} :=']
        for k,(module,start,length) in enumerate(groups):
            expr=f'{module}.get ⟨i.val-{start},by omega⟩'
            lines.append(f'  if h{k} : i.val < {start+length} then {expr} else' if k+1<len(groups) else '  '+expr)
        lines += ['',f'theorem {name}_checked (i : Fin {name}Count) : {claim} := by',
                  f'  unfold {name}','  split_ifs',*[f'  · exact {module}.checked _' for module,_,_ in groups]]
        outputs[DEST/f'{name.capitalize()}.lean']=close(lines,NAMESPACE)

    groups=grouped('Supports',rules,512,'Support rowCount',lambda t:'⟨'+','.join(map(str,t))+'⟩',
                   ['Compact.Cases.C898.SharedDictionary'],'(get i).Check rows')
    combine('rules',groups,'Support rowCount',len(rules),'(rules i).Check rows')
    groups=grouped('Links',kept,128,'Link poseCount rulesCount',
                   lambda r:f'⟨{r["source"]},{r["target"]},{nums(r["support_ids"])}⟩',
                   ['Compact.Cases.C898.RetainedRelaxation.Rules'],'(get i).Check dictionary rules')
    combine('links',groups,'Link poseCount rulesCount',len(kept),'(links i).Check dictionary rules')
    lines=header(['Compact.Cases.C898.RetainedRelaxation.Links'],NAMESPACE)
    lines += ['theorem link_sound (i : Fin linksCount) (q : S12Pilot.OpenSquare)',
              '    (h : (poses (links i).source).OrientedRealizes q) :',
              '    (poses (links i).target).OrientedRealizes q :=',
              '  (links i).sound dictionary rules (links_checked i) positive_denominators rules_checked q h','']
    lines += [f'def {r["name"]} : Link poseCount rulesCount := links {i}' for i,r in enumerate(kept)]
    lines += ['','#print axioms link_sound']
    outputs[DEST/'All.lean']=close(lines,NAMESPACE)
    old_to_new={m['old_index']:m['index'] for m in mapping}
    chord_audit=[]
    for step in (9,10):
        source=CASE/f'ChordStep{step}.lean';text=source.read_text()
        match=re.search(r'def relaxationIds : List \(Fin linksCount\) := \[([\d, ]*)\]',text)
        assert match
        old_ids=list(map(int,match[1].split(',')))
        new_ids=[old_to_new[i] for i in old_ids]
        text=text[:match.start(1)]+', '.join(map(str,new_ids))+text[match.end(1):]
        assert text.count('import Compact.Cases.C898.Relaxation.All')==1
        text=text.replace('import Compact.Cases.C898.Relaxation.All',
                          'import Compact.Cases.C898.RetainedRelaxation.All')
        assert text.count(' C898Relaxation ')==1
        text=text.replace(' C898Relaxation ',' C898RetainedRelaxation ')
        output=CASE/f'ChordStep{step}Retained.lean';outputs[output]=text
        chord_audit.append({'step':step,'original':str(source.relative_to(ROOT)),
                            'original_sha256':sha(source),'output':str(output.relative_to(ROOT)),
                            'old_ids':old_ids,'new_ids':new_ids,
                            'changes':'only relaxation import/namespace and bijective link-ID replacement; all geometry and theorem declarations preserved'})
    assert sum(len(v.encode()) for v in outputs.values())<8*1024**2
    for path,text in outputs.items():
        path.parent.mkdir(parents=True,exist_ok=True)
        temporary=path.with_suffix('.lean.tmp');temporary.write_text(text);temporary.replace(path)
    with (ROOT/'evidence/c898-retained-relaxation-link-map.json').open('w') as f:
        json.dump(mapping,f,separators=(',',':'));f.write('\n')
    report={'scope':'retained927 pair/chord links; source assembled, no Lean acceptance',
            'removed_incoming_links':1121,'retained_links':927,'support_rules':7086,
            'removed_support_rules':15504-7086,'support_batch_size':8,
            'namespace':NAMESPACE,'rule_chunk_size':512,'link_chunk_size':128,
            'input_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [witness,original_map]},
            'chord_callers':chord_audit,
            'outputs':{str(p.relative_to(ROOT)):{'bytes':len(t.encode()),'lines':t.count('\n'),
                       'sha256':sha(p)} for p,t in outputs.items()},
            'elapsed_seconds':time.monotonic()-started,
            'integration':'all13 cached pair steps consume the retained map; final mixed assembly must import ChordStep9Retained/10Retained instead of old chord callers; old incoming route stays inactive provenance'}
    (ROOT/'evidence/c898-retained-relaxations.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['retained_links','support_rules','removed_support_rules','elapsed_seconds']}))


if __name__=='__main__':main()
