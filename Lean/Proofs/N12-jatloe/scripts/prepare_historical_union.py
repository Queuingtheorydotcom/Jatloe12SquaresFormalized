#!/usr/bin/env python3
"""One exact all-six historical bank, emitted only as a parent-run proposal.

Each leaf module contains at most2048 original records. Small facade trees
join those leaves with the original separator records, preserving the exact
existing sparse API and all114465/28235 original IDs. No active edits, Lean,
search, subprocess, network, or generated certificate claims.
"""
from pathlib import Path
import argparse,hashlib,json,resource,shutil,signal,sys,time

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'evidence/historical-compact-data'
DEST=ROOT/'evidence/proposals/HistoricalUnion'
LEAF_LIMIT=2048


def need(test,message):
    if not test:raise ValueError(message)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def sources_for(rows,poses):
    """Pure exact source specification, also used by the alias activation guard."""
    need(all(row['index']==i and row['denominator']>0 for i,row in enumerate(rows)),
        'row IDs/positive denominators differ from original table')
    need(all(pose['index']==i and 0<=pose['angle']<192 and
        all(0<=r<len(rows) for r in pose['rows']) for i,pose in enumerate(poses)),
        'pose/angle/row IDs differ from original table')
    outputs={};chunks=[]
    outputs['Compact/HistoricalData/Counts.lean']=f'''namespace N12Compact.HistoricalData
abbrev rowCount : Nat := {len(rows)}
abbrev poseCount : Nat := {len(poses)}
end N12Compact.HistoricalData
'''
    def row_text(i):
        row=rows[i]
        return ','.join(map(str,row['integers']))+','+str(row['strict']).lower()+','+str(row['denominator']-1)
    def value(kind,i):
        if kind=='Rows':
            r=rows[i]
            return '(⟨'+','.join(map(str,r['integers']))+','+str(r['strict']).lower()+f'⟩,{r["denominator"]-1})'
        return '('+str(poses[i]['angle'])+', ['+','.join(map(str,poses[i]['rows']))+'])'
    def build(kind,start,stop):
        count=stop-start
        if count<=LEAF_LIMIT:
            namespace=f'N12Compact.HistoricalData.{kind}Chunks'
            name=f'part{start:06}'
            module=f'Compact.HistoricalData.{kind}Chunks.Part{start:06}'
            path=module.replace('.','/')+'.lean'
            typ='SparseLiteral.Tree (IntegerSupport.Row × Nat)' if kind=='Rows' else \
                'SparseLiteral.Tree (Fin 192 × List (Fin rowCount))'
            parser='sparse_rows%' if kind=='Rows' else f'sparse_poses% 192 {len(rows)}'
            records=[f'{i}:'+row_text(i) if kind=='Rows' else
                f'{i}:{poses[i]["angle"]};'+','.join(map(str,poses[i]['rows'])) for i in range(start,stop)]
            outputs[path]='\n'.join(['import Compact.Core.SparseLiteral',
                'import Compact.HistoricalData.Counts','',f'namespace {namespace}',
                'set_option Elab.async false',f'noncomputable def {name} : {typ} := {parser} "',
                *records,'"',f'end {namespace}',''])
            chunks.append({'kind':kind,'start':start,'stop':stop,'module':module,'path':path})
            return f'{kind}Chunks.{name}'
        middle=(start+stop)//2
        left=build(kind,start,middle);right=build(kind,middle+1,stop)
        return f'(.node {middle} {value(kind,middle)}\n  {left}\n  {right})'
    row_tree=build('Rows',0,len(rows));pose_tree=build('Poses',0,len(poses))
    row_imports=['import '+c['module'] for c in chunks if c['kind']=='Rows']
    pose_imports=['import '+c['module'] for c in chunks if c['kind']=='Poses']
    outputs['Compact/HistoricalData/SharedRows.lean']='\n'.join(row_imports)+f'''

/-! Complete original all-six rows. Every in-range ID is present exactly once;
bounded leaf modules avoid elaborating the complete constructor tree at once. -/
namespace N12Compact.HistoricalData
open IntegerSupport
set_option Elab.async false
noncomputable def rowData : SparseLiteral.Tree (Row × Nat) :=
  {row_tree}
noncomputable def rowPair (index : Nat) : Row × Nat :=
  SparseLiteral.lookup (⟨0,0,0,false⟩,0) rowData index
noncomputable def rows (i : Fin rowCount) : Row := (rowPair i.val).1
noncomputable def denominators (i : Fin rowCount) : Nat := (rowPair i.val).2+1
theorem positive_denominators (i : Fin rowCount) : 0 < denominators i := Nat.zero_lt_succ _
end N12Compact.HistoricalData
'''
    outputs['Compact/HistoricalData/SharedPoses.lean']='\n'.join([
        'import Compact.HistoricalData.SharedRows','import S12.OwnerEnclosure',*pose_imports])+f'''

namespace N12Compact.HistoricalData
open S12
set_option Elab.async false
noncomputable def poseData : SparseLiteral.Tree (Fin 192 × List (Fin rowCount)) :=
  {pose_tree}
noncomputable def poseRecord (index : Nat) : Fin 192 × List (Fin rowCount) :=
  SparseLiteral.lookup (0,[]) poseData index
noncomputable def poseAngle (i : Fin poseCount) : Fin 192 := (poseRecord i.val).1
noncomputable def poseRows (i : Fin poseCount) : List (Fin rowCount) := (poseRecord i.val).2
noncomputable def poses (angles : Fin 192 → {{w : AngleEnclosure // w.Check}})
    (i : Fin poseCount) : PoseLeaf :=
  ⟨angles (poseAngle i), (poseRows i).map (fun r => (rows r).normalized (denominators r))⟩
end N12Compact.HistoricalData
'''
    return outputs,chunks


def validate_bank(bank_root,rows,poses):
    expected,_=sources_for(rows,poses)
    for name,text in expected.items():
        path=bank_root/name
        need(path.is_file() and path.read_bytes()==text.encode(),
            'bank is not the complete exact all-six source: '+str(path))
    return {name:sha(text.encode()) for name,text in expected.items()}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',action='store_true')
    need(parser.parse_args().run,'parent bounded slot and --run required')
    start=time.monotonic();stage=DEST.with_name(DEST.name+'.staging')
    need(not DEST.exists() and not stage.exists(),'refusing existing proposal')
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        need(time.monotonic()-start<55 and rss<256*1024**2,'55second/256MiB guard')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    sources={}
    def load(name):
        path=BASE/name;raw=path.read_bytes();sources[str(path.relative_to(ROOT))]=sha(raw)
        return json.loads(raw)
    rows=load('rows.json');poses=load('poses.json');outputs,chunks=sources_for(rows,poses);guard()
    need(sum(len(s.encode()) for s in outputs.values())<32*1024**2,'32MiB source output cap')
    stage.mkdir(parents=True)
    try:
        for name,source in outputs.items():
            guard();path=stage/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        exact=validate_bank(stage,rows,poses)
        report={'scope':'Exact complete shared source proposal; Lean replay and activation pending',
            'row_count':len(rows),'pose_count':len(poses),'leaf_limit':LEAF_LIMIT,
            'chunks':chunks,'sources':sources,'outputs':exact,'lean_modules':len(outputs),
            'lean_lines':sum(s.count('\n') for s in outputs.values()),
            'lean_bytes':sum(len(s.encode()) for s in outputs.values()),
            'seconds':time.monotonic()-start}
        (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        stage.rename(DEST)
        print(json.dumps({k:v for k,v in report.items() if k not in ('chunks','sources','outputs')},indent=2))
    except BaseException:
        shutil.rmtree(stage);raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
