#!/usr/bin/env python3
"""Prepare C713's exact active dictionary with stable all-six global IDs.

No active edits. Root-only --run under256MiB/60sec; output<=8MiB. Every
original domain, pair source, complete neighbor domain, surviving piece,
retained relaxation endpoint, block and strict complement is retained.
Unselected global IDs have explicit defaults, not claimed original values.
The final original entrance/exit and all finite membership checks must replay.
"""
from collections import defaultdict
from pathlib import Path
import argparse,hashlib,json,resource,shutil,signal,sys,time
from audit_historical_direct_cover import ROOT,need

DEST=ROOT/'evidence/proposals/C713Sparse'


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',action='store_true')
    if not ap.parse_args().run:ap.error('prepared only; parent bounded serial slot and --run required')
    start=time.monotonic();stage=DEST.with_name(DEST.name+'.staging')
    need(not DEST.exists() and not stage.exists(),'refusing existing output')
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        if time.monotonic()-start>55 or rss>256*1024**2:raise RuntimeError('256MiB/55sec limit')
    def stop(*_):raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    stage.mkdir(parents=True)
    try:
        base=ROOT/'evidence/historical-compact-data';hashes={}
        def load(name):
            p=base/name;raw=p.read_bytes();hashes[str(p.relative_to(ROOT))]=hashlib.sha256(raw).hexdigest()
            return json.loads(raw)
        manifest=load('manifest.json');need(manifest['status'].startswith('data assembled'),'incomplete input')
        data=load('C713.json');rows=load('rows.json');poses=load('poses.json');blocks=load('blocks.json');links=load('links.json')
        selected=defaultdict(set);row_reasons=defaultdict(set);block_ids=set();link_ids=set()
        def add_pose(i,why):
            need(type(i)is int and 0<=i<len(poses),'invalid pose ID');selected[i].add(why)
        for name,domain in data['domains'].items():
            for i in domain:add_pose(i,'original_domain')
        for plan in data['plans']:
            add_pose(plan['source'],'pair_source')
            for i in data['domains'][plan['neighbors_name']]:add_pose(i,'complete_neighbor_domain')
            for i in plan['pieces']:add_pose(i,'surviving_piece')
            for i in plan['targets']:add_pose(i,'outgoing_target')
            link_ids.update(plan['links'])
            if plan['block'] is not None:block_ids.add(plan['block'])
        for i in sorted(link_ids):
            link=links[i];need(link['index']==i,'link index mismatch')
            add_pose(link['source'],'relaxation_source');add_pose(link['target'],'relaxation_target')
        for pid in selected:
            for rid in poses[pid]['rows']:row_reasons[rid].add('selected_pose')
        for bid in block_ids:
            for rid in blocks[bid]['rows']:row_reasons[rid].add('actual_block')
        def key(row):return (*row['integers'],row['strict'],row['denominator'])
        row_index={key(row):row['index'] for row in rows};complements={}
        for bid in sorted(block_ids):
            for rid in blocks[bid]['rows']:
                row=rows[rid];opposite=(*(-x for x in row['integers']),not row['strict'],row['denominator'])
                need(opposite in row_index,'missing exact strict complement for row '+str(rid))
                cid=row_index[opposite];complements[rid]=cid;row_reasons[cid].add('strict_complement')
        # Fan bases are certified subsets of these exact block+source contexts;
        # verify the successful pilot explicitly rather than infer membership.
        fans_path=ROOT/'evidence/historical-fans-713/fans.json';raw=fans_path.read_bytes()
        hashes[str(fans_path.relative_to(ROOT))]=hashlib.sha256(raw).hexdigest();fans=json.loads(raw)
        for record in fans['context_records']:
            for _,first,second,*_ in record['entries']:
                need(first in row_reasons and second in row_reasons,'fan basis outside selected semantic closure')
        need(not fans['empty_contexts'],'unexpected C713 empty fallback')
        row_ids=sorted(row_reasons);pose_ids=sorted(selected)
        need(all(r in row_reasons for p in pose_ids for r in poses[p]['rows']),'incomplete pose rows')
        row_source='''import Compact.Core.SparseLiteral

/-! C713 active rows with stable original all-six IDs. Unselected IDs use a
zero default and are outside this audited case closure. Extend the sparse
union with exact original records before activating another case. -/
namespace N12Compact.HistoricalData
open IntegerSupport
set_option Elab.async false
'''+f'abbrev rowCount : Nat := {len(rows)}\n'
        row_source+='noncomputable def rowData : SparseLiteral.Tree (Row × Nat) := sparse_rows% "\n'
        for i in row_ids:
            row=rows[i];need(row['denominator']>0,'nonpositive original denominator')
            row_source+=f'{i}:'+','.join(map(str,row['integers']))+','+str(row['strict']).lower()+','+str(row['denominator']-1)+'\n'
        row_source+='''"
noncomputable def rowPair (index : Nat) : Row × Nat :=
  SparseLiteral.lookup (⟨0,0,0,false⟩,0) rowData index
noncomputable def rows (i : Fin rowCount) : Row := (rowPair i.val).1
noncomputable def denominators (i : Fin rowCount) : Nat := (rowPair i.val).2+1
theorem positive_denominators (i : Fin rowCount) : 0 < denominators i := Nat.zero_lt_succ _
end N12Compact.HistoricalData
'''
        pose_source='''import Compact.HistoricalData.SharedRows
import S12.OwnerEnclosure

namespace N12Compact.HistoricalData
open S12 IntegerSupport
set_option Elab.async false
'''+f'abbrev poseCount : Nat := {len(poses)}\n'
        pose_source+=f'noncomputable def poseData : SparseLiteral.Tree (Fin 192 × List (Fin rowCount)) := sparse_poses% 192 {len(rows)} "\n'
        for i in pose_ids:pose_source+=f'{i}:{poses[i]["angle"]};'+','.join(map(str,poses[i]['rows']))+'\n'
        pose_source+='''"
noncomputable def poseRecord (index : Nat) : Fin 192 × List (Fin rowCount) :=
  SparseLiteral.lookup (0,[]) poseData index
noncomputable def poseAngle (i : Fin poseCount) : Fin 192 := (poseRecord i.val).1
noncomputable def poseRows (i : Fin poseCount) : List (Fin rowCount) := (poseRecord i.val).2
noncomputable def poses (angles : Fin 192 → {w : AngleEnclosure // w.Check})
    (i : Fin poseCount) : PoseLeaf :=
  ⟨angles (poseAngle i), (poseRows i).map (fun r => (rows r).normalized (denominators r))⟩
end N12Compact.HistoricalData
'''
        outputs={'Compact/HistoricalData/SharedRows.lean':row_source,'Compact/HistoricalData/SharedPoses.lean':pose_source}
        total=sum(len(s.encode()) for s in outputs.values());need(total<8*1024**2,'8MiB output cap')
        for name,source in outputs.items():
            guard();p=stage/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(source)
        report={'scope':'C713 source proposal; no Lean acceptance or whole-case claim',
          'case':713,'public_row_count':len(rows),'public_pose_count':len(poses),
          'selected_row_count':len(row_ids),'selected_pose_count':len(pose_ids),
          'selected_rows':row_ids,'selected_poses':pose_ids,'selected_blocks':sorted(block_ids),
          'selected_links':sorted(link_ids),'exact_complements':complements,'sources':hashes,
          'lean_lines':sum(s.count('\n') for s in outputs.values()),'lean_bytes':total,
          'missing_id_behavior':'Explicit zero-row / empty-pose defaults. They do not assert historical meanings for inactive IDs.',
          'active_routes':'All C713 initial/propagated domains and nine pair steps; direct height cut uses existing initial and Domain7_6 target IDs.',
          'outputs':[{'path':n,'sha256':hashlib.sha256(s.encode()).hexdigest(),'lines':s.count('\n'),'bytes':len(s.encode())} for n,s in outputs.items()],
          'seconds':time.monotonic()-start}
        (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');stage.rename(DEST)
        print(json.dumps({k:report[k] for k in ['selected_row_count','selected_pose_count','lean_lines','lean_bytes','seconds']}))
    except BaseException:
        shutil.rmtree(stage);raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)

if __name__=='__main__':main()
