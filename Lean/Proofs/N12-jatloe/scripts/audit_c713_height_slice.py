#!/usr/bin/env python3
"""Exact C713 backward-slice audit; prepared for one parent bounded slot.

Can the original owner7 reduced cover plus the marker-derived strict height
cut directly reach Domain7_6/7_7/7_8? Checks CLOSED relaxations, adds the valid
container box, and explicitly tests every absent target angle. No Lean claim,
no fan substitution, no source mutation. Maximum256MiB/60sec/8MiB output.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse,hashlib,itertools,json,re,resource,signal,sys,time
from audit_historical_direct_cover import ROOT,need


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',action='store_true')
    args=ap.parse_args()
    if not args.run:ap.error('prepared only; parent slot and --run required')
    start=time.monotonic()
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        if time.monotonic()-start>55 or rss>256*1024**2:raise RuntimeError('bounded audit limit')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    base=ROOT/'evidence/historical-compact-data'
    paths=[base/n for n in ['manifest.json','C713.json','poses.json','rows.json']]
    manifest,data,poses,rows=[json.loads(p.read_text()) for p in paths]
    need(manifest['status'].startswith('data assembled'),'incomplete source data')
    radius_path=ROOT/'vendor/S12/AngleChordRadiusData.lean'
    receipt=json.loads((ROOT/'evidence/inherited/evidence/C713/case-replay.json').read_text())
    radius_bytes=radius_path.read_bytes();radius_sha=hashlib.sha256(radius_bytes).hexdigest()
    need(radius_sha==receipt['local_source_sha256']['S12.AngleChordRadiusData'],'radius source hash mismatch')
    radii={int(m[0]):Q(m[1].replace('(','').replace(')','')) for m in re.findall(
      r'def angleChordRadius128_(\d+) : AngleChordRadiusCertificate := ⟨⟨angle128_\d+,angle128_\d+_checked⟩,[^,]+,([^⟩]+)⟩',radius_bytes.decode())}
    need(len(radii)==128,'radius grid incomplete')
    source=data['domains']['continuousScout713Domain7_0']
    targets={name:{poses[p]['angle']:p for p in data['domains'][name]} for name in
        ['continuousScout713Domain7_6','continuousScout713Domain7_7','continuousScout713Domain7_8']}
    report={'status':'incomplete','source_count':len(source),'lean_checked':False,
      'hypothesis':'actual original source owns top point and three distinct foreign owners own the closed y=87/50 row points',
      'height_cut':'centerY > 87/50 + original certified angle radius',
      'closed_relaxation_used':True,'container_box_added':True,'targets':{},'sources':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
      'radius_source_sha256':radius_sha}
    for name in targets:report['targets'][name]={'passed':0,'empty':0,'failed':[],'roots':[]}
    tested=0
    for pid in source:
        guard();p=poses[pid];angle=p['angle']-64;need(0<=angle<128,'wrong angle grid')
        cut=Q(87,50)+radii[angle]
        constraints=[tuple(rows[i]['integers']) for i in p['rows']]
        # Positive scaling clears the cut denominator. Actual strictness is
        # deliberately relaxed here, so successful checks are conservative.
        constraints += [(0,cut.denominator,-cut.numerator),(1,0,0),(-1,0,4),(0,1,0),(0,-1,4)]
        constraints=list(dict.fromkeys(constraints));vertices=set()
        for a,b in itertools.combinations(constraints,2):
            ax,ay,ac=a;bx,by,bc=b;D=ax*by-ay*bx
            if not D:continue
            X,Y=ay*bc-ac*by,ac*bx-ax*bc
            if D<0:X,Y,D=-X,-Y,-D
            tested+=1
            if all(x*X+y*Y+c*D>=0 for x,y,c in constraints):vertices.add((Q(X,D),Q(Y,D)))
        for name,target in targets.items():
            target_id=target.get(p['angle']);failure=None
            if target_id is None:
                if vertices:failure={'reason':'absent target has feasible closed center','point':list(map(str,next(iter(vertices))))}
            else:
                for rid in poses[target_id]['rows']:
                    a,b,c=rows[rid]['integers'];strict=rows[rid]['strict']
                    for x,y in vertices:
                        val=a*x+b*y+c
                        if val<0 or strict and val<=0:
                            failure={'reason':'target row fails','row':rid,'strict':strict,'point':[str(x),str(y)],'value':str(val)};break
                    if failure:break
            item={'source':pid,'angle':angle,'target':target_id,'feasible_vertices':len(vertices),'height':str(cut)}
            if failure:report['targets'][name]['failed'].append({**item,**failure})
            else:
                report['targets'][name]['passed']+=1
                if not vertices:report['targets'][name]['empty']+=1
            report['targets'][name]['roots'].append(item)
    report.update(status='complete exact finite audit; Lean instances pending',boundary_pairs=tested,elapsed_seconds=time.monotonic()-start)
    out=ROOT/'evidence/c713-height-slice-audit.json'
    raw=json.dumps(report,indent=2)+'\n';need(len(raw.encode())<8*1024**2,'report cap')
    tmp=out.with_suffix('.json.tmp');tmp.write_text(raw);tmp.replace(out)
    print(json.dumps({n:{k:v for k,v in d.items() if k!='roots' and k!='failed'}|{'failed':len(d['failed'])} for n,d in report['targets'].items()}))
    signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
