#!/usr/bin/env python3
"""Audit common-window vertical cuts and direct interval-complement plans."""
from provenance_source import read_bytes, read_text, text_stream
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
import json,re,time,resource
ROOT=Path(__file__).resolve().parents[1]
start=time.monotonic()
data=json.loads((ROOT/'evidence/c898-shared-pose-map.json').read_text())
poses={p['name']:p for p in data['poses']}
rows=[tuple(F(x,r['denominator']) for x in r['integers'])+(r['strict'],) for r in data['rows']]
text=read_text(ROOT/'vendor/S12/Push898Chunk56.lean')
decls={m[1]:m[0] for m in re.finditer(r'^(?:def|theorem) (\w+)\b.*?(?=^(?:def|theorem) |\Z)',text,re.M|re.S)}
radii={int(m[1]):F(m[2]) for m in re.finditer(r'^def angleChordRadius64_(\d+).*?,\(([^()]*)\)⟩$',(ROOT/'vendor/S12/AngleChordRadiusData.lean').read_text(),re.M)}
assert len(radii)==64
windows={}
for step in (9,10):
    m=re.search(r'columnWindow \(([^()]*)\) \(([^()]*)\)',decls[f'continuousScout898Step{step}WindowRows'])
    windows[step]=tuple(F(x) for x in m.groups())
def supports(a,b,t):
    det=a[0]*b[1]-a[1]*b[0]
    if not det:return False
    u,v=(t[0]*b[1]-t[1]*b[0])/det,(a[0]*t[1]-a[1]*t[0])/det
    slack=t[2]-u*a[2]-v*b[2]
    return u>=0 and v>=0 and slack>=0 and (not t[3] or slack>0 or u>0 and a[3] or v>0 and b[3])
def pair_for(sr,target,active=None):
    ids=range(len(sr)) if active is None else active
    pair=next((ij for ij in combinations(ids,2) if supports(sr[ij[0]],sr[ij[1]],target)),None)
    if pair is None and active is not None:
        pair=next(((i,j) for i in active for j in range(len(sr)) if i!=j and supports(sr[i],sr[j],target)),None)
    return pair
counts=Counter();neighbors=[];plans=[];failures=[]
for name,decl in decls.items():
    match=re.fullmatch(r'continuousScout898Step(9|10)Neighbor(\d+)Pose(\d+)',name)
    if not match:continue
    step,owner,index=map(int,match.groups());lo,hi=windows[step]
    pn=re.search(r'\+\+(\w+)\.inputs\.map',decl)[1];pose=poses[pn];sr=[rows[i] for i in pose['rows']]
    radius=radii[pose['angle']]
    proof_text=re.search(r'expandImplicationText inputs targets "([^"]*)"',decl)[1]
    out={'name':name,'step':step,'neighbor':owner,'pose':pose['index'],'angle':pose['angle'],'supports':[]}
    for direction,proof in zip((-1,1),proof_text.split(';')):
        target=(F(direction),F(0),radius+lo if direction==-1 else radius-hi,False)
        active=sorted({int(t.split(':')[1])-3 for t in proof.split(',') if F(t.split(':')[0])>0 and int(t.split(':')[1])>=3})
        pair=pair_for(sr,target,active)
        if pair is None:failures.append([name,direction]);continue
        out['supports'].append({'target':[str(v) for v in target[:3]]+[False],
                                'rows':[pose['rows'][i] for i in pair]})
        counts['neighbor_two_row_supports']+=1
    neighbors.append(out);counts['neighbor_leaves']+=1
for name,decl in decls.items():
    match=re.fullmatch(r'continuousScout898Step(9|10)Pose(\d+)Block',name)
    if not match:continue
    step,index=map(int,match.groups());lo,hi=windows[step]
    sn=re.search(r'FourVerticalChordWindow (\w+) ',decl)[1];source=poses[sn];sr=[rows[i] for i in source['rows']]
    radius=radii[source['angle']];lower,upper=lo-radius,hi+radius
    prefix=name[:-5]
    pieces=[p for pn,p in poses.items() if re.fullmatch(prefix+r'Piece\d+',pn)]
    out={'name':prefix,'step':step,'source':source['index'],'angle':source['angle'],
         'lower':str(lower),'upper':str(upper),'branches':[]}
    for direction,bound in ((-1,lower),(1,upper)):
        outside=(F(direction),F(0),-direction*bound,True)
        chosen=None
        for p in pieces:
            pr=[rows[i] for i in p['rows']]
            if all(r in sr or r==outside for r in pr):
                assert p['angle']==source['angle']
                chosen=p;break
        if chosen:
            counts['surviving_branches']+=1
            out['branches'].append({'direction':direction,'piece':chosen['index']})
        else:
            inside=tuple(-v for v in outside[:3])+(False,)
            pair=pair_for(sr,inside)
            if pair is None:failures.append([prefix,direction,'cannot exclude missing branch'])
            else:
                counts['excluded_branches']+=1
                out['branches'].append({'direction':direction,'excluded_by':[source['rows'][i] for i in pair]})
    plans.append(out);counts['plans']+=1
report={'scope':'Exact arithmetic and source-identity audit, not Lean acceptance.',
        'counts':dict(counts),'failures':failures,'seconds':time.monotonic()-start,
        'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(ROOT/'audit/c898-chord-supports.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/'evidence/c898-chord-window-supports.json').write_text(json.dumps({'windows':{k:list(map(str,v)) for k,v in windows.items()},'neighbors':neighbors,'plans':plans},separators=(',',':'))+'\n')
print(json.dumps(report,indent=2))
