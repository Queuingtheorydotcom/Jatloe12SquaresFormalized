#!/usr/bin/env python3
"""Bounded exact reconstruction experiment, not Lean proof acceptance."""
from provenance_source import read_bytes, read_text, text_stream
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from itertools import combinations
from functools import lru_cache
import hashlib
import json
import re
import time

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(r'^(?:noncomputable )?(?:def|theorem) ([A-Za-z0-9_]+)',re.M)
CAP = 64*1024**2
started = time.monotonic()
leaves, blocks, angles = {}, {}, {}
source_hashes = []

def declarations(number):
    p=ROOT/f'vendor/S12/Push898Chunk{number}.lean'
    raw=read_bytes(p)
    text=raw.decode()
    matches=list(DECL.finditer(text))
    for j,m in enumerate(matches):
        end=matches[j+1].start() if j+1<len(matches) else len(text)
        yield m.group(1),text[m.start():end]

for number in range(66):
    p=ROOT/f'vendor/S12/Push898Chunk{number}.lean'
    source_hashes.append({'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(read_bytes(p)).hexdigest()})
    for name,d in declarations(number):
        if re.search(r' : PoseLeaf :=',d[:200]):
            m=re.search(r'regionConstraintsFromText "([^"\n]*)"',d)
            if m:leaves[name]=m[1]
        if re.fullmatch(r'continuousScout898Step\d+Pose\d+BlockRows',name):
            blocks[name]=d.split('\n')[0].split(':=',1)[1].strip()
for line in (ROOT/'vendor/S12/AngleData.lean').read_text().splitlines():
    m=re.match(r'def angle64_(\d+) : AngleEnclosure := ⟨(.*)⟩$',line)
    if m:
        v=[F(x.replace('(','').replace(')','')) for x in m[2].split(',')]
        angles[int(m[1])]=(v[2],v[3],v[5])

@lru_cache(maxsize=4096)
def leaf_rows(name):
    text=leaves[name]
    return tuple(tuple([F(t) for t in row.split(',')[:3]]+[row.split(',')[3]=='1'])
                 for row in text.split(';')) if text else ()

@lru_cache(maxsize=1024)
def block_rows(name):
    text=blocks[name]
    if text=='[]':return ()
    matches=re.findall(r'⟨⟨!\[([^,\]]+),([^\]]+)\],([^⟩]+)⟩,(true|false)⟩',text)
    assert matches and len(matches)==text.count('⟨⟨!['),(name,text)
    return tuple(tuple([F(x.replace('(','').replace(')','')) for x in row[:3]]+[row[3]=='true']) for row in matches)

def radius(a,x,y):
    c,s,side=a
    return side/2*(abs(x*c+y*s)+abs(-x*s+y*c))

@lru_cache(maxsize=4096)
def axis_targets(ai,bi):
    a,b=angles[ai],angles[bi]
    axes=[(a[0],a[1]),(-a[1],a[0]),(b[0],b[1]),(-b[1],b[0])]
    return tuple((u,v,radius(a,u,v)+radius(b,u,v)) for x,y in axes for u,v in [(x,y),(-x,-y)])

def solve(rows,indices,direction):
    (x1,y1,_,_),(x2,y2,_,_)=[rows[i] for i in indices]
    x,y=direction;det=x1*y2-y1*x2
    if not det:return None
    weights=((x*y2-y*x2)/det,(x1*y-y1*x)/det)
    if any(w<0 for w in weights):return None
    return sum(w*rows[i][2] for w,i in zip(weights,indices)),indices,weights

def best_two(rows,active,direction):
    # One nonzero normal can be padded with a zero-weight independent row.
    candidates=active
    if len(active)<2:
        candidates=sorted(set(active)|{i for i,r in enumerate(rows) if r[0] or r[1]})
    options=[s for ids in combinations(candidates,2) if (s:=solve(rows,ids,direction)) is not None]
    return min(options,key=lambda x:x[0]) if options else None

summary=Counter();pattern=Counter();by_step={str(i):Counter() for i in list(range(9))+list(range(11,15))}
failures=[];output_bytes=0;original_weight_bytes=0
output_path=ROOT/'evidence/c898-all-pair-four-index-witnesses.jsonl'
with output_path.open('w') as out:
    for chunk in range(66):
        for name,d in declarations(chunk):
            m=re.fullmatch(r'continuousScout898Step(\d+)Pose(\d+)Overlap(\d+)',name)
            if not m:continue
            step=m[1];stat=by_step[step]
            ai,bi=[int(n) for n in re.findall(r'let [ab] : .*?angle64_(\d+)\.reference',d)]
            block,source=re.search(r'let ia := (\w+BlockRows)\+\+(\w+)\.inputs',d).groups()
            neighbor=re.search(r'let ib := (\w+)\.inputs',d)[1]
            A=block_rows(block)+leaf_rows(source);B=leaf_rows(neighbor)
            rows=[(x,y,F(0),F(0),z,t) for x,y,z,t in A]+[(F(0),F(0),x,y,z,t) for x,y,z,t in B]
            proof_text=re.search(r'\(axisOverlapForms a.val b.val\) "([^"\n]*)"',d)[1]
            original_weight_bytes+=len(proof_text)
            proofs=proof_text.split(';');assert len(proofs)==8
            record={'name':name,'source':source,'block':block,'neighbor':neighbor,'angles':[ai,bi],'supports':[],'fallbacks':{}}
            for axis,(proof,(nx,ny,radius_sum)) in enumerate(zip(proofs,axis_targets(ai,bi))):
                weights=[(F(t.split(':')[0]),int(t.split(':')[1])) for t in proof.split(',')]
                allrows=[(-nx,-ny,nx,ny,-radius_sum,False)]+rows
                assert all(w>=0 and i<len(allrows) for w,i in weights)
                assert all(sum(w*allrows[i][k] for w,i in weights)==0 for k in range(5)),(name,axis,'original arithmetic')
                assert any(w>0 and allrows[i][5] for w,i in weights)
                summary['original_exact_checks_passed']+=1;stat['implications']+=1
                aa=sorted({i-1 for w,i in weights if w and 0<i<=len(A) and (A[i-1][0] or A[i-1][1])})
                bb=sorted({i-1-len(A) for w,i in weights if w and i>len(A) and (B[i-1-len(A)][0] or B[i-1-len(A)][1])})
                pattern[f'{len(aa)}+{len(bb)}']+=1
                sa=best_two(A,aa,(nx,ny));sb=best_two(B,bb,(-nx,-ny))
                reason=None
                if sa is None or sb is None:reason='no independent support pair'
                else:
                    ca,aa,wa=sa;cb,bb,wb=sb
                    constant=-radius_sum+ca+cb
                    strict=constant<0 or any(w>0 and row[3] for w,row in zip(wa+wb,[A[i] for i in aa]+[B[i] for i in bb]))
                    if constant>0 or not strict:reason='constant or strictness'
                if reason:
                    record['supports'].append(None);record['fallbacks'][str(axis)]=proof
                    failures.append([name,axis,reason]);stat['fallbacks']+=1;summary['fallbacks']+=1
                else:
                    indices=[*aa,*bb];assert all(0<=i<65536 for i in indices)
                    record['supports'].append(indices);stat['four_index']+=1;summary['four_index']+=1
            summary['certificates']+=1;stat['certificates']+=1
            line=json.dumps(record,separators=(',',':'))+'\n';output_bytes+=len(line.encode())
            if output_bytes>CAP:raise RuntimeError('64MiB output cap')
            out.write(line)
        if chunk%8==0:
            print(json.dumps({'chunk':chunk,'certificates':summary['certificates'],'seconds':round(time.monotonic()-started,2)}),flush=True)
assert summary['certificates']==25843
result={'scope':'All13 historical C898 pairwise steps; exact Python rational audit only; no Lean theorem acceptance.',
        'counts':dict(summary),'by_step':{k:dict(v) for k,v in by_step.items()},'support_patterns':dict(pattern),
        'original_weight_text_bytes':original_weight_bytes,'u16_support_payload_bytes':8*summary['four_index'],
        'actual_jsonl_bytes':output_bytes,'actual_jsonl_sha256':hashlib.sha256(output_path.read_bytes()).hexdigest(),
        'source_files':source_hashes,'failures':failures,'seconds':time.monotonic()-started,
        'still_required':'Lean integer determinant checker, exact source/block/neighbor coverage and target identity,15-step assembly with2 chord steps; all original assumptions preserved.'}
(ROOT/'audit/c898-all-pair-support-reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['source_files','failures','by_step']},indent=2))
