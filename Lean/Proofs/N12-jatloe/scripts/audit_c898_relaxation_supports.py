#!/usr/bin/env python3
"""Bounded exact audit of all recovered C898 relaxation links; no Lean replay."""
from provenance_source import read_bytes, read_text, text_stream
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
import json, re, time, resource

ROOT = Path(__file__).resolve().parents[1]
start = time.monotonic()
data = json.loads((ROOT/'evidence/c898-shared-pose-map.json').read_text())
poses = {p['name']: p for p in data['poses']}
raw = data['rows']
rows = [tuple(F(x,r['denominator']) for x in r['integers'])+(r['strict'],) for r in raw]
counts, failures, links = Counter(), [], []

def supports(a,b,t):
    det = a[0]*b[1]-a[1]*b[0]
    if not det: return False
    u,v = (t[0]*b[1]-t[1]*b[0])/det, (a[0]*t[1]-a[1]*t[0])/det
    slack = t[2]-u*a[2]-v*b[2]
    return u>=0 and v>=0 and slack>=0 and (not t[3] or slack>0 or u>0 and a[3] or v>0 and b[3])

for chunk in range(66):
    with text_stream(ROOT/f'vendor/S12/Push898Chunk{chunk}.lean') as stream:
        for line_no,line in enumerate(stream,1):
            if ' : RelaxationLink :=' not in line: continue
            m = re.search(r'^def (\w+) : RelaxationLink := ⟨(\w+),(\w+),.*?"([^"]*)"',line)
            assert m, (chunk,line_no,line[:150])
            name,sn,tn,text = m.groups()
            s,t = poses[sn],poses[tn]
            assert s['angle']==t['angle'], name
            sr,tr = [rows[i] for i in s['rows']],[rows[i] for i in t['rows']]
            proofs = text.split(';')
            assert len(proofs)==len(tr),name
            record={'name':name,'source':s['index'],'target':t['index'],'proofs':[]}
            counts['links']+=1;counts['old_weight_bytes']+=len(text)
            for target_id,target,proof in zip(t['rows'],tr,proofs):
                counts['target_occurrences']+=1
                terms=[(F(a),int(b)) for a,b in (term.split(':') for term in proof.split(','))]
                opposite=tuple(-v for v in target[:3])+(not target[3],)
                allrows=[opposite]+sr
                assert all(w>=0 and 0<=i<len(allrows) for w,i in terms),name
                assert all(sum(w*allrows[i][k] for w,i in terms)==0 for k in range(3)),name
                assert any(w>0 and allrows[i][3] for w,i in terms),name
                if target_id in s['rows']:
                    record['proofs'].append([target_id,'alias']);counts['aliases']+=1;continue
                active=sorted({i-1 for w,i in terms if w>0 and i>0 and (sr[i-1][0] or sr[i-1][1])})
                pair=next((ij for ij in combinations(active,2) if supports(sr[ij[0]],sr[ij[1]],target)),None)
                if pair is None:
                    # Rank-one original supports need an unused independent row at weight zero.
                    pair=next(((i,j) for i in active for j in range(len(sr)) if i!=j and supports(sr[i],sr[j],target)),None)
                if pair is None:
                    failures.append([name,target_id,active]);record['proofs'].append([target_id,'fallback',proof]);counts['fallbacks']+=1
                else:
                    record['proofs'].append([target_id,s['rows'][pair[0]],s['rows'][pair[1]]]);counts['two_row']+=1
            links.append(record)
distinct={tuple(p) for w in links for p in w['proofs'] if p[1]!='alias' and p[1]!='fallback'}
counts['distinct_two_row_checks']=len(distinct)
report={'scope':'Exact rational reconstruction only; Lean checks and original-model assembly remain required.',
        'counts':dict(counts),'failures':failures,'seconds':time.monotonic()-start,
        'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(ROOT/'audit/c898-relaxation-supports.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/'evidence/c898-relaxation-two-index-witnesses.json').write_text(json.dumps(links,separators=(',',':'))+'\n')
print(json.dumps(report,indent=2))
