from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import re

pt = lambda x, y: (F(str(x)), F(str(y)))
markers = [pt(1,.914),pt(.914,1),pt(3,.914),pt(3.086,1),pt(3,3.086),pt(3.086,3),pt(1,3.086),pt(.914,3),pt(1.65,1.65),pt(2.35,1.65),pt(2.35,2.35),pt(1.65,2.35),pt(.914,2),pt(2,.914),pt(3.086,2),pt(2,3.086)]
aux = [pt(1,1.74),pt(1,2.26),pt(1.6,1),pt(1.6,3),pt(2,1.74),pt(2,2.26),pt(2.4,1),pt(2.4,3),pt(3,1.74),pt(3,2.26),pt(1,1.6),pt(1,2.4),pt(1.74,1),pt(1.74,2),pt(1.74,3),pt(2.26,1),pt(2.26,2),pt(2.26,3),pt(3,1.6),pt(3,2.4)]
seed = [[pt(1.12,1),pt(1.74,1),pt(1.87,.76)],[pt(1,1.12),pt(1,1.74),pt(.76,1.87)],[pt(3,1)],[pt(3,3)],[pt(1,3)]] + [[]]*7
indices = [[0],[1],[2,3],[4,5],[6,7],[9],[10],[11],[12],[13],[14],[15]]
rows = re.findall(r'^    \[(.*)\][,]?', Path('Completion/Cases/C981/VectorData.lean').read_text(), re.M)
cross = lambda a,b,c: (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def hull(points):
    points=sorted(set(points)); low=[]; high=[]
    for p in points:
        while len(low)>1 and cross(low[-2],low[-1],p)<=0: low.pop()
        low.append(p)
    for p in reversed(points):
        while len(high)>1 and cross(high[-2],high[-1],p)<=0: high.pop()
        high.append(p)
    return low[:-1]+high[:-1] if len(points)>1 else points

def contains(p,h):
    return all(cross(a,b,p)>=0 for a,b in zip(h,h[1:]+h[:1])) if len(h)>=3 else p in h

def intersection(a,b,c,d):
    u=(b[0]-a[0],b[1]-a[1]); v=(d[0]-c[0],d[1]-c[1]); w=(c[0]-a[0],c[1]-a[1]); det=u[0]*v[1]-v[0]*u[1]
    if not det: return None
    t=(w[0]*v[1]-v[0]*w[1])/det; s=(w[0]*u[1]-u[0]*w[1])/det
    if 0<=t<=1 and 0<=s<=1: return (a[0]+t*u[0],a[1]+t*u[1])

def completion(a,b,e):
    u=(e[0]-a[0],e[1]-a[1]); v=(e[0]-b[0],e[1]-b[1]); det=u[0]*v[1]-v[0]*u[1]
    if not det: return None
    z=a[0]*u[0]+a[1]*u[1]; w=b[0]*v[0]+b[1]*v[1]
    p=((z*v[1]-w*u[1])/det,(u[0]*w-v[0]*z)/det)
    if (p[0]-e[0])**2+(p[1]-e[1])**2>1 or cross(a,b,p)*cross(a,b,e)>=0 or cross(p,e,a)*cross(p,e,b)>=0: return None
    if max(p[0].denominator,p[1].denominator)<=10000: return p
    # Exact inward rational selection, checked by all four theorem tests.
    grid=1000; x=(p[0]*grid).__floor__(); y=(p[1]*grid).__floor__()
    candidates=[(F(x+u,grid),F(y+v,grid)) for u in [-1,0,1,2] for v in [-1,0,1,2]]
    candidates.sort(key=lambda z:(z[0]-p[0])**2+(z[1]-p[1])**2)
    for z in candidates:
        if (z[0]-e[0])**2+(z[1]-e[1])**2>1: continue
        if cross(a,b,z)*cross(a,b,e)>=0 or cross(z,e,a)*cross(z,e,b)>=0: continue
        if any((z[0]-v[0])*(e[0]-v[0])+(z[1]-v[1])*(e[1]-v[1])<0 for v in [a,b]): continue
        return z

def intersect_hulls(H):
    for i,j in combinations(range(12),2):
        for p in H[i]:
            if contains(p,H[j]): return (i,j,p)
        for a,b in zip(H[i],H[i][1:]+H[i][:1]):
            for c,d in zip(H[j],H[j][1:]+H[j][:1]):
                p=intersection(a,b,c,d)
                if p: return (i,j,p,('edge',a,b,c,d))

def explore(n, rounds=8):
    labels=[set(map(int,re.findall(r'\d+',a))) for a,b in re.findall(r'\{([^}]*)\}|(∅)',rows[n])]
    H=[hull([markers[k] for k in indices[i]]+seed[i]+[aux[k] for k in labels[i]]) for i in range(12)]
    H[8]=hull(H[8]+[pt(1,2.8)])
    H[9]=hull(H[9]+[pt(2.8,1)])
    base=[set(H[i]) for i in range(12)]; derivation={}
    for rnd in range(rounds):
        foreign=[(set(markers)-{markers[k] for k in indices[i]}) | (set(aux)-{aux[k] for k in labels[i]}) | {p for j in range(12) if j!=i for p in H[j]} for i in range(12)]
        new=[]; additions=0
        for i in range(12):
            points=list(H[i])
            for a,b in combinations(H[i],2):
                for e in sorted(foreign[i]):
                    p=completion(a,b,e)
                    if p is not None and p not in points:
                        points.append(p); additions+=1
                        derivation.setdefault((i,p),(rnd,a,b,e))
            new.append(hull(points))
        unchanged=H==new; H=new; win=intersect_hulls(H)
        print('row',n,'round',rnd+1,'additions',additions,'sizes',[len(h) for h in H],'win',win,flush=True)
        if win:
            def explain(i,p,seen):
                if (i,p) in seen: return
                seen.add((i,p))
                if p in base[i]: print('BASE',i,p,flush=True); return
                if (i,p) in derivation:
                    rnd,a,b,e=derivation[i,p]
                    print('FORCE',i,p,'from',a,b,'missing',e,flush=True)
                    explain(i,a,seen); explain(i,b,seen)
                    for j in range(12):
                        if j!=i and (e in base[j] or (j,e) in derivation): explain(j,e,seen); break
            seen=set()
            for i in win[:2]:
                for p in H[i]: explain(i,p,seen)
            return
        if not additions or unchanged: return

if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:]): explore(n)
