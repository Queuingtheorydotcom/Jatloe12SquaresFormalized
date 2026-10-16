"""Fixed exact pair witness and bounded saved-state membership audit; no solver."""
import ast
from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path
import re
import resource
import signal
import time

ROOT = Path(__file__).resolve().parents[1]
OLD = Path(__import__('os').environ.get('N12_LEGACY_PROJECT', str(ROOT.parent / 'n12-jatloe419')))
BASE = OLD/'evidence/C696/root-one'
A = F(1001,1000)
SQUARES = {
    7: (F(9,4),F(2499,1000),F(1),F(0)),
    10: (F(153,50),F(1513,1000),F(9991,10009),F(600,10009)),
}
COMPATIBLE_BINS = {7:(0,63),10:(1,)}


def literal(s):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int: return F(n.value)
        if isinstance(n,(ast.List,ast.Tuple)): return tuple(go(x) for x in n.elts)
        if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div): return go(n.left)/go(n.right)
        raise ValueError(ast.dump(n))
    return go(ast.parse(s,mode='eval').body)


def margin(square,p):
    x,y,c,s=square
    return min(A/2-abs(c*(p[0]-x)+s*(p[1]-y)),A/2-abs(-s*(p[0]-x)+c*(p[1]-y)))


def polygon_margin(p,polygon):
    ps=[tuple(F(z,10**8) for z in v) for v in polygon]
    return min((ps[(j+1)%len(ps)][0]-v[0])*(p[1]-v[1])-
               (ps[(j+1)%len(ps)][1]-v[1])*(p[0]-v[0]) for j,v in enumerate(ps))


def angle_radius_reach(k):
    endpoints=[(F(4096-j*j,4096+j*j),F(128*j,4096+j*j)) for j in (k,k+1)]
    crossing=(endpoints[0][0]-endpoints[0][1])*(endpoints[1][0]-endpoints[1][1])<=0
    radius=F(2071,10000) if crossing else min((c+s-2*c*s)/2 for c,s in endpoints)
    z=max(c+s for c,s in endpoints)
    reach=F(4571,5000) if crossing else (1+2*z-z*z)/2
    return radius,reach


def encode(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [encode(v) for v in x]
    return x


def main():
    resource.setrlimit(resource.RLIMIT_CPU,(10,10))
    signal.alarm(10)
    started=time.monotonic()
    trace_raw=(BASE/'trace.json').read_bytes()
    trace=json.loads(trace_raw)
    cache={}
    def load(key):
        if key not in cache:
            with gzip.open(BASE/'objects'/(key+'.json.gz'),'rb') as f: raw=f.read(1024**2+1)
            assert len(raw)<=1024**2 and hashlib.sha256(raw).hexdigest()==key
            cache[key]=json.loads(raw)
        return cache[key]
    def state(stage): return trace['tree']['steps'][stage-1]['after']
    auxiliary=[]
    aux_source=ROOT/'vendor/S12/AuxiliaryPoints.lean'
    aux_text=aux_source.read_text()
    for name in ('fPoints','gPoints'):
        auxiliary.extend(literal(re.search(r'def '+name+r'[^\n]* := (.+)',aux_text)[1]))
    marker_source=ROOT/'vendor/S12/Markers.lean'
    markers={15 if i=='_' else int(i):literal(p) for i,p in re.findall(
        r'\| (\d+|_) => (.+)',marker_source.read_text().split('def diameterLimit')[0])}
    squares={}
    history={}
    for owner,q in SQUARES.items():
        x,y,c,s=q
        assert c*c+s*s==1
        actual_markers=[i for i,p in markers.items() if margin(q,p)>0]
        actual_aux=[i for i,p in enumerate(auxiliary) if margin(q,p)>0]
        assert actual_markers==trace['groups'][owner]
        assert actual_aux==[i for i in range(20) if trace['masks'][owner]&(1<<i)]
        half_width=A/2*(abs(c)+abs(s))
        assert 0<x-half_width and x+half_width<4 and 0<y-half_width and y+half_width<4
        squares[owner]={'center':[x,y],'normal':[c,s],'side':A,'loU':c*x+s*y-A/2,
            'loV':-s*x+c*y-A/2,'exact_marker_indices':actual_markers,
            'exact_combined_auxiliary_indices':actual_aux,'contained_in_box':True,
            'state54_domain_hash':state(54)['domains'][owner],
            'minimum_state54_hull_margin':min(margin(q,tuple(F(z) for z in p)) for p in load(state(54)['hulls'])[owner])}
        assert squares[owner]['minimum_state54_hull_margin']>0
        changes=[]
        last=None
        for stage in range(54,len(trace['tree']['steps'])+1):
            st=state(stage)
            compatible=[row for row in load(st['domains'][owner]) if row[0] in COMPATIBLE_BINS[owner]]
            good=[row[0] for row in compatible if polygon_margin(q[:2],row[2])>=0]
            hull_min=min(margin(q,tuple(F(z) for z in p)) for p in load(st['hulls'])[owner])
            status=(tuple(good),hull_min>0)
            if status!=last:
                changes.append({'stage':stage,'preceding_action_index':stage-1,
                    'action':trace['tree']['steps'][stage-1]['action'],'compatible_member_bins':good,
                    'all_saved_hull_points_strictly_inside':hull_min>0,'minimum_hull_margin':hull_min,
                    'domain_hash':st['domains'][owner]})
                last=status
        assert changes[0]['compatible_member_bins'] and changes[0]['stage']==54
        history[owner]=changes
    x,y,c,s=SQUARES[10];X,Y,_,_=SQUARES[7]
    separation=s*(x-X)-c*(y-Y)-A/2*(1+c+s)
    target=98*x+49*(c+s-2*c*s)-347
    assert separation>0 and target<0 and F(1,64)<F(3,100)<F(2,64)

    def window(stage,target,owners):
        st=state(stage);ranges={}
        for owner in owners:
            bounds=[]
            for k,mask,ps in load(st['domains'][owner]):
                if mask&trace['masks'][target]: continue
                radius,reach=angle_radius_reach(k)
                xs=[F(p[0],10**8) for p in ps]
                bounds.append((min(max(xs)-radius,4-reach),max(min(xs)+radius,reach)))
            ranges[owner]=(max(lo for lo,hi in bounds),min(hi for lo,hi in bounds))
        return {'lower':max(lo for lo,hi in ranges.values()),'upper':min(hi for lo,hi in ranges.values()),'owner_ranges':ranges}
    windows=[];last=None
    for stage in range(54,79):
        w=window(stage,7,[0,6,11])
        if (w['lower'],w['upper'])!=last:
            windows.append(dict(stage=stage,action=trace['tree']['steps'][stage-1]['action'],**w))
            last=w['lower'],w['upper']
    assert windows[0]['upper']<F(9,5)<=windows[1]['upper'] and windows[1]['stage']==57
    windows10=[];last=None
    for stage in range(54,94):
        w=window(stage,10,[3,7,9])
        if (w['lower'],w['upper'])!=last:
            windows10.append(dict(stage=stage,action=trace['tree']['steps'][stage-1]['action'],**w))
            last=w['lower'],w['upper']
    # A second hand-constructed pair also obeys the newly proposed owner7 cut.
    stronger_squares={
        7:(F(231,100),F(4999,2000),F(1),F(0)),
        10:(F(307,100),F(189,125),F(9991,10009),F(600,10009)),
    }
    stronger_records={}
    stronger_history={}
    for owner,q in stronger_squares.items():
        x,y,c,s=q
        assert c*c+s*s==1
        marker_ids=[i for i,p in markers.items() if margin(q,p)>0]
        aux_ids=[i for i,p in enumerate(auxiliary) if margin(q,p)>0]
        assert marker_ids==trace['groups'][owner]
        assert aux_ids==[i for i in range(20) if trace['masks'][owner]&(1<<i)]
        half_width=A/2*(abs(c)+abs(s))
        assert 0<x-half_width and x+half_width<4 and 0<y-half_width and y+half_width<4
        min_hull=min(margin(q,tuple(F(z) for z in p)) for p in load(state(57)['hulls'])[owner])
        good=[row[0] for row in load(state(57)['domains'][owner])
            if row[0] in COMPATIBLE_BINS[owner] and polygon_margin(q[:2],row[2])>=0]
        assert good and min_hull>0
        stronger_records[owner]={'center':[x,y],'normal':[c,s],'side':A,
            'state57_member_bins':good,'minimum_state57_hull_margin':min_hull,
            'exact_marker_indices':marker_ids,'exact_combined_auxiliary_indices':aux_ids,
            'contained_in_box':True}
        for stage in range(58,len(trace['tree']['steps'])+1):
            st=state(stage)
            good=[row[0] for row in load(st['domains'][owner])
                if row[0] in COMPATIBLE_BINS[owner] and polygon_margin(q[:2],row[2])>=0]
            if not good:
                stronger_history[owner]={'first_domain_removal_stage':stage,
                    'action_index':stage-1,'action':trace['tree']['steps'][stage-1]['action'],
                    'domain_hash':st['domains'][owner]}
                break
        else:
            stronger_history[owner]={'survives_all_saved_domains_through_stage':len(trace['tree']['steps'])}
    x,y,c,s=stronger_squares[10];X,Y,_,_=stronger_squares[7]
    stronger_gap=s*(x-X)-c*(y-Y)-A/2*(1+c+s)
    stronger_target=98*x+49*(c+s-2*c*s)-347
    stronger_cut=X-F(1,2)
    assert stronger_gap>0 and stronger_target<0 and stronger_cut>windows[1]['upper']>F(9,5)
    receipt={'status':'EXACT_RATIONAL_COUNTEREXAMPLE_TO_LOCAL_PAIR_IMPLICATION',
        'scope':'Two real congruent disjoint contained OpenSquares matching owners7/10 exact marker and auxiliary ownership, state54 strict hulls and pose polygons. This is not a twelve-square packing.',
        'sources':{'trace_sha256':hashlib.sha256(trace_raw).hexdigest(),
            'state54_hulls_hash':state(54)['hulls'],
            'markers_sha256':hashlib.sha256(marker_source.read_bytes()).hexdigest(),
            'auxiliary_sha256':hashlib.sha256(aux_source.read_bytes()).hexdigest()},
        'squares':squares,'owner10_half_angle':F(3,100),
        'owner7_axis_endpoint_bins':[0,63],
        'separating_normal_from_owner7_to_owner10':[s,-c],
        'strict_projection_gap':separation,'violated_target_value':target,
        'saved_state_membership_changes':history,
        'owner7_vertical_window_changes_neighbors_0_6_11':windows,
        'owner10_vertical_window_neighbors_3_7_9_at_stage93':window(93,10,[3,7,9]),
        'owner10_vertical_window_changes_neighbors_3_7_9':windows10,
        'stronger_owner7_capacity_cut_counterexample':{
            'scope':'State57 owner7/10 local facts plus X7-rho7>9/5, even exceeding the full stage57 common-window upper endpoint, still do not imply the owner10 radius cut.',
            'squares':stronger_records,'strict_projection_gap':stronger_gap,
            'violated_target_value':stronger_target,'owner7_X_minus_radius':stronger_cut,
            'saved_state_first_domain_removals':stronger_history},
        'caveat':'Exact window arithmetic is a candidate source check. No initial coverage, transition ancestry, or Lean replay was performed.',
        'seconds':time.monotonic()-started,'peak_self_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'saved_objects_read':len(cache)}
    assert receipt['peak_self_rss_bytes']<128*1024**2
    out=Path(__file__).with_name('c696-pair-cut-audit.json')
    out.write_text(json.dumps(encode(receipt),indent=2)+'\n')
    print(json.dumps(encode({k:receipt[k] for k in ('status','strict_projection_gap','violated_target_value','seconds','peak_self_rss_bytes','saved_objects_read')})))


if __name__=='__main__':main()
