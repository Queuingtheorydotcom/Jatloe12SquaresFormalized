#!/usr/bin/env python3
"""Discover and emit exact shared fans for selected historical case routes.

Default pilot C713; repeat --case for the other five or use --all. Parent alone
runs it in a serial256MiB/120sec slot. Every selected original pair, every axis,
and every fallback is checked with exact integers. Missing feasible vertices
never implies emptiness: only explicit <=3-row strict Farkas certificates do.
Output is ordinary source/data awaiting Lean checking, capped at32MiB. No old
proofs, source interfaces or live import closures are changed.
"""
from bisect import bisect_right
from collections import Counter,defaultdict
from fractions import Fraction as Q
from functools import cmp_to_key,lru_cache
from itertools import combinations
from math import gcd
from pathlib import Path
import argparse,hashlib,json,resource,shutil,signal,sys,time
from audit_historical_direct_cover import ROOT,need
from boundary_fan_cycle import compact_cycle

ALL_CASES=(701,713,717,973,978,979)


def vertex(a,b):
    ax,ay,ac=a;bx,by,bc=b
    X,Y,D=ay*bc-ac*by,ac*bx-ax*bc,ax*by-ay*bx
    if not D:return None
    if D<0:X,Y,D=-X,-Y,-D
    g=gcd(gcd(abs(X),abs(Y)),D)
    return X//g,Y//g,D//g


def cone(a,b,x,y):
    ax,ay,_=a;bx,by,_=b;d=ax*by-ay*bx
    if not d:return None
    sign=1 if d>0 else -1
    u,v=sign*(x*by-y*bx),sign*(ax*y-ay*x)
    return (u,v) if u>=0 and v>=0 else None


def empty_witness(indices,rows):
    """Certificate itself establishes emptiness; absence of vertices does not."""
    def valid(ids,weights):
        weights=list(weights)
        if not any(weights) or any(w<0 for w in weights):return None
        total=[sum(w*rows[i]['integers'][j] for i,w in zip(ids,weights)) for j in range(3)]
        strict=any(w>0 and rows[i]['strict'] for i,w in zip(ids,weights))
        if total[:2]==[0,0] and (total[2]<0 or total[2]==0 and strict):
            g=0
            for w in weights:g=gcd(g,w)
            return {'rows':list(ids),'weights':[w//g for w in weights],
                    'constant':total[2]//g,'strict':strict}
    for i in indices:
        w=valid([i],[1])
        if w:return w
    for i,j in combinations(indices,2):
        a,b=rows[i]['integers'],rows[j]['integers']
        k=0 if a[0] or b[0] else 1
        w=valid([i,j],[abs(b[k]),abs(a[k])])
        if w:return w
    for i,j,k in combinations(indices,3):
        a,b,c=[rows[n]['integers'] for n in (i,j,k)]
        weights=[b[0]*c[1]-b[1]*c[0],c[0]*a[1]-c[1]*a[0],a[0]*b[1]-a[1]*b[0]]
        w=valid([i,j,k],weights) or valid([i,j,k],[-v for v in weights])
        if w:return w
    return None


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run',action='store_true');ap.add_argument('--case',type=int,action='append',choices=ALL_CASES)
    ap.add_argument('--all',action='store_true');ap.add_argument('--output')
    ap.add_argument('--derived-bases',action='store_true',
        help='emit checked one-time Cramer materialization instead of redundant basis fields')
    ap.add_argument('--boundary-cycles',action='store_true',
        help='store cyclic boundary row IDs and derive adjacent bases/start keys; retain checked legacy fallback')
    args=ap.parse_args()
    if not args.run:ap.error('prepared only; parent slot and --run required')
    cases=ALL_CASES if args.all else tuple(sorted(set(args.case or [713])))
    label='-'.join(map(str,cases));lean_label='_'.join(map(str,cases))
    suffix='-cycles' if args.boundary_cycles else '-derived' if args.derived_bases else ''
    out=(ROOT/(args.output or f'evidence/historical-fans-{label}{suffix}')).resolve()
    need(out.is_relative_to((ROOT/'evidence').resolve()),'output must be under evidence')
    stage=out.with_name(out.name+'.staging');need(not out.exists() and not stage.exists(),'existing output')
    stage.mkdir(parents=True);start=time.monotonic();written=0
    report={'status':'incomplete','cases':cases,'lean_checked':False,'whole_cases_proved':False,
            'failures':[],'empty_contexts':[],'sources':{},'derived_bases':args.derived_bases,
            'boundary_cycles':args.boundary_cycles,
            'limits':{'rss_mib':256,'seconds':120,'output_mib':32}}
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        if time.monotonic()-start>115:raise TimeoutError('115sec working deadline')
        if rss>256*1024**2:raise MemoryError('256MiB RSS limit')
    def stop(*_):raise TimeoutError('termination requested')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    def read(path):
        raw=path.read_bytes();report['sources'][str(path.relative_to(ROOT))]=hashlib.sha256(raw).hexdigest()
        return json.loads(raw)
    def write(path,chunks):
        nonlocal written
        p=stage/path;p.parent.mkdir(parents=True,exist_ok=True)
        with p.open('w') as f:
            for text in chunks:
                guard();written+=len(text.encode())
                if written>32*1024**2:raise MemoryError('32MiB output limit')
                f.write(text)
        raw=p.read_bytes()
        return {'path':str(path),'lines':raw.count(b'\n'),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
    try:
        base=ROOT/'evidence/historical-compact-data'
        manifest=read(base/'manifest.json');need(manifest['status'].startswith('data assembled'),'incomplete source data')
        rows=read(base/'rows.json');poses=read(base/'poses.json');blocks=read(base/'blocks.json')
        contexts=read(base/'contexts.json');refs=read(base/'references.json')
        case_data={case:read(base/f'C{case}.json') for case in cases}
        need(len(refs)==192,'reference grid shape')
        context_ids={(c['angle'],tuple(c['inputs'])):c['index'] for c in contexts}
        # Exact angle order is an untrusted lookup hint; pair checking proves all
        # actual directions and never assumes that this permutation is geometric.
        order=sorted(range(192),key=cmp_to_key(lambda a,b:
            (refs[a]['s']*refs[b]['c']>refs[b]['s']*refs[a]['c'])-
            (refs[a]['s']*refs[b]['c']<refs[b]['s']*refs[a]['c'])))
        rank={a:i for i,a in enumerate(order)}
        directions=[]
        for quadrant in range(4):
            for angle in order:
                c,s=refs[angle]['c'],refs[angle]['s']
                directions.append([(c,s),(-s,c),(-c,-s),(s,-c)][quadrant])
        def keys(angle):return [q*192+rank[angle] for q in range(4)]
        def ctx(pose,block=None):
            p=poses[pose];inputs=([] if block is None else blocks[block]['rows'])+p['rows']
            return context_ids[(p['angle'],tuple(inputs))]
        requests=defaultdict(int);plans=[];requested_pairs=0
        angle_masks={a:sum(1<<k for k in keys(a)) for a in range(192)}
        def mask_keys(mask):
            while mask:
                bit=mask & -mask
                yield bit.bit_length()-1
                mask-=bit
        for case,data in case_data.items():
            for p in data['plans']:
                if p['block'] is None:continue
                source=ctx(p['source'],p['block']);a=poses[p['source']]['angle']
                neighbors=data['domains'][p['neighbors_name']]
                neighbor_contexts=[ctx(n) for n in neighbors]
                plans.append({'case':case,'step':p['step'],'name':p['name'],'source':source,
                              'neighbors':neighbor_contexts,'source_pose':p['source'],'block':p['block']})
                need(len(neighbors)==p['historical_pair_count'],'original neighbor coverage mismatch')
                requested_pairs+=len(neighbors)
                for n,cid in zip(neighbors,neighbor_contexts):
                    requested=angle_masks[a]|angle_masks[poses[n]['angle']]
                    requests[source]|=requested;requests[cid]|=requested
        fans={};empty={};stats=Counter();failures=[]
        @lru_cache(maxsize=None)
        def find_empty(cid):return empty_witness(list(dict.fromkeys(contexts[cid]['inputs'])),rows)
        for cid,needed in sorted(requests.items()):
            guard();indices=list(dict.fromkeys(contexts[cid]['inputs']));basis=[]
            for i,j in combinations(indices,2):
                v=vertex(rows[i]['integers'],rows[j]['integers'])
                if v is None:continue
                stats['line_intersections']+=1;X,Y,D=v
                if all((lambda a:a[0]*X+a[1]*Y+a[2]*D>=0)(rows[k]['integers']) for k in indices):
                    basis.append((i,j,X,Y,D))
            if not basis:
                certificate=find_empty(cid)
                if certificate:empty[cid]=certificate;continue
                failures.append({'kind':'no_feasible_vertex_and_no_empty_certificate','context':cid});continue
            entries=[];failed=None
            for key in mask_keys(needed):
                x,y=directions[key];best=None;best_constant=None;best_strict=False
                for candidate in basis:
                    i,j,X,Y,D=candidate
                    weights=cone(rows[i]['integers'],rows[j]['integers'],x,y)
                    if weights is None:continue
                    strict=(weights[0]>0 and rows[i]['strict']) or (weights[1]>0 and rows[j]['strict'])
                    constant=-x*X-y*Y
                    if best is None or constant*best[4]<best_constant*D or constant*best[4]==best_constant*D and strict and not best_strict:
                        best=candidate;best_constant=constant;best_strict=strict
                if best is None:failed=key;break
                if not entries or entries[-1][1:]!=best:
                    entries.append((key if entries else 0,*best))
            if failed is not None:
                certificate=find_empty(cid)
                if certificate:empty[cid]=certificate
                else:failures.append({'kind':'uncovered_support_direction','context':cid,'key':failed})
                continue
            fans[cid]=entries;stats['fan_entries']+=len(entries);stats['vertex_basis_candidates']+=len(basis)
            stats['support_requests']+=needed.bit_count()
        cycles={};cycle_fallbacks=Counter()
        if args.boundary_cycles:
            # A shorter representation is adopted only if every requested
            # bound is at least as strong with strictness preserved. The full
            # original pair loop below then rechecks all eight actual axes.
            for cid,entries in list(fans.items()):
                guard()
                candidate=compact_cycle(rows,entries,directions,mask_keys(requests[cid]))
                if candidate['cycle'] is None:
                    cycle_fallbacks[candidate['reason']]+=1
                else:
                    cycles[cid]=candidate['cycle'];fans[cid]=candidate['entries']
            stats['cyclic_contexts']=len(cycles)
            stats['boundary_row_identifiers']=sum(map(len,cycles.values()))
            stats['derived_cycle_entries']=sum(len(fans[cid]) for cid in cycles)
            stats['legacy_fallback_contexts']=sum(cycle_fallbacks.values())
        starts={cid:[entry[0] for entry in entries] for cid,entries in fans.items()}
        def select(cid,key):return fans[cid][bisect_right(starts[cid],key)-1]
        @lru_cache(maxsize=8192)
        def target(a,b,key):
            A,B=refs[a],refs[b];x,y=directions[key]
            scale=2*A['denominator']*A['sideDenominator']*B['denominator']*B['sideDenominator']
            ra=A['sideNumerator']*(abs(x*A['c']+y*A['s'])+abs(-x*A['s']+y*A['c']))
            rb=B['sideNumerator']*(abs(x*B['c']+y*B['s'])+abs(-x*B['s']+y*B['c']))
            return scale,ra*B['denominator']*B['sideDenominator']+rb*A['denominator']*A['sideDenominator']
        verified=0;empty_pairs=0;pair_failures=[]
        for plan in plans:
            source=plan['source'];a=contexts[source]['angle']
            for neighbor in plan['neighbors']:
                if source in empty or neighbor in empty:empty_pairs+=1;continue
                if source not in fans or neighbor not in fans:
                    pair_failures.append({'kind':'unresolved_context','plan':plan['name'],'neighbor_context':neighbor});continue
                b=contexts[neighbor]['angle'];bad=None
                for key in keys(a)+keys(b):
                    x,y=directions[key];A=select(source,key);B=select(neighbor,(key+384)%768)
                    _,i,j,X,Y,D=A;_,k,l,U,V,E=B
                    wa=cone(rows[i]['integers'],rows[j]['integers'],x,y)
                    wb=cone(rows[k]['integers'],rows[l]['integers'],-x,-y)
                    need(wa is not None and wb is not None,'fan compression lost a cone')
                    strict=(wa[0]>0 and rows[i]['strict']) or (wa[1]>0 and rows[j]['strict']) or (wb[0]>0 and rows[k]['strict']) or (wb[1]>0 and rows[l]['strict'])
                    scale,constant=target(a,b,key)
                    lhs=scale*(E*(-x*X-y*Y)+D*(x*U+y*V));rhs=D*E*constant
                    if lhs>rhs or lhs==rhs and not strict:bad={'key':key,'lhs':str(lhs),'rhs':str(rhs),'strict':strict};break
                if bad:
                    # An actually infeasible context may have closed vertices but
                    # no strictly feasible point. Preserve a checked fallback.
                    fallback=None
                    for cid in (source,neighbor):
                        fallback=find_empty(cid)
                        if fallback:empty[cid]=fallback;break
                    if fallback:empty_pairs+=1
                    else:pair_failures.append({'kind':'pair_axis_failure','plan':plan['name'],'neighbor_context':neighbor,**bad})
                else:verified+=1
        # Every failure is preserved, never silently replaced with a success.
        report.update(status='complete exact fan audit; Lean replay pending',requested_pairs=requested_pairs,
            verified_pairs=verified,pairs_closed_by_empty_certificate=empty_pairs,
            requested_contexts=len(requests),fan_contexts=len(fans),empty_context_count=len(empty),
            all_selected_pairs_pass=not failures and not pair_failures,
            failure_count=len(failures)+len(pair_failures),failures=(failures+pair_failures)[:100],
            cycle_fallback_reasons=dict(cycle_fallbacks),
            statistics=dict(stats),elapsed_seconds=time.monotonic()-start)
        files=[]
        def fan_json():
            yield '{"context_records":[';first=True
            for cid,entries in sorted(fans.items()):
                if not first:yield ','
                first=False;yield json.dumps({'context':cid,'entries':entries,
                    'boundary_cycle':cycles.get(cid)},separators=(',',':'))
            yield '],"empty_contexts":'+json.dumps(empty,separators=(',',':'))+',"plans":'+json.dumps(plans,separators=(',',':'))+',"angle_order":'+json.dumps(order)+'}\n'
        files.append(write(Path('fans.json'),fan_json()))
        # Concrete Lean data avoids one generated declaration suite per context.
        # The generic RawContext.Check/certify adapter retains every proof obligation.
        active=sorted(cid for cid in fans if cid not in empty)
        def row_text(i):
            r=rows[i];return '⟨'+','.join(map(str,r['integers']))+','+str(r['strict']).lower()+'⟩'
        if args.boundary_cycles:
            def direction_source():
                yield 'import Compact.Core.BoundaryFanSyntax\n\n'
                yield f'namespace N12Compact.HistoricalFans.C{lean_label}\n'
                yield 'def directions : Array N12Compact.ReferenceAxis.Direction := #[\n'
                for x,y in directions:yield f'  ⟨{x},{y},1⟩,\n'
                yield f']\nend N12Compact.HistoricalFans.C{lean_label}\n'
            files.append(write(Path(f'lean/Compact/HistoricalFans/C{lean_label}/Directions.lean'),direction_source()))
        for chunk in range((len(active)+31)//32):
            selected=active[chunk*32:(chunk+1)*32]
            def source_lines(chunk=chunk,selected=selected):
                yield 'import Compact.Core.VertexFanTable\n'
                if args.derived_bases or args.boundary_cycles:yield 'import Compact.Core.BasisMaterializeSyntax\n'
                if args.boundary_cycles:
                    yield f'import Compact.HistoricalFans.C{lean_label}.Directions\n'
                yield f'import Compact.HistoricalData.SharedRows\n\nnamespace N12Compact.HistoricalFans.C{lean_label}\nopen N12Compact.HistoricalData N12Compact.VertexFanTable\nset_option Elab.async false\n'
                yield f'def contexts{chunk:03} : Array (RawContext rowCount) := #[\n'
                for cid in selected:
                    c=contexts[cid];r=refs[c['angle']]
                    if cid in cycles:
                        yield '  materialize_boundary_fan% (BoundaryFan.context rows\n'
                        yield '    ['+','.join(map(str,c['inputs']))+'] '
                        yield '⟨'+','.join(map(str,[r['c'],r['s'],r['denominator'],r['sideNumerator'],r['sideDenominator']]))+'⟩\n'
                        yield '    directions ['+','.join(map(str,cycles[cid]))+']),\n'
                        continue
                    yield '  ⟨['+','.join(map(str,c['inputs']))+'],\n'
                    yield '   ⟨'+','.join(map(str,[r['c'],r['s'],r['denominator'],r['sideNumerator'],r['sideDenominator']]))+'⟩,#[\n'
                    for key,i,j,X,Y,D in fans[cid]:
                        if args.derived_bases or args.boundary_cycles:
                            yield f'    ⟨{key},{i},{j},materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows {i}) (rows {j})⟩,\n'
                        else:
                            yield f'    ⟨{key},{i},{j},⟨{row_text(i)},{row_text(j)},{X},{Y},{D}⟩⟩,\n'
                    yield '   ]⟩,\n'
                yield ']\n'
                yield f'theorem contexts{chunk:03}_checked (i : Fin {len(selected)}) :\n'
                yield f"    (contexts{chunk:03}[i.val]'(by change i.val < {len(selected)}; exact i.isLt)).Check rows := by\n"
                yield f'  revert i\n  decide +kernel\nend N12Compact.HistoricalFans.C{lean_label}\n'
            files.append(write(Path(f'lean/Compact/HistoricalFans/C{lean_label}/Contexts{chunk:03}.lean'),source_lines()))
        report['files']=files;report['lean_lines']=sum(f['lines'] for f in files if f['path'].endswith('.lean'))
        report['lean_modules']=sum(f['path'].endswith('.lean') for f in files)
        report['remaining']=['Lean checks of all emitted context tables and empty certificates',
            'all original pair checks and exact global ID/angle/reference adapters',
            'all relaxation, pruning-cover, chord and original-entrance obligations']
        write(Path('manifest.json'),[json.dumps(report,indent=2)+'\n'])
        stage.rename(out)
        print(json.dumps({k:report[k] for k in ['status','cases','requested_pairs','verified_pairs',
            'pairs_closed_by_empty_certificate','requested_contexts','fan_contexts','empty_context_count',
            'all_selected_pairs_pass','lean_lines','lean_modules','elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(stage);raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
