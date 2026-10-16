#!/usr/bin/env python3
"""Parent-run exact fusion of the accepted terminal's 61 context caches.

Every original pose, block, key, ordered row-pair fan and primitive vertex is
checked against the existing source and authenticated pose-map values. Public
terminal declarations keep their types; the whole overlap theorem text is
unchanged. Output is an isolated source proposal, never proof acceptance.
"""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
import re
import shutil
import signal

ROOT=Path(__file__).resolve().parents[1]
CASE=Path('Compact/Cases/C898')
DEST=ROOT/'evidence/proposals/C898TerminalContexts'


def sha(raw):return hashlib.sha256(raw).hexdigest()


def vertex(a,b):
    ax,ay,ac=a;bx,by,bc=b
    x,y,d=ay*bc-ac*by,ac*bx-ax*bc,ax*by-ay*bx
    assert d!=0
    if d<0:x,y,d=-x,-y,-d
    factor=gcd(abs(x),gcd(abs(y),d))
    return x//factor,y//factor,d//factor


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',action='store_true')
    args=parser.parse_args()
    if not args.run:parser.error('parent must schedule --run')
    stage=DEST.with_name(DEST.name+'.staging');assert not DEST.exists() and not stage.exists()
    def stop(*_):raise TimeoutError('25-second source reconstruction guard')
    signal.signal(signal.SIGALRM,stop);signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    signal.alarm(25);inputs={}
    def read(relative):
        raw=(ROOT/relative).read_bytes();assert len(raw)<16*1024**2
        inputs[str(relative)]=sha(raw);return raw
    try:
        old_data=read(CASE/'PairStep14CachedData.lean').decode()
        old_contexts=read(CASE/'PairStep14CachedContexts.lean').decode()
        old_terminal=read(CASE/'PairStep14CommonPoint.lean').decode()
        bank=json.loads(read('evidence/c898-shared-pose-map.json'))
        original=json.loads(read('evidence/c898-step14-cached-pair-pilot.json'))
        # The old pilot pins its source map; its exact source records are also
        # checked below. New Lean checks bind every materialized value anew.
        assert inputs['evidence/c898-shared-pose-map.json']==original['input_sha256']['evidence/c898-shared-pose-map.json']
        assert original['contexts']==61 and original['cached_basis_entries']==297
        rows,poses=bank['rows'],bank['poses']
        contexts=re.findall(r'def cachedPose(\d+) : PoseContext where\n'
            r'  pose := (\d+)\n  block := (\[\]|blockRows \d+)\n'
            r'  keyAngle := (\d+)\n  context := cachedContext(\d+)\n',old_contexts)
        fans={int(i):body for i,body in re.findall(r'def cachedEntries(\d+) : Array \(Entry rowCount\) := #\[\n(.*?)\n\]',old_data,re.S)}
        assert len(contexts)==len(fans)==61
        lines=['import Compact.Cases.C898.FusedContextSyntax','',
            'set_option Elab.async false','set_option maxRecDepth 10000',
            'set_option linter.unnecessarySeqFocus false','',
            'namespace N12Compact.C898Cached','open C898Shared CachedSupportFan',
            'noncomputable section','']
        records=[];entry_count=0
        entry_pattern=re.compile(r'  ⟨(\d+), (\d+), (\d+), ⟨⟨(-?\d+), (-?\d+), (-?\d+), (true|false)⟩, '
            r'⟨(-?\d+), (-?\d+), (-?\d+), (true|false)⟩, (-?\d+), (-?\d+), (\d+)⟩⟩,')
        for expected,(cid,pose,block,key,context_id) in enumerate(contexts):
            cid,pose,key,context_id=map(int,(cid,pose,key,context_id))
            assert cid==expected==context_id and poses[pose]['angle']==key
            body=fans[cid];entries=[]
            for line in body.splitlines():
                match=entry_pattern.fullmatch(line);assert match is not None,(cid,line[:100])
                k,a,b,ax,ay,ac,astrict,bx,by,bc,bstrict,x,y,d=match.groups()
                k,a,b=int(k),int(a),int(b)
                ar,br=[int(ax),int(ay),int(ac)],[int(bx),int(by),int(bc)]
                assert rows[a]['integers']==ar and rows[b]['integers']==br
                assert rows[a]['strict']==(astrict=='true') and rows[b]['strict']==(bstrict=='true')
                assert vertex(ar,br)==(int(x),int(y),int(d))
                entries.append((k,a,b));entry_count+=1
            assert entries
            expected_inputs=('' if block=='[]' else block+' ++ ')+f'poseRows {pose}'
            assert f'def cachedInputs{cid} : List (Fin rowCount) := {expected_inputs}\n' in old_data
            lines += [f'checked_c898_fan cachedPose{cid} TerminalCommon.terminalRawContext{cid} :=',
                f'  ⟨{pose},{block},{key}⟩ using c898_entries%(#[']
            for k,a,b in entries:
                lines += [f'    ⟨{k},{a},{b},materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows {a}) (rows {b})⟩,']
            lines += ['  ])','']
            records.append({'context':cid,'pose':pose,'block':block,'key':key,'entries':entries})
        assert entry_count==297,('original terminal entry count changed',entry_count)
        tail=old_contexts[old_contexts.index('def cachedStep14SourceData'):]
        new_contexts='\n'.join(lines)+tail
        pattern=re.compile(r'def terminalRawContext(\d+) : RawSupportFan.Context :=\n'
            r'  materialize_raw_fan% \(cachedPose\1.context.numeric\)\n'
            r'theorem terminalRawContext\1_exact : terminalRawContext\1 = cachedPose\1.context.numeric := rfl\n\n')
        relocated=set()
        def remove(match):
            number=int(match.group(1));assert number not in relocated;relocated.add(number);return ''
        new_terminal=pattern.sub(remove,old_terminal)
        assert relocated==set(range(61))
        # All actual point checks, metadata and original whole-stage theorem
        # remain literally unchanged; only the above cache declarations move.
        outputs={str(CASE/'PairStep14CachedContexts.lean'):new_contexts,
                 str(CASE/'PairStep14CommonPoint.lean'):new_terminal}
        total=sum(len(t.encode()) for t in outputs.values());assert total<2*1024**2
        report={'scope':'Exact terminal fan reconstruction and cache relocation; whole-stage theorem source unchanged.',
            'lean_checked':False,'contexts':61,'entries':entry_count,
            'all_original_primitive_vertices_exact':True,'terminal_cache_apis_relocated':61,
            'removed_active_dependency_after_activation':'Compact.Cases.C898.PairStep14CachedData',
            'inputs':inputs,'records':records,
            'before':{'lines':sum(t.count('\n') for t in [old_data,old_contexts,old_terminal]),
                      'bytes':sum(len(t.encode()) for t in [old_data,old_contexts,old_terminal])},
            'after':{'lines':sum(t.count('\n') for t in outputs.values()),'bytes':total},
            'output_files':{p:{'sha256':sha(t.encode()),'lines':t.count('\n'),'bytes':len(t.encode())} for p,t in outputs.items()},
            'remaining':['Fused helper replay','All 61 context checks','Unchanged complete terminal point theorem replay']}
        stage.mkdir(parents=True)
        for relative,text in outputs.items():
            target=stage/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text)
        (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');stage.rename(DEST)
        print(json.dumps({k:v for k,v in report.items() if k not in {'inputs','records','output_files'}}))
    except BaseException:
        if stage.exists():shutil.rmtree(stage)
        raise
    finally:signal.alarm(0)


if __name__=='__main__':main()
