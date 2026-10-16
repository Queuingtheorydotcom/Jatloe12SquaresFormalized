#!/usr/bin/env python3
"""Exact active semantic graphs for six historical cases; parent-only slot.

--audit only measures the true source/neighbor/target domain closure. --emit
writes a new proposal with conditional original-packing stage contracts and
their proved terminal composition. It does not prove those pending stages,
does not import legacy JSON proof contracts, and does not modify active data.
No bisection ancestry, pair pieces or unused steps enter this semantic bank.
Run serially under the parent's256MiB/60second guard; outputs capped at8MiB.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,re,resource,shutil,signal,sys,time

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'evidence/historical-compact-data'
DEST=ROOT/'evidence/proposals/HistoricalGraphs'
CASES=(701,713,717,973,978,979)


def need(test,message):
    if not test:raise ValueError(message)


def digest(data):return hashlib.sha256(data).hexdigest()


def owner(name):
    m=re.fullmatch(r'continuousScout\d+Domain(\d+)_(\d+)',name)
    need(m is not None,'non-original domain '+name)
    return int(m[1])


def read_case(case,manifest,audit,cover_rows,provenance,guard):
    path=BASE/f'C{case}.json';raw=path.read_bytes()
    provenance[str(path.relative_to(ROOT))]=digest(raw)
    data=json.loads(raw);need(data['case']==case,'case mismatch')
    modules=[(int(m[1]),source) for source in manifest['sources']
        if (m:=re.fullmatch(fr'S12.Push{case}Chunk(\d+)',source['module']))]
    need(modules,'no authenticated terminal module')
    source=max(modules,key=lambda item:item[0])[1]
    path=ROOT/source['path'];blob=gzip.decompress(path.read_bytes())
    need(digest(blob)==source['sha256'],'terminal source hash mismatch')
    provenance[str(path.relative_to(ROOT))]=digest(blob)
    text=blob.decode();guard()
    fm=re.search(fr'^def case{case}Family : Finset Nat := (\{{[^}}]*\}})',text,re.M)
    need(fm is not None,'missing original family')
    family=tuple(map(int,re.findall(r'\d+',fm[1])))
    positions=[i for i,(cid,values) in enumerate(cover_rows) if cid==case]
    need(len(positions)==1,'ambiguous original row')
    position=positions[0]
    need(set(cover_rows[position][1])==set(family),'family differs from CoverData')
    # C979's final chunk contains the actual-packing adapter but its original
    # mixed geometry theorem ends the previous authenticated chunk.
    mixed_text=text
    if case==979:
        semantic=[s for n,s in modules if n==159]
        need(len(semantic)==1,'C979: missing authenticated semantic chunk159')
        semantic_source=semantic[0];semantic_path=ROOT/semantic_source['path']
        semantic_blob=gzip.decompress(semantic_path.read_bytes())
        need(digest(semantic_blob)==semantic_source['sha256'],'C979: semantic chunk hash mismatch')
        provenance[str(semantic_path.relative_to(ROOT))]=digest(semantic_blob)
        mixed_text=semantic_blob.decode()
    mm=re.search(fr'^theorem mixedGeometryScout{case}_impossible\b(.*?)(?=^#print|^def case|^end S12)',
        mixed_text,re.M|re.S)
    need(mm is not None,f'C{case}: missing original semantic composition')
    mixed=mm[0]
    masks=re.search(r'let masks : Fin (\d+) → Nat := !\[([^\]]+)\]',text)
    need(masks is not None,'missing original actual-owner binding')
    mask_values=list(map(int,masks[2].split(',')))
    need(len(mask_values)==int(masks[1]),'owner binding arity')
    initials={};qowners={};owner_masks={}
    for m in re.finditer(r'\((h\d+) : OrientedPoseCovered (continuousScout\d+Domain\d+_0) \(q (\d+)\)\)',mixed):
        proof,domain,qi=m[1],m[2],int(m[3])
        need(qi<len(mask_values),'owner index outside original binding')
        initials[proof]=domain;qowners[qi]=owner(domain)
        owner_masks[owner(domain)]=mask_values[qi]
    need(initials,'no original incoming semantic contracts')
    expected={int(k):v for k,v in audit['owner_masks'].items()}
    need(owner_masks==expected,'audited original owner map mismatch')
    transitions=sorted(data['transitions'],key=lambda step:step['step'])
    proofs=dict(initials);stages={}
    for tr in transitions:
        step=tr['step'];names=tr['names'];kind=tr['kind']
        need(kind in ('PruningCoverCheck','WindowChordPruningCoverCheck',
            'VerticalChordPruningCoverCheck'),'unknown stage type')
        source_domain,target=names[0],names[2]
        block=re.search(fr'^  have hstep{step} := (.*?)(?=^  (?:have|let|obtain|rcases|exact)|\Z)',
            mixed,re.M|re.S)
        need(block is not None,'stage absent from original semantic proof')
        need(all(name in block[1] for name in names),'stage graph differs from original statement')
        if kind=='PruningCoverCheck':
            neighbors=[names[1]]
            call=re.search(r'\(q (\d+)\) \(q (\d+)\) (h(?:step)?\d+) '
                r'\(oriented_coverage_forget _ _ (h(?:step)?\d+)\)',block[1])
            need(call is not None,'unsupported original pair semantic call')
            need(proofs[call[3]]==source_domain and proofs[call[4]]==neighbors[0],
                'pair proof ancestry differs')
            need(qowners[int(call[1])]==owner(source_domain) and
                qowners[int(call[2])]==owner(neighbors[0]),'pair owner mismatch')
        else:
            im=re.search(fr'let indices{step} : Fin 4 → Fin \d+ := !\[([^\]]+)\]',mixed)
            need(im is not None,'missing four-square index binding')
            indices=list(map(int,im[1].split(',')))
            need(len(indices)==4 and len(set(indices))==4,'non-distinct chord owners')
            refs=re.findall(r'· exact (h(?:step)?\d+)\b',block[1])
            need(len(refs)==3,'chord must retain three actual neighbors')
            neighbors=[proofs[ref] for ref in refs]
            need([qowners[i] for i in indices]==[owner(source_domain)]+list(map(owner,neighbors)),
                'chord owner vector differs from original semantics')
            source_ref=re.search(fr'wd{step} (h(?:step)?\d+) \(by',block[1])
            need(source_ref and proofs[source_ref[1]]==source_domain,'chord source ancestry')
        need(source_domain in data['domains'] and target in data['domains'] and
             all(n in data['domains'] for n in neighbors),'domain data absent')
        need(owner(source_domain)==owner(target),'stage changes actual owner')
        stages[target]={'step':step,'kind':kind,'source':source_domain,
            'neighbors':neighbors,'target':target}
        proofs[f'hstep{step}']=target
    terminal=transitions[-1]['names'][2]
    need(data['domains'][terminal]==[],'original terminal domain is not empty')
    active_domains=set();active_steps={};active_initials=set()
    def visit(domain):
        if domain in active_domains:return
        active_domains.add(domain)
        if domain in stages:
            stage=stages[domain];active_steps[stage['step']]=stage
            visit(stage['source'])
            for neighbor in stage['neighbors']:visit(neighbor)
        else:
            need(domain in initials.values(),'unproved predecessor outside original entrances')
            active_initials.add(domain)
    visit(terminal)
    selected_domains={name:data['domains'][name] for name in sorted(active_domains)}
    return {'case':case,'family':family,'row':position,'owners':owner_masks,
        'domains':selected_domains,'initials':sorted(active_initials,key=owner),
        'stages':sorted(active_steps.values(),key=lambda step:step['step']),
        'terminal':terminal,'original_stages':len(transitions),
        'unused_steps':sorted(tr['step'] for tr in transitions if tr['step'] not in active_steps),
        'authenticated_module':source['module']}


def grouped(values,width=16):
    return ',\n    '.join(','.join(map(str,values[i:i+width])) for i in range(0,len(values),width))


def case_source(case):
    cid=case['case'];ns=f'N12Compact.Preservation.C{cid}'
    out=['import Compact.Preservation.HistoricalDictionary','import Compact.Assembly.RowIdentity','',
      '/-! Exact original active graph. `Pending` records unfinished entrance and',
      'stage proofs. The terminal composition below is conditional, not a case completion. -/',
      f'namespace {ns}','open S12 S12Pilot S12Completion HistoricalBank',
      'set_option Elab.async false','noncomputable section','',
      'def family : Finset Nat := {'+','.join(map(str,case['family']))+'}','']
    for name,ids in case['domains'].items():
        out += [f'def {name}Ids : List (Fin poseCount) := [',
            '    '+grouped(ids)+']',f'def {name} : List PoseLeaf := {name}Ids.map poses','']
    def covered(name):
        return f'OrientedPoseCovered {name} (p.square (ownerIndex p {case["owners"][owner(name)]}))'
    out += ['structure Pending : Prop where']
    for name in case['initials']:
        out += [f'  initial{owner(name)} : ∀ p : NormalizedPacking,',
            f'    codedMarkerFamily p = family → {covered(name)}']
    for stage in case['stages']:
        out += [f'  /-- Original {stage["kind"]}, step{stage["step"]}. -/',
            f'  step{stage["step"]} : ∀ p : NormalizedPacking, codedMarkerFamily p = family →']
        out += ['    '+covered(name)+' →' for name in [stage['source']]+stage['neighbors']]
        out += ['    '+covered(stage['target'])]
    out += ['', 'theorem family_impossible (pending : Pending) (p : NormalizedPacking)',
        '    (hf : codedMarkerFamily p = family) : False := by']
    known={}
    for name in case['initials']:
        proof=f'h{owner(name)}';known[name]=proof
        out += [f'  have {proof} := pending.initial{owner(name)} p hf']
    for stage in case['stages']:
        proof=f'hstep{stage["step"]}'
        args=' '.join(known[name] for name in [stage['source']]+stage['neighbors'])
        out += [f'  have {proof} := pending.step{stage["step"]} p hf {args}']
        known[stage['target']]=proof
    out += [f'  obtain ⟨leaf,member,_⟩ := {known[case["terminal"]]}',
        '  exact List.not_mem_nil member','',
        'private theorem row_checked :',
        f'    (RowIdentity.rowAt {case["row"]}).originalId = {cid} ∧',
        f'    (RowIdentity.rowAt {case["row"]}).groups = family := by decide +kernel','',
        f'theorem excludes_case (pending : Pending) : ExcludesCase {cid} := by',
        '  intro r hr hid p hf',
        '  apply family_impossible pending p',
        f'  exact hf.trans (RowIdentity.family_at {case["row"]} {cid} family row_checked r hr hid)','',
        '#print axioms family_impossible','#print axioms excludes_case','end',f'end {ns}','']
    return '\n'.join(out)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit',action='store_true');parser.add_argument('--emit',action='store_true')
    parser.add_argument('--alias-bank',type=Path,
        help='Use only an exact complete bank at this source root, checked before alias emission')
    args=parser.parse_args();need(args.audit or args.emit,'parent must select --audit or --emit')
    start=time.monotonic();stage=DEST.with_name(DEST.name+'.staging')
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        need(time.monotonic()-start<55 and rss<256*1024**2,'55second/256MiB guard')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    provenance={}
    def load(path):
        raw=path.read_bytes();provenance[str(path.relative_to(ROOT))]=digest(raw)
        return json.loads(raw)
    manifest=load(BASE/'manifest.json');need(manifest['status'].startswith('data assembled'),'unavailable source audit')
    audits=load(ROOT/'evidence/historical-direct-cover-audit.json')['cases']
    cover_path=ROOT/'vendor/S12/CoverData.lean';raw=cover_path.read_bytes()
    provenance[str(cover_path.relative_to(ROOT))]=digest(raw)
    cover_rows=[(int(cid),tuple(map(int,values.split(',')))) for cid,values in
        re.findall(r'⟨(\d+),\{([0-9,]+)\}',raw.decode())]
    need(len(cover_rows)==577,'original table row count differs')
    cases=[]
    for cid in CASES:
        try:
            cases.append(read_case(cid,manifest,next(a for a in audits if a['case']==cid),
                cover_rows,provenance,guard))
        except (ValueError,KeyError) as error:
            raise ValueError(f'C{cid} source audit: {error}') from error
    poses=load(BASE/'poses.json');rows=load(BASE/'rows.json');guard()
    pose_ids=sorted({pid for case in cases for domain in case['domains'].values() for pid in domain})
    need(all(0<=pid<len(poses) and poses[pid]['index']==pid for pid in pose_ids),'pose identity failure')
    row_ids=sorted({rid for pid in pose_ids for rid in poses[pid]['rows']})
    need(all(0<=rid<len(rows) and rows[rid]['index']==rid and rows[rid]['denominator']>0 for rid in row_ids),
        'row identity or denominator failure')
    report={'scope':'Conditional graph preservation; no pending stage is asserted proved.',
        'lean_checked':False,'cases':[{k:v for k,v in c.items() if k not in ('domains','stages')}|
            {'active_stages':len(c['stages']),'pair_stages':sum(s['kind']=='PruningCoverCheck' for s in c['stages']),
             'chord_stages':sum(s['kind']!='PruningCoverCheck' for s in c['stages']),
             'domain_count':len(c['domains']),'domain_pose_occurrences':sum(map(len,c['domains'].values()))}
            for c in cases], 'semantic_pose_count':len(pose_ids),'semantic_row_count':len(row_ids),
        'full_original_pose_count':len(poses),'full_original_row_count':len(rows),'sources':provenance}
    if args.emit:
        need(not DEST.exists() and not stage.exists(),'refusing existing proposal')
        # Different namespace prevents C713-only sparse defaults from acquiring
        # historical meanings. The parent must merge/alias this bank before
        # activating all six production cases; the proposal is not double-imported.
        bank=['import Compact.Core.SparseLiteral','import S12.OwnerEnclosure',
          'import S12.AngleData64','import S12.AngleData128','',
          'namespace N12Compact.Preservation.HistoricalBank','open S12 IntegerSupport',
          'set_option Elab.async false','noncomputable section',
          f'abbrev rowCount : Nat := {len(rows)}',f'abbrev poseCount : Nat := {len(poses)}',
          'def rowData : SparseLiteral.Tree (Row × Nat) := sparse_rows% "']
        bank += [f'{i}:'+','.join(map(str,rows[i]['integers']))+','+str(rows[i]['strict']).lower()+','+
            str(rows[i]['denominator']-1) for i in row_ids]
        bank += ['"','def rowPair (i : Nat) : Row × Nat := SparseLiteral.lookup (⟨0,0,0,false⟩,0) rowData i',
          'def rows (i : Fin rowCount) : Row := (rowPair i.val).1',
          'def denominators (i : Fin rowCount) : Nat := (rowPair i.val).2+1',
          f'def poseData : SparseLiteral.Tree (Fin 192 × List (Fin rowCount)) := sparse_poses% 192 {len(rows)} "']
        bank += [f'{i}:{poses[i]["angle"]};'+','.join(map(str,poses[i]['rows'])) for i in pose_ids]
        bank += ['"','def poseRecord (i : Nat) : Fin 192 × List (Fin rowCount) :=',
          '  SparseLiteral.lookup (0,[]) poseData i',
          'def angles (i : Fin 192) : {w : AngleEnclosure // w.Check} :=',
          '  if i.val < 64 then (angles64[i.val]?).getD ⟨angle64_0,angle64_0_checked⟩',
          '  else (angles128[i.val-64]?).getD ⟨angle128_0,angle128_0_checked⟩',
          'def poses (i : Fin poseCount) : PoseLeaf :=',
          '  ⟨angles (poseRecord i.val).1, (poseRecord i.val).2.map',
          '    (fun r => (rows r).normalized (denominators r))⟩',
          'end','end N12Compact.Preservation.HistoricalBank','']
        if args.alias_bank:
            from prepare_historical_union import validate_bank
            bank_hashes=validate_bank(args.alias_bank,rows,poses)
            report['shared_bank_root']=str(args.alias_bank)
            report['shared_bank_exact_sources']=bank_hashes
            report['dictionary_strategy']='One complete shared bank; this proposal emits aliases only.'
            bank=['import Compact.Cases.C713.SharedDictionary','',
                'namespace N12Compact.Preservation.HistoricalBank',
                'abbrev rowCount := HistoricalData.rowCount',
                'abbrev poseCount := HistoricalData.poseCount',
                'noncomputable abbrev poses := C713Shared.poses',
                'end N12Compact.Preservation.HistoricalBank','']
        else:
            report['dictionary_strategy']='Isolated semantic-bank fallback. Do not duplicate in final proof closure.'
        outputs={'Compact/Preservation/HistoricalDictionary.lean':'\n'.join(bank)}
        outputs.update({f'Compact/Preservation/C{c["case"]}.lean':case_source(c) for c in cases})
        need(sum(len(s.encode()) for s in outputs.values())<8*1024**2,'8MiB output cap')
        stage.mkdir(parents=True)
        try:
            for name,source in outputs.items():
                guard();path=stage/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
            report.update(lean_lines=sum(s.count('\n') for s in outputs.values()),
                lean_bytes=sum(len(s.encode()) for s in outputs.values()),
                outputs=[{'path':n,'sha256':digest(s.encode()),'lines':s.count('\n')} for n,s in outputs.items()])
            (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
            stage.rename(DEST)
        except BaseException:
            shutil.rmtree(stage);raise
    report['seconds']=time.monotonic()-start
    (ROOT/'evidence/historical-active-graphs-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sources','outputs')},indent=2))
    signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
