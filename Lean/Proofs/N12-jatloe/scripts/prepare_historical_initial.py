#!/usr/bin/env python3
"""Prepare original-packing entrances for the five cases beside C713.

Parent-only --run,256MiB/120sec,12MiB source output. No Lean, search, network,
subprocess, active-source modification or extra pose/row dictionary. C713's
separately owned source is preserved. Every other entrance targets the existing
Preservation graph's original domain and actual owner mask, including all empty
angles. Source proposals are never proof-acceptance receipts.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import argparse,gzip,hashlib,json,re,resource,shutil,signal,sys,time
from build_c898_direct_initial import strongest_original_indices
from audit_c898_direct_cover import point_forms

ROOT=Path(__file__).resolve().parents[1]
CASES=(701,717,973,978,979)
DEST=ROOT/'evidence/proposals/HistoricalInitial'


def need(test,message):
    if not test:raise ValueError(message)


def sha(data):return hashlib.sha256(data).hexdigest()


def header(imports,namespace):
    return '\n'.join('import '+name for name in imports)+f'''

namespace {namespace}
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

'''


def footer(namespace):return f'\nend\nend {namespace}\n'


def namespace(case):return f'N12Compact.C{case}RecipeInitial'


def points(values):
    def rational(value):
        q=Q(value)
        return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
    return '['+', '.join(f'({rational(x)},{rational(y)})' for x,y in values)+']'


def batch_source(case,owner,batch,records):
    ns=namespace(case);name=f'entries{owner}_{batch}'
    out=header([f'Compact.Cases.C{case}.RecipeInitial.Inputs',
                'Compact.Bridge.CheckedRecipeCommand'],ns)
    out+='open DirectPoseCover Preservation.InitialBank\n\n'
    names=[]
    for r in records:
        entry=f'entry{owner}_{r["angle"]}';names.append(entry)
        target='none' if r['target'] is None else 'some '+str(r['target'])
        out+=f'checked_recipe {entry} (bank, inside{owner}, outside{owner}) := '
        out+=f'⟨{r["bank_angle"]}, ['+', '.join(map(str,r['indices']))+f'], {target}⟩\n'
    out+=f'\ndef {name} : List (DirectRecipeTable.Entry bank inside{owner} outside{owner}) :=\n'
    out+='  ['+', '.join(names)+']\n\n'
    out+=f'''private theorem {name}_literal_checked :
    ∀ entry ∈ {name}, DirectRecipeCheck.LiteralCheck entry := by
  simp only [{name}, List.forall_mem_cons]
  exact ⟨'''+', '.join(n+'_literal_checked' for n in names)+', by simp⟩\n\n'
    out+=f'''theorem {name}_checked : ∀ entry ∈ {name}, entry.Check :=
  DirectRecipeCheck.all_checked {name} {name}_literal_checked
'''
    return out+footer(ns)


def owner_source(case,owner,grid):
    ns=namespace(case);batches=grid//8
    out=header([f'Compact.Cases.C{case}.RecipeInitial.Batches.Owner{owner:02}Batch{b:02}'
                for b in range(batches)]+[f'Compact.Preservation.C{case}'],ns)
    out+='open DirectPoseCover Preservation.InitialBank\n\n'
    out+=f'def entries{owner} : List (DirectRecipeTable.Entry bank inside{owner} outside{owner}) :=\n  '
    out+=' ++\n  '.join(f'entries{owner}_{b}' for b in range(batches))+'\n\n'
    out+=f'''theorem entries{owner}_checked : ∀ entry ∈ entries{owner}, entry.Check := by
  unfold entries{owner}
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨'''+', '.join(f'entries{owner}_{b}_checked' for b in range(batches))+'⟩\n\n'
    out+=f'''def owner{owner} : Owner :=
  DirectRecipeTable.checkedOwner bank inside{owner} outside{owner} entries{owner} entries{owner}_checked

theorem owner{owner}_checked : owner{owner}.Check :=
  DirectRecipeTable.checkedOwner_check bank inside{owner} outside{owner}
    entries{owner} entries{owner}_checked angles{grid}_cover_kernel

theorem owner{owner}_leaves_shared :
    owner{owner}.leaves = Preservation.C{case}.continuousScout{case}Domain{owner}_0 := by
  unfold owner{owner}
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl
'''
    return out+footer(ns)


def entry_source(case,owners):
    ns=f'N12Compact.C{case}Entry'
    out=header(['Compact.Bridge.DirectOwnerFamily',f'Compact.Cases.C{case}.EntryPoints']+
        [f'Compact.Cases.C{case}.RecipeInitial.Owner{owner:02}' for owner in owners],ns)
    out+=f'open DirectPoseCover C{case}RecipeInitial\n\n'
    for owner,mask in owners.items():
        target=f'Preservation.C{case}.continuousScout{case}Domain{owner}_0'
        out+=f'''theorem owner{owner}_premises_checked :
    PointPremises.Check case{case}Domain{owner} commonPoints{case} inside{owner} outside{owner} := by
  decide +kernel

def owner{owner}_entry : CertifiedOwner case{case}Family commonPoints{case} :=
  ⟨case{case}Domain{owner}, owner{owner}, owner{owner}_checked, owner{owner}_premises_checked,
   {target}, owner{owner}_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner{owner}_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C{case}.family) :
    OrientedPoseCovered {target} (p.square (ownerIndex p {mask})) := by
  change codedMarkerFamily p = case{case}Family at hf
  exact owner{owner}_entry.sound p hf

'''
    return out+footer(ns)


def ownership_source(case,text,foundation):
    """Original checked domains and convex ownership witnesses, no region trees.

    Upper bounds3 in C717/C979 use a distinct, symbolically complete size≤3
    checker. The original DirectSingleDomain.Check conclusion is unchanged.
    """
    first=text.index(f'def case{case}Family')
    last=text.index(f'def sharedCommonEnclosure{case}_0',first)
    text=text[first:last]
    starts=list(re.finditer(r'^(?:noncomputable )?(?:def|theorem|lemma) (\w+)',text,re.M))
    known={re.sub(r'\s','',expression):int(index) for index,expression in re.findall(
        r'^def localQuery(\d+) : LocalQuery := (.+)$',foundation,re.M)}
    chunks={'base':[],'single':[],'domains':[],'refined':[],'points':[]}
    queries={};aliases={};signatures={};single_upper={};upper3=[]
    for i,start in enumerate(starts):
        name=start[1];body=text[start.start():starts[i+1].start() if i+1<len(starts) else len(text)]
        body=re.split(r'^end(?: S12)?\s*$',body,maxsplit=1,flags=re.M)[0].rstrip()+'\n'
        if name==f'case{case}_ownership' or name.startswith((f'case{case}RefinedDomains',f'domains{case}')):continue
        if name.startswith(f'query{case}_'):
            if not name.endswith('_checked'):
                match=re.match(r'def \w+ : LocalQuery := (.+)',body)
                need(match is not None,'unsupported original query '+name)
                fields=re.match(r'⟨(\d+),(\d+),(\{[^}]*\}|∅),',match[1])
                need(fields is not None,'unsupported query signature '+name)
                signatures[name]=fields.groups()
                existing=known.get(re.sub(r'\s','',match[1]))
                if existing is not None:
                    aliases[name]=existing;body=f'def {name} : LocalQuery := localQuery{existing}\n'
            elif name.removesuffix('_checked') in aliases:
                query=name.removesuffix('_checked');existing=aliases[query]
                body=f'''theorem {name} : {query}.Check :=
  c{case}_query_at queryChunk{existing//50} queryChunk{existing//50}_checked ⟨{existing%50}, by decide⟩
'''
            group=int(re.match(rf'query{case}_(\d+)',name)[1])//64
            queries.setdefault(group,[]).append(body.replace('native_decide','decide +kernel'))
            continue
        if name==f'case{case}Family':key='base'
        elif name.startswith(f'single{case}_'):key='single'
        elif name.startswith(f'domain{case}'):key='domains'
        elif name.startswith((f'refined{case}',f'case{case}Domain')):key='refined'
        elif name.startswith((f'commonPoint{case}',f'commonPoints{case}')):key='points'
        else:raise ValueError('unmapped original ownership declaration '+name)
        if key=='single' and not name.endswith('_checked'):
            fields=re.match(r'def \w+ : DirectSingleDomain := ⟨\d+,\d+,(\d+),',body)
            need(fields is not None,'unsupported original single domain '+name)
            single_upper[name]=int(fields[1]);need(int(fields[1])<=3,'unrecognized owner bound')
        chunks[key].append(body.replace('native_decide','decide +kernel'))
    chunks['base'].append(f'''theorem c{case}_query_at (queries : List LocalQuery)
    (checked : queries.all (fun w => decide w.Check) = true)
    (i : Fin queries.length) : (queries.get i).Check :=
  of_decide_eq_true (List.all_eq_true.mp checked _ (List.get_mem queries i))
''')
    singles=''.join(chunks['single'])
    pattern=re.compile(rf'(def (single{case}_\d+_\d+) : DirectSingleDomain := [^\n]+)\n'
        rf'theorem \2_checked : \2.Check case{case}Family (\d) := by decide \+kernel')
    def simplify(match):
        definition,name,kind=match.groups()
        checker='SmallOwnerDomain'
        if single_upper[name]>2:upper3.append(name);checker='SmallOwnerDomainThree'
        selected=re.findall(rf'⟨(query{case}_\d+),\1_checked⟩',definition)
        table='['+','.join('('+','.join(signatures[q])+')' for q in selected)+']'
        return definition+f'''\nprivate def {name}Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  {table}
theorem {name}_checked : {name}.Check case{case}Family {kind} :=
  N12Compact.{checker}.checked {name} case{case}Family {kind}
    {name}Signatures (by rfl) (by decide) (by decide +kernel)
'''
    singles,number=pattern.subn(simplify,singles)
    need(number==len(single_upper)==24,'incomplete single-domain checker coverage')
    prefix=f'Compact/Cases/C{case}/';module=f'Compact.Cases.C{case}'
    outputs={prefix+'EntryQueryBase.lean':header(['S12.DirectSingleDomain','S12.LocalQueryData'],'S12')+
        ''.join(chunks['base'])+footer('S12')}
    query_modules=[]
    for group,bodies in sorted(queries.items()):
        name=f'{module}.EntryQuery{group:02}';query_modules.append(name)
        outputs[name.replace('.','/')+'.lean']=header([module+'.EntryQueryBase'],'S12')+''.join(bodies)+footer('S12')
    helper='Compact.Bridge.SmallOwnerDomainThree' if upper3 else 'Compact.Bridge.SmallOwnerDomain'
    outputs[prefix+'EntryQueries.lean']=header([helper]+query_modules,'S12')+singles+footer('S12')
    for key,title,imports in [('domains','Domains',[module+'.EntryQueries']),
        ('refined','Refined',[module+'.EntryDomains','S12.DomainRefinement']),
        ('points','Points',[module+'.EntryRefined','S12.DomainHullPoint'])]:
        outputs[prefix+'Entry'+title+'.lean']=header(imports,'S12')+''.join(chunks[key])+footer('S12')
    return outputs,{'original_ownership_lines':text.count('\n'),'query_aliases':len(aliases),
                    'upper_three_checked_signatures':upper3}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',action='store_true')
    if not parser.parse_args().run:parser.error('prepared only; parent serial slot and --run required')
    started=time.monotonic();stage=DEST.with_name(DEST.name+'.staging')
    need(not DEST.exists() and not stage.exists(),'refusing existing proposal/staging')
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        need(time.monotonic()-started<115 and rss<256*1024**2,'115second/256MiB limit')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    provenance={}
    def load(path):
        raw=path.read_bytes();provenance[str(path.relative_to(ROOT))]=sha(raw);return json.loads(raw)
    try:
        audit=load(ROOT/'evidence/historical-direct-cover-audit.json')
        audits={c['case']:c for c in audit['cases']};need(set(audits)==set(CASES)|{713},'case coverage differs')
        base=ROOT/'evidence/historical-compact-data'
        poses=load(base/'poses.json');names={}
        raw=(base/'names.jsonl').read_bytes();provenance[str((base/'names.jsonl').relative_to(ROOT))]=sha(raw)
        for line in raw.splitlines():
            item=json.loads(line)
            if re.fullmatch(r'continuousScout(?:701|717|973|978|979)Initial\d+_\d+',item['name']):
                need(item['kind']=='pose','initial name is not pose');names[item['name']]=item['index']
        del raw
        angle_path=ROOT/'vendor/S12/AngleData.lean';angle_raw=angle_path.read_bytes()
        provenance[str(angle_path.relative_to(ROOT))]=sha(angle_raw)
        angles={(int(n),int(i)):[Q(x.strip().strip('()')) for x in fields.split(',')]
            for n,i,fields in re.findall(r'def angle(64|128)_(\d+) : AngleEnclosure := ⟨([^⟩]+)⟩',angle_raw.decode())}
        foundation_path=ROOT/'source/S12/LocalQueryData.lean';foundation=foundation_path.read_text()
        provenance[str(foundation_path.relative_to(ROOT))]=sha(foundation.encode())
        shared_ns='N12Compact.Preservation.InitialBank'
        outputs={'Compact/Preservation/InitialBank.lean':header([
            'Compact.Bridge.DirectRecipeDictionary','Compact.Cases.C713.SharedDictionary'],shared_ns)+'''
def bank : DirectRecipeTable.Bank 192 HistoricalData.poseCount :=
  DirectRecipeTable.Bank.ofDictionary C713Shared.dictionary HistoricalData.positive_denominators

theorem angles64_cover_kernel : CoversInterval 0 1 (angles64.map Subtype.val) := by
  decide +kernel

theorem angles128_cover_kernel : CoversInterval 0 1 (angles128.map Subtype.val) :=
  C713Shared.angles128_cover_kernel
'''+footer(shared_ns)}
        reports=[];all_records=[]
        for case in CASES:
            guard();a=audits[case];need(a['all_checked_roots_pass'] and a['all_initial_roots_audited'],'incomplete audit')
            data=load(base/f'C{case}.json');receipt=load(ROOT/f'evidence/inherited/evidence/C{case}/case-replay.json')['local_source_sha256']
            need(receipt['S12.AngleData']==sha(angle_raw),'angle provenance differs')
            owners={int(k):v for k,v in a['owner_masks'].items()};original={(r['owner'],r['angle']):r for r in a['roots']}
            ns=namespace(case);prefix=f'Compact/Cases/C{case}/RecipeInitial/'
            inputs=header(['Compact.Preservation.InitialBank','Compact.Bridge.DirectPoseForms'],ns)
            records=[];counts=Counter()
            for own in a['owners']:
                owner=own['owner'];grid=own['N'];need(grid in (64,128) and owner in owners,'unsupported original owner/grid')
                offset=0 if grid==64 else 64
                inputs+=f'def inside{owner} : List (ℚ × ℚ) := {points(own["inside"])}\n'
                inputs+=f'def outside{owner} : List (ℚ × ℚ) := {points(own["outside"])}\n\n'
                selected=[]
                for angle in range(grid):
                    _,_,c,s,outer,_,wall=angles[grid,angle]
                    rows=[row for p in own['inside'] for row in point_forms(c,s,Q(1001,1000)*outer,p)]
                    wall_start=len(rows);rows += [(Q(1),Q(0),-wall/2),(Q(-1),Q(0),4-wall/2),
                        (Q(0),Q(1),-wall/2),(Q(0),Q(-1),4-wall/2)]
                    indices=strongest_original_indices(rows)
                    need(len(indices)==8 and all(i in indices for i in range(wall_start,wall_start+4)),'invalid premise selection')
                    old=original[owner,angle];need(old['passed'],'failed original root audit')
                    target=None if old['target_pose'] is None else names[old['target_pose']]
                    if target is None:need(not old['absent_pose_closed_nonempty'],'unproved empty root')
                    else:need(poses[target]['angle']==offset+angle,'pose/angle mismatch')
                    selected.append({'case':case,'owner':owner,'angle':angle,'bank_angle':offset+angle,
                                     'indices':indices,'target':target})
                    counts['empty_roots' if target is None else 'retained_roots']+=1
                need([r['target'] for r in selected if r['target'] is not None]==
                     data['domains'][f'continuousScout{case}Domain{owner}_0'],'original reduced-domain order differs')
                records.extend(selected)
                for batch in range(grid//8):
                    outputs[prefix+f'Batches/Owner{owner:02}Batch{batch:02}.lean']=batch_source(case,owner,batch,selected[batch*8:batch*8+8])
                outputs[prefix+f'Owner{owner:02}.lean']=owner_source(case,owner,grid)
            need(len(records)==len(original),'not all original roots emitted')
            outputs[prefix+'Inputs.lean']=inputs+footer(ns)
            outputs[prefix+'Entry.lean']=entry_source(case,owners)
            sources=[s for s in a['sources'] if re.fullmatch(rf'S12.Push{case}Chunk\d+',s['module'])]
            terminal=max(sources,key=lambda s:int(s['module'].split('Chunk')[1]))
            blob=gzip.open(ROOT/terminal['path'],'rb').read()
            need(sha(blob)==receipt[terminal['module']]==terminal['sha256'],'ownership source provenance differs')
            provenance[terminal['path']]=sha(blob)
            more,ownership=ownership_source(case,blob.decode(),foundation);outputs.update(more)
            reports.append({'case':case,'owners':owners,'roots':len(records),'numeric_batches':len(records)//8,
                            **counts,**ownership});all_records.extend(records)
        need(len(all_records)==4992,'other-five root count differs')
        total=sum(len(text.encode()) for text in outputs.values());need(total<12*1024**2,'12MiB output cap')
        guard();stage.mkdir(parents=True)
        for relative,text in outputs.items():
            path=stage/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        report={'scope':'Other-five original-packing entrance proposals, reusing the separately owned C713 route.',
            'lean_checked':False,'cases':reports,'records':all_records,'semantic_roots':4992,'numeric_batches':624,
            'source_pose_rows_duplicated':0,'domain_id_tables_duplicated':0,'sources':provenance,
            'lean_modules':len(outputs),'lean_lines':sum(t.count('\n') for t in outputs.values()),'lean_bytes':total,
            'outputs':[{'path':name,'sha256':sha(text.encode()),'lines':text.count('\n')} for name,text in outputs.items()],
            'remaining':['Parent replay of all numeric roots and original ownership certificates',
                'C717/C979 use the separate SmallOwnerDomainThree theorem; generic and concrete replay required',
                'Actual pair/chord transition proofs and final case composition remain separate obligations'],
            'seconds':time.monotonic()-started}
        (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');stage.rename(DEST)
        print(json.dumps({k:report[k] for k in ('semantic_roots','numeric_batches','lean_modules','lean_lines','lean_bytes','seconds')}))
    except BaseException:
        if stage.exists():shutil.rmtree(stage)
        raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
