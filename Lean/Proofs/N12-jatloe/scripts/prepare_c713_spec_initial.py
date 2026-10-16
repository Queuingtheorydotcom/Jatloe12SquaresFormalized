#!/usr/bin/env python3
"""Prepare exact C713 owner entrances and 128-angle direct-cover records.

Source preparation only: root runs --run under 256 MiB/120sec. No Lean,
network, subprocess or active source modification. Output <=8 MiB under
one new evidence/proposals directory, atomically installed after all checks.
Every original owner, empty angle and reduced pose ID is retained. Target rows
come from the shared dictionary, never a copied owner-local target pool.
--checked-command prepares a separate proposal using one semantic command per
root and at most eight root checks per module. Activate only after the shared
CheckedRecipeCommand pilot has passed the parent's Lean replay.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import argparse,gzip,hashlib,json,re,resource,shutil,signal,sys,time
from build_c898_direct_initial import strongest_original_indices
from audit_c898_direct_cover import point_forms
from audit_historical_direct_cover import ROOT,need

OWNERS={0:1,1:2,5:192,6:512,7:2304,8:4096,9:8192,10:16384,11:32768}
NS='N12Compact.C713RecipeInitial'
DEST=ROOT/'evidence/proposals/C713RecipeTable'


def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return h.hexdigest()


def header(imports,namespace=NS):
    opened='open S12 S12Pilot'+(' DirectPoseCover' if namespace==NS or namespace.endswith('C713Entry') else '')
    return '\n'.join('import '+s for s in imports)+f'''\n
namespace {namespace}
{opened}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

'''


def footer(namespace=NS):return f'\nend\nend {namespace}\n'


def qtext(value):
    v=Q(value)
    return str(v.numerator) if v.denominator==1 else f'({v.numerator}/{v.denominator})'


def points(values):return '['+', '.join(f'({qtext(x)},{qtext(y)})' for x,y in values)+']'


def bank_source():
    return header(['Compact.Bridge.DirectRecipeDictionary','Compact.Cases.C713.SharedDictionary',
        'Compact.Cases.C713.RecipeInitial.Inputs'])+'''
def bank : DirectRecipeTable.Bank 192 HistoricalData.poseCount :=
  DirectRecipeTable.Bank.ofDictionary C713Shared.dictionary HistoricalData.positive_denominators

theorem bank_pose (i : Fin HistoricalData.poseCount) : bank.poses i = C713Shared.poses i := rfl
'''+footer()


def batch_source(owner,batch,records):
    name=f'entries{owner}_{batch}'
    text=f'def {name} : List (DirectRecipeTable.Entry bank inside{owner} outside{owner}) :=\n'
    text+=f'  cached_recipe_table%(bank, inside{owner}, outside{owner})[\n'
    specs=[]
    for rec in records:
        target='none' if rec['target'] is None else 'some '+str(rec['target'])
        specs.append(f'    ⟨{64+rec["angle"]}, ['+', '.join(map(str,rec['indices']))+f'], {target}⟩')
    text+=',\n'.join(specs)+']\n\n'
    text+=f'''theorem {name}_checked : ∀ entry ∈ {name}, entry.Check := by
  letI : Decidable (∀ entry ∈ {name}, entry.Check) := List.decidableBAll _ {name}
  decide +kernel

'''
    return text


def command_batch_source(owner,batch,records,namespace=NS):
    need(0<len(records)<=8,'checked command batch must contain one to eight roots')
    text=header(['Compact.Cases.C713.RecipeInitial.Bank',
        'Compact.Bridge.CheckedRecipeCommand'],namespace)
    if namespace!=NS:text+='open C713RecipeInitial\n\n'
    names=[]
    for rec in records:
        name=f'entry{owner}_{rec["angle"]}';names.append(name)
        target='none' if rec['target'] is None else 'some '+str(rec['target'])
        text+=f'checked_recipe {name} (bank, inside{owner}, outside{owner}) := '
        text+=f'⟨{64+rec["angle"]}, ['+', '.join(map(str,rec['indices']))+f'], {target}⟩\n'
    table=f'entries{owner}_{batch}'
    text+=f'\ndef {table} : List (DirectRecipeTable.Entry bank inside{owner} outside{owner}) :=\n'
    text+='  ['+', '.join(names)+']\n\n'
    text+=f'''private theorem {table}_literal_checked :
    ∀ entry ∈ {table}, DirectRecipeCheck.LiteralCheck entry := by
  simp only [{table}, List.forall_mem_cons]
  exact ⟨'''+', '.join(name+'_literal_checked' for name in names)+', by simp⟩\n\n'
    text+=f'''theorem {table}_checked : ∀ entry ∈ {table}, entry.Check :=
  DirectRecipeCheck.all_checked {table} {table}_literal_checked
'''
    return text+footer(namespace)


def owner_source(owner,records,checked_command=False):
    imports=([f'Compact.Cases.C713.RecipeInitial.Batches.Owner{owner:02}Batch{batch:02}'
        for batch in range(16)] if checked_command else ['Compact.Cases.C713.RecipeInitial.Bank'])
    text=header(imports)
    if not checked_command:
        for batch in range(16):text+=batch_source(owner,batch,records[8*batch:8*batch+8])
    text+=f'def entries{owner} : List (DirectRecipeTable.Entry bank inside{owner} outside{owner}) :=\n  '
    text+=' ++\n  '.join(f'entries{owner}_{batch}' for batch in range(16))+'\n\n'
    text+=f'''theorem entries{owner}_checked : ∀ entry ∈ entries{owner}, entry.Check := by
  unfold entries{owner}
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨'''+', '.join(f'entries{owner}_{batch}_checked' for batch in range(16))+'⟩\n\n'
    text+=f'''def owner{owner} : Owner :=
  DirectRecipeTable.checkedOwner bank inside{owner} outside{owner} entries{owner} entries{owner}_checked

theorem owner{owner}_checked : owner{owner}.Check :=
  DirectRecipeTable.checkedOwner_check bank inside{owner} outside{owner}
    entries{owner} entries{owner}_checked C713Shared.angles128_cover_kernel
'''
    return text+footer()


def owner_bridge(owner):
    return header([f'Compact.Cases.C713.RecipeInitial.Data{owner:02}',
        'Compact.Cases.C713.SharedDomains'])+f'''
theorem owner{owner}_leaves_shared :
    owner{owner}.leaves = C713Shared.continuousScout713Domain{owner}_0 := by
  unfold owner{owner}
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

#print axioms owner{owner}_leaves_shared
'''+footer()


def entry_source():
    ns='N12Compact.C713Entry'
    text=header(['Compact.Bridge.DirectOwnerFamily','Compact.Cases.C713.EntryPoints',
                 'Compact.Cases.C713.RecipeInitial.All'],ns)+'open C713RecipeInitial\n\n'
    for owner,mask in OWNERS.items():
        text+=f'''theorem owner{owner}_premises_checked :
    PointPremises.Check case713Domain{owner} commonPoints713 inside{owner} outside{owner} := by
  decide +kernel

def owner{owner}_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain{owner}, owner{owner}, owner{owner}_checked, owner{owner}_premises_checked,
   C713Shared.continuousScout713Domain{owner}_0, owner{owner}_leaves_shared⟩

theorem owner{owner}_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain{owner}_0
      (p.square (ownerIndex p {mask})) :=
  owner{owner}_entry.sound p hf

'''
    return text+footer(ns)



def split_query_sources(bodies):
    """Separate query checks from the stronger domain-enumeration checks."""
    base=[];queries={};singles=[]
    for body in bodies:
        match=re.match(r'(?:def|theorem) (\w+)',body)
        need(match is not None,'unrecognized query declaration')
        name=match[1]
        if name.startswith('query713_'):
            index=int(re.match(r'query713_(\d+)',name)[1])
            queries.setdefault(index//64,[]).append(body)
        elif name.startswith('single713_'):singles.append(body)
        else:
            need(name in ('case713Family','c713_query_at'),'unexpected shared query declaration')
            base.append(body)
    outputs={'Compact/Cases/C713/EntryQueryBase.lean':
        header(['S12.DirectSingleDomain','S12.LocalQueryData'],'S12')+''.join(base)+footer('S12')}
    modules=[]
    for group,parts in sorted(queries.items()):
        module=f'Compact.Cases.C713.EntryQuery{group:02}'
        modules.append(module)
        outputs[module.replace('.','/')+'.lean']=header(
            ['Compact.Cases.C713.EntryQueryBase'],'S12')+''.join(parts)+footer('S12')
    foundation=(ROOT/'source/S12/LocalQueryData.lean').read_text()
    literal_queries={name:expr for name,expr in re.findall(
        r'^def (localQuery\d+) : LocalQuery := (.+)$',foundation,re.M)}
    signatures={}
    for body in bodies:
        found=re.match(r'def (query713_\d+) : LocalQuery := (.+)',body)
        if not found:continue
        name,expr=found.groups();expr=literal_queries.get(expr,expr)
        fields=re.match(r'⟨(\d+),(\d+),(\{[^}]*\}|∅),',expr)
        need(fields is not None,'query signature prefix '+name)
        signatures[name]=fields.groups()
    single_text=''.join(singles)
    pattern=re.compile(r'(def (single713_\d+_\d+) : DirectSingleDomain := [^\n]+)\n'
        r'theorem \2_checked : \2.Check case713Family (\d) := by decide \+kernel')
    def simplify_single(match):
        definition,name,kind=match.groups()
        selected=re.findall(r'⟨(query713_\d+),\1_checked⟩',definition)
        table='['+','.join('('+','.join(signatures[q])+')' for q in selected)+']'
        return definition+f'\nprivate def {name}Signatures : List N12Compact.SmallOwnerDomain.Signature :=\n  '+table+f'\ntheorem {name}_checked : {name}.Check case713Family {kind} :=\n  N12Compact.SmallOwnerDomain.checked {name} case713Family {kind}\n    {name}Signatures (by rfl) (by decide) (by decide +kernel)\n'
    single_text,number=pattern.subn(simplify_single,single_text)
    need(number==24,'single-domain signature coverage')
    outputs['Compact/Cases/C713/EntryQueries.lean']=header(
        ['Compact.Bridge.SmallOwnerDomain']+modules,'S12')+single_text+footer('S12')
    return outputs


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',action='store_true')
    ap.add_argument('--checked-command',action='store_true')
    args=ap.parse_args()
    if not args.run:ap.error('prepared only; parent serial slot and --run required')
    destination=DEST.with_name('C713RecipeCommand') if args.checked_command else DEST
    start=time.monotonic();stage=destination.with_name(destination.name+'.staging')
    need(not destination.exists() and not stage.exists(),'refusing existing output')
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        if time.monotonic()-start>115 or rss>256*1024**2:raise RuntimeError('256MiB/115sec limit')
    def stop(*_):raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    stage.mkdir(parents=True)
    try:
        base=ROOT/'evidence/historical-compact-data'
        paths=[ROOT/'evidence/historical-direct-cover-audit.json',base/'manifest.json',base/'C713.json',
               base/'poses.json',base/'names.jsonl',ROOT/'vendor/S12/AngleData.lean',
               ROOT/'evidence/inherited/evidence/C713/case-replay.json']
        audit_doc=json.loads(paths[0].read_text());audit=next(c for c in audit_doc['cases'] if c['case']==713)
        need(audit['all_checked_roots_pass'] and audit['all_initial_roots_audited'],'incomplete audit')
        need(audit['owner_masks']=={str(k):v for k,v in OWNERS.items()},'owner map mismatch')
        manifest=json.loads(paths[1].read_text());need(manifest['status'].startswith('data assembled'),'incomplete dictionary')
        data=json.loads(paths[2].read_text());poses=json.loads(paths[3].read_text())
        receipt=json.loads(paths[6].read_text())['local_source_sha256']
        angle_bytes=paths[5].read_bytes();need(hashlib.sha256(angle_bytes).hexdigest()==receipt['S12.AngleData'],'angle hash mismatch')
        angles={int(i):[Q(x.strip().strip('()')) for x in values.split(',')]
          for i,values in re.findall(r'def angle128_(\d+) : AngleEnclosure := ⟨([^⟩]+)⟩',angle_bytes.decode())}
        need(set(angles)==set(range(128)),'incomplete angle128 grid')
        names={}
        with paths[4].open() as f:
            for line in f:
                record=json.loads(line)
                if re.fullmatch(r'continuousScout713Initial\d+_\d+',record['name']):
                    need(record['kind']=='pose','wrong initial record kind');names[record['name']]=record['index']
        owners={o['owner']:o for o in audit['owners']};need(set(owners)==set(OWNERS),'owner coverage mismatch')
        original={(item['owner'],item['angle']):item for item in audit['roots']}
        need(len(original)==1152,'root count mismatch')
        outputs={};counts=Counter();records=[]
        inputs=header(['Compact.Bridge.DirectPoseForms','Compact.Cases.C713.SharedDictionary'])
        for owner in OWNERS:
            inputs+=f'def inside{owner} : List (ℚ × ℚ) := {points(owners[owner]["inside"])}\n'
            inputs+=f'def outside{owner} : List (ℚ × ℚ) := {points(owners[owner]["outside"])}\n\n'
            selected=[]
            for angle in range(128):
                _,_,c,s,outer,_,wall=angles[angle]
                rows=[row for point in owners[owner]['inside'] for row in point_forms(c,s,Q(1001,1000)*outer,point)]
                wall_start=len(rows)
                rows += [(Q(1),Q(0),-wall/2),(Q(-1),Q(0),4-wall/2),
                         (Q(0),Q(1),-wall/2),(Q(0),Q(-1),4-wall/2)]
                indices=strongest_original_indices(rows)
                need(len(indices)==8 and all(i in indices for i in range(wall_start,wall_start+4)),'unexpected original normal structure')
                old=original[owner,angle];need(old['passed'],'failed audit root')
                target=None if old['target_pose'] is None else names[old['target_pose']]
                if target is not None:need(poses[target]['angle']==angle+64,'target angle mismatch')
                else:need(not old['absent_pose_closed_nonempty'],'unproved empty angle')
                selected.append({'owner':owner,'angle':angle,'indices':indices,'target':target})
                counts['empty_angles' if target is None else 'target_angles']+=1
            need([r['target'] for r in selected if r['target'] is not None]==
              data['domains'][f'continuousScout713Domain{owner}_0'],'original domain order mismatch')
            records.extend(selected)
            if args.checked_command:
                for batch in range(16):
                    path=f'Compact/Cases/C713/RecipeInitial/Batches/Owner{owner:02}Batch{batch:02}.lean'
                    outputs[path]=command_batch_source(owner,batch,selected[8*batch:8*batch+8])
            outputs[f'Compact/Cases/C713/RecipeInitial/Data{owner:02}.lean']=owner_source(
                owner,selected,args.checked_command)
            outputs[f'Compact/Cases/C713/RecipeInitial/Owner{owner:02}.lean']=owner_bridge(owner)
        outputs['Compact/Cases/C713/RecipeInitial/Inputs.lean']=inputs+footer()
        outputs['Compact/Cases/C713/RecipeInitial/Bank.lean']=bank_source()
        outputs['Compact/Cases/C713/RecipeInitial/All.lean']='\n'.join(
          f'import Compact.Cases.C713.RecipeInitial.Owner{owner:02}' for owner in OWNERS)+'\n'
        outputs['Compact/Cases/C713/RecipeInitial/Entry.lean']=entry_source()
        if args.checked_command:
            outputs['Compact/Cases/C713/RecipeInitial/CommandPilot.lean']=command_batch_source(
                0,0,records[:8],'N12Compact.C713RecipeCommandPilot')
        else:
            outputs['Compact/Cases/C713/RecipeInitial/Pilot.lean']=header([
              'Compact.Cases.C713.RecipeInitial.Bank'])+batch_source(0,0,records[:1])+footer()
        # Shared exact dictionary: original64 then original128, as authenticated
        # by the compact data emitter. The current case selects only128 IDs.
        ns='N12Compact.C713Shared'
        shared=header(['Compact.HistoricalData.SharedPoses','Compact.Bridge.IndexedRelaxation',
          'S12.AngleData64','S12.AngleData128'],ns)
        shared+='''def angles (i : Fin 192) : {w : AngleEnclosure // w.Check} :=
  if i.val < 64 then (angles64[i.val]?).getD ⟨angle64_0,angle64_0_checked⟩
  else (angles128[i.val-64]?).getD ⟨angle128_0,angle128_0_checked⟩

def dictionary : IndexedRelaxation.Dictionary HistoricalData.rowCount HistoricalData.poseCount 192 :=
  ⟨HistoricalData.rows, HistoricalData.denominators, angles,
   HistoricalData.poseAngle, HistoricalData.poseRows⟩

def poses : Fin HistoricalData.poseCount → PoseLeaf := dictionary.pose

theorem angles128_cover_kernel : CoversInterval 0 1 (angles128.map Subtype.val) := by
  decide +kernel
'''
        outputs['Compact/Cases/C713/SharedDictionary.lean']=shared+footer(ns)
        domains=header(['Compact.Cases.C713.SharedDictionary'],ns)
        for name,ids in data['domains'].items():
            domains+=f'def {name}Ids : List (Fin HistoricalData.poseCount) := ['+','.join(map(str,ids))+']\n'
            domains+=f'def {name} : List PoseLeaf := {name}Ids.map poses\n\n'
        outputs['Compact/Cases/C713/SharedDomains.lean']=domains+footer(ns)
        # Preserve all original ownership certificates, but use kernel checks.
        path=ROOT/'evidence/historical/source-gzip/S12/Push713Chunk92.lean.gz'
        raw=gzip.open(path,'rb').read();need(hashlib.sha256(raw).hexdigest()==receipt['S12.Push713Chunk92'],'entrance source hash mismatch')
        text=raw.decode();text=text[text.index('def case713Family'):text.index('def sharedCommonEnclosure713_0')]
        # This selected interval includes original query proofs, domain refinements
        # and common owned points. No old continuous roots or propagation imports.
        starts=list(re.finditer(r'^(?:noncomputable )?(?:def|theorem|lemma) (\w+)',text,re.M))
        chunks={'queries':[],'domains':[],'refined':[],'points':[]}
        query_source=(ROOT/'source/S12/LocalQueryData.lean').read_text()
        known_queries={re.sub(r'\s','',expr):int(index) for index,expr in re.findall(
          r'^def localQuery(\d+) : LocalQuery := (.+)$',query_source,re.M)}
        aliases={}
        for i,match in enumerate(starts):
            name=match[1];body=text[match.start():starts[i+1].start() if i+1<len(starts) else len(text)]
            # Chunk concatenation has namespace/section delimiters between
            # declarations. They are not part of the declarations being kept.
            body=re.split(r'^end(?: S12)?\s*$',body,maxsplit=1,flags=re.M)[0].rstrip()+'\n'
            if name=='case713_ownership' or name.startswith(('case713RefinedDomains','domains713')):continue
            if name=='case713Family' or name.startswith(('query713','single713')):section='queries'
            elif name.startswith('domain713'):section='domains'
            elif name.startswith('refined713') or name.startswith('case713Domain'):section='refined'
            elif name.startswith('commonPoint713') or name=='commonPoints713':section='points'
            else:raise RuntimeError('unmapped entrance declaration '+name)
            if name.startswith('query713_') and not name.endswith('_checked'):
                found=re.match(r'def \w+ : LocalQuery := (.+)',body)
                if found:
                    existing=known_queries.get(re.sub(r'\s','',found[1]))
                    if existing is not None:
                        aliases[name]=existing
                        body=f'def {name} : LocalQuery := localQuery{existing}\n'
            elif name.endswith('_checked') and name.removesuffix('_checked') in aliases:
                original_name=name.removesuffix('_checked');existing=aliases[original_name]
                body=f'''theorem {name} : {original_name}.Check :=
  c713_query_at queryChunk{existing//50} queryChunk{existing//50}_checked ⟨{existing%50}, by decide⟩
'''
            chunks[section].append(body.replace('native_decide','decide +kernel'))
        chunks['queries'].insert(0, 'theorem c713_query_at (queries : List LocalQuery)\n    (checked : queries.all (fun w => decide w.Check) = true)\n    (i : Fin queries.length) : (queries.get i).Check :=\n  of_decide_eq_true (List.all_eq_true.mp checked _ (List.get_mem queries i))\n\n')
        imports={'queries':['S12.DirectSingleDomain','S12.LocalQueryData'],
          'domains':['Compact.Cases.C713.EntryQueries'],
          'refined':['Compact.Cases.C713.EntryDomains','S12.DomainRefinement'],
          'points':['Compact.Cases.C713.EntryRefined','S12.DomainHullPoint']}
        outputs.update(split_query_sources(chunks['queries']))
        for key,title in [('domains','Domains'),('refined','Refined'),('points','Points')]:
            outputs[f'Compact/Cases/C713/Entry{title}.lean']=header(imports[key],'S12')+''.join(chunks[key])+footer('S12')
        need(counts=={'empty_angles':94,'target_angles':1058},'root outcome mismatch')
        total=sum(len(v.encode()) for v in outputs.values());need(total<8*1024**2,'8MiB output limit')
        for name,source in outputs.items():
            guard();p=stage/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(source)
        report={'status':'complete source proposal; no Lean acceptance','case':713,
          'checked_command':args.checked_command,
          'representation':('One original root specification per checked_recipe command; '
            'separate cached entry and ordinary kernel theorem; eight roots per module.'
            if args.checked_command else 'Original cached recipe table batches.'),
          'semantic_roots':1152,'numeric_batches':144,**counts,'serialized_target_rows':0,
          'lean_modules':len(outputs),'lean_lines':sum(s.count('\n') for s in outputs.values()),
          'lean_bytes':total,'entrance_original_sha256':receipt['S12.Push713Chunk92'],
          'existing_query_proofs_reused':len(aliases),
          'inputs':{str(p.relative_to(ROOT)):sha(p) for p in paths},'records':records,
          'remaining':['Lean replay of exact ownership and direct-cover source',
            'new occupied-row height transition to Domain7_6',
            'nine checked pair/relaxation transitions and final contradiction'],
          'outputs':[{'path':name,'sha256':hashlib.sha256(source.encode()).hexdigest(),
            'lines':source.count('\n'),'bytes':len(source.encode())} for name,source in outputs.items()],
          'seconds':time.monotonic()-start}
        (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        stage.rename(destination)
        print(json.dumps({k:report[k] for k in ['status','semantic_roots','empty_angles',
          'target_angles','lean_modules','lean_lines','lean_bytes','seconds']}))
    except BaseException:
        shutil.rmtree(stage);raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)

if __name__=='__main__':main()
