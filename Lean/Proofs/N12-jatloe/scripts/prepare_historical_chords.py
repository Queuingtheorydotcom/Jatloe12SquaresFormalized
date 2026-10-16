#!/usr/bin/env python3
"""Prepare direct original-domain certificates for twenty historical chords.

Parent serial slot only: --run, 256 MiB / 180 seconds, 16 MiB output.
No Lean, solver, network, subprocess or active-source write. Every branch
retains the exact source rows and a strict interval complement. It must imply
one original final target in full, or an explicit <=3-row Farkas contradiction.
Unreconstructed branches are reported as gaps; they never generate admissions.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from pathlib import Path
import argparse, hashlib, json, re, resource, shutil, signal, sys, time

from audit_historical_outside_coverage import Context
from audit_historical_bank_reachability import JSONStream
from audit_historical_direct_cover import declarations
from prepare_historical_graphs import read_case
from provenance_source import read_bytes

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT/'evidence/historical-compact-data'
DEST = ROOT/'evidence/proposals/HistoricalChords'
CASES = (701,713,717,973,978,979)
MODULE = 'Compact.Preservation.Chords'
NS = 'N12Compact.Preservation.Chords'
CAP = 16*1024**2


def need(test, message):
    if not test:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound_row(horizontal, bound, lower, strict):
    coefficient = bound.denominator if lower else -bound.denominator
    constant = -bound.numerator if lower else bound.numerator
    return (0,coefficient,constant,strict) if horizontal else (coefficient,0,constant,strict)


def hint_text(hint):
    if hint[0] == 'copy': return '.copy '+str(hint[1])
    if hint[0] == 0: return '.constant'
    if hint[0] == 1: return '.single '+str(hint[1])
    need(hint[0] == 2, 'unknown checked hint')
    return '.pair '+str(hint[1])+' '+str(hint[2])


def hint_list(hints):
    return '['+', '.join(map(hint_text,hints))+']'


def row_expr(row):
    return '⟨'+','.join(map(str,row[:3]))+','+str(row[3]).lower()+'⟩'


def rat(value):
    return '('+str(value)+')'


def header(imports, namespace, case=None):
    lines = ['import '+module for module in imports]+['',
        'set_option Elab.async false','set_option maxRecDepth 10000',
        'set_option linter.unnecessarySeqFocus false','',
        'namespace '+namespace,
        'open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan',
        'open N12Compact.Preservation.HistoricalBank', 'noncomputable section','']
    if case is not None: lines += ['open N12Compact.Preservation.C'+str(case),'']
    return lines


def finish(lines, namespace):
    return '\n'.join(lines+['','end','end '+namespace,''])


def radius_name(angle):
    return 'radius'+str(angle)


def radius_source(radii):
    namespace = NS+'.Radii'
    lines = header(['Compact.Bridge.AngleSection','S12.AngleData64','S12.AngleData128'],namespace)
    lines[lines.index('open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan')] = 'open S12 S12Pilot'
    lines[lines.index('open N12Compact.Preservation.HistoricalBank')] = 'open AngleSection'
    for angle,(upper,radius) in sorted(radii.items()):
        original = f'angle64_{angle}' if angle<64 else f'angle128_{angle-64}'
        name = radius_name(angle)
        lines += [f'def {name} : Radius := ⟨{rat(upper)},{rat(radius)}⟩',
            f'theorem {name}_checked : {name}.Check {original} := by',
            f'  norm_num [{name},Radius.Check,{original},supportQuadratic,',
            '    Quadratic.CheckOn,Quadratic.evalRat]','']
    return finish(lines,namespace)


def list_checked(lines, name, values, type_name, predicate):
    lines += [f'checked_chord_collection {name} : ({type_name}) =>',
        f'  (fun (entry : {type_name}) => {predicate}) := [',
        '    '+',\n    '.join(', '.join(values[i:i+12]) for i in range(0,len(values),12))+']','']


def stage_source(case, stage, radii):
    cid,step = case['case'],stage['step']
    namespace = f'{NS}.C{cid}Step{step:02}'
    horizontal = str(stage['horizontal']).lower()
    lines = header(['Compact.Bridge.ChordSyntax','Compact.Bridge.ChordPacking',
        MODULE+'.Radii',f'Compact.Preservation.C{cid}'],namespace,cid)
    lines += ['open N12Compact.Preservation.Chords.Radii',
        f'def horizontal : Bool := {horizontal}',
        f'def lo : ℚ := {rat(stage["lo"])}',f'def hi : ℚ := {rat(stage["hi"])}',
        'theorem ordered : lo ≤ hi := by norm_num [lo,hi]','']
    # Every entry is a separate bounded command. Large proof-bearing literal
    # vectors never enter the numerical checker.
    for owner, records in enumerate(stage['neighbor_records']):
        names=[]
        for index,record in enumerate(records):
            name=f'neighbor{owner}_{index}';names.append(name)
            source,angle=record['source'],record['angle']
            lines += [f'checked_chord_neighbor {name} (dictionary,horizontal,lo,hi) := '+
                f'({source},{radius_name(angle)},{radius_name(angle)}_checked,{hint_list(record["hints"])})']
        list_checked(lines,f'neighbors{owner}',names,'Neighbor dictionary','entry.Check horizontal lo hi')
        lines += [f'theorem neighbors{owner}_sources : neighbors{owner}.map Neighbor.source =',
            f'    {stage["neighbors"][owner]}Ids := by rfl','']
    plan_names=[]
    for index,record in enumerate(stage['plans']):
        source,angle=record['source'],record['angle'];name=f'plan{index}';plan_names.append(name)
        outcomes=[]
        for branch in record['branches']:
            if branch['kind']=='keep':
                outcomes.append(f'chord_keep%({branch["target"]},{hint_list(branch["hints"])})')
            else:
                witness=branch['witness']
                positions='['+','.join(str(i) for i,w in witness)+']'
                terms='['+','.join(f'({weight},{i})' for i,weight in witness)+']'
                outcomes.append(f'chord_close%(⟨{positions},{terms}⟩)')
        lines += [f'checked_chord_plan {name} (dictionary,horizontal,lo,hi) := '+
            f'({source},{radius_name(angle)},{radius_name(angle)}_checked,{outcomes[0]},{outcomes[1]})']
    list_checked(lines,'plans',plan_names,'IndexedChord.Plan dictionary horizontal lo hi','entry.Check')
    target_ids=[branch['target'] for plan in stage['plans'] for branch in plan['branches']
        if branch['kind']=='keep']
    lines += [f'theorem plans_sources : plans.map IndexedChord.Plan.source = {stage["source"]}Ids := by rfl',
        'def outputIds : List (Fin poseCount) := ['+','.join(map(str,target_ids))+']',
        'theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl',
        f'theorem outputs_mem : outputIds.all (fun i => decide (i ∈ {stage["target"]}Ids)) = true := by',
        '  decide +kernel',
        f'theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ {stage["target"]}Ids := by',
        '  intro plan member target included',
        '  have hm : target ∈ outputIds := by',
        '    rw [← outputs_exact]',
        '    exact List.mem_flatMap.mpr ⟨plan,member,included⟩',
        '  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)','',
        'theorem sound (q : Fin 4 → OpenSquare)',
        '    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))',
        '    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))',
        f'    (incoming : OrientedPoseCovered {stage["source"]} (q 0))']
    lines += [f'    (h{owner} : OrientedPoseCovered {domain} (q {owner+1}))'
        for owner,domain in enumerate(stage['neighbors'])]
    lines += [f'    : OrientedPoseCovered {stage["target"]} (q 0) := by',
        '  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators',
        f'    {stage["source"]}Ids {stage["target"]}Ids plans',
        '    plans_sources outputs_included plans_checked q side box disjoint incoming',
        '  intro cut low high i','  fin_cases i']
    for owner,domain in enumerate(stage['neighbors']):
        lines += ['  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators',
            f'      {domain}Ids neighbors{owner} neighbors{owner}_sources neighbors{owner}_checked',
            f'      (q {owner+1}) (side {owner+1}) h{owner} cut low high']
    masks=[case['owners'][int(re.search(r'Domain(\d+)_',domain)[1])]
        for domain in [stage['source']]+stage['neighbors']]
    need(len(set(masks))==4,'original chord owners are not distinct')
    lines += ['', 'def masks : Fin 4 → Nat := !['+','.join(map(str,masks))+']',
        'theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel',
        'theorem masks_distinct : Function.Injective masks := by decide +kernel',
        'theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)',
        f'    (incoming : OrientedPoseCovered {stage["source"]} (p.square (ownerIndex p {masks[0]})))']
    lines += [f'    (h{owner} : OrientedPoseCovered {domain} (p.square (ownerIndex p {masks[owner+1]})))'
        for owner,domain in enumerate(stage['neighbors'])]
    lines += [f'    : OrientedPoseCovered {stage["target"]} (p.square (ownerIndex p {masks[0]})) := by',
        f'  apply ChordPacking.transfer family masks masks_members masks_distinct {stage["source"]} {stage["target"]}',
        '    !['+','.join(stage['neighbors'])+']',
        '    (fun q side box disjoint source neighbors =>',
        '      sound q side box disjoint source (neighbors 0) (neighbors 1) (neighbors 2))',
        '    p family_exact incoming',
        '  intro i; fin_cases i',
        '  · exact h0','  · exact h1','  · exact h2',
        '', '#print axioms packing_sound']
    lines += ['','#print axioms sound']
    return finish(lines,namespace)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',action='store_true')
    args=parser.parse_args();need(args.run,'parent must schedule --run')
    need(not DEST.exists(),'refusing existing chord proposal')
    staging=DEST.with_name(DEST.name+'.staging')
    need(not staging.exists(),'refusing an existing interrupted staging directory')
    started=time.monotonic();provenance={};source_provenance=[];written=0
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        need(rss<256*1024**2 and time.monotonic()-started<174,'256MiB/174second guard')
    def terminate(*_): raise RuntimeError('chord producer interrupted')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,terminate);signal.signal(signal.SIGINT,terminate)
    def load(path,expected=None):
        raw=path.read_bytes();need(expected is None or sha(raw)==expected,'changed input '+str(path))
        provenance[str(path.relative_to(ROOT))]=sha(raw);return json.loads(raw)
    def entries(path,expected):
        value=hashlib.sha256()
        with path.open('rb') as stream:
            for block in iter(lambda:stream.read(65536),b''):value.update(block);guard()
        need(value.hexdigest()==expected,'changed input '+str(path))
        provenance[str(path.relative_to(ROOT))]=expected
        stream=JSONStream(path,guard)
        try:yield from stream.array()
        finally:stream.file.close()
    def write(relative,text):
        nonlocal written
        raw=text.encode();written+=len(raw);need(written<CAP,'16MiB output guard')
        target=staging/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
        return {'bytes':len(raw),'lines':text.count('\n'),'sha256':sha(raw)}
    try:
        manifest=load(BASE/'manifest.json');expected={x['path']:x['sha256'] for x in manifest['output_files']}
        audits=load(ROOT/'evidence/historical-direct-cover-audit.json')['cases']
        cover_path=ROOT/'vendor/S12/CoverData.lean';cover_raw=read_bytes(cover_path)
        cover_rows=[(int(cid),tuple(map(int,values.split(',')))) for cid,values in
            re.findall(r'⟨(\d+),\{([0-9,]+)\}',cover_raw.decode())]
        need(len(cover_rows)==577,'wrong original catalogue')
        cases=[read_case(cid,manifest,next(a for a in audits if a['case']==cid),cover_rows,provenance,guard)
            for cid in CASES]
        stages=[(case,stage) for case in cases for stage in case['stages']
            if stage['kind']!='PruningCoverCheck' and case['case']!=713]
        need(len(stages)==20,'wrong original remaining chord scope')
        wanted={(case['case'],stage['step']):(case,stage) for case,stage in stages}
        selected_poses={i for case,stage in stages for domain in
            [stage['source'],stage['target']]+stage['neighbors'] for i in case['domains'][domain]}
        poses={p['index']:p for p in entries(BASE/'poses.json',expected['poses.json']) if p['index'] in selected_poses}
        need(set(poses)==selected_poses,'missing required pose')
        selected_rows={r for p in poses.values() for r in p['rows']}
        rows={r['index']:tuple(r['integers'])+(r['strict'],)
            for r in entries(BASE/'rows.json',expected['rows.json']) if r['index'] in selected_rows}
        need(set(rows)==selected_rows,'missing required row')
        source_hashes={s['module']:s['sha256'] for s in manifest['sources']}
        stage_modules=defaultdict(set)
        contracts=BASE/'remaining-contracts.jsonl'
        need(sha(contracts.read_bytes())==expected['remaining-contracts.jsonl'],'changed contract index')
        with contracts.open() as stream:
            for line in stream:
                item=json.loads(line);m=re.fullmatch(r'continuousScout(\d+)Step(\d+)Pose0Block(?:Rows)?',item['name'])
                if m and (int(m[1]),int(m[2])) in wanted:
                    stage_modules[(int(m[1]),int(m[2]))].add(item['module'])
        need(set(stage_modules)==set(wanted),'missing exact source-window module')
        selected_modules=set().union(*stage_modules.values())
        # Window metadata can finish the preceding bundle while Pose0 begins
        # the next; all candidates still require their receipt source hash.
        for module in tuple(selected_modules):
            m=re.fullmatch(r'S12.Push(\d+)Chunk(\d+)',module)
            if m and int(m[2]):
                previous=f'S12.Push{m[1]}Chunk{int(m[2])-1}'
                if previous in source_hashes:selected_modules.add(previous)
        pattern=re.compile(r'continuousScout(\d+)Step(\d+)(WindowRows|Pose0Block)')
        def selected(name):
            m=pattern.fullmatch(name)
            return bool(m and (int(m[1]),int(m[2])) in wanted)
        windows={}
        for module in sorted(selected_modules):
            for name,text in declarations(module,source_hashes,source_provenance,guard,selected):
                m=pattern.fullmatch(name);key=(int(m[1]),int(m[2]))
                if m[3]=='WindowRows':
                    value=re.search(r'(heightWindow|columnWindow)\s*\(([-0-9/]+)\)\s*\(([-0-9/]+)\)',text)
                    if value:parsed=(value[1]=='heightWindow',Q(value[2]),Q(value[3]))
                    else:continue
                else:
                    value=re.search(r':\s*(FourVerticalChordWindow|FourChordWindow)\b.*?:=\s*⟨\(([-0-9/]+)\),\(([-0-9/]+)\)',text,re.S)
                    need(value is not None,'unsupported original chord window '+name)
                    parsed=(value[1]=='FourChordWindow',Q(value[2]),Q(value[3]))
                need(key not in windows or windows[key]==parsed,'inconsistent source window')
                windows[key]=parsed
        need(set(windows)==set(wanted),'source window metadata incomplete')
        radius_path=ROOT/'vendor/S12/AngleChordRadiusData.lean';radius_raw=read_bytes(radius_path)
        need(sha(radius_raw)==source_hashes['S12.AngleChordRadiusData'],'radius source hash mismatch')
        radii={}
        for grid,angle,upper,radius in re.findall(
            r'^def angleChordRadius(64|128)_(\d+) : .*?⟩,\(([^()]*)\),\(([^()]*)\)⟩$',radius_raw.decode(),re.M):
            index=int(angle)+(64 if grid=='128' else 0);radii[index]=(Q(upper),Q(radius))
        need(len(radii)==192,'incomplete original radius table')
        failures=[];counts=Counter();records=[];used_angles=set()
        def local_rows(pid):return [rows[r] for r in poses[pid]['rows']]
        for case,stage in stages:
            guard();cid,step=case['case'],stage['step'];horizontal,lo,hi=windows[(cid,step)]
            need(lo<=hi,'reversed original chord window')
            record=dict(stage,case=cid,horizontal=horizontal,lo=str(lo),hi=str(hi),neighbor_records=[],plans=[])
            targets=defaultdict(list)
            for target in case['domains'][stage['target']]:targets[poses[target]['angle']].append(target)
            for owner,domain in enumerate(stage['neighbors']):
                values=[]
                for source in case['domains'][domain]:
                    guard();angle=poses[source]['angle'];used_angles.add(angle);radius=radii[angle][1]
                    context=Context(local_rows(source))
                    bounds=[bound_row(horizontal,hi-radius,True,False),bound_row(horizontal,lo+radius,False,False)]
                    hints=[context.hint(row) for row in bounds]
                    if any(h is None for h in hints):
                        failures.append({'case':cid,'step':step,'kind':'neighbor','source':source,'owner':owner})
                    values.append({'source':source,'angle':angle,'hints':hints})
                    counts['neighbor_pose_occurrences']+=1;counts['neighbor_bounds']+=2
                record['neighbor_records'].append(values)
            for source in case['domains'][stage['source']]:
                angle=poses[source]['angle'];used_angles.add(angle);radius=radii[angle][1];branches=[]
                for high,bound in ((False,lo-radius),(True,hi+radius)):
                    guard();cut=bound_row(horizontal,bound,high,True);inputs=[cut]+local_rows(source)
                    context=Context(inputs);empty=context.empty();counts['branch_contexts']+=1
                    if empty is not None:
                        branches.append({'kind':'close','witness':empty});counts['empty_branches']+=1
                        counts['empty_terms']+=len(empty);continue
                    success=None
                    for target in targets[angle]:
                        hints=[context.hint(row) for row in local_rows(target)]
                        if all(h is not None for h in hints):
                            success={'kind':'keep','target':target,'hints':hints};break
                    if success is None:
                        failures.append({'case':cid,'step':step,'kind':'source-branch','source':source,
                            'high':high,'candidates':targets[angle]});branches.append({'kind':'unresolved'})
                    else:
                        branches.append(success);counts['kept_branches']+=1
                        counts['target_row_checks']+=len(success['hints'])
                record['plans'].append({'source':source,'angle':angle,'branches':branches})
                counts['source_poses']+=1
            records.append(record);counts['stages']+=1
        staging.mkdir(parents=True)
        output={}
        certificate_info=write('certificates.json',json.dumps({'scope':'exact numerical proposal only; not Lean acceptance',
            'stages':records,'failures':failures},separators=(',',':'))+'\n')
        if not failures:
            relative=MODULE.replace('.','/')+'/Radii.lean'
            output[relative]=write(relative,radius_source({i:radii[i] for i in used_angles}))
            for case,stage in zip([c for c,s in stages],records):
                relative=MODULE.replace('.','/')+f'/C{case["case"]}Step{stage["step"]:02}.lean'
                output[relative]=write(relative,stage_source(case,stage,radii))
        report={'status':'source assembled; Lean acceptance pending' if not failures else 'exact reconstruction has explicit gaps',
            'scope':'twenty complete original chord transitions; C713 step5 uses the separate height proof',
            'lean_checked':False,'certificate_file':certificate_info,'counts':dict(counts),'failures':failures,'used_angles':sorted(used_angles),
            'inputs':provenance,'authenticated_sources':source_provenance,'output_files':output,
            'lean_lines':sum(v['lines'] for v in output.values()),'lean_bytes':sum(v['bytes'] for v in output.values()),
            'elapsed_seconds':time.monotonic()-started}
        write('manifest.json',json.dumps(report,indent=2)+'\n')
        staging.replace(DEST)
        print(json.dumps({k:report[k] for k in ('status','counts','lean_lines','lean_bytes','elapsed_seconds')}))
        print(json.dumps({'failures':len(failures),'first_failures':failures[:5]}))
    except BaseException:
        if staging.exists():shutil.rmtree(staging)
        raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
