#!/usr/bin/env python3
"""Prepare compact exact overlap adapters for original historical stages.

Parent-only --run,256MiB/120seconds; no Lean, numerical search, subprocesses,
archives, or active-source edits. One raw cache per used fan, one exact binding
per actual pose/block, and one semantic rectangle record per group. Ordinary
kernel checks remain in every emitted proof. Default C713; --cases all emits
all113 pair stages. Output is an isolated atomic proposal, never acceptance.
"""
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
FANS = ROOT / 'evidence/historical-fans-701-713-717-973-978-979-cycles/fans.json'
AUDIT = ROOT / 'evidence/historical-common-points'
PREFIX = 'Compact/HistoricalCommon'
MODULE = 'Compact.HistoricalCommon'
NS = 'N12Compact.HistoricalCommon'
FAN_MODULE = 'Compact.HistoricalFans.C701_713_717_973_978_979'
FAN_NS = 'N12Compact.HistoricalFans.C701_713_717_973_978_979'


def need(value, why):
    if not value:
        raise ValueError(why)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        for part in iter(lambda: source.read(65536), b''):
            h.update(part)
    return h.hexdigest()


def literal(values):
    return '[' + ','.join(map(str, values)) + ']'


def vector(values):
    return '!' + literal(values)


def header(imports, namespace):
    return '\n'.join('import ' + i for i in sorted(set(imports))) + f'''

namespace {namespace}
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

'''


def footer(namespace):
    return '\nend\nend ' + namespace + '\n'


def partition(box, rectangles):
    """Recover the audited binary subdivision, without enumerating pose pairs."""
    if len(rectangles)==1:
        need(rectangles[0]==box,'partition leaf does not equal current rectangle')
        return '.leaf'
    al,ah,bl,bh=box
    for axis,low,high in [(0,al,ah),(2,bl,bh)]:
        candidates=sorted({r[axis+1] for r in rectangles if low<r[axis+1]<high})
        for cut in candidates:
            left=[r for r in rectangles if r[axis+1]<=cut]
            right=[r for r in rectangles if cut<=r[axis]]
            if not left or not right or len(left)+len(right)!=len(rectangles):
                continue
            lbox=list(box);rbox=list(box)
            lbox[axis+1]=cut;rbox[axis]=cut
            constructor='.sourceCut' if axis==0 else '.neighborCut'
            return f'({constructor} {cut-low} {partition(lbox,left)} {partition(rbox,right)})'
    raise ValueError('rectangles do not have an exhaustive binary partition')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--cases', default='713')
    parser.add_argument('--fused', action='store_true',
                        help='replace old standalone fan closure by one checked context recipe')
    parser.add_argument('--header-plans', action='store_true',
                        help='bind exact source/block headers of the whole-target stages')
    parser.add_argument('--output')
    args = parser.parse_args()
    need(args.run, 'prepared only; parent must schedule --run')
    need(not args.header_plans or args.fused, 'whole-target stages require the fused route')
    cases = (701,713,717,973,978,979) if args.cases == 'all' else tuple(map(int,args.cases.split(',')))
    need(cases and set(cases) <= {701,713,717,973,978,979}, 'unsupported case selection')
    output=args.output or ('evidence/proposals/HistoricalCommonHeaderFused' if args.header_plans else
                          'evidence/proposals/HistoricalCommonFused' if args.fused else
                           'evidence/proposals/HistoricalCommon')
    out = (ROOT / output).resolve()
    need(out.is_relative_to(ROOT/'evidence/proposals'), 'proposal destination required')
    staging = out.with_name(out.name + '.staging')
    need(not out.exists() and not staging.exists(), 'refusing existing proposal')
    started = time.monotonic()
    provenance, written, outputs = {}, 0, []

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        rss *= 1 if sys.platform == 'darwin' else 1024
        need(rss < 256*1024**2, '256 MiB guard')
        need(time.monotonic()-started < 115, '115-second working deadline')

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,stop)
    signal.signal(signal.SIGINT,stop)

    def load(path):
        provenance[str(path.relative_to(ROOT))] = digest(path)
        with path.open() as source:
            return json.load(source)

    def write(relative, text):
        nonlocal written
        guard()
        written += len(text.encode())
        need(written < 16*1024**2, '16 MiB source proposal cap')
        path = staging / relative
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(text)
        outputs.append({'path':relative,'sha256':digest(path),'lines':text.count('\n'),
                        'bytes':len(text.encode())})

    try:
        audit_manifest = load(AUDIT/'manifest.json')
        need(audit_manifest['all_original_occurrences_accounted'] and
             audit_manifest['all_fallback_axes_rechecked'],'incomplete source audit')
        contexts = load(BASE/'contexts.json')
        poses = load(BASE/'poses.json')
        blocks = load(BASE/'blocks.json')
        fan_data = load(FANS)
        empty = {int(k):v for k,v in load(AUDIT/'empty-certificates.json').items()}
        data = {case:load(BASE/f'C{case}.json') for case in cases}
        stages = [s for s in load(AUDIT/'stages.json') if s['case'] in cases]
        for relative,actual in provenance.items():
            if relative in audit_manifest['sources']:
                need(actual==audit_manifest['sources'][relative],'audit source drift: '+relative)
        for item in audit_manifest['files']:
            relative=str((AUDIT/item['path']).relative_to(ROOT))
            if relative in provenance:
                need(provenance[relative]==item['sha256'],'audit output drift: '+relative)
        all_fans = sorted(int(f['context']) for f in fan_data['context_records']
                          if int(f['context']) not in empty)
        positions = {cid:i for i,cid in enumerate(all_fans)}
        need(len(positions)==12932,'unexpected certified fan count')
        order = fan_data['angle_order']
        need(sorted(order)==list(range(192)), 'angle-order permutation')
        ranks = [order.index(i) for i in range(192)]
        context_ids = {(c['angle'],tuple(c['inputs'])):c['index'] for c in contexts}
        need(len(context_ids)==len(contexts),'context key collision')
        for records in (contexts,poses,blocks):
            need(all(row['index']==i for i,row in enumerate(records)),'dictionary ID order')

        def binding(pose, block):
            rows = ([] if block is None else blocks[block]['rows']) + poses[pose]['rows']
            cid = context_ids[(poses[pose]['angle'],tuple(rows))]
            need(cid in positions or cid in empty,'missing fan and empty proof')
            return (cid,pose,-1 if block is None else block)

        all_bindings, stage_rows = set(), []
        for stage in stages:
            case,step = stage['case'],stage['step']
            original = [p for p in data[case]['plans'] if p['step']==step]
            blocked = [p for p in original if p['block'] is not None]
            names = data[case]['pair_steps'][str(step)]
            need(names==stage['domains'],'stage domain provenance')
            need([p['source'] for p in original]==data[case]['domains'][names[0]],'source coverage')
            need([p['origin'] for p in blocked]==stage['source_plans'],'blocked plan identity')
            sources = [binding(p['source'],p['block']) for p in blocked]
            neighbors = [binding(p,None) for p in data[case]['domains'][names[1]]]
            need([b[0] for b in sources]==stage['source_contexts'],'source context order')
            need([b[0] for b in neighbors]==stage['neighbor_contexts'],'neighbor context order')
            need(0<len(stage['groups'])<=100,'rectangle count needs simplification')
            all_bindings.update(sources+neighbors)
            stage_rows.append((stage,original,sources,neighbors))
        selected_bindings = sorted(all_bindings)
        binding_ids = {b:i for i,b in enumerate(selected_bindings)}
        canonical={}
        for b in selected_bindings:
            canonical.setdefault(b[0],b)
        cycles={int(record['context']):record['boundary_cycle']
                for record in fan_data['context_records']}
        if args.fused:
            need(all(cycles[b[0]] for b in selected_bindings if b[0] not in empty),
                 'fused mode requires an actual audited cycle for each nonempty context')
        used = sorted({b[0] for b in all_bindings if b[0] not in empty})
        cache_shards = {cid:i//32 for i,cid in enumerate(used)}
        staging.mkdir(parents=True)

        # The rank array only guides lookup; actual cone/axis checks prove geometry.
        keys = header(['Compact.Cases.C713.SharedDictionary'],NS)
        keys = keys.replace(' IntegerSupport IndexedCommonGroups ', ' IntegerSupport ')
        keys += 'def angleRank : Array Nat := #' + literal(ranks) + '\n\n'
        keys += '''def ownKeys (angle : Nat) (i : Fin 4) : Nat :=
  (angleRank[angle]?).getD 0 + 192 * (![0,2,1,3] i)

def pairKeys (source neighbor : Nat) (i : Fin 8) : Nat :=
  if h : i.val < 4 then ownKeys source ⟨i.val,h⟩
  else ownKeys neighbor ⟨i.val-4,by omega⟩

def opposite (key : Nat) : Nat := (key+384)%768
'''
        write(PREFIX+'/Keys.lean',keys+footer(NS))

        # A single authentic original blocked-source/neighbor pair is a quick
        # integration replay; it does not assert completion of its stage.
        _,_,pilot_sources,pilot_neighbors=stage_rows[0]
        pilot=[pilot_sources[0],pilot_neighbors[0]]
        need(all(b[0] not in empty for b in pilot),'pilot needs two nonempty fans')
        imports=[MODULE+'.Keys','Compact.Bridge.CheckedCommonContext',
                 'Compact.Bridge.CheckedCommonGroup','Compact.HistoricalData.SharedFanBlocks']
        if args.fused:
            imports += ['Compact.Bridge.CheckedCommonFanCommand',FAN_MODULE+'.Directions']
        else:
            imports += [FAN_MODULE+f'.Contexts{positions[b[0]]//32:03}' for b in pilot]
        pilot_ns=NS+'.Pilot'
        text=header(imports,pilot_ns)
        for role,(cid,pose,block) in zip(('Source','Neighbor'),pilot):
            index=positions[cid]
            chunk,offset=divmod(index,32)
            count=min(32,len(all_fans)-chunk*32)
            raw=f'({FAN_NS}.contexts{chunk:03}[{offset}]\'(by decide))'
            proof=f'({FAN_NS}.contexts{chunk:03}_checked ({offset} : Fin {count}))'
            rows='[]' if block==-1 else f'fanBlockRows {block}'
            if args.fused:
                text+=f'checked_common_fan context{role} (dictionary,{FAN_NS}.directions) := ⟨{pose},{rows}⟩ using {literal(cycles[cid])}\n'
            else:
                text+=f'cache_common_fan raw{role} (dictionary,{raw},{proof})\n'
                text+=f'bind_common_context context{role} (dictionary,raw{role}) := ⟨{pose},{rows}⟩\n'
        text+='''
def sources : Fin 1 → Context dictionary := fun _ => contextSource
def neighbors : Fin 1 → Context dictionary := fun _ => contextNeighbor
checked_axis_group group (sources,neighbors,positive_denominators,pairKeys,opposite) : 1 × 1 in (0,1,0,1)

theorem authentic_overlap : PairOverlaps contextSource contextNeighbor :=
  group.sound 0 0 (by decide +kernel)

#print axioms authentic_overlap
'''
        write(PREFIX+'/Pilot.lean',text+footer(pilot_ns))

        for start in ([] if args.fused else range(0,len(used),32)):
            chosen = used[start:start+32]
            imports = [FAN_MODULE+f'.Contexts{positions[cid]//32:03}' for cid in chosen]
            imports += ['Compact.Bridge.CheckedCommonContext','Compact.Cases.C713.SharedDictionary']
            text = header(imports,NS)
            for cid in chosen:
                index = positions[cid]
                chunk,offset = divmod(index,32)
                count = min(32,len(all_fans)-chunk*32)
                raw = f'({FAN_NS}.contexts{chunk:03}[{offset}]\'(by decide))'
                proof = f'({FAN_NS}.contexts{chunk:03}_checked ({offset} : Fin {count}))'
                text += f'cache_common_fan fan{cid} (dictionary,{raw},{proof})\n'
            write(PREFIX+f'/Raw{start//32:03}.lean',text+footer(NS))

        for start in range(0,len(selected_bindings),32):
            chosen = selected_bindings[start:start+32]
            if args.fused:
                imports=['Compact.Bridge.CheckedCommonFanCommand',FAN_MODULE+'.Directions']
                imports += [MODULE+f'.Bindings{binding_ids[canonical[b[0]]]//32:03}'
                    for b in chosen if b[0] not in empty and binding_ids[canonical[b[0]]]//32 < start//32]
            else:
                imports = [MODULE+f'.Raw{cache_shards[b[0]]:03}' for b in chosen if b[0] not in empty]
            imports += ['Compact.Bridge.CheckedCommonContext','Compact.HistoricalData.SharedFanBlocks',
                        'Compact.Cases.C713.SharedDictionary']
            text = header(imports,NS)
            text += 'set_option maxRecDepth 10000\n\n'
            for b in chosen:
                cid,pose,block = b
                idx = binding_ids[b]
                rows = '[]' if block == -1 else f'fanBlockRows {block}'
                head = f'⟨{pose},{rows}⟩'
                if cid in empty:
                    cert = empty[cid]
                    terms = '['+','.join(f'({w},{r})' for w,r in zip(cert['weights'],cert['rows']))+']'
                    text += f'checked_empty_context context{idx} (dictionary) := {head} using {terms}\n'
                elif args.fused and canonical[cid]==b:
                    text += f'checked_common_fan context{idx} (dictionary,{FAN_NS}.directions) := {head} using {literal(cycles[cid])}\n'
                elif args.fused:
                    cache='context'+str(binding_ids[canonical[cid]])+'_cache'
                    text += f'bind_common_context context{idx} (dictionary,{cache}) := {head}\n'
                else:
                    text += f'bind_common_context context{idx} (dictionary,fan{cid}) := {head}\n'
            write(PREFIX+f'/Bindings{start//32:03}.lean',text+footer(NS))

        emitted_stages = []
        for stage,original,sources,neighbors in stage_rows:
            case,step = stage['case'],stage['step']
            u,v = len(sources),len(neighbors)
            stage_ns = NS+f'.C{case}.Step{step:02}'
            stage_path = PREFIX+f'/C{case}/Step{step:02}'
            stage_module = MODULE+f'.C{case}.Step{step:02}'
            ids = [binding_ids[b] for b in sources+neighbors]
            imports = [MODULE+f'.Bindings{i//32:03}' for i in ids]
            imports += [MODULE+'.Keys','Compact.Bridge.CheckedCommonGroup']
            text = header(imports,stage_ns)
            for name,bindings in [('sources',sources),('neighbors',neighbors)]:
                text += f'def {name} : Fin {len(bindings)} → Context dictionary :=\n  '
                text += vector('context'+str(binding_ids[b]) for b in bindings)+'\n\n'
            write(stage_path+'Data.lean',text+footer(stage_ns))
            group_names=[]
            group_modules=[]
            for start in range(0,len(stage['groups']),4):
                text=header([stage_module+'Data'],stage_ns)
                for ordinal,group in enumerate(stage['groups'][start:start+4],start):
                    lo,hi,nlo,nhi=group['bounds']
                    need(0<=lo<hi<=u and 0<=nlo<nhi<=v,'scope outside stage')
                    name=f'group{ordinal}'
                    group_names.append(name)
                    scope=f'({lo},{hi-lo},{nlo},{nhi-nlo})'
                    if group['kind']=='common_point':
                        point='⟨'+','.join(map(str,group['point']))+'⟩'
                        text+=f'checked_point_group {name} (sources,neighbors,positive_denominators,ownKeys) : {u} × {v} in {scope} at {point}\n'
                    else:
                        need(group['kind']=='original_pair_axes','unknown group primitive')
                        # Large rectangles emit hundreds of kernel-checked blocks.
                        if (hi-lo)*(nhi-nlo) > 3000:
                            text+='set_option maxRecDepth 10000 in\nset_option maxHeartbeats 0 in\n'
                        text+=f'checked_axis_group {name} (sources,neighbors,positive_denominators,pairKeys,opposite) : {u} × {v} in {scope}\n'
                group_modules.append(stage_module+f'Groups{start//4:02}')
                write(stage_path+f'Groups{start//4:02}.lean',text+footer(stage_ns))
            pruning_bridge=('Compact.Bridge.CommonHeaderPruning' if args.header_plans else
                            'Compact.Bridge.CommonGroupPruning')
            text=header(group_modules+[pruning_bridge,
                'Compact.Bridge.CommonRectanglePartition',
                f'Compact.Cases.C{case}.DirectPruning.Step{step:02}'],stage_ns)
            text+='def groups : List (CheckedGroup sources neighbors) :=\n  '+literal(group_names)+'\n\n'
            text+='def scopes : List Scope :=\n  '+literal(n+'_scope' for n in group_names)+'\n\n'
            text+='theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl\n\n'
            tree=partition([0,u,0,v],[g['bounds'] for g in stage['groups']])
            text+=f'''def partition : RectanglePartition :=
  {tree}

theorem partition_checked : partition.Check ⟨0,{u},0,{v}⟩ scopes := by decide +kernel

theorem covered (i : Fin {u}) (j : Fin {v}) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

'''
            text+=f'''theorem pairs (i : Fin {u}) (j : Fin {v}) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  '''+literal('context'+str(binding_ids[b])+'_header' for b in sources)+'\n\n'
            text+=f'''set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange {u}).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  '''+literal(f'({p["source"]},'+('none' if p['block'] is None else f'some (fanBlockRows {p["block"]})')+')' for p in original)+'\n\n'
            direct=f'N12Compact.C{case}DirectPruning.Step{step:02}'
            domain_prefix='N12Compact.C713Shared.' if case==713 else f'N12Compact.Preservation.C{case}.'
            domain=domain_prefix+stage['domains'][1]
            original_headers=(direct+'.planHeaders' if args.header_plans else
                              direct+'.plans.map (fun plan => (plan.source,plan.block))')
            text+=f'''theorem planHeaders_exact :
    {original_headers} = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange {v}).map (fun j => (neighbors j).header.pose) = {domain}Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

'''
            if args.header_plans:
                text+=f'''theorem block_overlaps : {direct}.BlockOverlap := by
  change ∀ plan ∈ {direct}.planHeaders, HeaderOverlap dictionary {domain}Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors {domain}Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs
'''
            else:
                text+=f'''theorem block_overlaps : {direct}.BlockOverlap := by
  exact block_overlap sources neighbors {direct}.plans {domain}Ids
    sourceHeaders sourceHeaders_exact planHeaders planHeaders_exact source_matches
    neighbors_exact neighbor_unblocked pairs
'''
            text+='\n#print axioms block_overlaps\n'
            write(stage_path+'.lean',text+footer(stage_ns))
            emitted_stages.append({'case':case,'step':step,'groups':len(group_names),
                'sources':u,'neighbors':v,'original_pairs':stage['original_pairs'],
                'module':stage_module,'theorem':stage_ns+'.block_overlaps'})
        text=header([s['module'] for s in emitted_stages],NS)
        write(PREFIX+'/All.lean',text+footer(NS))
        report={'status':'source proposal; all numeric and original semantic replay pending',
            'cases':list(cases),'stages':emitted_stages,'input_sha256':provenance,
            'raw_caches':len(used),'actual_pose_block_bindings':len(selected_bindings),
            'fused_fan_recipes':args.fused,'imports_old_context_modules':not args.fused,
            'whole_target_header_plans':args.header_plans,
            'additional_noncanonical_bindings':sum(b!=canonical[b[0]] for b in selected_bindings),
            'scope_coverage':'binary subdivision induction; no pair matrix',
            'empty_bindings':sum(b[0] in empty for b in selected_bindings),
            'rectangle_records':sum(s['groups'] for s in emitted_stages),
            'per_pair_source_records':0,'lean_modules':len(outputs),
            'lean_lines':sum(o['lines'] for o in outputs),'lean_bytes':written,'outputs':outputs,
            'elapsed_seconds':time.monotonic()-started}
        (staging/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        staging.replace(out)
        print(json.dumps({k:report[k] for k in ['cases','raw_caches','actual_pose_block_bindings',
              'rectangle_records','lean_modules','lean_lines','lean_bytes','elapsed_seconds']}))
    except BaseException:
        if staging.exists():
            shutil.rmtree(staging)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':
    main()
