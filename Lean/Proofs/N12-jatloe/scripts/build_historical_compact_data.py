#!/usr/bin/env python3
"""Extract shared post-forest data for the six historical whole-case routes.

Prepared only: the parent must supply --run in its serial bounded slot. Streams
all authenticated source closures, then emits literal Lean rows/poses and exact
machine-readable domains, links, plans and transition bindings. No old code is
executed, no numerical support is trusted, and no theorem/check is fabricated.
Pair weights are replaced by complete source-plan x neighbor-domain obligations;
window/chord/tree contracts remain explicit source obligations. A manifest never
calls this a complete proof. Failed runs remove only their new staging directory.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import argparse, gzip, hashlib, json, math, re, resource, shutil, signal, sqlite3, sys, time
from audit_historical_direct_cover import ROOT, declarations, need, Unsupported

CASES=(701,713,717,973,978,979)
EXPLICIT=re.compile(r'⟨⟨!\[([^,\]]+),([^\]]+)\],([^⟩]+)⟩,(true|false)⟩')
LOCAL=re.compile(r'continuousScout(701|713|717|973|978|979)(?:Initial|Step|Domain)')
POSE=re.compile(r'⟨⟨angle(64|128)_(\d+),\w+⟩,regionConstraintsFromText "([^"\n]*)"')


def compact(value): return json.dumps(value,separators=(',',':'),ensure_ascii=False)


def split_top(text):
    """Split constructor fields, never commas inside lists/constructors/strings."""
    result=[];start=0;stack=[];quoted=False;escaped=False
    pairs={')':'(',']':'[','}':'{','⟩':'⟨'}
    for i,c in enumerate(text):
        if quoted:
            if escaped:escaped=False
            elif c=='\\':escaped=True
            elif c=='"':quoted=False
            continue
        if c=='"':quoted=True
        elif c in '([{⟨':stack.append(c)
        elif c in ')]}⟩':
            need(stack and stack.pop()==pairs[c], 'unbalanced literal constructor')
        elif c==',' and not stack:result.append(text[start:i].strip());start=i+1
    need(not stack and not quoted,'unterminated literal constructor')
    result.append(text[start:].strip())
    return result


def list_names(expr):
    expr=expr.strip()
    need(expr.startswith('[') and expr.endswith(']'),'not a literal name list')
    names=split_top(expr[1:-1]) if expr[1:-1].strip() else []
    need(all(re.fullmatch(r'\w+',x) for x in names),'non-name list member')
    return names


def body_of(text):
    # Declaration iterator may include section terminators after a final item.
    body=text.split(':=',1)[1].strip()
    return re.split(r'\n(?:end\b|#print\b|section\b)',body,maxsplit=1)[0].strip()


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run',action='store_true')
    ap.add_argument('--output',default='evidence/historical-compact-data')
    args=ap.parse_args()
    if not args.run:ap.error('prepared only; parent compute slot and --run required')
    out=(ROOT/args.output).resolve()
    need(out.is_relative_to((ROOT/'evidence').resolve()),'output outside evidence')
    stage=out.with_name(out.name+'.staging')
    need(not out.exists() and not stage.exists(),'output or staging already exists')
    stage.mkdir(parents=True)
    started=time.monotonic();written=0;db=None
    report={'status':'incomplete','proof_assembled':False,'lean_checked':False,
      'scope':list(CASES),'sources':[],'unconverted_contracts':[],
      'limits':{'rss_mib':256,'seconds':120,'scratch_mib':192,'retained_mib':64},
      'replaces_initial_forests':False}

    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform!='darwin':rss*=1024
        if time.monotonic()-started>115:raise TimeoutError('115-second working deadline')
        if rss>256*1024**2:raise MemoryError('256MiB self RSS limit')

    def terminate(*_):raise TimeoutError('termination requested')
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,terminate);signal.signal(signal.SIGINT,terminate)

    def write(path,chunks):
        nonlocal written
        path=stage/path;path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('wb') as f:
            for chunk in chunks:
                guard();b=chunk.encode() if isinstance(chunk,str) else chunk
                written+=len(b)
                if written>64*1024**2:raise MemoryError('64MiB retained output limit')
                f.write(b)
        return {'path':str(path.relative_to(stage)),'bytes':path.stat().st_size,
                'lines':sum(1 for _ in path.open('rb')),
                'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

    try:
        expected={}
        for case in CASES:
            receipt=json.loads((ROOT/f'evidence/inherited/evidence/C{case}/case-replay.json').read_text())
            for module,sha in receipt['local_source_sha256'].items():
                if module.startswith('S12.'):
                    need(expected.setdefault(module,sha)==sha,f'inconsistent hash {module}')
        db=sqlite3.connect(stage/'scratch.sqlite')
        db.executescript('''PRAGMA page_size=4096; PRAGMA max_page_count=49152;
PRAGMA journal_mode=OFF; PRAGMA cache_size=-8192; PRAGMA temp_store=FILE;
CREATE TABLE objects(kind TEXT,value TEXT,id INTEGER,PRIMARY KEY(kind,value)) WITHOUT ROWID;
CREATE UNIQUE INDEX object_ids ON objects(kind,id);
CREATE TABLE named(name TEXT PRIMARY KEY,kind TEXT,value TEXT) WITHOUT ROWID;
CREATE TABLE symbols(id INTEGER PRIMARY KEY,name TEXT UNIQUE);
CREATE TABLE pairs(plan INTEGER,number INTEGER,source INTEGER,neighbor INTEGER,block INTEGER,
 refa INTEGER,refb INTEGER,PRIMARY KEY(plan,number)) WITHOUT ROWID;
CREATE TABLE auxiliary(name TEXT PRIMARY KEY,kind TEXT,value TEXT) WITHOUT ROWID;
''')
        seq=Counter();counts=Counter();unknown=Counter();angle_data={}
        pair_modules=defaultdict(set)

        @lru_cache(maxsize=8192)
        def symbol(name):
            db.execute('INSERT OR IGNORE INTO symbols(name) VALUES (?)',(name,))
            return db.execute('SELECT id FROM symbols WHERE name=?',(name,)).fetchone()[0]

        @lru_cache(maxsize=8192)
        def unsymbol(ident):return db.execute('SELECT name FROM symbols WHERE id=?',(ident,)).fetchone()[0]

        def intern(kind,value):
            value=compact(value)
            old=db.execute('SELECT id FROM objects WHERE kind=? AND value=?',(kind,value)).fetchone()
            if old:return old[0]
            ident=seq[kind];seq[kind]+=1
            db.execute('INSERT INTO objects VALUES (?,?,?)',(kind,value,ident))
            return ident

        def save(name,kind,value,table='named'):
            value=compact(value)
            old=db.execute(f'SELECT kind,value FROM {table} WHERE name=?',(name,)).fetchone()
            need(old is None or old==(kind,value),f'duplicate inconsistent {name}')
            db.execute(f'INSERT OR IGNORE INTO {table} VALUES (?,?,?)',(name,kind,value))

        def row(fields):
            need(len(fields)==4,'bad row arity')
            q=[Q(x.replace('(','').replace(')','').strip()) for x in fields[:3]]
            need(fields[3] in ('1','0','true','false'),'bad strict bit')
            den=math.lcm(*(x.denominator for x in q))
            return intern('row',{'integers':[int(x*den) for x in q],
                'strict':fields[3] in ('1','true'),'denominator':den})

        def pose(name):
            found=db.execute('SELECT kind,value FROM named WHERE name=?',(name,)).fetchone()
            need(found is not None,f'missing pose {name}')
            kind,value=found;value=json.loads(value)
            if kind=='pose':return value
            need(kind=='rawpose',f'not a pose {name}: {kind}')
            grid,angle,raw=value
            ids=[row(x.split(',')) for x in raw.split(';')] if raw else []
            index=intern('pose',{'angle':angle+(64 if grid==128 else 0),'rows':ids})
            db.execute('UPDATE named SET kind=?,value=? WHERE name=?',('pose',str(index),name))
            counts['materialized_pose_names']+=1
            return index

        def value(kind,index):
            result=db.execute('SELECT value FROM objects WHERE kind=? AND id=?',(kind,index)).fetchone()
            need(result is not None,f'missing object {kind}/{index}')
            return json.loads(result[0])

        def unsupported(module,name,kind,text):
            unknown[kind]+=1
            # These contracts point to immutable source, rather than duplicating
            # huge old certificate weights or pretending the obligation vanished.
            save(name,kind,{'module':module,'declaration_sha256':hashlib.sha256(text.encode()).hexdigest(),
                 'statement':text.split(':=',1)[0].strip()},'auxiliary')

        for module in sorted(expected):
            for name,text in declarations(module,expected,report['sources'],guard,lambda _:True):
                guard();first=text.splitlines()[0];local=LOCAL.match(name)
                if name.startswith('continuous') and ': PoseLeaf :=' in first:
                    m=POSE.search(text)
                    need(m is not None,f'unsupported required pose syntax {name}')
                    save(name,'rawpose',[int(m[1]),int(m[2]),m[3]])
                    continue
                angle=re.fullmatch(r'angle(64|128)_(\d+)',name)
                if angle and ': AngleEnclosure :=' in first:
                    expr=body_of(text);need(expr.startswith('⟨') and expr.endswith('⟩'),'angle constructor')
                    fields=split_top(expr[1:-1]);need(len(fields)>=7,'short angle constructor')
                    qs=[Q(x.replace('(','').replace(')','').strip()) for x in fields]
                    angle_data[name]=qs
                    continue
                continuous=name.startswith('continuous')
                if not continuous and not re.fullmatch(r'mixedGeometryScout(?:701|713|717|973|978|979)_impossible',name):continue
                if ': List PoseLeaf :=' in first:
                    expr=body_of(text)
                    if expr.startswith('['):save(name,'domain_names',list_names(expr))
                    elif re.fullmatch(r'\w+',expr):save(name,'domain_alias',expr)
                    else:unsupported(module,name,'nonliteral domain',text)
                elif re.fullmatch(r'continuous.*Step\d+Plans',name):
                    expr=body_of(text)
                    if expr.startswith('['):save(name,'plan_list_names',list_names(expr))
                    elif re.fullmatch(r'\w+',expr):save(name,'plan_list_alias',expr)
                    else:unsupported(module,name,'nonliteral plan list',text)
                elif name.endswith('BlockRows'):
                    expr=body_of(text);fields=EXPLICIT.findall(expr)
                    if expr=='[]' or expr.startswith('[') and fields and len(fields)==expr.count('⟨⟨!['):
                        save(name,'rawblock',[list(f) for f in fields])
                    else:unsupported(module,name,'chord region alias',text)
                elif 'axisOverlapForms a.val b.val' in text or ': EncodedAxisCertificate :=' in first:
                    count=re.fullmatch(r'(.*)Overlap(\d+)(?:Encoded)?',name)
                    need(count is not None,f'unsupported pair name {name}')
                    pair_modules[count[1]].add(module)
                    counts['imported_pair_declarations']+=1
                elif ': RelaxationLink :=' in first:
                    m=re.search(r':=\s*⟨(\w+),(\w+),',text)
                    need(m is not None,f'unsupported relaxation {name}')
                    save(name,'link_names',[m[1],m[2]])
                elif ': CertifiedPosePruning :=' in first:
                    expr=body_of(text);need(expr.startswith('⟨') and expr.endswith('⟩'),f'bad plan {name}')
                    fields=split_top(expr[1:-1]);need(len(fields)==6,f'plan field count {name}')
                    links=re.findall(r'⟨(\w+),\w+⟩',fields[4])
                    save(name,'pair_plan_names',{'source':fields[0],'neighbors_name':fields[1],
                        'pruning':fields[2],'targets':list_names(fields[3]),'links':links})
                elif local and re.search(r': (?:WindowChordPruningCoverCheck|VerticalChordPruningCoverCheck|PruningCoverCheck) ',first):
                    head=text.split(':=',1)[0]
                    save(name,'transition',{'case':int(re.search(r'Scout(\d+)',name)[1]),
                        'step':int(re.search(r'Step(\d+)',name)[1]),'kind':re.search(r': (\w+)',head)[1],
                        'statement':head.strip(),
                        'names':re.findall(r'continuous\w+',head)[1:]})
                elif ': PruneBlock :=' in first:
                    m=re.search(r':=\s*⟨(\w+),',text)
                    need(m is not None,f'unsupported PruneBlock {name}')
                    save(name,'prune_block',m[1])
                elif ': PosePruning ' in first:
                    m=re.search(r': PosePruning (\w+) (\w+) :=\s*⟨(\[.*?\]),',text,re.S)
                    need(m is not None,f'unsupported PosePruning {name}')
                    blocks=re.findall(r'⟨(\w+),\w+⟩',m[3])
                    need(len(blocks)==m[3].count('⟨'),f'nonliteral pruning blocks {name}')
                    save(name,'pruning_shape',{'source':m[1],'neighbors':m[2],'blocks':blocks})
                    unsupported(module,name,'pruning tree contract',text)
                elif ': RegionTree :=' in first:
                    unsupported(module,name,'pruning tree contract',text)
                elif any(x in first for x in (': FourChord',': CertifiedWindow',': CertifiedVertical',': WindowChord',': VerticalChord')):
                    unsupported(module,name,'chord contract',text)
                elif 'mixedGeometryScout' in name and name.endswith('_impossible'):
                    save(name,'whole_chain',{'statement':text.split(':=',1)[0].strip(),
                        'proof_calls':re.findall(r'\bcontinuous\w+|\b\w*Chord\w+',body_of(text)),
                        'source':module,'sha256':hashlib.sha256(text.encode()).hexdigest()})
            db.commit()

        @lru_cache(maxsize=1024)
        def domain(name,seen=()):
            need(name not in seen,f'cyclic domain {name}')
            found=db.execute('SELECT kind,value FROM named WHERE name=?',(name,)).fetchone()
            need(found is not None,f'missing domain {name}')
            kind,data=found;data=json.loads(data)
            if kind=='domain_alias':return domain(data,seen+(name,))
            need(kind=='domain_names',f'not a domain {name}: {kind}')
            return tuple(pose(n) for n in data)

        # All current-domain names preserve order, multiplicity and predecessor aliases.
        domain_names=[r[0] for r in db.execute("SELECT name FROM named WHERE kind IN ('domain_names','domain_alias') ORDER BY name") if LOCAL.match(r[0])]
        for name in domain_names:domain(name)
        def link(name):
            old=db.execute("SELECT value FROM auxiliary WHERE name=? AND kind='link'",(name,)).fetchone()
            if old:return json.loads(old[0])
            found=db.execute("SELECT value FROM named WHERE name=? AND kind='link_names'",(name,)).fetchone()
            need(found is not None,f'missing link {name}')
            source,target=json.loads(found[0])
            index=intern('link',{'source':pose(source),'target':pose(target)})
            save(name,'link',index,'auxiliary')
            return index

        @lru_cache(maxsize=1024)
        def plan_list(name,seen=()):
            need(name not in seen,f'cyclic plan list {name}')
            found=db.execute('SELECT kind,value FROM named WHERE name=?',(name,)).fetchone()
            need(found is not None,f'missing plan list {name}')
            kind,data=found;data=json.loads(data)
            if kind=='plan_list_alias':return plan_list(data,seen+(name,))
            need(kind=='plan_list_names',f'not a plan list {name}: {kind}')
            return tuple(data)

        # Resolve complete current transition aliases, including reused predecessor
        # pruning stages. A direct initial cover removes forests, not these steps.
        uses=[];plan_names=set()
        for name,payload in db.execute("SELECT name,value FROM named WHERE kind='transition' ORDER BY name"):
            transition=json.loads(payload)
            if transition['kind']!='PruningCoverCheck':continue
            need(len(transition['names'])==4,f'pair transition arity {name}')
            source,neighbors,target,plans=transition['names']
            members=plan_list(plans)
            uses.append({'case':transition['case'],'step':transition['step'],
                         'source':source,'neighbors':neighbors,'target':target,
                         'plans_name':plans,'plans':members})
            plan_names.update(members)
        # Chord links remain materialized with their exact endpoints.
        for name, in db.execute("SELECT name FROM named WHERE kind='link_names' ORDER BY name"):
            if LOCAL.match(name):link(name)
        resolve_link=link
        # Second authenticated stream reads only pair definitions for live plans.
        # No table of unused predecessor pair witnesses is ever materialized.
        live_prefixes={name.removesuffix('Plan') for name in plan_names}
        selected_modules=set().union(*(pair_modules[p] for p in live_prefixes))
        pair_provenance=[]
        def wanted_pair(name):
            match=re.fullmatch(r'(.*)Overlap(\d+)(?:Encoded)?',name)
            return match is not None and match[1] in live_prefixes
        for module in sorted(selected_modules):
            for name,text in declarations(module,expected,pair_provenance,guard,wanted_pair):
                if 'axisOverlapForms a.val b.val' not in text and ': EncodedAxisCertificate :=' not in text.splitlines()[0]:continue
                count=re.fullmatch(r'(.*)Overlap(\d+)(?:Encoded)?',name)
                bound=re.findall(r'let [ab] : .*?angle(64|128)_(\d+)\.(?:reference|unitReference)',text)
                a=re.search(r'let ia := (\w+BlockRows)\s*\+\+\s*(\w+)\.inputs',text)
                b=re.search(r'let ib := (\w+)\.inputs',text)
                need(count and len(bound)==2 and a and b,f'unsupported selected pair {name}')
                refs=[int(i)+(64 if int(g)==128 else 0) for g,i in bound]
                db.execute('INSERT INTO pairs VALUES (?,?,?,?,?,?,?)',
                    (symbol(count[1]),int(count[2]),symbol(a[2]),symbol(b[1]),symbol(a[1]),*refs))
                counts['pair_declarations']+=1
            db.commit()
        report['selected_pair_source_pass']=pair_provenance
        # Check original witness coverage exactly, then discard per-pair duplication.
        plan_names=sorted(plan_names)
        for name in plan_names:
            data=json.loads(db.execute('SELECT value FROM named WHERE name=?',(name,)).fetchone()[0])
            prefix=name.removesuffix('Plan');neighbors=list(domain(data['neighbors_name']))
            source=pose(data['source']);ps=value('pose',source);records=[]
            for number,a,b,block,ra,rb in db.execute('SELECT number,source,neighbor,block,refa,refb FROM pairs WHERE plan=? ORDER BY number',(symbol(prefix),)):
                a,b,block=unsymbol(a),unsymbol(b),unsymbol(block)
                need(pose(a)==source and ra==ps['angle'],f'wrong source/reference {name}')
                neighbor=pose(b);need(value('pose',neighbor)['angle']==rb,f'wrong neighbor angle {name}')
                found=db.execute('SELECT kind,value FROM named WHERE name=?',(block,)).fetchone()
                need(found and found[0] in ('block','rawblock'),f'pair block unresolved {name}/{block}')
                if found[0]=='rawblock':
                    bid=intern('block',[row(f) for f in json.loads(found[1])])
                    db.execute('UPDATE named SET kind=?,value=? WHERE name=?',('block',str(bid),block))
                else:bid=json.loads(found[1])
                records.append((number,neighbor,bid))
            shape=db.execute("SELECT value FROM named WHERE name=? AND kind='pruning_shape'",(data['pruning'],)).fetchone()
            need(shape is not None,f'missing pruning shape {name}')
            shape=json.loads(shape[0])
            need(pose(shape['source'])==source and domain(shape['neighbors'])==tuple(neighbors),f'pruning premise mismatch {name}')
            need(len(shape['blocks'])<=1,f'multiple prune blocks need explicit representation {name}')
            if not shape['blocks']:
                need(not records,f'witnesses without block {name}')
                block=None
            else:
                declared=db.execute("SELECT value FROM named WHERE name=? AND kind='prune_block'",(shape['blocks'][0],)).fetchone()
                need(declared is not None,f'missing prune block {name}')
                block_name=json.loads(declared[0])
                found=db.execute('SELECT kind,value FROM named WHERE name=?',(block_name,)).fetchone()
                need(found and found[0] in ('block','rawblock'),f'unresolved actual block {block_name}')
                if found[0]=='rawblock':
                    block=intern('block',[row(f) for f in json.loads(found[1])])
                    db.execute('UPDATE named SET kind=?,value=? WHERE name=?',('block',str(block),block_name))
                else:block=json.loads(found[1])
                need([r[0] for r in records]==list(range(len(records))),f'noncontiguous witnesses {name}')
                need([r[1] for r in records]==neighbors,f'incomplete neighbor coverage {name}')
                need(all(r[2]==block for r in records),f'mismatched actual block {name}')
            links=[];pieces=[]
            for link in data['links']:
                index=resolve_link(link);links.append(index);pieces.append(value('link',index)['source'])
            targets=[pose(n) for n in data['targets']]
            need(all(value('link',i)['target'] in targets for i in links),f'wrong target link {name}')
            route={'origin':name,'source':source,'block':block,'pieces':pieces,'neighbors_name':data['neighbors_name'],
                'targets':targets,'links':links,'historical_pair_count':len(records),'pruning_contract':data['pruning']}
            save(name,'pair_plan',route,'auxiliary')
            counts['covered_pair_declarations']+=len(records)
        need(counts['pair_declarations']==counts['covered_pair_declarations'],'uncovered selected pair records')
        counts['unused_imported_pair_declarations']=counts['imported_pair_declarations']-counts['covered_pair_declarations']
        # Verify every selected source and outgoing target across each alias boundary.
        for use in uses:
            selected=[json.loads(db.execute("SELECT value FROM auxiliary WHERE name=? AND kind='pair_plan'",(n,)).fetchone()[0]) for n in use['plans']]
            need([p['source'] for p in selected]==list(domain(use['source'])),f'incomplete source coverage {use}')
            for p in selected:
                need(domain(p['neighbors_name'])==domain(use['neighbors']),f'neighbor alias mismatch {use}')
                need(all(t in domain(use['target']) for t in p['targets']),f'target coverage mismatch {use}')

        # Materialized exact contexts are reusable by arbitrary-grid CachedSupportFan.
        for _,payload in db.execute("SELECT name,value FROM auxiliary WHERE kind='pair_plan' ORDER BY name"):
            p=json.loads(payload)
            if p['block'] is None:continue
            a=value('pose',p['source']);inputs=value('block',p['block'])+a['rows']
            intern('context',{'angle':a['angle'],'inputs':inputs})
            for b in domain(p['neighbors_name']):
                q=value('pose',b);intern('context',{'angle':q['angle'],'inputs':q['rows']})
        db.commit()

        # Data interchange is streamed; row/pose identifiers are stable and global.
        files=[]
        for kind in ('row','pose','block','link','context'):
            def objects(kind=kind):
                yield '[\n'
                for index,payload in db.execute('SELECT id,value FROM objects WHERE kind=? ORDER BY id',(kind,)):
                    if index:yield ',\n'
                    data=json.loads(payload)
                    if kind=='row':data={'index':index,**data}
                    elif kind=='block':data={'index':index,'rows':data}
                    else:data={'index':index,**data}
                    yield compact(data)
                yield '\n]\n'
            files.append(write(Path(kind+'s.json'),objects()))
        def named_records():
            for name,kind,payload in db.execute("SELECT name,kind,value FROM named WHERE kind IN ('pose','block') ORDER BY name"):
                yield compact({'name':name,'kind':kind,'index':json.loads(payload)})+'\n'
            for name,payload in db.execute("SELECT name,value FROM auxiliary WHERE kind='link' ORDER BY name"):
                yield compact({'name':name,'kind':'link','index':json.loads(payload)})+'\n'
        files.append(write(Path('names.jsonl'),named_records()))
        for case in CASES:
            def case_data(case=case):
                yield '{"case":'+str(case)+',"domains":{'
                first=True
                needed_domains={name for name in domain_names if name.startswith(f'continuousScout{case}')}
                for use in uses:
                    if use['case']!=case:continue
                    for plan in use['plans']:
                        data=json.loads(db.execute("SELECT value FROM auxiliary WHERE name=? AND kind='pair_plan'",(plan,)).fetchone()[0])
                        needed_domains.add(data['neighbors_name'])
                for name in sorted(needed_domains):
                    if not first:yield ','
                    first=False;yield compact(name)+':'+compact(list(domain(name)))
                yield '},"plans":[';first=True
                for use in uses:
                    if use['case']!=case:continue
                    for name in use['plans']:
                        payload=db.execute("SELECT value FROM auxiliary WHERE name=? AND kind='pair_plan'",(name,)).fetchone()[0]
                        p=json.loads(payload)
                        if not first:yield ','
                        first=False;yield compact({'name':name,'case':case,'step':use['step'],**p})
                yield '],"transitions":[';first=True
                for name,payload in db.execute("SELECT name,value FROM named WHERE kind='transition' ORDER BY name"):
                    p=json.loads(payload)
                    if p['case']!=case:continue
                    if not first:yield ','
                    first=False;yield compact({'name':name,**p})
                yield '],\"pair_steps\":'+compact({u['step']:[u['source'],u['neighbors'],u['target']] for u in uses if u['case']==case})+'}\n'
            files.append(write(Path(f'C{case}.json'),case_data()))
        def obligations():
            for name,kind,payload in db.execute("SELECT name,kind,value FROM auxiliary WHERE kind NOT IN ('link','pair_plan') ORDER BY name"):
                yield compact({'name':name,'kind':kind,**json.loads(payload)})+'\n'
            for name,payload in db.execute("SELECT name,value FROM named WHERE kind='whole_chain' ORDER BY name"):
                yield compact({'name':name,'kind':'whole-chain',**json.loads(payload)})+'\n'
        files.append(write(Path('remaining-contracts.jsonl'),obligations()))

        # Literal Lean data is portable: copy lean/Compact into the chosen overlay
        # only after review. No proof import is changed by this prepared emitter.
        lean=Path('lean/Compact/HistoricalData')
        chunk_size=4096;row_modules=[]
        for chunk in range((seq['row']+chunk_size-1)//chunk_size):
            module=f'Compact.HistoricalData.Rows{chunk:03}';row_modules.append(module)
            def row_lines(chunk=chunk):
                yield 'import Compact.Core.RowSyntax\n\nnamespace N12Compact.HistoricalData\nopen IntegerSupport\nset_option Elab.async false\n'
                yield f'noncomputable def rows{chunk:03} : Array (Array (Row × Nat)) := row_text% "\n'
                for payload, in db.execute("SELECT value FROM objects WHERE kind='row' AND id>=? AND id<? ORDER BY id",(chunk*chunk_size,(chunk+1)*chunk_size)):
                    r=json.loads(payload);x,y,c=r['integers']
                    yield f'{x},{y},{c},{str(r["strict"]).lower()},{r["denominator"]-1}\n'
                yield '"\nend N12Compact.HistoricalData\n'
            files.append(write(lean/f'Rows{chunk:03}.lean',row_lines()))
        def shared_rows():
            for module in row_modules:yield f'import {module}\n'
            yield '\nnamespace N12Compact.HistoricalData\nopen IntegerSupport\nset_option Elab.async false\n'
            yield f'abbrev rowCount : Nat := {seq["row"]}\n'
            yield 'noncomputable def rowPair (index : Nat) : Row × Nat :=\n'
            for chunk in range(len(row_modules)):
                yield f'  if index < {(chunk+1)*chunk_size} then RowSyntax.lookup rows{chunk:03} (index - {chunk*chunk_size}) else\n'
            yield '  (⟨0, 0, 0, false⟩, 0)\n'
            yield 'noncomputable def rows (i : Fin rowCount) : Row := (rowPair i.val).1\n'
            yield 'noncomputable def denominators (i : Fin rowCount) : Nat := (rowPair i.val).2 + 1\n'
            yield 'theorem positive_denominators (i : Fin rowCount) : 0 < denominators i := Nat.zero_lt_succ _\n'
            yield 'end N12Compact.HistoricalData\n'
        files.append(write(lean/'SharedRows.lean',shared_rows()))
        pose_modules=[]
        for chunk in range((seq['pose']+2047)//2048):
            module=f'Compact.HistoricalData.Poses{chunk:03}';pose_modules.append(module)
            def pose_lines(chunk=chunk):
                yield 'import Compact.Core.PoseSyntax\nimport Compact.HistoricalData.SharedRows\n\nnamespace N12Compact.HistoricalData\nset_option Elab.async false\n'
                yield f'noncomputable def poses{chunk:03} : Array (Array (Fin 192 × List (Fin rowCount))) := pose_text% 192 {seq["row"]} "\n'
                for payload, in db.execute("SELECT value FROM objects WHERE kind='pose' AND id>=? AND id<? ORDER BY id",(chunk*2048,(chunk+1)*2048)):
                    p=json.loads(payload);yield str(p['angle'])+';'+','.join(map(str,p['rows']))+'\n'
                yield '"\nend N12Compact.HistoricalData\n'
            files.append(write(lean/f'Poses{chunk:03}.lean',pose_lines()))
        def shared_poses():
            for module in pose_modules:yield f'import {module}\n'
            yield 'import S12.OwnerEnclosure\n\nnamespace N12Compact.HistoricalData\nopen S12 IntegerSupport\nset_option Elab.async false\n'
            yield f'abbrev poseCount : Nat := {seq["pose"]}\n'
            yield 'noncomputable def poseRecord (index : Nat) : Fin 192 × List (Fin rowCount) :=\n'
            for chunk in range(len(pose_modules)):
                yield f'  if index < {(chunk+1)*2048} then PoseSyntax.lookup poses{chunk:03} (0, []) (index - {chunk*2048}) else\n'
            yield '  (0, [])\n'
            yield 'noncomputable def poseAngle (i : Fin poseCount) : Fin 192 := (poseRecord i.val).1\n'
            yield 'noncomputable def poseRows (i : Fin poseCount) : List (Fin rowCount) := (poseRecord i.val).2\n'
            yield '/-- The adapter must supply the authenticated 64-then-128 original angle grid. -/\n'
            yield 'noncomputable def poses (angles : Fin 192 → { w : AngleEnclosure // w.Check }) (i : Fin poseCount) : PoseLeaf :=\n'
            yield '  ⟨angles (poseAngle i), (poseRows i).map (fun r => (rows r).normalized (denominators r))⟩\n'
            yield 'end N12Compact.HistoricalData\n'
        files.append(write(lean/'SharedPoses.lean',shared_poses()))
        # No implicit angle normalization: exact original values and rational side.
        refs=[]
        for grid in (64,128):
            for angle in range(grid):
                name=f'angle{grid}_{angle}';need(name in angle_data,f'missing reference {name}')
                q=angle_data[name]
                # AngleEnclosure fields are lower,upper,c,s,outer,inner,... .
                c,s,side=q[2],q[3],q[5];den=math.lcm(c.denominator,s.denominator)
                refs.append({'name':name,'c':int(c*den),'s':int(s*den),'denominator':den,
                    'sideNumerator':side.numerator,'sideDenominator':side.denominator})
        files.append(write(Path('references.json'),[compact(refs)+'\n']))
        report.update(status='data assembled; semantic and numerical obligations pending',
            counts=dict(counts),unique_objects=dict(seq),unsupported_contract_counts=dict(unknown),
            output_files=files,elapsed_seconds=time.monotonic()-started,
            lean_lines=sum(f['lines'] for f in files if f['path'].endswith('.lean')),
            lean_modules=sum(f['path'].endswith('.lean') for f in files),
            scratch_bytes=(stage/'scratch.sqlite').stat().st_size,
            deferred=['cached fan certificates and all eight original axis checks',
                      'pruning-tree/piece coverage and every chord/window contraction',
                      'relaxation implication checks for retained source/target link pairs',
                      'all six direct initial original-model entrances and complete chain adapters'])
        db.close();db=None;(stage/'scratch.sqlite').unlink()
        write(Path('manifest.json'),[json.dumps(report,indent=2)+'\n'])
        stage.rename(out)
        print(compact({'status':report['status'],'output':str(out),'rows':seq['row'],
                      'poses':seq['pose'],'lean_lines':report['lean_lines'],'lean_modules':report['lean_modules']}))
    except BaseException as error:
        if db is not None:db.close()
        shutil.rmtree(stage)
        print(compact({'status':'stopped; new staging output cleaned','error':str(error)}),file=sys.stderr)
        raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
