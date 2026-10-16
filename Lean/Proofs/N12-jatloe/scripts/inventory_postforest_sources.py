#!/usr/bin/env python3
"""Prepared bounded schema count after the seven direct initial covers.

No generation, compilation, numerical search or recovered-code execution.
Reconciles every old regionTreeFromText root; inventories exact remaining
case-local poses/blocks and pair-context references without assuming their
checks pass. Explicit --run and an external bounded.py slot are required.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import argparse
import hashlib
import json
import math
import re
import resource
import signal
import sqlite3
import sys
import time
from audit_historical_direct_cover import ROOT, declarations, Unsupported, need

CASES = (701, 713, 717, 898, 973, 978, 979)
EXPLICIT = re.compile(r'⟨⟨!\[([^,\]]+),([^\]]+)\],([^⟩]+)⟩,(true|false)⟩')


class Stop(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', action='store_true')
    ap.add_argument('--output',default='evidence/postforest-source-inventory.json')
    args = ap.parse_args()
    if not args.run:
        ap.error('Prepared only; explicit --run requires the parent compute slot.')
    started = time.monotonic()
    out = ROOT/args.output
    need(out.resolve().is_relative_to((ROOT/'evidence').resolve()), 'output must stay under evidence')
    scratch = out.with_suffix('.sqlite.tmp')
    need(not scratch.exists(), 'scratch path already exists')
    report = {'status':'incomplete','sources':[],'unsupported':[],
              'scope':'All seven historical source closures; exact post-forest structural counts only.',
              'limits':{'rss_mib':256,'seconds':120,'scratch_bytes':64*1024**2,'output_bytes':8*1024**2},
              'whole_proof_bound_established':False,'lean_generation_or_check':False}
    expected = {}
    for case in CASES:
        receipt = json.loads((ROOT/f'evidence/inherited/evidence/C{case}/case-replay.json').read_text())
        for module,sha in receipt['local_source_sha256'].items():
            if module.startswith('S12.'):
                need(expected.setdefault(module,sha) == sha, f'inconsistent shared hash {module}')
    direct = json.loads((ROOT/'evidence/historical-direct-cover-audit.json').read_text())
    need(direct.get('all_selected_initial_covers_pass'), 'six-case direct audit not complete')
    c898 = json.loads((ROOT/'evidence/c898-direct-cover-all.json').read_text())
    need(not c898['failures'] and c898['counts']['owner_angles'] == 704, 'C898 direct audit incomplete')
    direct_roots = {r['historical_root'] for case in direct['cases'] for r in case['roots']}
    direct_roots.update(f'region898Root{r["owner"]}_{r["angle"]}' for r in c898['cases'])
    report['direct_cover_roots'] = len(direct_roots)
    report['absent_target_angles'] = sum(r['target_pose'] is None for case in direct['cases'] for r in case['roots']) + c898['counts']['absent_pose_angles']
    report['direct_audit_sha256'] = {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (ROOT/'evidence/historical-direct-cover-audit.json',ROOT/'evidence/c898-direct-cover-all.json')}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':rss *= 1024
        if time.monotonic()-started > 115 or rss > 256*1024**2:
            raise Stop('internal time/RSS limit')

    def terminate(*_):raise Stop('termination requested')
    signal.signal(signal.SIGALRM,guard)
    signal.signal(signal.SIGTERM,terminate)
    signal.signal(signal.SIGINT,terminate)
    signal.setitimer(signal.ITIMER_REAL,.2,.2)
    db=sqlite3.connect(scratch)
    db.executescript('''PRAGMA page_size=4096; PRAGMA max_page_count=16384;
PRAGMA journal_mode=OFF; PRAGMA cache_size=-8192; PRAGMA temp_store=FILE;
CREATE TABLE object(kind TEXT,value TEXT,id INTEGER,PRIMARY KEY(kind,value)) WITHOUT ROWID;
CREATE TABLE named(name TEXT PRIMARY KEY,kind TEXT,value TEXT) WITHOUT ROWID;
CREATE TABLE symbol(id INTEGER PRIMARY KEY,name TEXT UNIQUE);
CREATE TABLE pair_binding(source INTEGER,neighbor INTEGER,block INTEGER,PRIMARY KEY(source,neighbor,block)) WITHOUT ROWID;
CREATE TABLE context(value TEXT PRIMARY KEY) WITHOUT ROWID;
''')
    sequence=Counter(); counts=Counter(); families=defaultdict(Counter); schemas=Counter()
    supported_pair_cases=Counter(); unknown_count=Counter(); direct_seen=set()
    transitions=[]; examples=[]

    def intern(kind,value):
        text=json.dumps(value,separators=(',',':'))
        old=db.execute('SELECT id FROM object WHERE kind=? AND value=?',(kind,text)).fetchone()
        if old:return old[0]
        ident=sequence[kind];sequence[kind]+=1
        db.execute('INSERT INTO object VALUES (?,?,?)',(kind,text,ident))
        return ident

    def row(fields):
        need(len(fields)==4,'unsupported row arity')
        q=[Q(x.replace('(','').replace(')','').strip()) for x in fields[:3]]
        need(fields[3] in ('0','1','false','true'),'unsupported strictness')
        den=math.lcm(*(x.denominator for x in q))
        nums=[int(x*den) for x in q]
        gcd=math.gcd(*nums)
        primitive=[x//gcd for x in nums] if gcd else [0,0,0]
        exact=intern('row',list(map(str,q))+[fields[3] in ('1','true')])
        intern('primitive_row',primitive+[fields[3] in ('1','true')])
        return exact

    def save(name,kind,value):
        text=json.dumps(value,separators=(',',':'))
        old=db.execute('SELECT kind,value FROM named WHERE name=?',(name,)).fetchone()
        need(old is None or old==(kind,text),f'duplicate definition {name}')
        db.execute('INSERT OR IGNORE INTO named VALUES (?,?,?)',(name,kind,text))

    @lru_cache(maxsize=8192)
    def symbol(name):
        db.execute('INSERT OR IGNORE INTO symbol(name) VALUES (?)',(name,))
        return db.execute('SELECT id FROM symbol WHERE name=?',(name,)).fetchone()[0]

    @lru_cache(maxsize=8192)
    def symbol_name(ident):
        return db.execute('SELECT name FROM symbol WHERE id=?',(ident,)).fetchone()[0]

    def unsupported(module,name,reason):
        unknown_count[reason]+=1
        if len(report['unsupported'])<80:report['unsupported'].append([module,name,reason])

    try:
        for module in sorted(expected):
            for name,text in declarations(module,expected,report['sources'],guard,lambda _:True):
                guard();head=text.split(':=',1)[0];first=text.splitlines()[0]
                trees=re.findall(r'regionTreeFromText "([^"\n]*)"',text)
                if trees:
                    root=re.fullmatch(r'region(.+)Root(\d+)_(\d+)',name)
                    family=root[1] if root else 'non-PoseRoot/'+head[:100]
                    is_direct=name in direct_roots
                    counts['all_regionTreeFromText_occurrences']+=len(trees)
                    families[family]['tree_occurrences']+=len(trees)
                    families[family]['direct_cover_occurrences']+=len(trees) if is_direct else 0
                    if is_direct:direct_seen.add(name)
                    for tree in trees:
                        for node in tree.split('\\n'):
                            families[family]['node_'+node.split('|',1)[0]]+=1
                    if not root and len(examples)<20:examples.append([module,name,head[:180]])
                local=re.match(r'continuousScout(701|713|717|898|973|978|979)(Initial|Step)',name)
                if name.startswith('continuous') and ': PoseLeaf :=' in first:
                    m=re.search(r'⟨⟨(angle\d+_\d+),\w+⟩,regionConstraintsFromText "([^"\n]*)"',text)
                    if not m:unsupported(module,name,'nonliteral remaining PoseLeaf');continue
                    if not local:
                        save(name,'rawpose',[m[1],m[2]])
                        continue
                    ids=[row(t.split(',')) for t in m[2].split(';')] if m[2] else []
                    value=[m[1],ids]
                    intern('pose',value);save(name,'pose',value)
                    counts['remaining_pose_declarations']+=1
                    counts['remaining_pose_row_occurrences']+=len(ids)
                    schemas[f'{local[1]}/pose/{local[2]}']+=1
                if local and name.endswith('BlockRows'):
                    expr=first.split(':=',1)[1].strip();fields=EXPLICIT.findall(expr)
                    if not (expr=='[]' or fields and len(fields)==expr.count('⟨⟨![')):
                        unsupported(module,name,'nonliteral block rows');continue
                    ids=[row(list(f)) for f in fields]
                    intern('block',ids);save(name,'block',ids)
                    counts['remaining_block_declarations']+=1
                encoded_axis = local and ': EncodedAxisCertificate :=' in first
                if local and ('axisOverlapForms a.val b.val' in text or encoded_axis):
                    counts['remaining_pair_declarations']+=1
                    if encoded_axis:counts['encoded_pair_declarations']+=1
                    bound=re.findall(r'let [ab] : .*?(angle\d+_\d+)\.(?:reference|unitReference)',text)
                    source=re.search(r'let ia := (\w+BlockRows)\s*\+\+\s*(\w+)\.inputs',text)
                    neighbor=re.search(r'let ib := (\w+)\.inputs',text)
                    if len(bound)!=2 or not source or not neighbor:
                        unsupported(module,name,'unsupported pair source/neighbor binding');continue
                    db.execute('INSERT OR IGNORE INTO pair_binding VALUES (?,?,?)',
                               tuple(symbol(n) for n in (source[2],neighbor[1],source[1])))
                    supported_pair_cases[local[1]]+=1
                if local and ': RelaxationLink :=' in first:
                    schemas[f'{local[1]}/relaxation_links']+=1
                step=re.fullmatch(r'continuousScout(701|713|717|898|973|978|979)Step(\d+)_checked',name)
                if step:
                    schemas[f'{step[1]}/step_check_declarations']+=1
                    transitions.append({'case':int(step[1]),'step':int(step[2]),'statement':head.strip()})
                if re.fullmatch(r'mixedGeometryScout(?:701|713|717|898|973|978|979)_impossible',name):
                    case=re.search(r'\d+',name)[0]
                    for token in re.findall(r'\b(?:continuousScout\w+|\w*Chord\w*|\w*Vertical\w*|\w*Window\w*)',text):
                        if len(token)<150:schemas[f'{case}/mixed_call/'+token]+=1
            db.commit()
        report['source_scope_complete']=len(report['sources'])==len(expected)
        report['all_direct_roots_found']=direct_seen==direct_roots
        report['direct_roots_missing']=sorted(direct_roots-direct_seen)
        report['extra_tree_occurrences']=counts['all_regionTreeFromText_occurrences']-len(direct_seen)
        # Resolve contexts only after all definitions, retaining exact row membership.
        unresolved=0
        unresolved_kinds=Counter()
        unresolved_examples=[]
        for source,neighbor,block in db.execute('SELECT source,neighbor,block FROM pair_binding'):
            guard()
            source,neighbor,block=map(symbol_name,(source,neighbor,block))
            values=[]
            for name,kind in ((source,'pose'),(neighbor,'pose'),(block,'block')):
                found=db.execute('SELECT kind,value FROM named WHERE name=?',(name,)).fetchone()
                if found and found[0]=='rawpose' and kind=='pose':
                    angle,raw=json.loads(found[1])
                    ids=[row(t.split(',')) for t in raw.split(';')] if raw else []
                    value=[angle,ids];intern('pose',value)
                    db.execute('UPDATE named SET kind=?,value=? WHERE name=?',
                               ('pose',json.dumps(value,separators=(',',':')),name))
                    counts['required_predecessor_pose_declarations']+=1
                    found=('pose',json.dumps(value,separators=(',',':')))
                if not found or found[0]!=kind:
                    unresolved_kinds[kind+'/'+re.sub(r'\d+', '#', name)]+=1
                    if len(unresolved_examples)<40:
                        unresolved_examples.append({'source':source,'neighbor':neighbor,'block':block,
                                                    'missing':name,'required_kind':kind})
                    break
                values.append(json.loads(found[1]))
            if len(values)!=3:
                unresolved+=1;continue
            for context in (values[0][1]+values[2],values[1][1]):
                canonical=json.dumps(sorted(set(context)),separators=(',',':'))
                db.execute('INSERT OR IGNORE INTO context VALUES (?)',(canonical,))
        counts['unresolved_pair_bindings']=unresolved
        report['unresolved_binding_kinds']=dict(unresolved_kinds)
        report['unresolved_binding_examples']=unresolved_examples
        counts['distinct_pair_bindings']=db.execute('SELECT COUNT(*) FROM pair_binding').fetchone()[0]
        counts['distinct_remaining_pair_contexts']=db.execute('SELECT COUNT(*) FROM context').fetchone()[0]
        counts['context_row_memberships']=sum(len(json.loads(x[0])) for x in db.execute('SELECT value FROM context'))
        report['status']='structural inventory complete; numerical checks not run'
    except (Stop,Unsupported,sqlite3.Error) as error:
        report['status']='stopped safely; partial scope only';report['stop_reason']=str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        report['counts']=dict(counts);report['unique_structures']=dict(sequence)
        report['tree_families']={k:dict(v) for k,v in families.items()}
        report['schemas']=dict(schemas);report['pair_cases']=dict(supported_pair_cases)
        report['unsupported_counts']=dict(unknown_count);report['nonroot_tree_examples']=examples
        report['transitions']=transitions
        report['elapsed_seconds']=time.monotonic()-started
        report['scratch_bytes']=scratch.stat().st_size if scratch.exists() else 0
        report['costs_not_counted']=['actual packing entrances and imported helper dependencies',
            'cached planar vertices and complete direction-cone coverage',
            'all pair strictness/slack checks and any unsupported pair schemas',
            'relaxation witnesses, chord checks, branches and semantic assembly',
            'all original cases outside these seven']
        db.close();scratch.unlink(missing_ok=True)
    temporary=out.with_suffix('.json.tmp');written=0
    try:
        with temporary.open('wb') as f:
            for token in json.JSONEncoder(separators=(',',':')).iterencode(report):
                b=token.encode();written+=len(b)
                if written>8*1024**2:raise Stop('output cap')
                f.write(b)
        temporary.replace(out)
    finally:temporary.unlink(missing_ok=True)
    print(json.dumps({'status':report['status'],'sources':len(report['sources']),
                      'counts':report['counts'],'unique_structures':report['unique_structures'],
                      'output':str(out.relative_to(ROOT))}))


if __name__=='__main__':main()
