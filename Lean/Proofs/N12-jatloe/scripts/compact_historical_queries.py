#!/usr/bin/env python3
"""Prepare exact shared-query entrances; never edit active Lean or run Lean.

Existing certified queries are selected directly from their checked canonical
chunks, so case-specific aliases disappear. Genuinely new query expressions
are interned across all five entrances and kernel checked once per expression.
Every original owner keeps its exact ordered query values and signature check.
Parent-only --run,256MiB/115seconds,16MiB isolated proposal with source hashes.
"""
from pathlib import Path
import argparse, hashlib, json, re, resource, shutil, signal, sys, time

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'evidence/proposals/HistoricalInitial'
DEST=ROOT/'evidence/proposals/HistoricalInitialSharedQueries'
POOL='Compact/HistoricalOwnership/Queries'
NAMESPACE='N12Compact.HistoricalOwnership.Queries'


def need(test,reason):
    if not test:
        raise ValueError(reason)


def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as source:
        for part in iter(lambda:source.read(65536),b''):
            h.update(part)
    return h.hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',action='store_true')
    args=parser.parse_args()
    need(args.run,'prepared only; parent must schedule --run')
    staging=DEST.with_name(DEST.name+'.staging')
    need(not DEST.exists() and not staging.exists(),'refusing existing proposal')
    started=time.monotonic()

    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        rss*=1 if sys.platform=='darwin' else 1024
        need(rss<256*1024**2 and time.monotonic()-started<115,'resource guard')

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,stop)
    signal.signal(signal.SIGINT,stop)
    manifest=json.loads((SOURCE/'manifest.json').read_text())
    inputs={};texts={};outputs=[];size=0
    try:
        for row in manifest['outputs']:
            path=SOURCE/row['path']
            need(digest(path)==row['sha256'],'modified source proposal: '+row['path'])
            inputs[row['path']]=row['sha256']
            texts[row['path']]=path.read_text()
        aliases={};fresh={};pool=[];query_files=[];by_case={}
        for relative in texts:
            if not re.search(r'/EntryQuery\d+\.lean$',relative):
                continue
            query_files.append(relative)
        # Iterate separately so the exact expression, rather than a theorem's
        # formatting or local name, determines shared geometric proof identity.
        for relative in query_files:
            for match in re.finditer(r'^def (query(\d+)_\d+) : LocalQuery := (.+)$',texts[relative],re.M):
                name,case,expression=match.groups()
                need(name not in aliases,'duplicate original query name')
                canonical=re.fullmatch(r'localQuery(\d+)',expression.strip())
                if canonical:
                    aliases[name]={'kind':'canonical','id':int(canonical[1])}
                else:
                    key=re.sub(r'\s','',expression)
                    if key not in fresh:
                        fresh[key]=len(pool)
                        pool.append(expression)
                    aliases[name]={'kind':'new','id':fresh[key]}
                by_case.setdefault(int(case),[]).append(name)
        need(set(by_case)=={701,717,973,978,979},'unexpected entrance case set')
        need(len(aliases)==7102,'original query count changed')
        expected={row['case']:row['query_aliases'] for row in manifest['cases']}
        for case,names in by_case.items():
            need(sum(aliases[n]['kind']=='canonical' for n in names)==expected[case],
                 'canonical alias count drift')

        def selected(name):
            record=aliases[name]
            if record['kind']=='canonical':
                return '(certified_query% '+str(record['id'])+')'
            return NAMESPACE+'.query'+str(record['id'])+'_certified'

        def write(relative,text):
            nonlocal size
            guard()
            size+=len(text.encode())
            need(size<16*1024**2,'16 MiB source guard')
            path=staging/relative
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(text)
            outputs.append({'path':relative,'sha256':digest(path),'lines':text.count('\n'),
                            'bytes':len(text.encode())})

        staging.mkdir(parents=True)
        for start in range(0,len(pool),32):
            text='''import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

'''
            for i,expression in enumerate(pool[start:start+32],start):
                text+=f'checked_local_query query{i} := {expression}\n'
            text+='\nend N12Compact.HistoricalOwnership.Queries\n'
            write(POOL+f'{start//32:03}.lean',text)
        selections=0
        domain_selections=0
        used_names=[]
        for relative,text in texts.items():
            if relative in query_files:
                continue
            if relative.endswith('/EntryQueries.lean'):
                case=int(re.search(r'/C(\d+)/EntryQueries',relative)[1])
                text=re.sub(r'^import Compact\.Cases\.C\d+\.EntryQuery\d+\n','',text,flags=re.M)
                imports=['Compact.Bridge.SharedLocalQueries',f'Compact.Cases.C{case}.EntryQueryBase']
                imports += [POOL.replace('/','.')+f'{i:03}' for i in sorted({
                    aliases[name]['id']//32 for name in by_case[case] if aliases[name]['kind']=='new'})]
                text=''.join('import '+i+'\n' for i in imports)+text
                def substitute(match):
                    nonlocal selections
                    selections+=1
                    used_names.append(match[1])
                    return selected(match[1])
                text=re.sub(r'⟨(query\d+_\d+),\1_checked⟩',substitute,text)
                need(not re.search(r'\bquery\d+_\d+',text),'unreplaced query occurrence')
            elif relative.endswith('/EntryDomains.lean'):
                def substitute_remove(match):
                    nonlocal domain_selections
                    domain_selections+=1
                    used_names.append(match[2])
                    return ('N12Compact.SharedLocalQueries.remove _ '+match[1]+' '+selected(match[2]))
                text=re.sub(r'\.remove _ (\w+) (query\d+_\d+) \2_checked\b',
                            substitute_remove,text)
                need(not re.search(r'\bquery\d+_\d+',text),'unreplaced original domain-filter query')
            elif re.search(r'\bquery\d+_\d+',text):
                raise ValueError('unexpected query consumer: '+relative)
            write(relative,text)
        need(selections+domain_selections==len(aliases) and set(used_names)==set(aliases),
             'some original query not consumed exactly once by an owner or domain filter')
        before=sum(row['lines'] for row in manifest['outputs'])
        after=sum(row['lines'] for row in outputs)
        report={'status':'shared-query source proposal; ordinary kernel replay pending',
            'source_manifest_sha256':digest(SOURCE/'manifest.json'),
            'input_sha256':inputs,'original_query_uses':len(aliases),
            'canonical_uses_without_aliases':sum(r['kind']=='canonical' for r in aliases.values()),
            'distinct_new_query_records':len(pool),'ordered_owner_selections':selections,
            'original_domain_filter_selections':domain_selections,
            'query_bindings':aliases,'lean_modules':len(outputs),'lean_lines':after,
            'previous_lean_lines':before,'lines_removed':before-after,'lean_bytes':size,
            'outputs':outputs,'elapsed_seconds':time.monotonic()-started,
            'trust':'canonical queries retain existing foundation proofs; all new queries use decide +kernel'}
        (staging/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        staging.replace(DEST)
        print(json.dumps({k:report[k] for k in ['original_query_uses','canonical_uses_without_aliases',
            'distinct_new_query_records','lean_modules','lean_lines','lines_removed','lean_bytes',
            'elapsed_seconds']}))
    except BaseException:
        if staging.exists():
            shutil.rmtree(staging)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':
    main()
