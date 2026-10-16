#!/usr/bin/env python3
"""Prepare exact shared initial-cover batch source; coordinator runs --run.

Eight independent checked_recipe declarations remain eight independent kernel
checks. Only their common declaration/list-proof scaffolding is shared. Reads
the hash-verified five-case query-sharing proposal and active C713/C898 batch
files, writes a changed-files-only overlay, and measures the actual seven-entry
import closure before and after. No Lean, search, subprocess or active edits.
Guards:256MiB,115seconds,8MiB output; atomic cleanup on failure.
"""
from pathlib import Path
import argparse, hashlib, json, re, resource, shutil, signal, sys, time

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'evidence/proposals/HistoricalInitialSharedQueries'
DEST=ROOT/'evidence/proposals/InitialBatchSharing'
CASES=(701,713,717,898,973,978,979)
HELPER='Compact.Bridge.InitialCoverBatch'


def need(value,reason):
    if not value:
        raise ValueError(reason)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def imports(text):
    text=re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    text=re.sub(r'--[^\n]*','',text)
    return [word for line in re.findall(r'^\s*import\s+([^\n]+)',text,re.M)
            for word in line.split()]


def transform(relative,text):
    case=int(re.search(r'/C(\d+)/RecipeInitial/',relative)[1])
    ns=f'N12Compact.C{case}RecipeInitial'
    need(re.findall(r'^namespace (\S+)',text,re.M)==[ns], 'unexpected batch namespace')
    matches=re.findall(r'^checked_recipe (\w+) \(bank, (inside\d+), (outside\d+)\) := (.+)$',text,re.M)
    need(len(matches)==8, 'production batch must have exactly eight separate records: '+relative)
    names=[row[0] for row in matches]
    need(len(set(names))==8,'duplicate entry name')
    inside,outside=matches[0][1:3]
    need(all(row[1:3]==(inside,outside) for row in matches),'mixed owner premises')
    need(inside[6:]==outside[7:],'inside/outside owner mismatch')
    owner=inside[6:]
    need(all(re.fullmatch(r'entry'+owner+r'_\d+',name) for name in names),'entry owner drift')
    batch=re.search(r'^(?:noncomputable )?def (entries\d+_\d+) : List \(DirectRecipeTable.Entry bank '+
                    re.escape(inside+' '+outside)+r'\) :=\s*\[([^\]]+)\]',text,re.M)
    need(batch is not None,'missing original typed batch list')
    batchname=batch[1]
    need([x.strip() for x in batch[2].split(',')]==names,'original list order differs')
    declarations=re.findall(r'^(?:private |noncomputable )?(def|theorem) (\w+)',text,re.M)
    need(declarations==[('def',batchname),('theorem',batchname+'_literal_checked'),
                        ('theorem',batchname+'_checked')], 'unrecognized batch declarations')
    proof=re.search(r'  exact ⟨([^\n]+)⟩',text)
    need(proof is not None and [x.strip() for x in proof[1].split(',')]==
         [name+'_literal_checked' for name in names]+['by simp'],
         'original batch proof does not match all separate facts')
    need('DirectRecipeCheck.all_checked '+batchname+' '+batchname+'_literal_checked' in text,
         'original semantic acceptance bridge changed')
    source_imports=imports(text)
    need(source_imports.count('Compact.Bridge.CheckedRecipeCommand')==1,'unexpected helper imports')
    retained=[item for item in source_imports if item!='Compact.Bridge.CheckedRecipeCommand']
    need(len(retained)==1, 'unexpected batch data imports')
    bank=(ns+'.bank') if case in (713,898) else 'N12Compact.Preservation.InitialBank.bank'
    point_ns='N12Compact.C898DirectInitial' if case==898 else ns
    result=''.join('import '+item+'\n' for item in retained+[HELPER])+'\n'
    result+=f'checked_initial_batch {ns}.{batchname}\n'
    result+=f'  ({bank}, {point_ns}.{inside},\n   {point_ns}.{outside})\n[\n'
    result+=',\n'.join('  '+row[0]+' := '+row[3] for row in matches)+'\n]\n'
    # Copy, rather than normalize or reconstruct, each actual semantic recipe.
    emitted=re.findall(r'^  (\w+) := (.+?)(?:,)?$',result,re.M)
    need(emitted==[(row[0],row[3]) for row in matches],'emitted recipe byte identity/order drift')
    return result,{'case':case,'batch':ns+'.'+batchname,
        'arguments':[bank,point_ns+'.'+inside,point_ns+'.'+outside],
        'records':[{'name':row[0],'spec':row[3]} for row in matches]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',action='store_true')
    args=parser.parse_args()
    need(args.run,'prepared only; coordinator must schedule --run')
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
    try:
        manifest_path=BASE/'manifest.json'
        manifest_bytes=manifest_path.read_bytes()
        manifest=json.loads(manifest_bytes)
        overlay={};provenance={};changed={};records=[];outputs=[];total_bytes=0
        for item in manifest['outputs']:
            data=(BASE/item['path']).read_bytes()
            need(sha(data)==item['sha256'],'source proposal drift: '+item['path'])
            overlay[item['path']]=data.decode()
            provenance[str((BASE/item['path']).relative_to(ROOT))]=item['sha256']
        selected={path:text for path,text in overlay.items()
                  if re.search(r'/RecipeInitial/Batches/Owner\d+Batch\d+\.lean$',path)}
        need(len(selected)==624,'other-five batch count changed')
        for case,pattern,expected in [(713,'Batches/Owner*Batch*.lean',144),
                                      (898,'Batch??_??.lean',88)]:
            paths=sorted((ROOT/f'Compact/Cases/C{case}/RecipeInitial').glob(pattern))
            need(len(paths)==expected,'active batch count changed: '+str(case))
            for path in paths:
                data=path.read_bytes();relative=str(path.relative_to(ROOT))
                provenance[relative]=sha(data);selected[relative]=data.decode()
        need(len(selected)==856,'whole seven-case batch count changed')
        for relative,text in sorted(selected.items()):
            guard()
            replacement,record=transform(relative,text)
            changed[relative]=replacement
            record.update({'path':relative,'before_sha256':sha(text.encode()),
                'after_sha256':sha(replacement.encode()),'before_lines':text.count('\n'),
                'after_lines':replacement.count('\n')})
            records.append(record)
        need(sum(len(record['records']) for record in records)==6848,'root record count changed')

        closure_sources={}
        def closure(after):
            seen=set();active=set();ordered=[];stats=[]
            def visit(module):
                if module in seen or module.split('.')[0] not in {'Compact','Completion','S12'}:
                    return
                need(module not in active,'import cycle: '+module)
                active.add(module)
                relative=module.replace('.','/')+'.lean'
                if module.startswith('S12.'):
                    relative='source/'+relative
                if after and relative in changed:
                    text=changed[relative];origin='changed overlay'
                elif relative in overlay:
                    text=overlay[relative];origin='shared-query proposal'
                else:
                    path=ROOT/relative
                    need(path.is_file(),'missing local import: '+module)
                    text=path.read_text();origin='active source'
                guard()
                if origin=='active source':
                    closure_sources[relative]=sha(text.encode())
                for dependency in imports(text):
                    visit(dependency)
                active.remove(module);seen.add(module);ordered.append(module)
                stats.append({'module':module,'path':relative,'origin':origin,
                    'sha256':sha(text.encode()),'lines':text.count('\n'),'bytes':len(text.encode())})
            for case in CASES:
                visit(f'Compact.Cases.C{case}.RecipeInitial.Entry')
            return {'modules':len(ordered),'lines':sum(item['lines'] for item in stats),
                    'bytes':sum(item['bytes'] for item in stats),'sources':stats,
                    'scope':'all seven original-owner initial entrance import closures; excludes external libraries'}
        before=closure(False);after=closure(True)
        staging.mkdir(parents=True)
        for relative,text in changed.items():
            total_bytes+=len(text.encode())
            need(total_bytes<8*1024**2,'8 MiB proposal guard')
            path=staging/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            outputs.append({'path':relative,'sha256':sha(text.encode()),'lines':text.count('\n'),
                            'bytes':len(text.encode())})
        report={'status':'source overlay only; eight separate ordinary kernel checks retained per batch',
            'base_overlay':str(BASE.relative_to(ROOT)),
            'base_manifest_sha256':sha(manifest_bytes),'input_sha256':provenance,
            'closure_active_sha256':closure_sources,'cases':list(CASES),'batches':len(records),
            'root_records':6848,'records':records,'outputs':outputs,
            'lean_modules':len(outputs),'lean_lines':sum(item['lines'] for item in outputs),
            'previous_batch_lines':sum(row['before_lines'] for row in records),
            'batch_lines_removed':sum(row['before_lines']-row['after_lines'] for row in records),
            'lean_bytes':total_bytes,'before_entrance_closure':before,'after_entrance_closure':after,
            'closure_lines_removed':before['lines']-after['lines'],
            'elapsed_seconds':time.monotonic()-started}
        (staging/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        staging.replace(DEST)
        print(json.dumps({key:report[key] for key in ['batches','root_records','lean_modules',
            'lean_lines','previous_batch_lines','batch_lines_removed','closure_lines_removed',
            'lean_bytes','elapsed_seconds']}))
    except BaseException:
        if staging.exists():
            shutil.rmtree(staging)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':
    main()
