#!/usr/bin/env python3
"""Render the successful twenty-stage chord audit using shared commands.

Coordinator-only --run:128MiB/60seconds,8MiB output. Reuses the already
discovered exact witnesses; performs no search or compilation. The emitted
commands independently kernel-check every record later. Active sources and
the original larger proposal remain untouched.
"""
from pathlib import Path
import argparse,hashlib,json,re,resource,shutil,signal,sys,time
from prepare_historical_chords import (ROOT,BASE,CASES,MODULE,NS,stage_source,
    radius_source,read_case,read_bytes,Q,need)

OLD=ROOT/'evidence/proposals/HistoricalChords'
DEST=ROOT/'evidence/proposals/HistoricalChordsCompact'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',action='store_true')
    args=parser.parse_args();need(args.run,'parent serial slot and --run required')
    staging=DEST.with_name(DEST.name+'.staging')
    need(not DEST.exists() and not staging.exists(),'refusing existing compact proposal')
    started=time.monotonic();provenance={};written=0
    def digest(raw):return hashlib.sha256(raw).hexdigest()
    def guard(*_):
        rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
        need(rss<128*1024**2 and time.monotonic()-started<55,'128MiB/55second guard')
    def load(path):
        raw=path.read_bytes();provenance[str(path.relative_to(ROOT))]=digest(raw);return json.loads(raw)
    signal.signal(signal.SIGALRM,guard);signal.setitimer(signal.ITIMER_REAL,.2,.2)
    try:
        old=load(OLD/'manifest.json');certificates=load(OLD/'certificates.json')
        need(old['status']=='source assembled; Lean acceptance pending' and not old['failures'],
            'initial exact reconstruction did not succeed')
        need(not certificates['failures'] and len(certificates['stages'])==20,'incomplete chord records')
        if 'certificate_file' in old:
            need(provenance[str((OLD/'certificates.json').relative_to(ROOT))]==
                old['certificate_file']['sha256'],'changed numerical record file')
        manifest=load(BASE/'manifest.json')
        audits=load(ROOT/'evidence/historical-direct-cover-audit.json')['cases']
        cover=read_bytes(ROOT/'vendor/S12/CoverData.lean').decode()
        cover_rows=[(int(cid),tuple(map(int,values.split(',')))) for cid,values in
            re.findall(r'⟨(\d+),\{([0-9,]+)\}',cover)]
        cases={cid:read_case(cid,manifest,next(a for a in audits if a['case']==cid),
            cover_rows,provenance,guard) for cid in CASES}
        raw=read_bytes(ROOT/'vendor/S12/AngleChordRadiusData.lean')
        expected=next(s['sha256'] for s in manifest['sources'] if s['module']=='S12.AngleChordRadiusData')
        need(digest(raw)==expected,'radius source changed')
        radii={int(angle)+(64 if grid=='128' else 0):(Q(upper),Q(radius))
            for grid,angle,upper,radius in re.findall(
                r'^def angleChordRadius(64|128)_(\d+) : .*?⟩,\(([^()]*)\),\(([^()]*)\)⟩$',raw.decode(),re.M)}
        need(len(radii)==192,'incomplete radius metadata')
        wanted={(cid,s['step']) for cid,case in cases.items() for s in case['stages']
            if cid!=713 and s['kind']!='PruningCoverCheck'}
        need(wanted=={(s['case'],s['step']) for s in certificates['stages']},'stage scope changed')
        output={};staging.mkdir(parents=True)
        def write(relative,source):
            nonlocal written
            raw=source.encode();written+=len(raw);need(written<8*1024**2,'8MiB output guard')
            path=staging/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
            output[relative]={'bytes':len(raw),'lines':source.count('\n'),'sha256':digest(raw)}
        write(MODULE.replace('.','/')+'/Radii.lean',radius_source({i:radii[i] for i in old['used_angles']}))
        for stage in certificates['stages']:
            guard();cid=stage['case'];case=cases[cid]
            graph=next(s for s in case['stages'] if s['step']==stage['step'])
            need(all(stage[k]==graph[k] for k in ('source','target','neighbors','kind')),'source graph changed')
            need([p['source'] for p in stage['plans']]==case['domains'][stage['source']],
                'original source pose coverage changed')
            for domain,records in zip(stage['neighbors'],stage['neighbor_records']):
                need([n['source'] for n in records]==case['domains'][domain],'neighbor coverage changed')
            for plan in stage['plans']:
                need(len(plan['branches'])==2,'missing interval-complement branch')
                for branch in plan['branches']:
                    need(branch['kind'] in ('keep','close'),'unresolved branch')
                    if branch['kind']=='keep':
                        need(branch['target'] in case['domains'][stage['target']],'foreign target')
            write(MODULE.replace('.','/')+f'/C{cid}Step{stage["step"]:02}.lean',stage_source(case,stage,radii))
        report={'scope':'Twenty original chord transitions with all actual normalized-packing adapters.',
            'status':'compact source assembled; new commands and all records require Lean replay',
            'lean_checked':False,'counts':old['counts'],'source_inputs':provenance,
            'original_proposal_manifest_sha256':provenance[str((OLD/'manifest.json').relative_to(ROOT))],
            'output_files':output,'lean_modules':len(output),
            'lean_lines':sum(v['lines'] for v in output.values()),'lean_bytes':written,
            'elapsed_seconds':time.monotonic()-started}
        (staging/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        staging.replace(DEST)
        print(json.dumps({k:report[k] for k in ('lean_modules','lean_lines','lean_bytes','elapsed_seconds')}))
    except BaseException:
        if staging.exists():shutil.rmtree(staging)
        raise
    finally:signal.setitimer(signal.ITIMER_REAL,0)


if __name__=='__main__':main()
