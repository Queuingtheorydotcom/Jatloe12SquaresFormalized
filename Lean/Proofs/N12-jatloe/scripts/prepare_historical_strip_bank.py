#!/usr/bin/env python3
"""Parent-only exact strip re-emission of the inactive boxed direct bank.

All boxes, IDs, coefficients, strictness and denominators remain unchanged.
Only the audited disjoint raw-row pairs become shared geometric strip records.
The accepted box literal still builds the identical ordinary balanced tree.
No active changes, Lean run or numerical search. Serial200MiB/60s; internal
190MiB/55s; transactional output16MiB, with a separate exact-original pilot.
"""
from pathlib import Path
import argparse, hashlib, json, re, resource, shutil, signal, sys, time

from prepare_historical_box_bank import decode_line

ROOT = Path(__file__).resolve().parents[1]
BANK = ROOT/'evidence/historical-box-bank'
AUDIT = ROOT/'evidence/historical-strip-recipes'


def need(test, message):
    if not test:
        raise ValueError(message)


def literal(source):
    match = re.search(r'(boxed_sparse_rows%|sparse_rows%) "\n(.*?)\n"',source,re.S)
    need(match is not None, 'expected original or boxed sparse literal')
    lines = match.group(2).splitlines()
    rows, boxed = {}, set()
    for line in lines:
        decoded = decode_line(line)
        need(not rows.keys() & decoded.keys(), 'duplicate source row ID')
        rows.update(decoded)
        if line.startswith('B:'):
            boxed.update(decoded)
    return match,lines,rows,boxed


def decode_strip(text):
    kind, body = text.split(':',1)
    fields = body.split(';')
    if kind == 'M':
        need(len(fields) == 5,'invalid M strip')
        ids,normal,bounds,denominators,mask = fields
        scales = '1,1'
    else:
        need(kind == 'P' and len(fields) == 6,'invalid P strip')
        ids,normal,scales,bounds,denominators,mask = fields
    a,b = map(int,ids.split(','))
    x,y = map(int,normal.split(','))
    k,K = map(int,scales.split(','))
    lo,hi = map(int,bounds.split(','))
    d,D = map(int,denominators.split(','))
    mask = int(mask)
    need(a != b and k > 0 and K > 0 and min(d,D) >= 0 and 0 <= mask < 4,
         'invalid scales, IDs, denominators or strictness')
    return {a:(k*x,k*y,-lo,bool(mask & 1),d),
            b:(-K*x,-K*y,hi,bool(mask & 2),D)}


def rewrite(source, records):
    match,lines,rows,boxed = literal(source)
    available = rows.keys()-boxed
    chosen = [entry for entry in records if set(entry['rows']) <= available]
    if not chosen:
        return source,[],0
    used,starters = set(),{}
    for entry in chosen:
        ids = entry['rows']
        need(not used.intersection(ids),'audited strips overlap')
        decoded = decode_strip(entry['recipe'])
        need(decoded == {rid:rows[rid] for rid in ids},'strip changes an original row')
        used.update(ids)
        starters[min(ids)] = entry['recipe']
    output = []
    for line in lines:
        if line.startswith('B:'):
            output.append(line)
            continue
        rid = int(line.split(':',1)[0])
        if rid in starters:
            output.append(starters[rid])
        elif rid not in used:
            output.append(line)
    decoded = {}
    for line in output:
        value = decode_strip(line) if line.startswith(('M:','P:')) else decode_line(line)
        need(not decoded.keys() & value.keys(),'duplicate emitted row ID')
        decoded.update(value)
    need(decoded == rows,'complete emitted leaf differs')
    prefix = source[:match.start()].replace('import Compact.Core.BoxRowSyntax',
        'import Compact.Core.StripRowSyntax').replace('import Compact.Core.SparseLiteral',
        'import Compact.Core.StripRowSyntax')
    result = prefix+'strip_sparse_rows% "\n'+'\n'.join(output)+'\n"'+source[match.end():]
    return result,list(used),len(chosen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',action='store_true')
    parser.add_argument('--output',default='evidence/historical-strip-bank')
    args = parser.parse_args()
    need(args.run,'parent serial slot and --run required')
    dest = (ROOT/args.output).resolve()
    need(dest.is_relative_to(ROOT/'evidence'),'output must be under evidence')
    stage = dest.with_name(dest.name+'.staging')
    need(not dest.exists() and not stage.exists(),'refusing existing output')
    started = time.monotonic()
    sources = {}
    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 190*1024**2 and time.monotonic()-started < 55,'190MiB/55second working guard')
    def stop(*_):
        raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM,stop)
    signal.signal(signal.SIGINT,stop)
    def read(path,expected=None):
        need(path.stat().st_size <= 16*1024**2,'oversized source/metadata input')
        raw = path.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        need(expected is None or digest == expected,'source hash mismatch: '+str(path))
        sources[str(path.relative_to(ROOT))] = digest
        guard()
        return raw.decode()
    stage.mkdir(parents=True)
    try:
        audit = json.loads(read(AUDIT/'manifest.json'))
        need(audit['status'].startswith('complete exact co-occurring'),'strip audit missing')
        bankpath = BANK/'manifest.json'
        bank = json.loads(read(bankpath,audit['sources'][str(bankpath.relative_to(ROOT))]))
        records = json.loads(read(AUDIT/'strips.json'))
        need(len(records) == audit['selected_disjoint_strips'],'audited pair scope differs')
        all_ids = [rid for entry in records for rid in entry['rows']]
        need(len(set(all_ids)) == 2*len(records),'audited rows are not disjoint')
        seen = set()
        count = size = lines = written = 0
        hashes = {}
        changed = []
        for name,digest in bank['outputs'].items():
            source = read(BANK/'proposal'/name,digest)
            if '/RowsChunks/' in name:
                local = [record for record in records if record['leaf'] == name]
                source,ids,n = rewrite(source,local)
                need(n == len(local),'an audited strip is missing from its original leaf')
                need(not seen.intersection(ids),'strip emitted twice')
                seen.update(ids)
                count += n
                if n:
                    changed.append({'path':name,'strips':n})
            raw = source.encode()
            size += len(raw)
            lines += source.count('\n')
            written += len(raw)
            need(written <= 16*1024**2,'16MiB output cap')
            path = stage/'proposal'/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(raw)
            hashes[name] = hashlib.sha256(raw).hexdigest()
            guard()
        need(count == len(records) and seen == set(all_ids),'full strip scope not emitted')
        # Preserve the active original leaf's exact tree; its already boxed
        # pilot supplies the local box choices and leaves crossing strips raw.
        boxed_pilot_path = ROOT/'Compact/HistoricalData/BoxPilot.lean'
        original_path = ROOT/'Compact/HistoricalData/RowsChunks/Part000000.lean'
        boxed_pilot = read(boxed_pilot_path)
        original = read(original_path)
        _,_,original_rows,_ = literal(original)
        _,_,pilot_rows,_ = literal(boxed_pilot)
        need(original_rows == pilot_rows,'active boxed pilot differs from original row data')
        with_strips,_,pilot_count = rewrite(boxed_pilot,records)
        need(pilot_count > 0,'no audited strip in original pilot leaf')
        payload = with_strips.split('strip_sparse_rows% "\n',1)[1].split('\n"',1)[0]
        pilot = '''import Compact.Core.StripRowSyntax
import Compact.HistoricalData.RowsChunks.Part000000

namespace N12Compact.HistoricalStripPilot
open IntegerSupport
set_option Elab.async false
noncomputable def rows : SparseLiteral.Tree (Row × Nat) := strip_sparse_rows% "
'''+payload+'''
"
theorem exact_original : rows = HistoricalData.RowsChunks.part000000 := rfl
end N12Compact.HistoricalStripPilot
#print axioms N12Compact.HistoricalStripPilot.exact_original
'''
        pilot_name = 'pilot/Compact/HistoricalData/StripPilot.lean'
        path = stage/pilot_name
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(pilot)
        written += len(pilot.encode())
        report = {
            'status':'complete exact strip-bank source proposal; generic proof, pilot and activation pending',
            'sources':sources,'outputs':hashes,'original_row_count':bank['original_row_count'],
            'original_pose_count':bank['original_pose_count'],'preserved_box_groups':bank['grouped_boxes'],
            'grouped_strips':count,'grouped_strip_rows':len(seen),
            'source_lines':lines,'source_bytes':size,'source_modules':len(hashes),
            'prior_source_lines':bank['source_lines'],'prior_source_bytes':bank['source_bytes'],
            'actual_lines_saved':bank['source_lines']-lines,
            'actual_bytes_saved':bank['source_bytes']-size,'changed_leaves':changed,
            'pilot':{'path':pilot_name,'strips':pilot_count,'original':str(original_path.relative_to(ROOT)),
                'source_lines':pilot.count('\n'),'sha256':hashlib.sha256(pilot.encode()).hexdigest()},
            'kernel_representation':'Same ordinary balanced literal row tree and identical original IDs. All boxes preserved; no lookup layer or numerical obligation removed.',
            'required_before_activation':['Accept StripRowRecipe and StripRowSyntax plus exact-original pilot under existing resource guard.',
                'Meet all boxed/direct-bank consumer activation gates; this proposal does not bypass any unfinished stage.',
                'Verify all output hashes and count the complete actual root closure including shared generic modules.'],
            'seconds':time.monotonic()-started,
        }
        blob = (json.dumps(report,indent=2)+'\n').encode()
        written += len(blob)
        need(written <= 16*1024**2,'16MiB output cap')
        (stage/'manifest.json').write_bytes(blob)
        guard()
        stage.rename(dest)
        print(json.dumps({key:report[key] for key in ('status','grouped_strips','source_lines',
            'source_bytes','source_modules','actual_lines_saved','actual_bytes_saved','pilot','seconds')},indent=2))
    except BaseException:
        shutil.rmtree(stage,ignore_errors=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)


if __name__ == '__main__':
    main()
