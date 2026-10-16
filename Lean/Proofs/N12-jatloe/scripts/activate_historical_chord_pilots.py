#!/usr/bin/env python3
"""Activate exactly two authenticated whole chord pilots, with rollback.

Parent-only --run; no Lean, numeric search, network or unrelated mutation.
The shared radius module and C717 step18 / C701 step23 are the only targets.
Existing differing sources are refused. Idempotent repeats retain the original
receipt. Ordinary failure removes only files written by this invocation.
"""
from pathlib import Path
import argparse,hashlib,json,os,signal,time

ROOT=Path(__file__).resolve().parents[1]
PROPOSAL=ROOT/'evidence/proposals/HistoricalChordsCompact'
TARGETS=('Compact/Preservation/Chords/Radii.lean',
    'Compact/Preservation/Chords/C717Step18.lean',
    'Compact/Preservation/Chords/C701Step23.lean')


def digest(raw):return hashlib.sha256(raw).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',action='store_true')
    args=parser.parse_args()
    if not args.run:parser.error('parent must schedule --run')
    started=time.monotonic();written=[];temporary=[]
    manifest_raw=(PROPOSAL/'manifest.json').read_bytes();manifest=json.loads(manifest_raw)
    payload={}
    for relative in TARGETS:
        expected=manifest['output_files'][relative];raw=(PROPOSAL/relative).read_bytes()
        assert digest(raw)==expected['sha256'] and len(raw)==expected['bytes']
        assert raw.count(b'\n')==expected['lines']
        target=ROOT/relative
        assert not target.is_symlink()
        if target.exists():assert digest(target.read_bytes())==digest(raw), ('differing active source',relative)
        payload[relative]=raw
    assert sum(map(len,payload.values()))<512*1024
    try:
        for relative,raw in payload.items():
            target=ROOT/relative
            if target.exists():continue
            target.parent.mkdir(parents=True,exist_ok=True)
            temp=target.with_suffix('.lean.chord-pilot-tmp')
            assert not temp.exists();temporary.append(temp)
            temp.write_bytes(raw);os.replace(temp,target)
            written.append((relative,digest(raw)))
        report={'scope':'Exact source activation for two complete original chord transitions; Lean replay pending.',
            'proposal_manifest_sha256':digest(manifest_raw),
            'outputs':{relative:manifest['output_files'][relative] for relative in TARGETS},
            'new_files':[relative for relative,_ in written],
            'lean_checked':False,'elapsed_seconds':time.monotonic()-started}
        receipt=ROOT/'evidence/historical-chord-pilots-activation.json'
        if not receipt.exists():receipt.write_text(json.dumps(report,indent=2)+'\n')
        else:
            previous=json.loads(receipt.read_text())
            assert previous['proposal_manifest_sha256']==report['proposal_manifest_sha256']
            assert previous['outputs']==report['outputs']
        print(json.dumps({'new_files':len(written),'pilots':['C717Step18','C701Step23'],
            'elapsed_seconds':time.monotonic()-started}))
    except BaseException:
        for relative,expected in reversed(written):
            target=ROOT/relative
            if target.exists() and digest(target.read_bytes())==expected:target.unlink()
        raise
    finally:
        for path in temporary:path.unlink(missing_ok=True)


if __name__=='__main__':main()
