#!/usr/bin/env python3
"""Parent-run exact unused-label removal, retaining every indexed pose.

The explicit current virtual delivery census defines consumers. Alias values
and source hashes remain in the proposal manifest; no certificate/data record
or proof obligation is removed, and no active source is edited.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import signal

ROOT=Path(__file__).resolve().parents[1]
RELATIVE=Path('Compact/Cases/C898/SharedPoses.lean')
DEST=ROOT/'evidence/proposals/C898PoseLabels'


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',action='store_true')
    args=parser.parse_args()
    if not args.run:parser.error('parent must schedule --run')
    assert not DEST.exists()
    def stop(*_):raise TimeoutError('20-second source-only guard')
    signal.signal(signal.SIGALRM,stop);signal.alarm(20)
    try:
        census_path=ROOT/'evidence/virtual-preferred-source-budget.json'
        census_raw=census_path.read_bytes();census=json.loads(census_raw)
        raw=(ROOT/RELATIVE).read_bytes();source=raw.decode()
        pattern=re.compile(r'^noncomputable def (continuousScout898\w+) : PoseLeaf := poses (\d+)\n',re.M)
        aliases={name:int(index) for name,index in pattern.findall(source)}
        assert len(aliases)==2196,('pose label scope changed',len(aliases))
        names=set(aliases);used=set();read_bytes=0;consumer_hashes={}
        for item in census['files']:
            path=ROOT/item['path']
            if path==ROOT/RELATIVE:continue
            payload=path.read_bytes();read_bytes+=len(payload)
            assert read_bytes<=64*1024**2,'64-MiB source read cap'
            assert sha(payload)==item['sha256'],('refresh the virtual census first',item['path'])
            found=set(re.findall(r'\bcontinuousScout898\w+\b',payload.decode()))&names
            if found:
                consumer_hashes[item['path']]=sha(payload);used.update(found)
        removed={name:index for name,index in aliases.items() if name not in used}
        result=pattern.sub(lambda match:match.group() if match.group(1) in used else '',source)
        # The complete indexed dictionary and all row/angle definitions are byte-identical.
        marker='/-- Names retain the authenticated source identifiers and exact row order. -/'
        assert source.split(marker)[0]==result.split(marker)[0]
        assert len(pattern.findall(result))==len(used)
        # The heading remains valid even when no alias declarations survive.
        result=result.replace(marker, marker.replace('/--', '/-', 1))
        output=result.encode();target=DEST/RELATIVE;target.parent.mkdir(parents=True)
        target.write_bytes(output)
        report={'scope':'Unused source labels only; every original indexed pose is retained unchanged.',
            'lean_checked':False,'census_sha256':sha(census_raw),'source_sha256':sha(raw),
            'unused_labels_removed':len(removed),'used_labels_retained':len(used),
            'original_indexed_pose_data_byte_identical':True,'removed_label_map':removed,
            'consumer_hashes':consumer_hashes,
            'before':{'lines':raw.count(b'\n'),'bytes':len(raw)},
            'output_files':{str(RELATIVE):{'sha256':sha(output),'lines':output.count(b'\n'),'bytes':len(output)}}}
        (DEST/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:v for k,v in report.items() if k not in {'removed_label_map','consumer_hashes'}}))
    finally:signal.alarm(0)


if __name__=='__main__':main()
