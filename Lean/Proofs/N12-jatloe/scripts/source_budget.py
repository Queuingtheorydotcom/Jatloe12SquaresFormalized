#!/usr/bin/env python3
"""Measure an entire explicit proof import closure, never just its wrappers.

Both bytes and tokens are counted to prevent line packing from faking a
smaller proof. This reports source size, not mathematical completeness or
a prediction of certificates that have not yet been constructed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from verify import ROOT, closure, path

def measure(files):
    records=[]
    for file in sorted(files):
        raw=file.read_bytes()
        records.append({'path':str(file.relative_to(ROOT)), 'bytes':len(raw),
            'lines':len(raw.splitlines()),
            'lexical_items':len(re.findall(rb'\w+|[^\w\s]',raw)),
            'largest_line_bytes':max(map(len,raw.splitlines()),default=0),
            'sha256':hashlib.sha256(raw).hexdigest()})
    return {'modules':len(records),'lines':sum(x['lines'] for x in records),
            'bytes':sum(x['bytes'] for x in records),
            'lexical_items':sum(x['lexical_items'] for x in records),
            'files':records}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('roots',nargs='+')
    parser.add_argument('--line-cap',type=int,default=300000)
    parser.add_argument('--byte-cap',type=int,default=40000000)
    parser.add_argument('--report',type=Path,default=ROOT/'evidence/source-budget.json')
    args=parser.parse_args()
    scoped=measure({path(m) for m in closure(args.roots)})
    all_source=measure({p for base in ['Compact','Completion','source','adapters']
                       for p in (ROOT/base).rglob('*.lean')} | {ROOT/'Compact.lean'})
    result={'roots':args.roots,'scope':'entire resolved local import closure',
        'closure':scoped,'all_resident_active_and_draft_source':all_source,
        'excluded_from_source_count':['pinned external Lean/Mathlib libraries',
            'immutable duplicate vendor provenance; included if imported',
            'old proof archives, which are NOT dependencies of these roots'],
        'limits':{'lean_lines':args.line_cap,'source_bytes':args.byte_cap},
        'within_current_source_limits':scoped['lines']<=args.line_cap and scoped['bytes']<=args.byte_cap,
        'full_original_proof_assembled':False,
        'eventual_submillion_bound_established':False,
        'note':'The seven historical exclusions and baseline replacement still need compact certificates. Their cost cannot be omitted from a final proof-size claim.'}
    args.report.parent.mkdir(parents=True,exist_ok=True)
    args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['closure','all_resident_active_and_draft_source']}))
    print(json.dumps({'closure':{k:v for k,v in scoped.items() if k!='files'},
                      'resident':{k:v for k,v in all_source.items() if k!='files'}}))
    if not result['within_current_source_limits']:
        raise SystemExit(1)

if __name__=='__main__':main()
