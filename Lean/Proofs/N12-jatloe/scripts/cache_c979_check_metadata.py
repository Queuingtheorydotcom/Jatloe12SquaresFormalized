#!/usr/bin/env python3
"""Separate proof-bearing query equality from the literal ownership check.

The small ownership predicate reads only the four literal domain fields.
Its decision can therefore use an empty query list; the real query list is
retained in the domain and bound to the exact signatures separately.
Every added equality and metadata check must still pass ordinary Lean.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def main():
    count = 0
    for path in sorted((ROOT/'Compact/Cases/C979/EntryQueryChunks').glob('Chunk*.lean')):
        source = path.read_text()
        name = re.search(r'^def (single979_\d+_[01]) :', source, re.M).group(1)
        if f'private theorem {name}_queries_exact' in source:
            continue
        match = re.search(r'^def '+name+r' : DirectSingleDomain := ⟨(\d+),(\d+),(\d+),(\[.*?\]),\[', source, re.M)
        if not match:
            raise ValueError('Unexpected literal domain fields in '+str(path))
        mask,low,high,allowed = match.groups()
        bridge = 'SmallOwnerDomainThree' if int(high)>2 else 'SmallOwnerDomain'
        kind = name.rsplit('_',1)[1]
        sig = name+'Signatures'
        lemma = f'private theorem {name}_queries_exact :\n'+\
            f'    {sig} = {name}.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl\n'+\
            f'#check {name}_queries_exact\n\n'+\
            f'private theorem {name}_metadata :\n'+\
            f'    N12Compact.{bridge}.Check {name} case979Family {kind} {sig} := by\n'+\
            f'  change N12Compact.{bridge}.Check (⟨{mask},{low},{high},{allowed},[]⟩ : DirectSingleDomain)\n'+\
            f'    case979Family {kind} {sig}\n  decide +kernel\n'+\
            f'#check {name}_metadata\n\n'
        source = source.replace(f'theorem {name}_checked',lemma+f'theorem {name}_checked',1)
        old=f'{sig} (by rfl) (by decide) (by decide +kernel)'
        new=f'{sig} {name}_queries_exact (by decide) {name}_metadata'
        if old not in source:
            raise ValueError('Unexpected original check in '+str(path))
        source=source.replace(old,new,1)
        path.write_text(source)
        count += 1
    report={'domains_with_separated_metadata':count,
        'original_query_lists_preserved':True,'original_public_contracts_preserved':True,
        'metadata_proofs_require_lean_replay':True,'new_modules':0}
    (ROOT/'.verification/c979-metadata-caching.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__=='__main__': main()
