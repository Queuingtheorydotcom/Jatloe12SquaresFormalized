#!/usr/bin/env python3
"""Elaborate the unchanged certified selections in small shared modules."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def main():
    original=(ROOT/'.verification/source-backups/C979.EntryQueries.original.txt').read_text()
    ids=sorted(set(map(int,re.findall(r'\(certified_query% (\d+)\)',original))))
    dest=ROOT/'Compact/Cases/C979/SharedSelections'
    dest.mkdir(parents=True,exist_ok=True)
    chunks=[ids[i:i+16] for i in range(0,len(ids),16)]
    for i,chunk in enumerate(chunks):
        previous='Compact.Cases.C979.EntryQueryChunks.Imports' if i==0 else f'Compact.Cases.C979.SharedSelections.Chunk{i-1:02}'
        source=f'import {previous}\n\nnamespace N12Compact.C979SharedSelections\n'+\
            'open S12\nset_option Elab.async false\nset_option maxRecDepth 100000\n'+\
            'set_option maxHeartbeats 2000000\n'
        for n in chunk:
            source+=f'\nnoncomputable def selected{n} : {{q : LocalQuery // q.Check}} := (certified_query% {n})\n'
        source+='end N12Compact.C979SharedSelections\n'
        (dest/f'Chunk{i:02}.lean').write_text(source)
    for path in (ROOT/'Compact/Cases/C979/EntryQueryChunks').glob('Chunk*.lean'):
        source=path.read_text()
        source=re.sub(r'\(certified_query% (\d+)\)',
            lambda m:'N12Compact.C979SharedSelections.selected'+m.group(1),source)
        source=re.sub(r'^import Compact.Cases.C979.(?:EntryQueryChunks.(?:Imports|Chunk\d+)|SharedSelections.Chunk\d+)',
            f'import Compact.Cases.C979.SharedSelections.Chunk{len(chunks)-1:02}',
            source,count=1,flags=re.M)
        path.write_text(source)
    report={'original_certified_terms':len(ids),'terms_per_module':16,
        'new_modules':len(chunks),'original_certified_expressions_preserved':True,
        'public_domain_statements_preserved':True,'requires_lean_replay':True}
    (ROOT/'.verification/c979-shared-selections.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__=='__main__':main()
