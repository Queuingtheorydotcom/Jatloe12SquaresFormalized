#!/usr/bin/env python3
"""Factor the unchanged 24 C979 domain blocks for bounded serial checking.

Public definitions, statements, query terms and checks are copied verbatim.
The recorded source backup makes the factoring repeatable without a restore.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Compact/Cases/C979/EntryQueries.lean'
BACKUP = ROOT / '.verification/source-backups/C979.EntryQueries.original.txt'
DEST = ROOT / 'Compact/Cases/C979/EntryQueryChunks'

def main():
    current = SOURCE.read_text()
    if current.startswith('import Compact.Cases.C979.EntryQueryChunks.Chunk'):
        original = BACKUP.read_text()
    else:
        original = current
        if BACKUP.exists() and BACKUP.read_text() != original:
            raise RuntimeError('The recorded original differs; refusing to overwrite it')
        BACKUP.parent.mkdir(parents=True, exist_ok=True)
        BACKUP.write_text(original)
    starts = [m.start() for m in re.finditer(r'^def single979_\d+_[01] :', original, re.M)]
    if len(starts) != 24 or not original.endswith('end\nend S12\n'):
        raise ValueError('Unexpected original domain structure')
    imports, preamble = original[:starts[0]].split('namespace S12\n', 1)
    blocks = [original[start:end] for start,end in zip(starts, starts[1:] +
        [len(original)-len('end\nend S12\n')])]
    if any(len(re.findall(r'^theorem single979_\d+_[01]_checked', block, re.M)) != 1
           for block in blocks):
        raise ValueError('A domain block lost its public check')
    DEST.mkdir(parents=True, exist_ok=True)
    (DEST / 'Imports.lean').write_text(imports)
    for i, block in enumerate(blocks):
        previous = 'Imports'
        (DEST / f'Chunk{i:02}.lean').write_text(
            f'import Compact.Cases.C979.EntryQueryChunks.{previous}\n\n' +
            'namespace S12\n' + preamble + block + 'end\nend S12\n')
    SOURCE.write_text('\n'.join(f'import Compact.Cases.C979.EntryQueryChunks.Chunk{i:02}' for i in range(24))+'\n\n' +
        '/-! The original 24 public domains and their checks are factored into\n'
        'small serial modules; their terms and statements are unchanged. -/\n')
    report = {'original_sha256':hashlib.sha256(original.encode()).hexdigest(),
        'public_domain_blocks':24, 'verbatim_blocks':True,
        'new_modules':25, 'fresh_lean_replay_complete':False}
    (ROOT/'.verification/c979-entry-factoring.json').write_text(
        json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__ == '__main__':
    main()
