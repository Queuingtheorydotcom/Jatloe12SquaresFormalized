#!/usr/bin/env python3
"""Move exact Short54 declarations into independent, bounded-size modules.

The inverse audit reconstructs the unfactored Inputs source, including every
literal and theorem. This is a source integrity check, not Lean acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'Compact/Completion/C981/ShortCertificate54'
MOD = 'Compact.Completion.C981.ShortCertificate54'
NS = 'N12Compact.C981CompletionShort54'
FOOTER = '\nend\nend ' + NS + '\n'
CHUNK_SIZE = 512
MANIFEST = ROOT / 'audit/short54-inputs-factor.json'


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def data_module(imports, declarations):
    return '\n'.join('import ' + name for name in imports) + f'''

namespace {NS}
open N12Compact IntegerSupport
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

''' + declarations + FOOTER


def split_inputs(source):
    start = source.index('def row0 : Row :=')
    if not source.endswith(FOOTER):
        raise ValueError('Unexpected Inputs footer')
    prefix = source[:start]
    declarations = source[start:-len(FOOTER)].splitlines(keepends=True)
    groups = {'row': [], 'den': [], 'basis': []}
    for line in declarations:
        match = re.fullmatch(r'def (row|den|basis)(\d+) : [^\n]+\n', line)
        if match is None:
            raise ValueError('Unexpected atom declaration')
        kind, index = match.groups()
        if int(index) != len(groups[kind]):
            raise ValueError('Nonconsecutive or duplicate atom name')
        groups[kind].append(line)
    if ''.join(sum(groups.values(), [])) != source[start:-len(FOOTER)]:
        raise ValueError('Atoms are not in row/den/basis order')
    files = {'InputMetadata': prefix + FOOTER}
    chunks = []
    row_modules = {}
    for kind, lines in groups.items():
        for offset in range(0, len(lines), CHUNK_SIZE):
            name = 'InputAtoms/' + kind.capitalize() + f'{offset // CHUNK_SIZE:02}'
            body = ''.join(lines[offset:offset + CHUNK_SIZE])
            if kind == 'row':
                imports = ['Compact.Core.IntegerSupport']
                for index in range(offset, min(offset + CHUNK_SIZE, len(lines))):
                    row_modules[index] = MOD + '.' + name.replace('/', '.')
            elif kind == 'den':
                # Keep the common namespace header; this import exports Row.
                imports = ['Compact.Core.IntegerSupport']
            else:
                ids = {int(index) for index in re.findall(r'\brow(\d+)\b', body)}
                imports = ['Compact.Core.VertexSupport'] + sorted({row_modules[i] for i in ids})
            files[name] = data_module(imports, body)
            chunks.append({'file': name + '.lean', 'kind': kind,
                           'start': offset, 'count': len(lines[offset:offset + CHUNK_SIZE]),
                           'declarations_sha256': sha(body), 'source_sha256': sha(files[name])})
    files['Inputs'] = '\n'.join('import ' + MOD + '.' + name.replace('/', '.')
                               for name in files) + '\n'
    report = {'kind': 'exact_source_factorization', 'lean_accepted': False,
              'original_inputs_sha256': sha(source), 'chunk_size': CHUNK_SIZE,
              'atom_counts': {kind: len(lines) for kind, lines in groups.items()},
              'metadata_sha256': sha(files['InputMetadata']),
              'aggregate_sha256': sha(files['Inputs']), 'chunks': chunks}
    return files, report


def check():
    report = json.loads(MANIFEST.read_text())
    metadata = (OUT / 'InputMetadata.lean').read_text()
    if sha(metadata) != report['metadata_sha256'] or not metadata.endswith(FOOTER):
        raise ValueError('Metadata differs')
    bodies = []
    for chunk in report['chunks']:
        source = (OUT / chunk['file']).read_text()
        body = ''.join(re.findall(r'^def (?:row|den|basis)\d+ : [^\n]+\n', source, re.M))
        if sha(body) != chunk['declarations_sha256'] or sha(source) != chunk['source_sha256']:
            raise ValueError('Chunk differs: ' + chunk['file'])
        bodies.append(body)
    original = metadata[:-len(FOOTER)] + ''.join(bodies) + FOOTER
    files, expected = split_inputs(original)
    if expected != report:
        raise ValueError('Inverse differs from the saved original source')
    for name, source in files.items():
        if (OUT / (name + '.lean')).read_text() != source:
            raise ValueError('Generated source differs: ' + name)
    print(json.dumps({'source_inverse': 'pass', 'original_inputs_sha256': sha(original),
                      'atom_counts': report['atom_counts'], 'data_modules': len(files),
                      'lean_accepted': False}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        check()
        return
    source = (OUT / 'Inputs.lean').read_text()
    files, report = split_inputs(source)
    for name, text in files.items():
        target = OUT / (name + '.lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(json.dumps(report, indent=2) + '\n')
    check()


if __name__ == '__main__':
    main()
