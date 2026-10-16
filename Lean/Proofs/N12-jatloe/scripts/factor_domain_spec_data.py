#!/usr/bin/env python3
"""Audit the exact eight-way DomainSpecData factoring; --write creates it.

The original 128 checks are retained unchanged. This script never runs Lean.
Combined specifications import the earlier chunks containing their single
specifications, so no declaration is copied or checked twice.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('source/S12/DomainSpecData.lean')
HELPERS = Path('source/S12/DomainSpecDataChunks')
MANIFEST = ROOT/'evidence/domain-spec-data-factoring.json'
ASYNC = 'set_option Elab.async false\n'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def original_at(commit):
    prefix = subprocess.check_output(
        ['git', 'rev-parse', '--show-prefix'], cwd=ROOT, text=True).strip()
    return subprocess.check_output(
        ['git', 'show', f'{commit}:{prefix}{SOURCE.as_posix()}'], cwd=ROOT)


def split_original(original):
    text = original.decode()
    header, body = text.split('def singleSpec0 ', 1)
    declarations, trailer = ('def singleSpec0 '+body).split('#print axioms ', 1)
    trailer = '#print axioms '+trailer
    assert header == ('import S12.DomainSpecs\nnamespace S12\n'
                      'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n')
    assert trailer == ('#print axioms singleSpec0_checked\n'
                       '#print axioms combinedSpec0_checked\nend S12\n')
    lines = declarations.splitlines(keepends=True)
    assert len(lines) == 256, 'Expected exactly 128 definition/check pairs'
    names, pairs = [], []
    for i in range(0, len(lines), 2):
        definition, proof = lines[i:i+2]
        match = re.fullmatch(r'def ((single|combined)Spec\d+) : (Single|Combined)Spec := .*\n', definition)
        assert match, 'Unexpected original definition'
        name = match[1]
        assert match[2].capitalize() == match[3]
        assert proof == f'theorem {name}_checked : {name}.Check := by native_decide\n'
        assert name not in names
        references = set(re.findall(r'\b(?:single|combined)Spec\d+\b', definition))-{name}
        assert references <= set(names), 'Forward or undefined data dependency'
        names.append(name)
        pairs.append(definition+proof)
    assert names == [f'singleSpec{i}' for i in range(103)]+[f'combinedSpec{i}' for i in range(25)]
    return header, names, pairs, trailer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    commit = previous['original_commit'] if previous else subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    original = original_at(commit)
    header, names, pairs, trailer = split_original(original)
    owners = {name:i//16 for i, name in enumerate(names)}
    expected, modules = {}, []
    for group in range(8):
        path = HELPERS/f'Chunk{group:02}.lean'
        selected = pairs[group*16:(group+1)*16]
        references = set(re.findall(r'\b(?:single|combined)Spec\d+\b', ''.join(selected)))
        dependencies = sorted({owners[name] for name in references}-{group})
        assert all(dep < group for dep in dependencies)
        imports = ''.join(f'import S12.DomainSpecDataChunks.Chunk{dep:02}\n' for dep in dependencies)
        helper_header = 'import S12.DomainSpecs\n'+imports+header.removeprefix('import S12.DomainSpecs\n')+ASYNC
        contents = (helper_header+''.join(selected)+'end S12\n').encode()
        expected[path] = contents
        modules.append({'path':path.as_posix(), 'first_declaration':names[group*16],
            'last_declaration':names[(group+1)*16-1], 'definition_count':16,
            'native_check_count':16, 'earlier_helper_imports':dependencies,
            'sha256':sha(contents), 'header':helper_header})
    wrapper = ''.join(f'import S12.DomainSpecDataChunks.Chunk{i:02}\n' for i in range(8))
    wrapper += header.removeprefix('import S12.DomainSpecs\n')+ASYNC+trailer
    expected[SOURCE] = wrapper.encode()
    if args.write:
        assert (ROOT/SOURCE).read_bytes() in (original, expected[SOURCE]), \
            'Unexpected wrapper edits; refusing overwrite'
        for path, contents in expected.items():
            if path != SOURCE and (ROOT/path).exists():
                assert (ROOT/path).read_bytes() == contents, f'Unexpected helper edits: {path}'
        for path, contents in expected.items():
            (ROOT/path).parent.mkdir(parents=True, exist_ok=True)
            (ROOT/path).write_bytes(contents)
    for path, contents in expected.items():
        assert (ROOT/path).read_bytes() == contents, f'Factored source differs: {path}'
    assert set((ROOT/HELPERS).glob('*.lean')) == {ROOT/path for path in expected if path != SOURCE}
    # Reconstruct using the actual on-disk helper declarations, not generated
    # expected data; eliminate only the new imports, options and namespaces.
    reconstructed = []
    for item in modules:
        actual = (ROOT/item['path']).read_text()
        assert actual.startswith(item['header']) and actual.endswith('end S12\n')
        reconstructed.append(actual[len(item['header']):-len('end S12\n')])
    inverse = (header+''.join(reconstructed)+trailer).encode()
    assert inverse == original, 'Inverse reconstruction differs from original'
    native_count = sum(data.count(b'by native_decide') for data in expected.values())
    assert native_count == original.count(b'by native_decide') == 128
    report = {'original_commit':commit, 'original_path':SOURCE.as_posix(),
        'original_sha256':sha(original), 'inverse_sha256':sha(inverse),
        'inverse_matches_original':True, 'wrapper_sha256':sha(expected[SOURCE]),
        'helper_modules':[{k:v for k,v in item.items() if k != 'header'} for item in modules],
        'preserved_definitions':128, 'preserved_theorems':128,
        'preserved_native_sites':128, 'additional_native_sites':0,
        'added_lean_modules':8, 'public_declaration_bodies_byte_identical':True,
        'lean_replay_performed_by_this_script':False}
    if args.write:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(json.dumps(report, indent=2)+'\n')
    else:
        assert previous == report, 'Factoring manifest differs from source audit'
    print(json.dumps({k:v for k,v in report.items() if k != 'helper_modules'}))


if __name__ == '__main__':
    main()
