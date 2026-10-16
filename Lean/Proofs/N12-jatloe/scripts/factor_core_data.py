#!/usr/bin/env python3
"""Audit exact CoreData factoring into fourteen modules; --write creates it.

Preserves all 419 original native checks and the aggregate list. No Lean run.
Each helper imports only the factored domain chunks used by its declarations.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('source/S12/CoreData.lean')
HELPERS = Path('source/S12/CoreDataChunks')
MANIFEST = ROOT/'evidence/core-data-factoring.json'
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
    header, body = text.split('def coreProof0 ', 1)
    declarations, tail = ('def coreProof0 '+body).split('def coreProofs ', 1)
    tail = 'def coreProofs '+tail
    assert header == ('import S12.CoreExclusion\nimport S12.DomainSpecData\n'
                      'namespace S12\nset_option maxRecDepth 100000\n'
                      'set_option maxHeartbeats 0\n')
    assert tail.endswith('\nend S12\n') and len(tail.splitlines()) == 2
    assert tail.startswith('def coreProofs : List {w : CoreProof // w.Check} := [')
    lines = declarations.splitlines(keepends=True)
    assert len(lines) == 838, 'Expected exactly 419 definition/check pairs'
    pairs = []
    for i in range(419):
        definition, proof = lines[2*i:2*i+2]
        assert re.fullmatch(rf'def coreProof{i} : CoreProof := .*\n', definition)
        assert proof == f'theorem coreProof{i}_checked : coreProof{i}.Check := by native_decide\n'
        assert re.findall(r'\bcoreProof\d+\b', definition) == [f'coreProof{i}']
        pairs.append(definition+proof)
    assert re.findall(r'\bcoreProof\d+\b', tail) == [f'coreProof{i}' for i in range(419)]
    return header, pairs, tail


def domain_owners():
    manifest = json.loads((ROOT/'evidence/domain-spec-data-factoring.json').read_text())
    owners = {}
    for item in manifest['helper_modules']:
        path = ROOT/item['path']
        data = path.read_bytes()
        assert sha(data) == item['sha256'], f'Domain helper changed: {path}'
        module = 'S12.DomainSpecDataChunks.'+path.stem
        for name in re.findall(r'^def ((?:single|combined)Spec\d+) ', data.decode(), re.M):
            assert name not in owners
            owners[name] = module
    assert set(owners) == {f'singleSpec{i}' for i in range(103)} | \
        {f'combinedSpec{i}' for i in range(25)}
    return owners


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    commit = previous['original_commit'] if previous else subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    original = original_at(commit)
    header, pairs, tail = split_original(original)
    owners = domain_owners()
    settings = header.split('namespace S12\n', 1)[1]
    expected, modules = {}, []
    for group in range(14):
        path = HELPERS/f'Chunk{group:02}.lean'
        start, end = group*32, min((group+1)*32, 419)
        selected = ''.join(pairs[start:end])
        references = set(re.findall(r'\b(?:single|combined)Spec\d+\b', selected))
        dependencies = sorted({owners[name] for name in references})
        helper_header = 'import S12.CoreExclusion\n'
        helper_header += ''.join(f'import {dep}\n' for dep in dependencies)
        helper_header += 'namespace S12\n'+settings+ASYNC
        contents = (helper_header+selected+'end S12\n').encode()
        expected[path] = contents
        modules.append({'path':path.as_posix(), 'core_proof_start':start,
            'definition_count':end-start, 'native_check_count':end-start,
            'domain_helper_imports':dependencies, 'sha256':sha(contents),
            'header':helper_header})
    wrapper = ''.join(f'import S12.CoreDataChunks.Chunk{i:02}\n' for i in range(14))
    wrapper += 'namespace S12\n'+settings+ASYNC+tail
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
    reconstructed = []
    for item in modules:
        actual = (ROOT/item['path']).read_text()
        assert actual.startswith(item['header']) and actual.endswith('end S12\n')
        reconstructed.append(actual[len(item['header']):-len('end S12\n')])
    actual_wrapper = (ROOT/SOURCE).read_text()
    actual_tail = 'def coreProofs '+actual_wrapper.split('def coreProofs ', 1)[1]
    inverse = (header+''.join(reconstructed)+actual_tail).encode()
    assert inverse == original, 'Inverse reconstruction differs from original'
    native_count = sum(data.count(b'by native_decide') for data in expected.values())
    assert native_count == original.count(b'by native_decide') == 419
    report = {'original_commit':commit, 'original_path':SOURCE.as_posix(),
        'original_sha256':sha(original), 'inverse_sha256':sha(inverse),
        'inverse_matches_original':True, 'wrapper_sha256':sha(expected[SOURCE]),
        'helper_modules':[{k:v for k,v in item.items() if k != 'header'} for item in modules],
        'preserved_definitions':419, 'preserved_theorems':419,
        'preserved_native_sites':419, 'additional_native_sites':0,
        'added_lean_modules':14, 'public_declaration_bodies_byte_identical':True,
        'aggregate_list_byte_identical':True,
        'lean_replay_performed_by_this_script':False}
    if args.write:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(json.dumps(report, indent=2)+'\n')
    else:
        assert previous == report, 'Factoring manifest differs from source audit'
    print(json.dumps({k:v for k,v in report.items() if k != 'helper_modules'}))


if __name__ == '__main__':
    main()
