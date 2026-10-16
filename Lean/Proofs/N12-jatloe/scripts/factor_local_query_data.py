#!/usr/bin/env python3
"""Factor or audit the original LocalQueryData declarations byte for byte.

Default mode audits only. --write makes seven independent source modules and
an import wrapper; it does not run Lean or introduce certificate checks.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('source/S12/LocalQueryData.lean')
HELPERS = Path('source/S12/LocalQueryDataChunks')
MANIFEST = ROOT/'evidence/local-query-data-factoring.json'
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
    header, body = text.split('def localQuery0 ', 1)
    declarations, tail = ('def localQuery0 '+body).split('def localQueries ', 1)
    tail = 'def localQueries '+tail
    locals_, chunks, proofs = {}, {}, {}
    for line in declarations.splitlines(keepends=True):
        match = re.fullmatch(r'def localQuery(\d+) : LocalQuery := .*\n', line)
        if match:
            i = int(match[1])
            assert i not in locals_
            assert re.findall(r'\blocalQuery\d+\b', line) == [f'localQuery{i}']
            locals_[i] = line
            continue
        match = re.fullmatch(r'def queryChunk(\d+) : List LocalQuery := .*\n', line)
        if match:
            i = int(match[1])
            assert i not in chunks
            chunks[i] = line
            assert [int(x) for x in re.findall(r'\blocalQuery(\d+)\b', line)] == \
                list(range(50*i, min(50*(i+1), 1721)))
            continue
        match = re.fullmatch(r'theorem queryChunk(\d+)_checked : .* := by native_decide\n', line)
        assert match, 'Unexpected declaration in original data'
        i = int(match[1])
        assert i not in proofs
        proofs[i] = line
    assert sorted(locals_) == list(range(1721))
    assert sorted(chunks) == sorted(proofs) == list(range(35))
    assert ASYNC not in header
    return header, locals_, chunks, proofs, tail


def wrapper_declarations(tail):
    body, trailer = tail.split('#print axioms localQueries_checked\n', 1)
    assert trailer == 'end S12\n', 'Unexpected wrapper trailer'
    starts = list(re.finditer(r'^(?:private )?(?:def|theorem) (\w+)\b', body, re.M))
    assert starts and starts[0].start() == 0
    declarations = {}
    for i, match in enumerate(starts):
        name = match[1]
        assert name not in declarations
        block = body[match.start():(starts[i+1].start() if i+1 < len(starts) else len(body))]
        statement, proof = block.split(':=', 1)
        declarations[name] = (statement, proof)
    return declarations


def audit_wrapper(original_tail, actual_tail):
    original = wrapper_declarations(original_tail)
    actual = wrapper_declarations(actual_tail)
    extra = set(actual)-set(original)
    assert extra <= {'queryChecks_append'}, 'Unexpected added wrapper declaration'
    assert set(original) <= set(actual), 'Missing public wrapper declaration'
    changes = []
    for name, (statement, body) in original.items():
        new_statement, new_body = actual[name]
        assert statement == new_statement, f'Public declaration statement changed: {name}'
        if body != new_body:
            assert name in {'localQueries_length', 'localQueries_all_checked'}, \
                f'Unexpected wrapper body change: {name}'
            changes.append({'declaration':name, 'original_proof_sha256':sha(body.encode()),
                            'current_proof_sha256':sha(new_body.encode())})
    helpers = []
    for name in sorted(extra):
        statement, body = actual[name]
        assert statement.startswith('private theorem '), 'Wrapper helper must be private'
        helpers.append({'declaration':name, 'statement':statement.strip(),
                        'proof_sha256':sha(body.encode())})
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b', actual_tail), \
        'Unexpected admission or trust primitive in wrapper'
    return changes, helpers


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--record-wrapper-proof-changes', action='store_true',
        help='audit and record the two intentional wrapper proof repairs; never edit source')
    args = parser.parse_args()
    assert not (args.write and args.record_wrapper_proof_changes)
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    commit = previous['original_commit'] if previous else subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    original = original_at(commit)
    header, locals_, chunks, proofs, tail = split_original(original)
    expected = {}
    modules = []
    for group in range(7):
        path = HELPERS/f'Chunk{group:02}.lean'
        query_start, query_end = group*250, min((group+1)*250, 1721)
        chunk_start, chunk_end = group*5, (group+1)*5
        contents = header+ASYNC+''.join(locals_[i] for i in range(query_start, query_end))
        contents += ''.join(chunks[i]+proofs[i] for i in range(chunk_start, chunk_end))
        contents += 'end S12\n'
        expected[path] = contents.encode()
        modules.append({'path':path.as_posix(), 'local_query_start':query_start,
            'local_query_count':query_end-query_start, 'query_chunk_start':chunk_start,
            'query_chunk_count':5, 'sha256':sha(expected[path])})
    wrapper = ''.join(f'import S12.LocalQueryDataChunks.Chunk{i:02}\n' for i in range(7))
    wrapper += header.removeprefix('import S12.LocalQuery\n')+ASYNC+tail
    expected[SOURCE] = wrapper.encode()
    if args.write:
        current = (ROOT/SOURCE).read_bytes()
        assert current in (original, (header+ASYNC+original.decode()[len(header):]).encode(),
                           expected[SOURCE]), 'Unexpected source edits; refusing overwrite'
        for path, contents in expected.items():
            (ROOT/path).parent.mkdir(parents=True, exist_ok=True)
            (ROOT/path).write_bytes(contents)
    for path, contents in expected.items():
        if path == SOURCE:
            continue
        assert (ROOT/path).read_bytes() == contents, f'Factored source differs: {path}'
    assert set((ROOT/HELPERS).glob('*.lean')) == {ROOT/path for path in expected if path != SOURCE}
    # Invert the actual helpers, restore the original declaration ordering, and
    # require exact equality with the pinned pre-factor source, including tail.
    actual_locals, actual_chunks, actual_proofs = {}, {}, {}
    for item in modules:
        for line in (ROOT/item['path']).read_text().splitlines(keepends=True):
            for pattern, dest in ((r'def localQuery(\d+) ', actual_locals),
                                  (r'def queryChunk(\d+) ', actual_chunks),
                                  (r'theorem queryChunk(\d+)_checked ', actual_proofs)):
                match = re.match(pattern, line)
                if match:
                    assert int(match[1]) not in dest
                    dest[int(match[1])] = line
    actual_wrapper = (ROOT/SOURCE).read_bytes()
    wrapper_header = wrapper.split('def localQueries ', 1)[0]
    assert actual_wrapper.decode().startswith(wrapper_header), 'Unexpected wrapper header'
    actual_tail = actual_wrapper.decode()[len(wrapper_header):]
    proof_changes, added_helpers = audit_wrapper(tail, actual_tail)
    if not args.record_wrapper_proof_changes and not args.write:
        assert previous and previous['wrapper_sha256'] == sha(actual_wrapper), \
            'Wrapper changed since recorded audit'
    inverse = (header+''.join(actual_locals[i] for i in range(1721))+
        ''.join(actual_chunks[i]+actual_proofs[i] for i in range(35))+actual_tail).encode()
    original_data = ''.join(locals_[i] for i in range(1721))+\
        ''.join(chunks[i]+proofs[i] for i in range(35))
    reconstructed_data = ''.join(actual_locals[i] for i in range(1721))+\
        ''.join(actual_chunks[i]+actual_proofs[i] for i in range(35))
    assert reconstructed_data == original_data, 'Data inverse differs from original'
    if not proof_changes and not added_helpers:
        assert inverse == original, 'Inverse reconstruction differs from original'
    native_count = sum(data.count(b'by native_decide')
        for path, data in expected.items() if path != SOURCE)+actual_wrapper.count(b'by native_decide')
    assert native_count == original.count(b'by native_decide') == 35
    report = {'original_commit':commit, 'original_path':SOURCE.as_posix(),
        'original_sha256':sha(original), 'inverse_sha256':sha(inverse),
        'inverse_matches_original':inverse == original,
        'original_data_sha256':sha(original_data.encode()),
        'reconstructed_data_sha256':sha(reconstructed_data.encode()),
        'wrapper_sha256':sha(actual_wrapper), 'helper_modules':modules,
        'preserved_local_query_definitions':1721, 'preserved_native_sites':native_count,
        'additional_native_sites':0, 'added_lean_modules':7,
        'declaration_bodies_byte_identical':not proof_changes and not added_helpers,
        'data_declaration_bodies_byte_identical':True,
        'public_declaration_statements_byte_identical':True,
        'intentional_wrapper_proof_changes':proof_changes, 'added_private_helpers':added_helpers,
        'lean_replay_performed_by_this_script':False}
    if args.write or args.record_wrapper_proof_changes:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(json.dumps(report, indent=2)+'\n')
    else:
        assert previous == report, 'Factoring manifest differs from source audit'
    print(json.dumps({k:v for k,v in report.items() if k != 'helper_modules'}))


if __name__ == '__main__':
    main()
