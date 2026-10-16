#!/usr/bin/env python3
"""Factor/audit twelve independent C981 allowed-list equalities, without Lean.

The default is a read-only inverse audit. --write emits one module per original
definition/equality pair and preserves the aggregate wrapper's public bodies.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('Completion/Cases/C981/Coverage/AllowedData.lean')
HELPERS = Path('Completion/Cases/C981/Coverage/Allowed')
MANIFEST = ROOT/'evidence/c981-allowed-data-factoring.json'
DOMAIN_IMPORT = 'import Completion.Cases.C981.OwnershipDomains\n'
REORDER_IMPORT = 'import Compact.Bridge.CoverageReorder\n'
END = 'end S12Completion.C981.Coverage\n'
DATA05 = Path('Completion/Cases/C981/Coverage/Data/Allowed05.lean')
DATA_IMPORT = 'import Completion.Cases.C981.Coverage.Data.Allowed05\n'
DATA_HEADER = ('import Mathlib.Data.Finset.Insert\n\n'
    'namespace S12Completion.C981.Coverage\nset_option Elab.async false\n'
    'set_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n\n')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--record-data-relocations', action='store_true',
        help='audit moved allowed literals and update only the manifest')
    args = parser.parse_args()
    assert not (args.write and args.record_data_relocations)
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    commit = previous['original_commit'] if previous else subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    prefix = subprocess.check_output(
        ['git', 'rev-parse', '--show-prefix'], cwd=ROOT, text=True).strip()
    original = subprocess.check_output(
        ['git', 'show', f'{commit}:{prefix}{SOURCE.as_posix()}'], cwd=ROOT)
    text = original.decode()
    header, rest = text.split('def allowed0 ', 1)
    declarations, tail = ('def allowed0 '+rest).split('def literalChoices ', 1)
    tail = 'def literalChoices '+tail
    starts = list(re.finditer(r'^def allowed(\d+) ', declarations, re.M))
    assert [int(m[1]) for m in starts] == list(range(12))
    blocks = [declarations[m.start():(starts[i+1].start() if i < 11 else len(declarations))]
        for i, m in enumerate(starts)]
    for i, block in enumerate(blocks):
        assert re.fullmatch(
            rf'def allowed{i} : List \(Finset Nat\) := [^\n]+\n'
            rf'theorem allowed{i}_exact : domain{i}\.allowed = allowed{i} := by decide \+kernel\n\n',
            block), f'Unexpected original owner block {i}'
    assert header.startswith(DOMAIN_IMPORT+REORDER_IMPORT)
    assert 'set_option Elab.async false\n' in header
    helper_header = header.replace(REORDER_IMPORT, '', 1).replace(
        'open S12 N12Compact.PrefixCoverage\n', 'open S12\n', 1)
    expected = {HELPERS/f'Owner{i:02}.lean':(helper_header+block+END).encode()
        for i, block in enumerate(blocks)}
    data_relocations = []
    owner_headers = [helper_header]*12
    moved_data = {}
    for i in range(12):
        data_path = Path(f'Completion/Cases/C981/Coverage/Data/Allowed{i:02}.lean')
        if not (ROOT/data_path).exists():
            continue
        definition, proof = blocks[i].split('\ntheorem ', 1)
        definition += '\n'
        expected_data = (DATA_HEADER+definition+END).encode()
        assert (ROOT/data_path).read_bytes() == expected_data, f'Moved allowed{i} literal differs'
        owner_headers[i] = f'import Completion.Cases.C981.Coverage.Data.Allowed{i:02}\n'+helper_header
        expected[HELPERS/f'Owner{i:02}.lean'] = (owner_headers[i]+'theorem '+proof+END).encode()
        moved_data[i] = data_path
        data_relocations.append({'path':data_path.as_posix(), 'declaration':f'allowed{i}',
            'sha256':sha(expected_data), 'declaration_sha256':sha(definition.encode())})
    imports = ''.join(f'import Completion.Cases.C981.Coverage.Allowed.Owner{i:02}\n'
        for i in range(12))
    wrapper_header = imports+header.removeprefix(DOMAIN_IMPORT)
    expected[SOURCE] = (wrapper_header+tail).encode()
    if args.write:
        assert (ROOT/SOURCE).read_bytes() in (original, expected[SOURCE]), \
            'Unexpected AllowedData edits; refusing overwrite'
        for path, contents in expected.items():
            (ROOT/path).parent.mkdir(parents=True, exist_ok=True)
            (ROOT/path).write_bytes(contents)
    for path, contents in expected.items():
        assert (ROOT/path).read_bytes() == contents, f'Factored source differs: {path}'
    assert set((ROOT/HELPERS).glob('*.lean')) == {ROOT/path for path in expected if path != SOURCE}
    actual_blocks = []
    for i in range(12):
        actual = (ROOT/HELPERS/f'Owner{i:02}.lean').read_text()
        assert actual.startswith(owner_headers[i]) and actual.endswith(END)
        block = actual[len(owner_headers[i]):-len(END)]
        if i in moved_data:
            data = (ROOT/moved_data[i]).read_text()
            block = data[len(DATA_HEADER):-len(END)]+block
        actual_blocks.append(block)
    actual_wrapper = (ROOT/SOURCE).read_text()
    assert actual_wrapper.startswith(wrapper_header)
    inverse = (header+''.join(actual_blocks)+actual_wrapper[len(wrapper_header):]).encode()
    assert inverse == original, 'Inverse differs from pinned original source'
    assert sum(data.count(b'decide +kernel') for data in expected.values()) == 12
    assert sum(data.count(b'native_decide') for data in expected.values()) == 0
    report = {'original_commit':commit, 'original_path':SOURCE.as_posix(),
        'original_sha256':sha(original), 'inverse_sha256':sha(inverse),
        'helper_modules':[{'path':path.as_posix(), 'sha256':sha(contents)}
            for path, contents in expected.items() if path != SOURCE],
        'wrapper_sha256':sha(expected[SOURCE]), 'added_lean_modules':12,
        'data_relocations':data_relocations,
        'relocated_data_modules_counted_in':('evidence/c981-coverage-pilot.json' if
            set(moved_data) <= {5} else ['evidence/c981-coverage-pilot.json',
                                      'evidence/c981-indexed-coverage-chunks.json']),
        'preserved_kernel_decisions':12, 'additional_native_sites':0,
        'public_declaration_bodies_byte_identical':True,
        'lean_replay_performed_by_this_script':False}
    if args.write or args.record_data_relocations:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(json.dumps(report, indent=2)+'\n')
    else:
        assert previous == report, 'Factoring manifest differs from source audit'
    print(json.dumps({k:v for k,v in report.items() if k != 'helper_modules'}))


if __name__ == '__main__':
    main()
