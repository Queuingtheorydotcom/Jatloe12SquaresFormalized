#!/usr/bin/env python3
"""Extract exact C981 coverage data and audit one 32-front indexed pilot.

Default mode audits only; --write creates three data modules and one pilot.
No full witness tables are generated, and no Lean command is run. Original
prefix values and original step proof bodies are preserved.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import signal
import subprocess
import time

from factor_c981_allowed_data import DATA05, DATA_HEADER, DATA_IMPORT, END
from factor_c981_prefix_literals import audit_data_declaration

ROOT = Path(__file__).resolve().parents[1]
BASE = Path('Completion/Cases/C981/Coverage')
MANIFEST = ROOT/'evidence/c981-coverage-pilot.json'
PILOT = Path('Compact/Completion/C981/CoveragePilot/Step10First32.lean')
TOKEN = re.compile(r'∅|\{[0-9]+(?:,[0-9]+)*\}')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def original_at(commit, path):
    prefix = subprocess.check_output(
        ['git', 'rev-parse', '--show-prefix'], cwd=ROOT, text=True, timeout=2).strip()
    data = subprocess.check_output(
        ['git', 'show', f'{commit}:{prefix}{path.as_posix()}'], cwd=ROOT, timeout=2)
    assert len(data) < 300000, 'Input exceeds the fixed pilot input limit'
    return data


def parse_row(text):
    text = text.strip().removesuffix(',')
    assert text.startswith('[') and text.endswith(']')
    body = text[1:-1]
    terms = TOKEN.findall(body)
    assert ','.join(terms) == body, 'Unexpected literal syntax'
    values = []
    for term in terms:
        members = [] if term == '∅' else [int(x) for x in term[1:-1].split(',')]
        assert len(set(members)) == len(members)
        assert all(0 <= x < 20 for x in members)
        values.append(sum(1 << x for x in members))
    return tuple(values)


def main():
    started = time.monotonic()
    # Input sizes and row counts bound allocations; check the observed peak
    # below. macOS does not reliably support lowering RLIMIT_DATA. A hard
    # process-memory cap can additionally be provided by the external guard.
    # Each read-only Git subprocess also has its own two-second timeout.
    signal.alarm(10)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--record-data-factoring', action='store_true',
        help='audit ordered literal chunks and update only the manifest')
    args = parser.parse_args()
    assert not (args.write and args.record_data_factoring)
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    commit = previous['original_commit'] if previous else subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True, timeout=2).strip()
    expected, permitted_old, records, parsed = {}, {}, [], {}
    for n, count in [(9,2148), (10,3143)]:
        name = f'prefix{n:02}'
        source = BASE/f'Prefix{n:02}.lean'
        target = BASE/f'Data/Prefix{n:02}.lean'
        original = original_at(commit, source)
        header, rest = original.decode().split('def '+name+' ', 1)
        declaration, tail = ('def '+name+' '+rest).split(f'theorem step{n:02} ', 1)
        tail = f'theorem step{n:02} '+tail
        assert tail == (f'theorem step{n:02} : StepCheck prefix{n-1:02} allowed{n-5} {name} := by\n'
                        '  decide +kernel\n'+END)
        assert declaration.startswith(f'def {name} : List (List (Finset Nat)) := [\n')
        payload = declaration.split(':=', 1)[1].strip()
        assert payload.startswith('[') and payload.endswith(']')
        rows = [parse_row(row) for row in payload[1:-1].strip().splitlines()]
        assert len(rows) == count and all(len(row) == n for row in rows)
        parsed[name] = rows
        data_import = f'import Completion.Cases.C981.Coverage.Data.Prefix{n:02}\n'
        expected[target] = (DATA_HEADER+declaration+END).encode()
        expected[source] = (data_import+header+tail).encode()
        permitted_old[source] = original
        records.append({'source':source.as_posix(), 'data_module':target.as_posix(),
            'original_sha256':sha(original), 'declaration_sha256':sha(declaration.encode()),
            'row_count':count, 'header':header, 'data_import':data_import})
    allowed_source = BASE/'AllowedData.lean'
    allowed_original = original_at(commit, allowed_source)
    match = re.search(r'^def allowed5 : List \(Finset Nat\) := [^\n]+\n',
        allowed_original.decode(), re.M)
    assert match, 'Original allowed5 declaration missing'
    allowed_declaration = match[0]
    choices = parse_row(allowed_declaration.split(':=', 1)[1])
    assert len(choices) == 64
    expected[DATA05] = (DATA_HEADER+allowed_declaration+END).encode()
    old_header = allowed_original.decode().split('def allowed0 ', 1)[0]
    old_header = old_header.replace('import Compact.Bridge.CoverageReorder\n', '', 1)
    old_header = old_header.replace('open S12 N12Compact.PrefixCoverage\n', 'open S12\n', 1)
    proof = 'theorem allowed5_exact : domain5.allowed = allowed5 := by decide +kernel\n\n'
    owner = BASE/'Allowed/Owner05.lean'
    permitted_old[owner] = (old_header+allowed_declaration+proof+END).encode()
    expected[owner] = (DATA_IMPORT+old_header+proof+END).encode()
    # The untrusted proposal is independently checked by the Lean pilot. Use
    # exact tuples of twenty-bit masks here only to propose original indices.
    positions = {}
    for i, row in enumerate(parsed['prefix10']):
        positions.setdefault(row, i)
    indices = []
    for front in parsed['prefix09'][:32]:
        for choice in choices:
            if all(choice & previous == 0 for previous in front):
                indices.append(positions[front+(choice,)])
    assert indices == list(range(172)), 'Pilot indices differ; do not expand scope'
    expected[PILOT] = '''import Compact.Bridge.PrefixCoverageIndexed
import Completion.Cases.C981.Coverage.Data.Prefix09
import Completion.Cases.C981.Coverage.Data.Prefix10
import Completion.Cases.C981.Coverage.Data.Allowed05

/-! Only the first 32 incoming fronts of the original step10 are checked here.
All original allowed5 choices are checked against the first 172 target rows.
Ordinary list membership then lifts this result to the full target list.
This pilot does not establish step10, the preceding chain, or the whole case. -/
namespace S12Completion.C981.CoveragePilot
open N12Compact.PrefixCoverage S12Completion.C981.Coverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem step10First32_indexed :
    IndexedStepCheck (prefix09.take 32) allowed5 (prefix10.take 172) (List.range 172) := by
  decide +kernel

theorem step10First32 : StepCheck (prefix09.take 32) allowed5 prefix10 :=
  stepCheck_mono_after
    (indexedStepCheck_sound (prefix09.take 32) allowed5 (prefix10.take 172)
      (List.range 172) step10First32_indexed)
    (fun _ member => List.mem_of_mem_take member)

#print axioms step10First32
end S12Completion.C981.CoveragePilot
'''.encode()
    if args.write:
        # Validate every existing file before changing any source.
        for path, data in expected.items():
            if (ROOT/path).exists():
                assert (ROOT/path).read_bytes() in (data, permitted_old.get(path)), \
                    f'Unexpected source edits; refusing overwrite: {path}'
        for path, data in expected.items():
            (ROOT/path).parent.mkdir(parents=True, exist_ok=True)
            (ROOT/path).write_bytes(data)
    prefix_data_paths = {Path(item['data_module']) for item in records}
    representation_changes = []
    for path, data in expected.items():
        if path in prefix_data_paths:
            declaration = data.decode()[len(DATA_HEADER):-len(END)]
            audit_data_declaration(path,declaration)
            if (ROOT/path).read_bytes() != data:
                representation_changes.append(path.as_posix())
        else:
            assert (ROOT/path).read_bytes() == data, f'Extracted source differs: {path}'
    for item in records:
        declaration = audit_data_declaration(item['data_module'],
            expected[Path(item['data_module'])].decode()[len(DATA_HEADER):-len(END)])
        wrapper = (ROOT/item['source']).read_text()
        wrapper_header = item['data_import']+item['header']
        assert wrapper.startswith(wrapper_header)
        inverse = (item['header']+declaration+wrapper[len(wrapper_header):]).encode()
        assert sha(inverse) == item['original_sha256'], 'Prefix inverse differs'
        item['inverse_sha256'] = sha(inverse)
    actual_allowed = (ROOT/DATA05).read_text()[len(DATA_HEADER):-len(END)]
    assert actual_allowed == allowed_declaration, 'Allowed data inverse differs'
    report = {'original_commit':commit,
        'prefixes':[{k:v for k,v in item.items() if k not in {'header','data_import'}} for item in records],
        'original_allowed_data_sha256':sha(allowed_original),
        'allowed5_declaration_sha256':sha(allowed_declaration.encode()),
        'files':[{'path':path.as_posix(), 'sha256':sha((ROOT/path).read_bytes())} for path in expected],
        'pilot_front_count':32, 'choice_count':64, 'candidate_pairs':2048,
        'compatible_extensions':172, 'witness':'List.range 172',
        'checked_target_slice':{'original':'prefix10','start':0,'count':172},
        'full_target_count':3143, 'lift_to_full_target':'stepCheck_mono_after / List.mem_of_mem_take',
        'added_lean_modules':4, 'additional_native_sites':0,
        'original_declarations_and_proofs_byte_identical':not representation_changes,
        'prefix_data_representation_changes':representation_changes,
        'original_prefix_values_and_proof_bodies_preserved':True,
        'lean_replay_performed_by_this_script':False}
    if args.write or args.record_data_factoring:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(json.dumps(report, indent=2)+'\n')
    else:
        assert previous == report, 'Pilot manifest differs from source audit'
    elapsed = time.monotonic()-started
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1048576
    assert elapsed < 10 and peak < 128, 'Pilot generator exceeded resource budget'
    signal.alarm(0)
    print(json.dumps({'audit':'passed', 'added_lean_modules':4, 'candidate_pairs':2048,
        'compatible_extensions':172, 'witness':'List.range 172',
        'elapsed_seconds':round(elapsed,4), 'max_rss_MiB':round(peak,2),
        'lean_replay_performed':False}))


if __name__ == '__main__':
    main()
