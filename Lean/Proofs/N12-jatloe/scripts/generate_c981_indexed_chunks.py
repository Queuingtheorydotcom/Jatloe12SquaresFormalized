#!/usr/bin/env python3
"""Plan, emit one chunk, or audit exact C981 indexed coverage certificates.

The default only reports a module budget. No batch mode exists. Explicit
actions may prepare four missing data modules, emit ONE checked chunk, or
emit ONE assembly after every chunk for that step exists. These are source
operations, never Lean runs. The original step10/11/12 proofs stay untouched.
Each bounded checker uses only its exact contiguous target interval; ordinary
take/drop membership lifts the result to the full original target list.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import signal
import subprocess
import sys

from factor_c981_allowed_data import DATA_HEADER, END
from factor_c981_coverage_pilot import parse_row
from factor_c981_prefix_literals import audit_data_declaration

ROOT = Path(__file__).resolve().parents[1]
BASE = Path('Completion/Cases/C981/Coverage')
OUTPUT = Path('Compact/Completion/C981/IndexedCoverage')
MANIFEST = ROOT/'evidence/c981-indexed-coverage-chunks.json'
PILOT_MANIFEST = ROOT/'evidence/c981-coverage-pilot.json'
PILOT_MODULE = 'Compact.Completion.C981.CoveragePilot.Step10First32'
COUNTS = {9:2148, 10:3143, 11:1668, 12:221}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source_module(path):
    return path.with_suffix('').as_posix().replace('/', '.')


def git_source(commit, path):
    prefix = subprocess.check_output(
        ['git', 'rev-parse', '--show-prefix'], cwd=ROOT, text=True, timeout=2).strip()
    data = subprocess.check_output(
        ['git', 'show', f'{commit}:{prefix}{path.as_posix()}'], cwd=ROOT, timeout=2)
    assert len(data) < 300000, f'Unexpectedly large pinned source: {path}'
    return data.decode()


def load_tables(commit):
    """Read pinned source and prepare exact relocations, but do not write."""
    tables, expected, old, audits = {}, {}, {}, []
    for number in range(9,13):
        source = BASE/f'Prefix{number:02}.lean'
        target = BASE/f'Data/Prefix{number:02}.lean'
        original = git_source(commit, source)
        header, rest = original.split(f'def prefix{number:02} ', 1)
        declaration, tail = (f'def prefix{number:02} '+rest).split(f'theorem step{number:02} ', 1)
        tail = f'theorem step{number:02} '+tail
        payload = declaration.split(':=',1)[1].strip()
        assert payload.startswith('[\n') and payload.endswith(']')
        rows = [parse_row(row) for row in payload[1:-1].strip().splitlines()]
        assert len(rows) == COUNTS[number] and all(len(row) == number for row in rows)
        tables[f'prefix{number:02}'] = rows
        extra_import = f'import {source_module(target)}\n'
        expected[target] = (DATA_HEADER+declaration+END).encode()
        expected[source] = (extra_import+header+tail).encode()
        old[source] = original.encode()
        audits.append({'source':source, 'data':target, 'header':header,
            'extra_import':extra_import, 'original_sha256':sha(original.encode()),
            'declaration_sha256':sha(declaration.encode())})
    original_allowed = git_source(commit, BASE/'AllowedData.lean')
    helper_header = original_allowed.split('def allowed0 ',1)[0]
    helper_header = helper_header.replace('import Compact.Bridge.CoverageReorder\n','',1)
    helper_header = helper_header.replace('open S12 N12Compact.PrefixCoverage\n','open S12\n',1)
    for owner in (5,6,7):
        declaration = re.search(rf'^def allowed{owner} : List \(Finset Nat\) := [^\n]+\n',
            original_allowed,re.M)[0]
        choices = parse_row(declaration.split(':=',1)[1])
        assert len(choices) == 64
        tables[f'allowed{owner}'] = choices
        target = BASE/f'Data/Allowed{owner:02}.lean'
        source = BASE/f'Allowed/Owner{owner:02}.lean'
        proof = f'theorem allowed{owner}_exact : domain{owner}.allowed = allowed{owner} := by decide +kernel\n\n'
        extra_import = f'import {source_module(target)}\n'
        expected[target] = (DATA_HEADER+declaration+END).encode()
        expected[source] = (extra_import+helper_header+proof+END).encode()
        old[source] = (helper_header+declaration+proof+END).encode()
        audits.append({'source':source, 'data':target, 'header':helper_header,
            'extra_import':extra_import, 'original_sha256':sha(old[source]),
            'declaration_sha256':sha(declaration.encode())})
    return tables,expected,old,audits


def table_audit(expected, old, audits, require_all=False):
    """Audit actual bytes and inverse ordering, including untouched proof bodies."""
    records = []
    for item in audits:
        source, data = item['source'], item['data']
        if not (ROOT/data).exists():
            assert not require_all, f'Data module missing: {data}'
            assert (ROOT/source).read_bytes() == old[source], f'Unfactored source changed: {source}'
            continue
        literal = expected[data].decode()[len(DATA_HEADER):-len(END)]
        if data.stem.startswith('Prefix'):
            declaration = audit_data_declaration(data,literal)
        else:
            assert (ROOT/data).read_bytes() == expected[data], f'Data changed: {data}'
            declaration = literal
        assert (ROOT/source).read_bytes() == expected[source], f'Original proof wrapper changed: {source}'
        wrapper_header = item['extra_import']+item['header']
        wrapper = (ROOT/source).read_text()
        inverse = (item['header']+declaration+wrapper[len(wrapper_header):]).encode()
        assert sha(inverse) == item['original_sha256'], f'Inverse reconstruction failed: {source}'
        records.append({'source':source.as_posix(), 'data':data.as_posix(),
            'original_sha256':item['original_sha256'], 'inverse_sha256':sha(inverse),
            'declaration_sha256':item['declaration_sha256']})
    return records


def propose_indices(before, choices, after):
    """One bounded slice only; the Lean checker must verify the proposal."""
    assert len(before) <= 256 and len(choices) <= 64 and len(after) <= 3143
    positions = {}
    for i,row in enumerate(after):
        positions.setdefault(row,i)
    indices = []
    for front in before:
        for choice in choices:
            if all(choice & previous == 0 for previous in front):
                indices.append(positions[front+(choice,)])
    return indices


def witness_expression(indices):
    if not indices:
        return '[]'
    if indices == list(range(indices[0], indices[0]+len(indices))):
        if indices[0] == 0:
            return f'List.range {len(indices)}'
        return f'(List.range {len(indices)}).map (fun i => i + {indices[0]})'
    return '['+','.join(map(str,indices))+']'


def exact_target_slice(indices):
    """Require every visited target, in order, to form one exact interval.

    This proposal is untrusted: Lean still checks every original front/choice
    pair and verifies each compatible extension against its actual slice row.
    Empty proposals use the empty initial slice, not a skipped traversal.
    """
    start = indices[0] if indices else 0
    count = len(indices)
    assert start >= 0 and indices == list(range(start,start+count)), \
        'Compatible target indices are not one ordered contiguous interval'
    return start,count,list(range(count))


def shape(step,size,chunk):
    total = math.ceil(COUNTS[step-1]/size)
    assert 0 <= chunk < total
    offset = size*chunk
    front = f'(prefix{step-1:02}.drop {offset})'
    # The final certificate checks the WHOLE remaining suffix. Assembly thus
    # needs no trusted row count or separate numerical length/drop equality.
    if chunk+1 < total:
        front = f'({front}.take {size})'
    return total,offset,front


def chunk_path(step,chunk):
    return OUTPUT/f'Step{step:02}/Chunk{chunk:03}.lean'


def chunk_name(step,chunk):
    return f'S12Completion.C981.IndexedCoverage.Step{step:02}.Chunk{chunk:03}.checked'


def is_pilot(step,size,chunk,decision_size=None):
    return decision_size is None and (step,size,chunk) == (10,32,0)


def render_chunk(tables,step,size,chunk,decision_size=None):
    if decision_size is not None:
        return render_split_chunk(tables,step,size,chunk,decision_size)
    total,offset,front = shape(step,size,chunk)
    rows = tables[f'prefix{step-1:02}'][offset:]
    if chunk+1 < total:
        rows = rows[:size]
    indices = propose_indices(rows,tables[f'allowed{step-5}'],tables[f'prefix{step:02}'])
    start,count,local_indices = exact_target_slice(indices)
    target = f'((prefix{step:02}.drop {start}).take {count})'
    witness = witness_expression(local_indices)
    imports = ['Compact.Bridge.PrefixCoverageIndexed',
        f'Completion.Cases.C981.Coverage.Data.Prefix{step-1:02}',
        f'Completion.Cases.C981.Coverage.Data.Prefix{step:02}',
        f'Completion.Cases.C981.Coverage.Data.Allowed{step-5:02}']
    code = ''.join(f'import {module}\n' for module in imports)
    code += f'''\nnamespace S12Completion.C981.IndexedCoverage.Step{step:02}.Chunk{chunk:03}
open N12Compact.PrefixCoverage S12Completion.C981.Coverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def indices : List Nat := {witness}

theorem indexed : IndexedStepCheck {front} allowed{step-5} {target} indices := by
  decide +kernel

theorem checked : StepCheck {front} allowed{step-5} prefix{step:02} :=
  stepCheck_after_slice {start} {count}
    (indexedStepCheck_sound {front} allowed{step-5} {target} indices indexed)

#print axioms checked
end S12Completion.C981.IndexedCoverage.Step{step:02}.Chunk{chunk:03}
'''
    return code.encode(),{'step':step,'chunk':chunk,'front_offset':offset,
        'front_count':len(rows),'checks_entire_remaining_suffix':chunk+1==total,
        'candidate_pairs':len(rows)*64,'index_count':len(indices),
        'target_slice_start':start,'target_slice_count':count,
        'target_slice_is_exact_ordered_compatible_interval':True,
        'indices_sha256':sha(json.dumps(indices,separators=(',',':')).encode()),
        'local_indices_sha256':sha(json.dumps(local_indices,separators=(',',':')).encode())}


def render_split_chunk(tables,step,size,chunk,decision_size):
    """Several bounded decisions inside ONE module; no length fact is trusted.

    The last decision checks the entire remaining front suffix. Structural
    take/drop composition therefore covers the exact original chunk even if
    an untrusted generator misreports row counts.
    """
    assert 1 <= decision_size <= size
    total,offset,front = shape(step,size,chunk)
    rows = tables[f'prefix{step-1:02}'][offset:]
    if chunk+1 < total:
        rows = rows[:size]
    decisions = max(1,math.ceil(len(rows)/decision_size))
    imports = ['Compact.Bridge.PrefixCoverageIndexed','Compact.Bridge.PrefixCoverageChunks',
        f'Completion.Cases.C981.Coverage.Data.Prefix{step-1:02}',
        f'Completion.Cases.C981.Coverage.Data.Prefix{step:02}',
        f'Completion.Cases.C981.Coverage.Data.Allowed{step-5:02}']
    code = ''.join(f'import {module}\n' for module in imports)
    code += f'''\nnamespace S12Completion.C981.IndexedCoverage.Step{step:02}.Chunk{chunk:03}
open N12Compact.PrefixCoverage S12Completion.C981.Coverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
'''
    records = []
    for part in range(decisions):
        local_offset = part*decision_size
        part_rows = rows[local_offset:]
        part_front = f'({front}.drop {local_offset})'
        if part+1 < decisions:
            part_rows = part_rows[:decision_size]
            part_front = f'({part_front}.take {decision_size})'
        indices = propose_indices(part_rows,tables[f'allowed{step-5}'],tables[f'prefix{step:02}'])
        start,count,local_indices = exact_target_slice(indices)
        target = f'((prefix{step:02}.drop {start}).take {count})'
        code += f'''
def indices{part} : List Nat := {witness_expression(local_indices)}

theorem indexed{part} : IndexedStepCheck {part_front} allowed{step-5} {target} indices{part} := by
  decide +kernel

theorem checked{part} : StepCheck {part_front} allowed{step-5} prefix{step:02} :=
  stepCheck_after_slice {start} {count}
    (indexedStepCheck_sound {part_front} allowed{step-5} {target} indices{part} indexed{part})
'''
        records.append({'part':part,'front_offset_in_chunk':local_offset,
            'front_count':len(part_rows),'checks_entire_remaining_suffix':part+1==decisions,
            'candidate_pairs':len(part_rows)*len(tables[f'allowed{step-5}']),
            'target_slice_start':start,'target_slice_count':count,
            'target_slice_is_exact_ordered_compatible_interval':True,
            'indices_sha256':sha(json.dumps(indices,separators=(',',':')).encode()),
            'local_indices_sha256':sha(json.dumps(local_indices,separators=(',',':')).encode())})
    code += f'\ntheorem checked : StepCheck {front} allowed{step-5} prefix{step:02} := by\n'
    for part in reversed(range(decisions)):
        goal = f'StepCheck ({front}.drop {part*decision_size}) allowed{step-5} prefix{step:02}'
        if part+1 == decisions:
            code += f'  have tail{part} : {goal} := checked{part}\n'
        else:
            code += f'  have tail{part} : {goal} := by\n'
            code += f'    apply takeDropStepCheck {decision_size}\n'
            code += f'    · exact checked{part}\n'
            code += f'    · simpa only [List.drop_drop] using tail{part+1}\n'
    code += f'''  simpa only [List.drop_zero] using tail0

#print axioms checked
end S12Completion.C981.IndexedCoverage.Step{step:02}.Chunk{chunk:03}
'''
    return code.encode(),{'step':step,'chunk':chunk,'front_offset':offset,
        'front_count':len(rows),'checks_entire_remaining_suffix':chunk+1==total,
        'fronts_per_decision':decision_size,'decisions':records}


def render_assembly(step,size,decision_size=None):
    total = math.ceil(COUNTS[step-1]/size)
    code = 'import Compact.Bridge.PrefixCoverageChunks\n'
    for chunk in range(total):
        module = PILOT_MODULE if is_pilot(step,size,chunk,decision_size) else source_module(chunk_path(step,chunk))
        code += f'import {module}\n'
    code += f'''\nnamespace S12Completion.C981.IndexedCoverage.Step{step:02}
open N12Compact.PrefixCoverage S12Completion.C981.Coverage
set_option Elab.async false
set_option maxRecDepth 100000

theorem complete : StepCheck prefix{step-1:02} allowed{step-5} prefix{step:02} := by
'''
    for chunk in reversed(range(total)):
        _,offset,front = shape(step,size,chunk)
        goal = f'StepCheck (prefix{step-1:02}.drop {offset}) allowed{step-5} prefix{step:02}'
        proof = chunk_name(step,chunk)
        if is_pilot(step,size,chunk,decision_size):
            proof = 'S12Completion.C981.CoveragePilot.step10First32'
        if chunk+1 == total:
            code += f'  have tail{chunk} : {goal} := {proof}\n'
        else:
            code += f'  have tail{chunk} : {goal} := by\n'
            code += f'    apply takeDropStepCheck {size}\n'
            code += f'    · simpa only [List.drop_zero] using {proof}\n'
            code += f'    · simpa only [List.drop_drop] using tail{chunk+1}\n'
    code += f'''  simpa only [List.drop_zero] using tail0

#print axioms complete
end S12Completion.C981.IndexedCoverage.Step{step:02}
'''
    return code.encode()


def write_checked(path,data):
    if (ROOT/path).exists():
        assert (ROOT/path).read_bytes() == data, f'Refusing to replace modified file: {path}'
    (ROOT/path).parent.mkdir(parents=True,exist_ok=True)
    (ROOT/path).write_bytes(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--action',choices=['plan','prepare-data','emit-chunk','assemble','audit'],default='plan')
    parser.add_argument('--fronts-per-chunk',type=int,default=32)
    parser.add_argument('--fronts-per-decision',type=int,
        help='split one chunk into smaller decisions within the same Lean module')
    parser.add_argument('--baseline-modules',type=int,required=True,
        help='fresh conservative selected whole-proof census before this campaign')
    parser.add_argument('--step',type=int,choices=[10,11,12])
    parser.add_argument('--chunk',type=int)
    args = parser.parse_args()
    size = args.fronts_per_chunk
    decision_size = args.fronts_per_decision
    assert 1 <= size <= 256 and args.baseline_modules > 0
    assert decision_size is None or 1 <= decision_size <= size
    counts = {step:math.ceil(COUNTS[step-1]/size) for step in (10,11,12)}
    reuse_pilot = decision_size is None and size == 32
    new_checks = sum(counts.values())-(1 if reuse_pilot else 0)
    forecast = args.baseline_modules+new_checks+4+3
    plan = {'chunks_per_step':counts,'reuse_existing_pilot':reuse_pilot,
        'fronts_per_decision':decision_size,
        'new_check_modules':new_checks,'new_data_modules':4,'new_assembly_modules':3,
        'projected_selected_modules':forecast,'preferred_module_limit':8000,
        'future_other_work_included':False,'lean_replay_performed':False}
    assert forecast <= 8000, f'Preferred whole-proof module budget exceeded: {forecast}'
    if args.action == 'plan':
        print(json.dumps(plan)); return
    # Bounded source work; never a batch or a Lean subprocess.
    signal.alarm(10)
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    pilot = json.loads(PILOT_MANIFEST.read_text())
    commit = pilot['original_commit']
    if previous:
        assert (previous['original_commit'],previous['fronts_per_chunk']) == (commit,size), \
            'Existing campaign differs; do not mix chunk sizes or baselines'
        assert previous.get('fronts_per_decision') == decision_size, 'Decision size differs'
    tables,expected,old,audits = load_tables(commit)
    table_audit(expected,old,audits)
    report = previous or {'original_commit':commit,'fronts_per_chunk':size,
        'fronts_per_decision':decision_size,
        'baseline_modules':args.baseline_modules,'plan':plan,'files':[]}
    if args.action == 'prepare-data':
        missing = [item for item in audits if not (ROOT/item['data']).exists()]
        assert len(missing) <= 4
        # All current files were checked above; preserve the exact literal and
        # original proof. The data split creates no new checks.
        for item in missing:
            write_checked(item['data'],expected[item['data']])
            (ROOT/item['source']).write_bytes(expected[item['source']])
        report['table_audits'] = table_audit(expected,old,audits,require_all=True)
        subprocess.run([sys.executable,'-B',str(ROOT/'scripts/factor_c981_allowed_data.py'),
            '--record-data-relocations'],cwd=ROOT,check=True,timeout=2,
            stdout=subprocess.DEVNULL)
    elif args.action in ('emit-chunk','assemble'):
        assert args.step is not None, '--step is required'
        step = args.step
        required = [BASE/f'Data/Prefix{step-1:02}.lean',BASE/f'Data/Prefix{step:02}.lean',
            BASE/f'Data/Allowed{step-5:02}.lean']
        assert all((ROOT/path).exists() for path in required), 'Prepare exact data modules first'
        if args.action == 'emit-chunk':
            assert args.chunk is not None, '--chunk is required'
            assert not is_pilot(step,size,args.chunk,decision_size), 'Reuse the existing pilot source for this slice'
            data,details = render_chunk(tables,step,size,args.chunk,decision_size)
            path = chunk_path(step,args.chunk)
        else:
            for chunk in range(counts[step]):
                if is_pilot(step,size,chunk,decision_size):
                    continue
                data,_ = render_chunk(tables,step,size,chunk,decision_size)
                assert (ROOT/chunk_path(step,chunk)).read_bytes() == data, 'Missing or changed chunk'
            data,details = render_assembly(step,size,decision_size),{'step':step,'assembly':True}
            path = OUTPUT/f'Step{step:02}.lean'
        write_checked(path,data)
        entry = {'path':path.as_posix(),'sha256':sha(data),**details}
        report['files'] = [x for x in report['files'] if x['path'] != entry['path']]+[entry]
        report['table_audits'] = table_audit(expected,old,audits)
    else:
        assert previous, 'No emitted campaign to audit'
        for entry in report['files']:
            if entry.get('assembly'):
                data = render_assembly(entry['step'],size,decision_size)
            else:
                data,details = render_chunk(tables,entry['step'],size,entry['chunk'],decision_size)
                assert all(entry[key] == value for key,value in details.items())
            assert sha(data) == entry['sha256']
            assert (ROOT/entry['path']).read_bytes() == data
        assert report['table_audits'] == table_audit(expected,old,audits)
    if args.action != 'audit':
        MANIFEST.parent.mkdir(parents=True,exist_ok=True)
        MANIFEST.write_text(json.dumps(report,indent=2)+'\n')
    signal.alarm(0)
    print(json.dumps({'action':args.action,'files_in_campaign':len(report['files']),**plan}))


if __name__ == '__main__':
    main()
