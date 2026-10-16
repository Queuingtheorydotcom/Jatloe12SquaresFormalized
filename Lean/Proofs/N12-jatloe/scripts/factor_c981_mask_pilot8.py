#!/usr/bin/env python3
"""Emit/audit one integer-coded eight-front pilot with exact correspondences.

Five reusable helpers prove 15 individual decoder identities each. The pilot
uses ordinary map rewrites to connect all original data, then checks every
front/choice pair using integer masks. This script never invokes Lean.
"""
import argparse
import json
from pathlib import Path
import resource
import signal
import time

from generate_c981_indexed_chunks import (
    exact_target_slice, load_tables, parse_row, propose_indices, sha, table_audit,
)

ROOT = Path(__file__).resolve().parents[1]
BASE = Path('Compact/Completion/C981/CoverageMasks')
PILOT = Path('Compact/Completion/C981/CoveragePilot/Step10Masks08.lean')
MANIFEST = ROOT/'evidence/c981-mask-pilot8.json'
IDENTITY_NS = 'S12Completion.C981.Coverage.MaskIdentities'


def literal(mask):
    assert 0 <= mask < 2**20
    return '{'+','.join(str(i) for i in range(20) if mask & (1<<i))+'}' if mask else '∅'


def rows_literal(rows,term=str,indent=''):
    return '[\n'+''.join(indent+'  ['+','.join(term(mask) for mask in row)+'],\n' for row in rows)+indent+']'


def module(path):
    return path.with_suffix('').as_posix().replace('/','.')


def main():
    started = time.monotonic()
    signal.alarm(10)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    original = json.loads((ROOT/'evidence/c981-coverage-pilot.json').read_text())
    commit = original['original_commit']
    tables,expected,old,audits = load_tables(commit)
    records = table_audit(expected,old,audits)
    records = [r for r in records if r['data'].endswith(('Prefix09.lean','Prefix10.lean','Allowed05.lean'))]
    before,choices = tables['prefix09'][:8],tables['allowed5']
    global_indices = propose_indices(before,choices,tables['prefix10'])
    start,count,indices = exact_target_slice(global_indices)
    assert (start,count,indices) == (0,46,list(range(46))), 'Pilot scope changed'
    after = tables['prefix10'][:46]
    pool = json.loads((ROOT/'evidence/c981-prefix-finset-pool.json').read_text())
    names = {parse_row('['+item['literal']+']')[0]:item['name'] for item in pool['constants']}
    assert all(mask in names for row in before+after for mask in row)
    masks = sorted(set(choices)|{mask for row in before+after for mask in row})
    assert len(masks) == 75
    for mask in masks:
        assert parse_row('['+literal(mask)+']') == (mask,), 'Mask/literal inverse failed'
    files = {}
    for number in range(5):
        path = BASE/f'Identities{number:02}.lean'
        code = f'''import Compact.Bridge.PrefixCoverageMasks
import Completion.Cases.C981.Coverage.Data.FinsetPool

namespace {IDENTITY_NS}
open N12Compact.PrefixCoverage S12Completion.C981.Coverage.Data.FinsetPool
set_option Elab.async false
'''
        for mask in masks[number*15:(number+1)*15]:
            value = names.get(mask,f'({literal(mask)} : Finset Nat)')
            code += f'\ntheorem decode_{mask} : Masks.decode 20 {mask} = {value} := by\n  decide +kernel\n'
        code += f'\nend {IDENTITY_NS}\n'
        files[path] = code.encode()
    code = ''.join(f'import {module(path)}\n' for path in files)
    code += '''import Completion.Cases.C981.Coverage.Data.Prefix09
import Completion.Cases.C981.Coverage.Data.Prefix10
import Completion.Cases.C981.Coverage.Data.Allowed05

/-! Integer computation for exactly eight original fronts and all 64 choices.
Every data correspondence below is proved in Lean. The resulting StepCheck
uses the full original target list; this is not the full step10 or case. -/
namespace S12Completion.C981.CoveragePilot
open N12Compact.PrefixCoverage S12Completion.C981.Coverage
open S12Completion.C981.Coverage.Data.FinsetPool
open S12Completion.C981.Coverage.MaskIdentities
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

'''
    code += f'def beforeCodes08 : List (List Nat) := {rows_literal(before)}\n\n'
    code += 'def choiceCodes08 : List Nat := ['+','.join(map(str,choices))+']\n\n'
    code += f'def afterCodes08 : List (List Nat) := {rows_literal(after)}\n\n'
    def identities(values):
        return ', '.join(f'decode_{mask}' for mask in sorted(values))
    code += 'theorem beforeCodes08_exact : Masks.decodeRows 20 beforeCodes08 = prefix09.take 8 := by\n'
    code += '  change Masks.decodeRows 20 beforeCodes08 = '+rows_literal(before,names.__getitem__,'  ')+'\n'
    code += '  simp only [beforeCodes08, Masks.decodeRows, Masks.decodeRow, List.map_cons, List.map_nil,\n    '
    code += identities({mask for row in before for mask in row})+']\n\n'
    code += 'theorem choiceCodes08_exact : choiceCodes08.map (Masks.decode 20) = allowed5 := by\n'
    code += '  simp only [choiceCodes08, allowed5, List.map_cons, List.map_nil,\n    '
    code += identities(set(choices))+']\n  rfl\n\n'
    code += 'theorem afterCodes08_exact : Masks.decodeRows 20 afterCodes08 = prefix10.take 46 := by\n'
    code += '  change Masks.decodeRows 20 afterCodes08 = '+rows_literal(after,names.__getitem__,'  ')+'\n'
    code += '  simp only [afterCodes08, Masks.decodeRows, Masks.decodeRow, List.map_cons, List.map_nil,\n    '
    code += identities({mask for row in after for mask in row})+']\n\n'
    code += '''theorem step10Masks08_indexed :
    Masks.IndexedStepCheck 20 beforeCodes08 choiceCodes08 afterCodes08 (List.range 46) := by
  decide +kernel

theorem step10Masks08 : StepCheck (prefix09.take 8) allowed5 prefix10 := by
  have decoded := Masks.indexedStepCheck_decoded 20 beforeCodes08 choiceCodes08 afterCodes08
    (List.range 46) step10Masks08_indexed
  rw [beforeCodes08_exact, choiceCodes08_exact, afterCodes08_exact] at decoded
  exact stepCheck_mono_after decoded (fun _ member => List.mem_of_mem_take member)

#print axioms step10Masks08
end S12Completion.C981.CoveragePilot
'''
    files[PILOT] = code.encode()
    report = {'original_commit':commit,'original_table_audit':records,
        'front_count':8,'choice_count':64,'candidate_pairs':512,'compatible_extensions':46,
        'target_slice_start':0,'target_slice_count':46,'all_original_choices_preserved':True,
        'original_row_order_preserved':True,'distinct_mask_identities':75,
        'identity_namespace':IDENTITY_NS,'identity_masks':masks,'added_lean_modules':6,
        'additional_native_sites':0,'lean_replay_performed':False,
        'files':[{'path':path.as_posix(),'sha256':sha(data)} for path,data in files.items()]}
    if args.write:
        for path,data in files.items():
            if (ROOT/path).exists():
                assert (ROOT/path).read_bytes() == data, f'Refusing to replace changed source: {path}'
        for path,data in files.items():
            (ROOT/path).parent.mkdir(parents=True,exist_ok=True)
            (ROOT/path).write_bytes(data)
        MANIFEST.write_text(json.dumps(report,indent=2)+'\n')
    assert all((ROOT/path).read_bytes() == data for path,data in files.items()), 'Pilot source changed'
    assert json.loads(MANIFEST.read_text()) == report, 'Pilot manifest differs'
    elapsed = time.monotonic()-started
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1048576
    assert elapsed < 10 and peak < 128, 'Source generation exceeded budget'
    signal.alarm(0)
    print(json.dumps({'audit':'passed','new_modules':6,'mask_identities':75,
        'source_bytes':sum(map(len,files.values())),'elapsed_seconds':round(elapsed,4),
        'max_rss_MiB':round(peak,2),'lean_replay_performed':False}))


if __name__ == '__main__':
    main()
