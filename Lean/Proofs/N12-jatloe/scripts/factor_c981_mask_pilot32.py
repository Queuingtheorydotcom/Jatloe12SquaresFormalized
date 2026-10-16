#!/usr/bin/env python3
"""Emit/audit only the 32-front exact mask pilot, reusing accepted identities."""
import argparse
import json
from pathlib import Path
import resource
import signal
import time

from factor_c981_mask_pilot8 import IDENTITY_NS, literal, module, rows_literal
from generate_c981_indexed_chunks import (
    exact_target_slice, load_tables, parse_row, propose_indices, sha, table_audit,
)

ROOT = Path(__file__).resolve().parents[1]
HELPER = Path('Compact/Completion/C981/CoverageMasks/Identities05.lean')
DATA = Path('Compact/Completion/C981/CoverageMasks/Step10Codes32.lean')
CHECK = Path('Compact/Completion/C981/CoveragePilot/Step10Masks32Check.lean')
PILOT = Path('Compact/Completion/C981/CoveragePilot/Step10Masks32.lean')
MANIFEST = ROOT/'evidence/c981-mask-pilot32.json'
PARTS = [(0,46),(46,46),(92,42),(134,38)]


def render_pilot(front_count,before,choices,after,names,helpers):
    """All four data lists come from the original fixed order, never a search."""
    suffix = f'{front_count:02}'
    target_count = len(after)
    term = lambda mask: names.get(mask,literal(mask))
    identities = lambda values: ', '.join(f'decode_{mask}' for mask in sorted(values))
    code = ''.join(f'import {module(path)}\n' for path in helpers)
    code += f'''import Completion.Cases.C981.Coverage.Data.Prefix09
import Completion.Cases.C981.Coverage.Data.Prefix10
import Completion.Cases.C981.Coverage.Data.Allowed05

/-! Integer computation for exactly {front_count} original fronts and all 64 choices.
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
    code += f'def beforeCodes{suffix} : List (List Nat) := {rows_literal(before)}\n\n'
    code += f'def choiceCodes{suffix} : List Nat := ['+','.join(map(str,choices))+']\n\n'
    code += f'def afterCodes{suffix} : List (List Nat) := {rows_literal(after)}\n\n'
    code += f'theorem beforeCodes{suffix}_exact : Masks.decodeRows 20 beforeCodes{suffix} = prefix09.take {front_count} := by\n'
    code += f'  change Masks.decodeRows 20 beforeCodes{suffix} = '+rows_literal(before,term,'  ')+'\n'
    code += f'  simp only [beforeCodes{suffix}, Masks.decodeRows, Masks.decodeRow, List.map_cons, List.map_nil,\n    '
    code += identities({mask for row in before for mask in row})+']\n\n'
    code += f'theorem choiceCodes{suffix}_exact : choiceCodes{suffix}.map (Masks.decode 20) = allowed5 := by\n'
    code += f'  simp only [choiceCodes{suffix}, allowed5, List.map_cons, List.map_nil,\n    '
    code += identities(set(choices))+']\n  rfl\n\n'
    code += f'theorem afterCodes{suffix}_exact : Masks.decodeRows 20 afterCodes{suffix} = prefix10.take {target_count} := by\n'
    code += f'  change Masks.decodeRows 20 afterCodes{suffix} = '+rows_literal(after,term,'  ')+'\n'
    code += f'  simp only [afterCodes{suffix}, Masks.decodeRows, Masks.decodeRow, List.map_cons, List.map_nil,\n    '
    code += identities({mask for row in after for mask in row})+']\n\n'
    code += f'''theorem step10Masks{suffix}_indexed :
    Masks.IndexedStepCheck 20 beforeCodes{suffix} choiceCodes{suffix} afterCodes{suffix} (List.range {target_count}) := by
  decide +kernel

theorem step10Masks{suffix} : StepCheck (prefix09.take {front_count}) allowed5 prefix10 := by
  have decoded := Masks.indexedStepCheck_decoded 20 beforeCodes{suffix} choiceCodes{suffix} afterCodes{suffix}
    (List.range {target_count}) step10Masks{suffix}_indexed
  rw [beforeCodes{suffix}_exact, choiceCodes{suffix}_exact, afterCodes{suffix}_exact] at decoded
  exact stepCheck_mono_after decoded (fun _ member => List.mem_of_mem_take member)

#print axioms step10Masks{suffix}
end S12Completion.C981.CoveragePilot
'''
    return code.encode()


def factor_pilot(combined):
    """Keep exact data/correspondences; replace only the integer checker.

    Historical inverse reconstruction explicitly restores the old checker and
    final adapter; it does not claim these two proof bodies stayed unchanged.
    """
    code = combined.decode()
    data_start = code.index('def beforeCodes32 ')
    proof_start = code.index('theorem beforeCodes32_exact ')
    check_start = code.index('theorem step10Masks32_indexed ')
    final_start = code.index('theorem step10Masks32 : ')
    data = code[data_start:proof_start]
    check = code[check_start:final_start]
    options = '''namespace S12Completion.C981.CoveragePilot
open N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

'''
    end = 'end S12Completion.C981.CoveragePilot\n'
    data_source = ('import Compact.Bridge.PrefixCoverageMasks\n\n'+options+data+end).encode()
    grouped = ''
    for part,(start,count) in enumerate(PARTS):
        front = f'(beforeCodes32.drop {8*part})'
        if part < 3:
            front = f'({front}.take 8)'
        target = f'((afterCodes32.drop {start}).take {count})'
        grouped += f'''theorem step10Masks32_part{part:02}_indexed :
    Masks.IndexedStepCheck 20 {front} choiceCodes32 {target} (List.range {count}) := by
  decide +kernel

theorem step10Masks32_part{part:02}_checked :
    Masks.MaskStepCheck 20 {front} choiceCodes32 afterCodes32 :=
  Masks.maskStepCheck_after_slice {start} {count}
    (Masks.indexedStepCheck_sound 20 {front} choiceCodes32 {target}
      (List.range {count}) step10Masks32_part{part:02}_indexed)

'''
    grouped += '''theorem step10Masks32_checked :
    Masks.MaskStepCheck 20 beforeCodes32 choiceCodes32 afterCodes32 := by
  have tail3 : Masks.MaskStepCheck 20 (beforeCodes32.drop 24) choiceCodes32 afterCodes32 :=
    step10Masks32_part03_checked
'''
    for part in (2,1,0):
        grouped += f'''  have tail{part} : Masks.MaskStepCheck 20 (beforeCodes32.drop {8*part}) choiceCodes32 afterCodes32 := by
    apply Masks.takeDropMaskStepCheck 8
    · exact step10Masks32_part{part:02}_checked
    · simpa only [List.drop_drop] using tail{part+1}
'''
    grouped += '  simpa only [List.drop_zero] using tail0\n\n'
    check_source = (f'import {module(DATA)}\nimport Compact.Bridge.PrefixCoverageMaskChunks\n\n'+
        options+grouped+'#print axioms step10Masks32_checked\n'+end).encode()
    added_import = f'import {module(CHECK)}\n'
    wrapper = added_import+code[:data_start]+code[proof_start:check_start]+code[final_start:]
    old_adapter = '''  have decoded := Masks.indexedStepCheck_decoded 20 beforeCodes32 choiceCodes32 afterCodes32
    (List.range 172) step10Masks32_indexed
'''
    new_adapter = '''  have decoded := Masks.maskStepCheck_sound 20 beforeCodes32 choiceCodes32 afterCodes32
    step10Masks32_checked
'''
    assert wrapper.count(old_adapter) == 1
    wrapper = wrapper.replace(old_adapter,new_adapter,1)
    inverse = wrapper.removeprefix(added_import)
    inverse = inverse.replace(new_adapter,old_adapter,1)
    inverse = inverse.replace('theorem beforeCodes32_exact ',data+'theorem beforeCodes32_exact ',1)
    inverse = inverse.replace('theorem step10Masks32 : ',check+'theorem step10Masks32 : ',1)
    assert inverse.encode() == combined, 'Declaration factoring inverse failed'
    return {DATA:data_source,CHECK:check_source,PILOT:wrapper.encode()}


def main():
    started = time.monotonic()
    signal.alarm(10)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    prior = json.loads((ROOT/'evidence/c981-mask-pilot8.json').read_text())
    commit = prior['original_commit']
    tables,expected,old,audits = load_tables(commit)
    records = table_audit(expected,old,audits)
    records = [r for r in records if r['data'].endswith(('Prefix09.lean','Prefix10.lean','Allowed05.lean'))]
    helpers = []
    for item in prior['files']:
        if '/CoverageMasks/Identities' in item['path']:
            path = Path(item['path'])
            assert sha((ROOT/path).read_bytes()) == item['sha256'], 'Existing identity helper changed'
            helpers.append(path)
    assert len(helpers) == 5
    before,choices = tables['prefix09'][:32],tables['allowed5']
    start,count,indices = exact_target_slice(propose_indices(before,choices,tables['prefix10']))
    assert (start,count,indices) == (0,172,list(range(172))), 'Pilot scope changed'
    after = tables['prefix10'][:172]
    for part,(expected_start,expected_count) in enumerate(PARTS):
        part_start,part_count,_ = exact_target_slice(
            propose_indices(before[part*8:(part+1)*8],choices,after))
        assert (part_start,part_count) == (expected_start,expected_count), 'Part target interval changed'
    pool = json.loads((ROOT/'evidence/c981-prefix-finset-pool.json').read_text())
    names = {parse_row('['+item['literal']+']')[0]:item['name'] for item in pool['constants']}
    assert all(mask in names for row in before+after for mask in row)
    masks = sorted(set(choices)|{mask for row in before+after for mask in row})
    additional = sorted(set(masks)-set(prior['identity_masks']))
    assert additional == [8,16424,147584,655488], 'Additional identity scope changed'
    helper = f'''import Compact.Bridge.PrefixCoverageMasks
import Completion.Cases.C981.Coverage.Data.FinsetPool

namespace {IDENTITY_NS}
open N12Compact.PrefixCoverage S12Completion.C981.Coverage.Data.FinsetPool
set_option Elab.async false
'''
    for mask in additional:
        assert parse_row('['+literal(mask)+']') == (mask,)
        helper += f'\ntheorem decode_{mask} : Masks.decode 20 {mask} = {names[mask]} := by\n  decide +kernel\n'
    helper += f'\nend {IDENTITY_NS}\n'
    combined = render_pilot(32,before,choices,after,names,helpers+[HELPER])
    files = {HELPER:helper.encode(),**factor_pilot(combined)}
    report = {'original_commit':commit,'original_table_audit':records,
        'reused_identity_manifest':'evidence/c981-mask-pilot8.json',
        'front_count':32,'choice_count':64,'candidate_pairs':2048,'compatible_extensions':172,
        'target_slice_start':0,'target_slice_count':172,'original_row_order_preserved':True,
        'additional_identity_masks':additional,'identity_namespace':IDENTITY_NS,
        'added_lean_modules':4,'additional_native_sites':0,'lean_replay_performed':False,
        'combined_pilot_sha256':sha(combined),'historical_combined_source_reconstruction_exact':True,
        'data_declarations_preserved':True,
        'correspondence_declarations_preserved':True,
        'intentional_proof_changes':['single indexed decision replaced by four8front decisions and structural composition',
            'final adapter now consumes the combined MaskStepCheck'],
        'integer_decision_parts':[{'front_offset':8*i,'target_start':start,'target_count':count,
            'checks_entire_remaining_suffix':i==3} for i,(start,count) in enumerate(PARTS)],
        'generic_chunk_bridge':'Compact.Bridge.PrefixCoverageMaskChunks',
        'files':[{'path':path.as_posix(),'sha256':sha(data)} for path,data in files.items()]}
    if args.write:
        for path,data in files.items():
            if (ROOT/path).exists():
                assert (ROOT/path).read_bytes() == data, f'Refusing changed source: {path}'
        for path,data in files.items():
            (ROOT/path).parent.mkdir(parents=True,exist_ok=True)
            (ROOT/path).write_bytes(data)
        MANIFEST.write_text(json.dumps(report,indent=2)+'\n')
    assert all((ROOT/path).read_bytes() == data for path,data in files.items()), 'Pilot source changed'
    assert json.loads(MANIFEST.read_text()) == report, 'Pilot audit differs'
    elapsed = time.monotonic()-started
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1048576
    assert elapsed < 10 and peak < 128, 'Source generation exceeded budget'
    signal.alarm(0)
    print(json.dumps({'audit':'passed','new_modules':4,'additional_identities':4,
        'source_bytes':sum(map(len,files.values())),'elapsed_seconds':round(elapsed,4),
        'max_rss_MiB':round(peak,2),'lean_replay_performed':False}))


if __name__ == '__main__':
    main()
