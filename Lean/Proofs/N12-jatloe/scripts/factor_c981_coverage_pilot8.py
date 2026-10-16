#!/usr/bin/env python3
"""Emit or audit only the first eight fronts of C981 step10; never run Lean."""
import argparse
import json
from pathlib import Path
import resource
import signal
import time

from generate_c981_indexed_chunks import (
    exact_target_slice, load_tables, propose_indices, sha, table_audit,
)

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('Compact/Completion/C981/CoveragePilot/Step10First08.lean')
MANIFEST = ROOT/'evidence/c981-coverage-pilot8.json'


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
    indices = propose_indices(tables['prefix09'][:8],tables['allowed5'],tables['prefix10'])
    start,count,local = exact_target_slice(indices)
    assert (start,count,local) == (0,46,list(range(46))), 'Pilot scope changed'
    source = '''import Compact.Bridge.PrefixCoverageIndexed
import Completion.Cases.C981.Coverage.Data.Prefix09
import Completion.Cases.C981.Coverage.Data.Prefix10
import Completion.Cases.C981.Coverage.Data.Allowed05

/-! Only the first eight incoming fronts of the original step10 are checked.
All 64 original allowed5 choices remain. Exact indexed equality is checked
against the first 46 target rows, then membership lifts to the full table.
This pilot does not establish step10, the preceding chain, or the whole case. -/
namespace S12Completion.C981.CoveragePilot
open N12Compact.PrefixCoverage S12Completion.C981.Coverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem step10First08_indexed :
    IndexedStepCheck (prefix09.take 8) allowed5 (prefix10.take 46) (List.range 46) := by
  decide +kernel

theorem step10First08 : StepCheck (prefix09.take 8) allowed5 prefix10 :=
  stepCheck_mono_after
    (indexedStepCheck_sound (prefix09.take 8) allowed5 (prefix10.take 46)
      (List.range 46) step10First08_indexed)
    (fun _ member => List.mem_of_mem_take member)

#print axioms step10First08
end S12Completion.C981.CoveragePilot
'''.encode()
    report = {
        'original_commit':commit,
        'original_table_audit':records,
        'source':SOURCE.as_posix(),'source_sha256':sha(source),
        'front_count':8,'choice_count':64,'candidate_pairs':512,
        'compatible_extensions':count,
        'checked_target_slice':{'original':'prefix10','start':start,'count':count},
        'full_target_count':3143,'witness':'List.range 46',
        'lift_to_full_target':'stepCheck_mono_after / List.mem_of_mem_take',
        'added_lean_modules':1,'additional_native_sites':0,
        'lean_replay_performed':False,
    }
    if args.write:
        if (ROOT/SOURCE).exists():
            assert (ROOT/SOURCE).read_bytes() == source, 'Refusing to replace changed source'
        (ROOT/SOURCE).parent.mkdir(parents=True,exist_ok=True)
        (ROOT/SOURCE).write_bytes(source)
        MANIFEST.write_text(json.dumps(report,indent=2)+'\n')
    assert (ROOT/SOURCE).read_bytes() == source, 'Pilot source changed'
    assert json.loads(MANIFEST.read_text()) == report, 'Pilot audit differs'
    elapsed = time.monotonic()-started
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1048576
    assert elapsed < 10 and peak < 128, 'Pilot audit exceeded resource budget'
    signal.alarm(0)
    print(json.dumps({'audit':'passed','fronts':8,'target_rows':count,
        'elapsed_seconds':round(elapsed,4),'max_rss_MiB':round(peak,2),
        'lean_replay_performed':False}))


if __name__ == '__main__':
    main()
