#!/usr/bin/env python3
"""Check independent roots serially, retaining diagnostics for every root.

Run under bounded.py. This merely dispatches verify.py: its source/object
validation and refusal to accept admissions are unchanged. The aggregate
receipt describes focused checks, never acceptance of the global theorem.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('local_verify', ROOT/'scripts/verify.py')
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)

def main():
    census = subprocess.run([sys.executable, '-B', str(ROOT/'scripts/source_census.py'), *sys.argv[1:]], cwd=ROOT)
    if census.returncode:
        raise SystemExit(census.returncode)
    records = []
    failed = {}
    for module in dict.fromkeys(sys.argv[1:]):
        blockers = [m for m in VERIFY.closure([module]) if m in failed and
            failed[m] == hashlib.sha256(VERIFY.path(m).read_bytes()).hexdigest()]
        if blockers:
            records.append({'root': module, 'returncode': 1,
                'dependency_blocked': blockers})
            print(json.dumps({'root': module, 'dependency_blocked': blockers}), flush=True)
            continue
        print(json.dumps({'checking_root': module}), flush=True)
        console = ROOT/'.verification'/(module+'.replay-console.log')
        with console.open('w') as log:
            result = subprocess.run([sys.executable, '-B',
                str(ROOT/'scripts/verify.py'), module], cwd=ROOT,
                stdout=log, stderr=subprocess.STDOUT)
        latest = ROOT/'.verification/latest-replay.json'
        replay = json.loads(latest.read_text()) if latest.exists() else None
        if result.returncode and replay:
            for record in replay.get('records', []):
                if record['returncode']:
                    failed[record['module']] = record['source_sha256']
        print(json.dumps({'root': module, 'returncode': result.returncode,
            'failed_modules': [r['module'] for r in (replay or {}).get('records', [])
                if r['returncode']], 'console': str(console)}), flush=True)
        records.append({'root': module, 'returncode': result.returncode,
            'replay': replay})
        (ROOT/'.verification/latest-team-replay.json').write_text(
            json.dumps({'records': records,
                'complete': len(records) == len(dict.fromkeys(sys.argv[1:])),
                'all_passed': all(r['returncode'] == 0 for r in records),
                'global_optimality_proved': False}, indent=2)+'\n')
    (ROOT/'.verification/latest-team-replay.json').write_text(
        json.dumps({'records': records, 'complete': True,
            'all_passed': all(r['returncode'] == 0 for r in records),
            'global_optimality_proved': False}, indent=2)+'\n')
    raise SystemExit(0 if all(r['returncode'] == 0 for r in records) else 1)

if __name__ == '__main__':
    main()
