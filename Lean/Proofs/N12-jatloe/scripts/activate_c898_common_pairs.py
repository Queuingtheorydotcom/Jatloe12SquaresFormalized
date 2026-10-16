#!/usr/bin/env python3
"""Activate the exact prepared C898 common-point source, never run Lean.

Coordinator-only --run after targeted validations;128MiB/60seconds,<=4MiB
additional retained source/staging. Verify every proposal hash and original
replacement hash first. Back up replaced originals and roll back this script's
changes on ordinary failure. No processes, network, object-file deletion, or
claims of whole-proof acceptance.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import resource
import shutil
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PROPOSAL = ROOT/'evidence/proposals/C898CommonPairs'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('prepared only; the coordinator must authorize activation with --run')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic()-started > 60 or rss > 128*1024**2:
            raise RuntimeError('activation reached128MiB/60seconds')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,0.2,0.2)
    manifest_path = PROPOSAL/'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    assert digest(ROOT/'evidence/c898-all-common-points.json') == manifest['audit_sha256']
    assert manifest['modules'] == len(manifest['outputs'])
    assert manifest['bytes'] <= 2*1024**2
    assert shutil.disk_usage(ROOT).free > 2*1024**3, 'free disk below2GiB'
    identity = digest(manifest_path)
    backup = ROOT/'evidence/retired/C898BeforeCommonGroups'/identity[:16]
    staging = ROOT/'evidence/staging/C898CommonGroups'/identity[:16]
    if staging.exists():
        raise RuntimeError('staging path already exists; inspect earlier interrupted activation before retrying')
    changes, originals = [], {}
    forbidden = re.compile(r'\b(?:sorry|admit|native_decide)\b|Lean\.ofReduceBool')
    for relative,expected in sorted(manifest['outputs'].items()):
        path = Path(relative)
        assert path.parts[:4] == ('Compact','Cases','C898','CachedPairs')
        assert '..' not in path.parts and path.suffix == '.lean'
        candidate = PROPOSAL/path
        assert candidate.is_file() and not candidate.is_symlink()
        assert digest(candidate) == expected['sha256'], ('changed proposal',relative)
        content = candidate.read_text()
        assert len(content.encode()) == expected['bytes']
        assert content.count('\n') == expected['lines']
        assert not forbidden.search(content), ('unexpected unchecked construct',relative)
        active = ROOT/path
        assert not active.is_symlink()
        previous = digest(active) if active.exists() else None
        if previous == expected['sha256']:
            continue
        if previous is not None:
            allowed = manifest.get('allowed_previous_sources',{}).get(relative,[])
            assert (manifest['input_sources'].get(relative) == previous or previous in allowed), (
                'unexpected active source change',relative)
            originals[relative] = previous
        changes.append((relative,previous,expected['sha256']))
    # All replacement APIs are theorem aliases with unchanged original types.
    for step in list(range(9))+[11,12,13]:
        relative = f'Compact/Cases/C898/CachedPairs/Step{step:02}.lean'
        expected = (PROPOSAL/relative).read_text()
        assert f'exact pairStep{step}_geometric_sound q t hq ht disjoint' in expected
        assert f'import Compact.Cases.C898.CachedPairs.Step{step:02}Geometric' in expected
    # The terminal alias is selected and validated independently. Preserve
    # the currently accepted terminal proof across this activation.
    terminal = ROOT/'Compact/Cases/C898/CachedPairs/Step14.lean'
    terminal_sha = digest(terminal)
    staging.mkdir(parents=True)
    applied = []
    try:
        for relative,previous,new_sha in changes:
            staged = staging/relative
            staged.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(PROPOSAL/relative,staged)
            assert digest(staged) == new_sha
            if previous is not None:
                saved = backup/relative
                saved.parent.mkdir(parents=True,exist_ok=True)
                if saved.exists():
                    assert digest(saved) == previous
                else:
                    shutil.copyfile(ROOT/relative,saved)
                assert digest(saved) == previous
        for relative,previous,new_sha in changes:
            active = ROOT/relative
            assert (digest(active) if active.exists() else None) == previous
            active.parent.mkdir(parents=True,exist_ok=True)
            os.replace(staging/relative,active)
            applied.append((relative,previous,new_sha))
            assert digest(active) == new_sha
        assert digest(terminal) == terminal_sha
        receipt = {'scope':'exact source activation only; complete candidate route assembled, no new Lean acceptance',
                   'proposal_manifest_sha256':identity,'proposal':str(PROPOSAL.relative_to(ROOT)),
                   'backup':str(backup.relative_to(ROOT)),
                   'changed':[{'path':path,'before_sha256':before,'after_sha256':after}
                              for path,before,after in applied],
                   'unchanged_terminal_sha256':terminal_sha,
                   'candidate_root':'Compact.Cases.C898.CompleteCached',
                   'object_files_modified':False,
                   'elapsed_seconds':time.monotonic()-started}
        target = ROOT/'evidence/c898-common-pairs-activation.json'
        # Idempotent activation must not erase the preceding replacement
        # receipt. Preserve each exact receipt before updating the current one.
        if target.exists():
            receipt_sha = digest(target)
            historical = ROOT/'evidence/retired/C898ActivationReceipts'/(receipt_sha+'.json')
            historical.parent.mkdir(parents=True,exist_ok=True)
            if historical.exists():
                assert digest(historical) == receipt_sha
            else:
                shutil.copyfile(target,historical)
            receipt['previous_receipt_sha256'] = receipt_sha
            receipt['previous_receipt_path'] = str(historical.relative_to(ROOT))
        temporary = target.with_suffix('.json.tmp')
        try:
            with temporary.open('w') as stream:
                json.dump(receipt,stream,indent=2);stream.write('\n')
            os.replace(temporary,target)
        finally:
            temporary.unlink(missing_ok=True)
    except BaseException:
        signal.setitimer(signal.ITIMER_REAL,0)
        # Do not delete a file if somebody changed it after our write.
        for relative,previous,new_sha in reversed(applied):
            active = ROOT/relative
            if not active.exists() or digest(active) != new_sha:
                continue
            if previous is None:
                active.unlink()
            else:
                restored = active.with_suffix('.lean.restore-tmp')
                shutil.copyfile(backup/relative,restored)
                os.replace(restored,active)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        shutil.rmtree(staging)
    print(json.dumps({'changed_files':len(applied),'proposal_modules':manifest['modules'],
                      'candidate_root':'Compact.Cases.C898.CompleteCached',
                      'elapsed_seconds':time.monotonic()-started}))


if __name__ == '__main__':
    main()
