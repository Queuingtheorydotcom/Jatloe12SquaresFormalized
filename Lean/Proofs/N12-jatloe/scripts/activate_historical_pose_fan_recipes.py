#!/usr/bin/env python3
"""Activate the authenticated historical fan recipe proposal, preserving backups.

Parent-run only. --pilot installs the two shared definitions and Contexts000;
the full invocation installs the same proposal after that pilot. All proposal
inputs/outputs are hash checked before any write. No cache, compiled object,
receipt index, proof obligation or unrelated source is removed or modified.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PROPOSAL = ROOT / 'evidence/proposals/HistoricalPoseFanRecipes'
OLD = ROOT / 'evidence/historical-fans-701-713-717-973-978-979-cycles/lean'
PREFIX = 'Compact/HistoricalFans/C701_713_717_973_978_979/'
SHARED = 'Compact/HistoricalData/SharedFanBlocks.lean'
PILOT = {SHARED, PREFIX + 'RecipeBank.lean', PREFIX + 'Contexts000.lean'}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def safe(root, relative):
    p = Path(relative)
    need(not p.is_absolute() and '..' not in p.parts, 'unsafe relative path')
    target = root / p
    need(target.resolve().is_relative_to(root.resolve()), 'path escapes root')
    current = target
    while current != root:
        need(not current.is_symlink(), 'symlink in selected path')
        current = current.parent
    return target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--pilot', action='store_true')
    args = parser.parse_args()
    need(args.run, 'explicit parent-run --run required')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        need(rss < 128 * 1024**2 and time.monotonic() - started < 60,
             '128 MiB/60 second activation guard')

    def stop(*_):
        raise InterruptedError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    lock = ROOT / 'evidence/.historical-pose-fan-activation.lock'
    need(not lock.exists(), 'existing activation lock: inspect before retrying')
    with lock.open('x') as f:
        f.write(str(os.getpid()) + '\n')
    changed = []
    temporaries = []
    try:
        manifest_path = PROPOSAL / 'manifest.json'
        identity = sha(manifest_path)
        manifest = json.loads(manifest_path.read_text())
        need(manifest['active_contexts'] == 12932 and
             manifest['all_input_lists_angles_and_references_exact'] and
             manifest['boundary_cycles_and_direction_array_unchanged'], 'proposal not complete')
        backup = ROOT / 'evidence/source-archive/historical-fans-before-pose-recipes' / identity[:16]
        outputs = {}
        total = 0
        for item in manifest['files']:
            source = safe(PROPOSAL, item['path'])
            need(source.is_file() and sha(source) == item['sha256'],
                 'proposal output changed: ' + item['path'])
            total += source.stat().st_size
            if not item['path'].endswith('.lean'):
                continue
            need(item['path'].startswith('lean/'), 'unexpected Lean output')
            relative = item['path'][5:]
            allowed = relative == SHARED or relative in {
                PREFIX + 'RecipeBank.lean', PREFIX + 'Directions.lean', PREFIX + 'All.lean'}
            allowed = allowed or bool(re.fullmatch(re.escape(PREFIX) + r'Contexts\d{3}\.lean', relative))
            need(allowed and relative not in outputs, 'unexpected/duplicate source destination')
            outputs[relative] = item
        need(total <= 16 * 1024**2, 'proposal payload exceeded cap')
        expected = {SHARED, PREFIX + 'RecipeBank.lean', PREFIX + 'Directions.lean', PREFIX + 'All.lean'}
        expected |= {PREFIX + f'Contexts{i:03}.lean' for i in range(405)}
        need(set(outputs) == expected, 'proposal file coverage changed')

        # Already-installed exact outputs are accepted after a pilot. Their
        # original input bytes must remain available either in our backup or
        # in the authenticated original cycle proposal.
        for relative, expected_sha in manifest['sources'].items():
            source = safe(ROOT, relative)
            need(source.is_file(), 'missing proposal input: ' + relative)
            actual = sha(source)
            if actual == expected_sha:
                continue
            need(relative in outputs and actual == outputs[relative]['sha256'],
                 'proposal input changed: ' + relative)
            prior = safe(backup, relative)
            original = prior if prior.is_file() else safe(OLD, relative)
            need(original.is_file() and sha(original) == expected_sha,
                 'original source backup unavailable: ' + relative)

        selected = PILOT if args.pilot else set(outputs)
        plan = []
        for relative in sorted(selected):
            item = outputs[relative]
            destination = safe(ROOT, relative)
            old_sha = sha(destination) if destination.exists() else None
            if old_sha == item['sha256']:
                continue
            expected_old = manifest['sources'].get(relative)
            need(old_sha == expected_old, 'unrecognized active destination: ' + relative)
            plan.append((relative, destination, old_sha, item))

        # Preserve every replaced source before the first active mutation.
        for relative, destination, old_sha, item in plan:
            if old_sha is None:
                continue
            saved = safe(backup, relative)
            saved.parent.mkdir(parents=True, exist_ok=True)
            if saved.exists():
                need(sha(saved) == old_sha, 'backup conflict')
            else:
                shutil.copyfile(destination, saved)
                need(sha(saved) == old_sha, 'backup verification failed')

        for relative, destination, old_sha, item in plan:
            need((sha(destination) if destination.exists() else None) == old_sha,
                 'active source changed during activation')
            destination.parent.mkdir(parents=True, exist_ok=True)
            temporary = destination.with_name(destination.name + '.fan-activation-tmp')
            need(not temporary.exists(), 'stale source temporary')
            temporaries.append(temporary)
            shutil.copyfile(safe(PROPOSAL, item['path']), temporary)
            need(sha(temporary) == item['sha256'], 'staged source verification failed')
            # Register rollback before replacement, so signals cannot leave an
            # installed source outside the transaction's restoration list.
            changed.append((relative, destination, old_sha))
            os.replace(temporary, destination)

        receipt = {'status': 'source activation only; whole fan replay still required',
            'mode': 'pilot' if args.pilot else 'full', 'proposal_sha256': identity,
            'backup': str(backup.relative_to(ROOT)), 'selected_sources': len(selected),
            'changed_sources': len(changed), 'active_contexts': 12932,
            'compiled_caches_modified': False, 'lean_acceptance_claimed': False,
            'files': [{'path': relative, 'sha256': outputs[relative]['sha256']}
                      for relative in sorted(selected)],
            'elapsed_seconds': time.monotonic() - started}
        suffix = 'pilot' if args.pilot else 'activation'
        target = ROOT / f'evidence/historical-pose-fan-{suffix}.json'
        temporary = target.with_suffix('.json.tmp')
        need(not temporary.exists(), 'stale receipt temporary')
        temporaries.append(temporary)
        temporary.write_text(json.dumps(receipt, indent=2) + '\n')
        os.replace(temporary, target)
        print(json.dumps({k: receipt[k] for k in ('status', 'mode', 'selected_sources',
            'changed_sources', 'elapsed_seconds')}))
    except BaseException:
        # Disable asynchronous interruption while restoring exact prior bytes.
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        for relative, destination, old_sha in reversed(changed):
            if old_sha is None:
                destination.unlink(missing_ok=True)
            else:
                shutil.copyfile(safe(backup, relative), destination)
                need(sha(destination) == old_sha, 'rollback verification failed')
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        for temporary in temporaries:
            temporary.unlink(missing_ok=True)
        lock.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
