#!/usr/bin/env python3
"""Activate the reviewed shared-stage proposal after coordinator approval.

This is a small file transaction, never a Lean or numerical computation.
C713 plan batches and its actual whole-chain adapter must remain byte-identical.
Only its nine reviewed stage wrappers may change to the shared theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
PROPOSAL = ROOT / 'evidence/proposals/HistoricalDirectPruningStages'
BACKUP = ROOT / 'evidence/backups/HistoricalDirectPruningStages'
RECEIPT = ROOT / 'evidence/historical-direct-pruning-stages-activation.json'
CASES = {701, 713, 717, 973, 978, 979}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            value.update(block)
    return value.hexdigest()


def safe_path(relative):
    path = Path(relative)
    need(not path.is_absolute() and '..' not in path.parts, 'unsafe output path')
    if relative != 'Compact/HistoricalDirectPruning.lean':
        match = re.fullmatch(r'Compact/Cases/C(\d+)/DirectPruning/(?:All|Step\d\d(?:Batch\d\d)?)\.lean', relative)
        need(match is not None and int(match[1]) in CASES, 'unexpected output path')
    return path


def metadata_text(source):
    block = re.search(r'theorem source_ids :.*?  cover_of_source_map[^\n]*\n',
                      source, re.S)
    need(block is not None, 'original source/target metadata absent')
    prefix = source[source.index('def plans :'):block.start()]
    return prefix.strip() + '\n' + block[0].strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--approved-manifest-sha256', required=True)
    args = parser.parse_args()
    need(args.run, 'coordinator activation approval and --run required')
    manifest_path = PROPOSAL / 'manifest.json'
    need(digest(manifest_path) == args.approved_manifest_sha256, 'reviewed manifest changed')
    manifest = json.loads(manifest_path.read_text())
    need(manifest['shared_stage_theorem'] and manifest['pair_stages'] == 113,
         'not the reviewed shared-stage proposal')
    need(manifest['original_plans'] == 9166 and manifest['direct_outside_contexts'] == 16896,
         'incomplete original plan scope')
    need(not BACKUP.exists() and not RECEIPT.exists(), 'refusing previous activation state')
    for relative, expected in manifest['input_sha256'].items():
        path = Path(relative)
        need(not path.is_absolute() and '..' not in path.parts, 'unsafe provenance path')
        need(digest(ROOT / path) == expected, 'input changed since proposal: ' + relative)
    changes, unchanged = [], []
    seen = set()
    for item in manifest['outputs']:
        relative = item['path']
        need(relative not in seen, 'duplicate output')
        seen.add(relative)
        path = safe_path(relative)
        prepared, active = PROPOSAL / path, ROOT / path
        need(not prepared.is_symlink() and not active.is_symlink(), 'refusing source symlink')
        need(digest(prepared) == item['sha256'], 'proposal output hash changed: ' + relative)
        previous = digest(active) if active.exists() else None
        if relative.startswith('Compact/Cases/C713/DirectPruning/') and active.exists():
            if re.search(r'/Step\d\d\.lean$', relative):
                need(metadata_text(active.read_text()) == metadata_text(prepared.read_text()),
                     'C713 repaired source/target metadata changed: ' + relative)
            else:
                need(previous == item['sha256'], 'accepted C713 data/assembly would change: ' + relative)
        record = {'path': relative, 'before_sha256': previous, 'sha256': item['sha256']}
        if previous == item['sha256']:
            unchanged.append(record)
        else:
            changes.append(record)
    need(len(seen) == manifest['lean_modules'], 'incomplete output list')
    need(sum((PROPOSAL / item['path']).stat().st_size for item in changes) < 8 * 1024**2,
         'activation exceeds small source transaction budget')
    BACKUP.mkdir(parents=True)
    applied = []
    temporary = []
    try:
        for item in changes:
            relative = Path(item['path'])
            active = ROOT / relative
            if item['before_sha256'] is not None:
                backup = BACKUP / relative
                backup.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(active, backup)
                need(digest(backup) == item['before_sha256'], 'backup verification failed')
        for item in changes:
            relative = Path(item['path'])
            active = ROOT / relative
            active.parent.mkdir(parents=True, exist_ok=True)
            temp = active.with_name(active.name + '.activation-tmp')
            need(not temp.exists(), 'refusing existing temporary file')
            temporary.append(temp)
            shutil.copyfile(PROPOSAL / relative, temp)
            need(digest(temp) == item['sha256'], 'staged copy verification failed')
            os.replace(temp, active)
            applied.append(item)
        for item in changes:
            need(digest(ROOT / item['path']) == item['sha256'], 'active source verification failed')
        receipt = {'status': 'source activation only; changed wrappers require replay',
                   'proposal_manifest_sha256': args.approved_manifest_sha256,
                   'changed': changes, 'unchanged': unchanged,
                   'preserved_c713_data_and_assembly': True,
                   'preserved_c713_repaired_metadata': True,
                   'backup': str(BACKUP.relative_to(ROOT))}
        RECEIPT.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({'changed_sources': len(changes), 'unchanged_sources': len(unchanged),
                          'receipt': str(RECEIPT.relative_to(ROOT))}))
    except BaseException:
        for item in reversed(applied):
            active = ROOT / item['path']
            if item['before_sha256'] is None:
                active.unlink()
            else:
                shutil.copyfile(BACKUP / item['path'], active)
                need(digest(active) == item['before_sha256'], 'rollback verification failed')
        if RECEIPT.exists():
            RECEIPT.unlink()
        raise
    finally:
        for path in temporary:
            if path.exists():
                path.unlink()


if __name__ == '__main__':
    main()
