#!/usr/bin/env python3
"""Activate the hash-checked C898 checked_recipe proposal, without running Lean.

Parent-only --run. Verifies all original-input and output hashes before editing;
backs up replaced source outside the active closure and rolls back ordinary
failures. Leaves obsolete diagnostics, object files and all other source alone.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import time

ROOT = Path(__file__).resolve().parents[1]
PROPOSAL = ROOT/'evidence/proposals/C898RecipeTable'
ACTIVE = ROOT/'Compact/Cases/C898/RecipeInitial'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    if not parser.parse_args().run:
        parser.error('prepared only; the parent must authorize activation with --run')
    started = time.monotonic()
    report_path = ROOT/'evidence/c898-spec-initial-proposal.json'
    report = json.loads(report_path.read_text())
    assert report['semantic_records'] == 704 and report['numeric_batches'] == 88
    assert report['maximum_roots_per_numeric_module'] == 8
    assert report['target_angles'] == 630 and report['empty_angles'] == 74
    assert report['numeric_declaration_strategy'].startswith('checked_recipe:')
    assert report['lean_modules'] == len(report['outputs']) == 114
    assert report['lean_bytes'] < 4*1024**2
    assert shutil.disk_usage(ROOT).free > 3*1024**3, 'free disk below3GiB'
    inputs = {'geometry': 'evidence/C898/raw/data/region898.json',
              'poses': 'evidence/c898-shared-pose-map.json',
              'angles': 'vendor/S12/AngleData.lean'}
    for name, relative in inputs.items():
        assert digest(ROOT/relative) == report['input_sha256'][name]
    assert digest(ROOT/'evidence/c898-direct-cover-all.json') == report['audit_sha256']
    assert digest(ROOT/'evidence/c898-domain-map.json') == report['domains_sha256']
    changes = []
    names = set()
    for output in report['outputs']:
        source = ROOT/output['path']
        assert source.parent == PROPOSAL and source.suffix == '.lean'
        assert source.name not in names and not source.is_symlink()
        names.add(source.name)
        assert digest(source) == output['sha256']
        content = source.read_bytes()
        assert len(content) == output['bytes'] and content.count(b'\n') == output['lines']
        destination = ACTIVE/source.name
        assert not destination.is_symlink()
        before = digest(destination) if destination.exists() else None
        if before == output['sha256']:
            continue
        assert before == report['active_source_sha256'][source.name], ('active source changed', source.name)
        changes.append((source, destination, before, output['sha256']))
    identity = digest(report_path)
    backup = ROOT/'evidence/source-archive/c898-before-checked-recipes'/identity[:16]
    applied = []
    try:
        for source, destination, before, after in changes:
            if before is not None:
                backup.mkdir(parents=True, exist_ok=True)
                saved = backup/destination.name
                if saved.exists():
                    assert digest(saved) == before
                else:
                    shutil.copyfile(destination, saved)
                assert digest(saved) == before
        for source, destination, before, after in changes:
            assert (digest(destination) if destination.exists() else None) == before
            temporary = destination.with_suffix('.lean.tmp')
            try:
                shutil.copyfile(source, temporary)
                assert digest(temporary) == after
                os.replace(temporary, destination)
            finally:
                temporary.unlink(missing_ok=True)
            applied.append((destination, before, after))
        receipt = {'scope': 'Source activation only; all704 root and whole-owner replays still required.',
                   'proposal_sha256': identity, 'semantic_records': 704,
                   'backup': str(backup.relative_to(ROOT)),
                   'changed': [{'path': str(path.relative_to(ROOT)), 'before_sha256': before,
                                'after_sha256': after} for path, before, after in applied],
                   'lean_lines': report['lean_lines'], 'lean_modules': report['lean_modules'],
                   'seconds': time.monotonic()-started, 'object_files_modified': False}
        (ROOT/'evidence/c898-checked-recipe-activation.json').write_text(json.dumps(receipt, indent=2)+'\n')
    except BaseException:
        for destination, before, after in reversed(applied):
            if destination.exists() and digest(destination) == after:
                if before is None:
                    destination.unlink()
                else:
                    shutil.copyfile(backup/destination.name, destination)
        raise
    print(json.dumps({'changed_modules': len(applied), 'semantic_records': 704,
                      'lean_lines': report['lean_lines'], 'seconds': time.monotonic()-started}))


if __name__ == '__main__':
    main()
