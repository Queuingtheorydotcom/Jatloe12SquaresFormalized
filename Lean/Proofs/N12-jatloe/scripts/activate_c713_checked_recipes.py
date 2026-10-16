#!/usr/bin/env python3
"""Activate only the authenticated C713 RecipeInitial proposal; parent-only.

Every accepted EntryQuery/EntryPoints source outside RecipeInitial is left
untouched. Replaced sources are backed up; ordinary failures roll back.
No compiler, cache deletion, historical-data mutation, or proof claim.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, time

ROOT = Path(__file__).resolve().parents[1]
PROPOSAL = ROOT / 'evidence/proposals/C713RecipeCommand'
PREFIX = Path('Compact/Cases/C713/RecipeInitial')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    if not parser.parse_args().run:
        parser.error('parent activation slot and --run required')
    started = time.monotonic()
    manifest_path = PROPOSAL / 'manifest.json'
    report = json.loads(manifest_path.read_text())
    assert report['case'] == 713 and report['checked_command'] is True
    assert (report['semantic_roots'], report['empty_angles'], report['target_angles']) == (1152, 94, 1058)
    assert len(report['records']) == 1152
    records = [(r['owner'], r['angle']) for r in report['records']]
    owners = sorted({owner for owner, _ in records})
    assert records == [(owner, angle) for owner in owners for angle in range(128)]
    assert sum(r['target'] is None for r in report['records']) == 94
    for relative, expected in report['inputs'].items():
        assert digest(ROOT / relative) == expected, ('input changed', relative)
    selected, seen = [], set()
    for item in report['outputs']:
        relative = Path(item['path'])
        assert not relative.is_absolute() and '..' not in relative.parts
        if not relative.is_relative_to(PREFIX):
            continue
        assert relative.suffix == '.lean' and relative not in seen
        seen.add(relative)
        source, target = PROPOSAL / relative, ROOT / relative
        assert not source.is_symlink() and not target.is_symlink()
        content = source.read_bytes()
        assert hashlib.sha256(content).hexdigest() == item['sha256']
        assert len(content) == item['bytes'] and content.count(b'\n') == item['lines']
        before = digest(target) if target.exists() else None
        selected.append((relative, source, target, before, item['sha256']))
    assert len(selected) == 167, ('unexpected RecipeInitial source count', len(selected))
    assert sum(source.stat().st_size for _, source, _, _, _ in selected) < 2 * 1024**2
    identity = digest(manifest_path)
    backup = ROOT / 'evidence/source-archive/c713-before-checked-recipes' / identity[:16]
    changed = [record for record in selected if record[3] != record[4]]
    applied = []
    try:
        for relative, source, target, before, after in changed:
            if before is not None:
                saved = backup / relative.relative_to(PREFIX)
                saved.parent.mkdir(parents=True, exist_ok=True)
                if saved.exists():
                    assert digest(saved) == before
                else:
                    shutil.copyfile(target, saved)
                assert digest(saved) == before
        for relative, source, target, before, after in changed:
            assert (digest(target) if target.exists() else None) == before
            target.parent.mkdir(parents=True, exist_ok=True)
            temporary = target.with_suffix('.lean.activation-tmp')
            assert not temporary.exists()
            try:
                shutil.copyfile(source, temporary)
                assert digest(temporary) == after
                os.replace(temporary, target)
            finally:
                temporary.unlink(missing_ok=True)
            applied.append((relative, target, before, after))
        receipt = {'status': 'source activation only; complete entrance replay pending',
            'proposal_sha256': identity, 'semantic_roots': 1152,
            'backup': str(backup.relative_to(ROOT)), 'activated_modules': len(selected),
            'activated_lines': sum(source.read_bytes().count(b'\n') for _, source, _, _, _ in selected),
            'changed': [{'path': str(relative), 'before_sha256': before, 'after_sha256': after}
                        for relative, _, before, after in applied],
            'preserved': 'Every path outside Compact/Cases/C713/RecipeInitial; all object files.',
            'seconds': time.monotonic() - started}
        receipt_path = ROOT / 'evidence/c713-checked-recipe-activation.json'
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    except BaseException:
        for relative, target, before, after in reversed(applied):
            if target.exists() and digest(target) == after:
                if before is None:
                    target.unlink()
                else:
                    shutil.copyfile(backup / relative.relative_to(PREFIX), target)
        raise
    print(json.dumps({key: receipt[key] for key in
                      ('status', 'semantic_roots', 'activated_modules', 'activated_lines', 'seconds')}))


if __name__ == '__main__':
    main()
