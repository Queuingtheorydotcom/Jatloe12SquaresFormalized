#!/usr/bin/env python3
"""Publish an explicit source checkpoint and two handoffs; never invoke Lean.

Unlike export_delivery.py's sub-300k delivery gate, this is an explicitly
unfinished preservation snapshot. It reports the preferred proof scope and
all other retained source separately. It never claims the size target is met.
Use bounded.py. No Git, network, compiler, producer or child process is invoked.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
MAX_BYTES = 180 * 1024**2
PRIVATE = re.compile(r'/(?:Users|home)/[A-Za-z0-9_.-]+/[^\s\"\'<>`)\]]+|/private/(?:tmp|var/folders)/[^\s\"\'<>`)\]]+')
SECRETS = re.compile(r'ghp_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{30,}|sk-proj-[A-Za-z0-9_-]{30,}|-----BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY-----')
BASE = 'c5c6144349a141e56ac43c81ed732f731c591eac'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def strip_lean(source):
    # Nested block comments, line comments and strings are not proof declarations.
    result, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            result.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            result.append(' ')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean comment')
    return ''.join(result)


def selected():
    files = set()
    for directory in ['Compact', 'Completion', 'source', 'adapters', 'scripts', 'audit', 'handoff']:
        for p in (ROOT / directory).rglob('*'):
            if p.is_file() and not p.is_symlink() and '__pycache__' not in p.parts:
                if p.suffix in {'.lean', '.py', '.md', '.json', '.jsonl', '.tsv', '.toml', '.sh'}:
                    files.add(p.relative_to(ROOT).as_posix())
    evidence = ROOT / 'evidence'
    omitted_trees = {'historical', 'source-archive', 'staging', 'retired', '__pycache__'}
    for p in evidence.rglob('*'):
        if not p.is_file() or p.is_symlink():
            continue
        relative = p.relative_to(evidence)
        if any(part in omitted_trees for part in relative.parts):
            continue
        if p.parent == evidence or 'manifest' in p.name.lower() or p.suffix == '.md':
            if p.suffix in {'.json', '.jsonl', '.md', '.tsv', '.txt', '.csv'}:
                files.add(p.relative_to(ROOT).as_posix())
    files.update(['Compact.lean', 'README.md', 'REFACTOR_PLAN.md', '.gitignore',
                  'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'])
    return sorted(files)


def stage(destination):
    if destination.exists():
        raise ValueError('Snapshot destination must be new; no existing files are replaced')
    names = selected()
    size = sum((ROOT / n).stat().st_size for n in names)
    if size > MAX_BYTES or shutil.disk_usage(destination.parent).free < 3 * 1024**3 + size:
        raise ValueError('Source checkpoint size/free-disk guard')
    preferred = json.loads((ROOT / 'evidence/active-preferred-source-budget.json').read_text())
    if preferred['unexpected_missing_imports']:
        raise ValueError('Unexpected missing preferred imports')
    active = {r['path']: r for r in preferred['files']}
    inventory, declarations, native, edited_docs = [], [], [], []
    checked_python = []
    destination.mkdir()
    def put(name, raw):
        out = destination / name
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(raw)
    try:
        for name in names:
            p = ROOT / name
            raw = p.read_bytes()
            if len(raw) > 16 * 1024**2:
                raise ValueError('Single-file guard: ' + name)
            text = raw.decode('utf-8')
            if p.suffix in {'.md', '.json', '.jsonl', '.tsv', '.txt', '.csv'}:
                clean = text.replace(str(ROOT), '.')
                clean = PRIVATE.sub(lambda m: 'LOCAL_PATH/' + Path(m.group()).name, clean)
                if clean != text:
                    edited_docs.append(name)
                text = clean
            if PRIVATE.search(text) or SECRETS.search(text) or 'file' + '://' in text:
                raise ValueError('Unresolved private path or secret pattern: ' + name)
            output = text.encode()
            if p.suffix == '.py':
                ast.parse(text, filename=name)
                checked_python.append(name)
            if p.suffix == '.lean':
                code = strip_lean(text)
                if re.search(r'\b(?:sorry|admit|sorryAx)\b|^\s*(?:private\s+|public\s+)?axiom\s', code, re.M):
                    declarations.append(name)
                sites = len(re.findall(r'\b(?:native_decide|ofReduceBool)\b', code))
                if sites:
                    native.append({'path': name, 'sites': sites, 'preferred': name in active})
                if name in active and sha(raw) != active[name]['sha256']:
                    raise ValueError('Preferred source changed after census: ' + name)
                inventory.append({'path': name, 'sha256': sha(output), 'bytes': len(output),
                                  'lines': len(output.splitlines()), 'preferred': name in active})
            put(name, output)
        if declarations:
            raise ValueError('Admission or custom axiom declaration: ' + repr(declarations))
        new_native = [r for r in native if r['path'].startswith(('Compact/', 'Completion/'))]
        if new_native:
            raise ValueError('Native decision site in new project source: ' + repr(new_native))
        if not set(active).issubset(names):
            raise ValueError('Preferred source omitted')
        put('handoff/source-inventory.json', encode({
            'preferred': preferred['summary'], 'all_retained_source': {
                'files': len(inventory), 'lines': sum(r['lines'] for r in inventory),
                'bytes': sum(r['bytes'] for r in inventory)}, 'files': inventory,
            'unselected_source_is_not_part_of_preferred_proof': True,
            'whole_theorem_complete': False, 'compiled_during_publication': False}))
        put('handoff/static-source-audit.json', encode({
            'scope': 'Source token/import/hash checks only, not Lean acceptance',
            'admission_or_custom_axiom_files': declarations,
            'inherited_native_sites': native, 'new_project_native_sites': new_native,
            'python_syntax_checked': checked_python, 'documentation_paths_redacted': edited_docs,
            'unexpected_preferred_imports': preferred['unexpected_missing_imports'],
            'retained_draft_missing_imports': preferred['missing_imports'],
            'compiled': False, 'private_archives_or_logs_included': False}))
        original = json.loads((ROOT / '.lake/packages/mathlib/lake-manifest.json').read_text())
        put('handoff/dependency-pins.json', encode({
            'lean': (ROOT / 'lean-toolchain').read_text().strip(),
            'mathlib': {'url': 'https://github.com/leanprover-community/mathlib4',
                        'rev': (ROOT / '.lake/packages/mathlib/.source-pin').read_text().strip()},
            'packages': [{k: p[k] for k in ['name', 'url', 'rev']} for p in original['packages']],
            'objects_included': False}))
        omitted = []
        for p in sorted((ROOT / 'evidence').rglob('*')):
            if p.is_file() and not p.is_symlink() and '__pycache__' not in p.parts:
                relative = p.relative_to(ROOT).as_posix()
                if relative not in names:
                    omitted.append({'path': relative, 'bytes': p.stat().st_size})
        put('handoff/omitted-evidence-inputs.json', encode({
            'reason': 'Historical raw corpora, superseded generated intermediates and duplicate proposal payloads are not build inputs for the preferred source. Current Lean source, all audit notes, producer scripts and selected provenance manifests are retained. Original local inputs remain untouched.',
            'records': omitted}))
        files = [{'path': p.relative_to(destination).as_posix(), 'sha256': sha(p.read_bytes()),
                  'bytes': p.stat().st_size} for p in sorted(destination.rglob('*')) if p.is_file()]
        payload_hash = sha(encode(files))
        put('handoff/PUBLICATION-MANIFEST.json', encode({
            'branch': '12Refractored', 'base_commit': BASE, 'files': files,
            'snapshot_sha256': payload_hash,
            'self_excluded': 'handoff/PUBLICATION-MANIFEST.json',
            'whole_theorem_complete': False, 'compilation_performed': False}))
        print(json.dumps({'staged_files': len(files) + 1, 'source_bytes': size,
                          'snapshot_sha256': payload_hash, 'preferred': preferred['summary'],
                          'all_retained_lean_lines': sum(r['lines'] for r in inventory),
                          'inherited_native_files': len(native)}))
    except BaseException:
        # Only this new, unpublished directory is removed on failure.
        shutil.rmtree(destination)
        raise


def archives(destination, output, commit):
    manifest = json.loads((destination / 'handoff/PUBLICATION-MANIFEST.json').read_text())
    if not re.fullmatch('[0-9a-f]{40}', commit):
        raise ValueError('Exact publication commit required')
    names = [r['path'] for r in manifest['files']] + ['handoff/PUBLICATION-MANIFEST.json']
    for record in manifest['files']:
        if sha((destination / record['path']).read_bytes()) != record['sha256']:
            raise ValueError('Staged source changed: ' + record['path'])
    output.mkdir(parents=True, exist_ok=True)
    receipt = {'commit': commit, 'snapshot_sha256': manifest['snapshot_sha256'], 'archives': []}
    for kind in ['lean', 'mathematics']:
        target = output / ('12Refractored-' + kind + '-handoff.zip')
        if target.exists():
            raise ValueError('Existing handoff archive will not be overwritten')
        prefix = '12Refractored-' + kind
        chosen = names if kind == 'lean' else [n for n in names if
            n.startswith(('handoff/', 'audit/', 'Compact/Geometry/', 'Compact/Bridge/',
                          'Compact/Assembly/', 'Compact/Core/', 'Completion/', 'source/',
                          'Compact/Cases/C868/', 'Compact/Cases/C849851/')) or
            n in {'Compact/Cases/C981Compact.lean', 'Compact/Cases/C1092Compact.lean',
                  'evidence/right-bar-broad-domains.json', 'evidence/preferred-delivery-roots.json'}]
        zip_manifest = []
        try:
            with zipfile.ZipFile(target, 'w', zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
                def add(name, raw):
                    info = zipfile.ZipInfo(prefix + '/' + name, (2026, 10, 11, 0, 0, 0))
                    info.compress_type = zipfile.ZIP_DEFLATED
                    info.external_attr = 0o100644 << 16
                    archive.writestr(info, raw)
                    zip_manifest.append({'path': name, 'sha256': sha(raw), 'bytes': len(raw)})
                for name in chosen:
                    add(name, (destination / name).read_bytes())
                add('PUBLICATION.json', encode({'repository': 'EvolvingPrograms/SquaresLean',
                    'branch': '12Refractored', 'commit': commit,
                    'snapshot_sha256': manifest['snapshot_sha256'], 'package': kind,
                    'mathematics_package_is_not_a_standalone_build': kind == 'mathematics'}))
                start = ('# Start here\n\nRead `handoff/' +
                         ('LEAN-HANDOFF.md' if kind == 'lean' else 'MATHEMATICS-HANDOFF.md') +
                         '`, then `handoff/CHECKPOINT.md`.\n\n' +
                         ('This is the complete retained source checkpoint; dependencies and compiled objects are excluded.\n' if kind == 'lean' else
                          'This package contains mathematical notes, exact contracts and relevant source references. Use the Lean ZIP or published branch for the complete build source.\n') +
                         '\nThe theorem remains unfinished. New source is uncompiled.\n')
                add('START-HERE.md', start.encode())
                add('ZIP-MANIFEST.json', encode({'files': zip_manifest.copy(),
                    'self_excluded': 'ZIP-MANIFEST.json'}))
            with zipfile.ZipFile(target) as archive:
                bad = archive.testzip()
                if bad:
                    raise ValueError('Archive CRC failure: ' + bad)
                for record in zip_manifest:
                    if sha(archive.read(prefix + '/' + record['path'])) != record['sha256']:
                        raise ValueError('Archive hash mismatch')
            receipt['archives'].append({'filename': target.name, 'bytes': target.stat().st_size,
                'sha256': sha(target.read_bytes()), 'files': len(zip_manifest), 'crc_and_hashes_pass': True})
        except BaseException:
            target.unlink(missing_ok=True)
            raise
    (output / 'PUBLICATION-RECEIPT.json').write_bytes(encode(receipt))
    print(json.dumps(receipt))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['stage', 'archives'])
    parser.add_argument('--destination', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--commit')
    args = parser.parse_args()
    if args.mode == 'stage':
        stage(args.destination)
    else:
        if not args.output or not args.commit:
            parser.error('Archives require --output and --commit')
        archives(args.destination, args.output, args.commit)


if __name__ == '__main__':
    main()
