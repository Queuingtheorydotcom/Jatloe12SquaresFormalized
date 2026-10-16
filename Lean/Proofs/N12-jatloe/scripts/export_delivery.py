#!/usr/bin/env python3
"""Plan, or explicitly install, a bounded portable source-only delivery.

No Lean, Lake, numerical producer, network request or Git mutation is run.
Default mode is read-only. --write stages an exact allowlisted snapshot;
--replace-existing additionally permits replacing the selected destination,
preserving its complete previous contents in a sibling backup.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import sys
import tempfile

sys.dont_write_bytecode = True
from verify import ROOT, closure, imports, path, has_admission

MANIFEST = ROOT / 'evidence/preferred-delivery-roots.json'
MATHLIB_PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
SCRIPTS = ['verify.py', 'bounded.py', 'source_budget.py', 'import_budget.py',
           'bootstrap_sources.py', 'prepare_cache.py', 'restore_cache.py',
           'export_delivery.py', 'CachePlan.lean']
EVIDENCE = ['evidence/preferred-delivery-roots.json',
            'evidence/virtual-preferred-source-config.json',
            'evidence/virtual-preferred-source-budget.json',
            'evidence/virtual-import-budget.json',
            'evidence/imported-source.json', 'evidence/congruent-sat-provenance.json',
            'evidence/seven-source-inventory.json',
            'evidence/historical-common-points/manifest.json',
            'evidence/historical-common-points/stages.json',
            'evidence/historical-common-points/own-support-selection.json',
            'evidence/historical-common-points/empty-certificates.json',
            'evidence/c898-all-common-points.json',
            'evidence/proposals/C898CommonPairs/manifest.json',
            'evidence/proposals/C898CyclicContexts/manifest.json',
            'evidence/historical-compact-data/manifest.json',
            'evidence/historical-fans-701-713-717-973-978-979-cycles/manifest.json',
            'evidence/current-assembled-source-budget.json',
            'evidence/preferred-source-budget.json',
            'evidence/proposals/HistoricalPoseFanRecipes/manifest.json',
            'evidence/all-import-budget.json',
            'evidence/c977-plan-dag.json', 'evidence/c977-replay-plan.json',
            'evidence/c977-vector-index-map.json',
            'evidence/c981-v116-symbolic.json', 'evidence/c981-vector-data-factor.json',
            'evidence/c981-ownership-import.json',
            'evidence/c981-catalogue-dependency-factor.json',
            'evidence/c898-terminal-common-activation.json',
            'audit/C981-evidence.json', 'audit/branch-heads-latest.json',
            'audit/branch-heads-2026-10-11.json',
            'audit/branch-comparisons-2026-10-11.json',
            'audit/branch-tree-refresh-2026-10-11.json',
            'audit/branch-library-sources-2026-10-11.json',
            'audit/branch-library-review-2026-10-11.json']
PERSONAL = re.compile(r'(?:/(?:Users|home)/[A-Za-z0-9_.-]+/|/private/(?:tmp|var/folders/[A-Za-z0-9_.-]+)/)[^\s\"\'<>`)\]]+')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def file_digest(file):
    result = hashlib.sha256()
    with file.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def scrub(text):
    # Documentation/metadata only. Lean and executable source are never edited.
    text = text.replace(str(ROOT), '.')
    return PERSONAL.sub(lambda m: 'LOCAL_PATH/' + Path(m.group()).name, text)


def safe_read(file):
    if file.is_symlink() or not file.is_file():
        raise ValueError('Missing or linked selected file: ' + str(file.relative_to(ROOT)))
    if not file.resolve().is_relative_to(ROOT.resolve()):
        raise ValueError('Selected file escapes project')
    return file.read_bytes()


def pins():
    math = ROOT / '.lake/packages/mathlib'
    if (math / '.source-pin').read_text().strip() != MATHLIB_PIN:
        raise ValueError('Installed Mathlib source pin does not match bootstrap pin')
    raw = json.loads((math / 'lake-manifest.json').read_text())
    packages = [{'name': 'mathlib', 'url': 'https://github.com/leanprover-community/mathlib4',
                 'rev': MATHLIB_PIN}]
    for p in raw['packages']:
        packages.append({key: p[key] for key in ['name', 'url', 'rev']})
    for p in packages:
        if not re.fullmatch(r'[0-9a-f]{40}', p['rev']):
            raise ValueError('Unpinned external dependency: ' + p['name'])
        actual = ROOT / '.lake/packages' / p['name'] / '.source-pin'
        if actual.read_text().strip() != p['rev']:
            raise ValueError('Dependency source pin differs: ' + p['name'])
    return {'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
            'packages': packages, 'external_sources_and_caches_exported': False,
            'restore': 'python3 scripts/bootstrap_sources.py (explicit network action)',
            'note': 'Pins identify sources; this is not a hash audit of external compiled objects.'}


def acceptance(modules, source_bytes):
    index = ROOT / '.verification/checked-modules.json'
    previous = json.loads(index.read_text()) if index.exists() else {}
    configuration = digest((ROOT / 'lean-toolchain').read_bytes() +
                           (ROOT / 'lake-manifest.json').read_bytes())
    fingerprints, valid, records = {}, {}, []
    for module in modules:
        raw = source_bytes[path(module).relative_to(ROOT).as_posix()]
        deps = [d for d in imports(raw.decode()) if d in fingerprints]
        source_hash = digest(raw)
        fingerprint = digest(json.dumps([configuration, source_hash,
            [(d, fingerprints[d]) for d in deps]], sort_keys=True).encode())
        fingerprints[module] = fingerprint
        old = previous.get(module)
        record = old.get('record', {}) if old else {}
        source_matches = record.get('source_sha256') == source_hash
        fingerprint_matches = bool(old) and old.get('fingerprint') == fingerprint
        obj = ROOT / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
        object_matches = bool(old) and obj.is_file() and file_digest(obj) == old.get('object_sha256')
        log = ROOT / '.verification' / (module + '.log')
        log_matches = bool(old) and log.is_file() and file_digest(log) == record.get('log_sha256')
        log_text = log.read_text() if log_matches else None
        log_admission_free = log_text is not None and not has_admission(log_text)
        own_valid = (source_matches and fingerprint_matches and object_matches and
                     record.get('returncode') == 0 and log_matches and log_admission_free)
        valid[module] = own_valid and all(valid[d] for d in deps)
        status = ('current_local_acceptance' if valid[module] else
                  'no_acceptance_receipt' if not old else
                  'previous_acceptance_not_current')
        axiom_lines = []
        if log_text is not None:
            axiom_lines = [scrub(line) for line in log_text.splitlines()
                           if 'depends on axioms:' in line or 'does not depend on any axioms' in line]
        records.append({'module': module, 'status': status, 'source_sha256': source_hash,
            'current_fingerprint': fingerprint, 'previous_fingerprint': old.get('fingerprint') if old else None,
            'source_matches_receipt': source_matches, 'dependency_configuration_matches': fingerprint_matches,
            'local_object_matches_receipt': object_matches,
            'all_local_dependencies_current': all(valid[d] for d in deps),
            'recorded_elapsed_seconds': record.get('elapsed_seconds'),
            'recorded_returncode': record.get('returncode'),
            'recorded_object_sha256': old.get('object_sha256') if old else None,
            'recorded_log_sha256': record.get('log_sha256'), 'log_matches_receipt': log_matches,
            'matched_log_admission_free': log_admission_free,
            'recorded_axiom_lines': axiom_lines})
    current_count = sum(r['status'] == 'current_local_acceptance' for r in records)
    return {'configuration_sha256': configuration,
        'scope': 'Same local source/dependency/configuration fingerprint and object hash rules as scripts/verify.py; no compilation performed during export.',
        'export_requires_full_lean_acceptance': False,
        'unverified_build_modules': len(records) - current_count,
        'all_selected_build_modules_currently_accepted': current_count == len(records),
        'source_export_is_not_proof_acceptance': True,
        'external_compiled_object_hashes_revalidated': False,
        'object_files_exported': False, 'whole_original_theorem_accepted': False,
        'counts': dict(Counter(r['status'] for r in records)), 'modules': records}


def make_payload(line_cap, byte_cap):
    selection = json.loads(MANIFEST.read_text())
    modules = closure(selection['roots'])
    files = {path(m).relative_to(ROOT).as_posix(): safe_read(path(m)) for m in modules}
    for module in modules:
        for dep in imports(files[path(module).relative_to(ROOT).as_posix()].decode()):
            if dep.split('.')[0] in {'Compact', 'Completion', 'S12'} and dep not in modules:
                raise ValueError('Source changed during import resolution; retry after edits stop.')
    expected_missing = {m for item in selection['unresolved_retained_draft_files']
                        for m in item.get('missing_imports', [item.get('missing_import')]) if m}
    pending = [ROOT / item['path'] for item in selection['unresolved_retained_draft_files']]
    while pending:
        draft = pending.pop()
        relative = draft.relative_to(ROOT).as_posix()
        if relative in files:
            continue
        files[relative] = safe_read(draft)
        for dep in imports(files[relative].decode()):
            if dep.split('.')[0] not in {'Compact', 'Completion', 'S12'}:
                continue
            source = path(dep)
            if not source.exists():
                if dep not in expected_missing:
                    raise ValueError('Unrecorded missing draft dependency: ' + dep)
            else:
                pending.append(source)
    exact_paths = set(files)
    for relative in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', '.gitignore']:
        files[relative] = safe_read(ROOT / relative)
        exact_paths.add(relative)
    for name in SCRIPTS:
        relative = 'scripts/' + name
        files[relative] = safe_read(ROOT / relative)
        exact_paths.add(relative)
    for relative in ['README.md', 'REFACTOR_PLAN.md'] + [
            p.relative_to(ROOT).as_posix() for p in sorted((ROOT / 'audit').glob('*.md'))] + EVIDENCE:
        files[relative] = scrub(safe_read(ROOT / relative).decode()).encode()
    for relative in exact_paths:
        if PERSONAL.search(files[relative].decode()):
            raise ValueError('Personal absolute path in exact source; fix explicitly before export: ' + relative)
    for relative, raw in files.items():
        if (b'file' + b'://') in raw or PERSONAL.search(raw.decode()):
            raise ValueError('Unresolved private local reference: ' + relative)
    lean = [{'path': relative, 'bytes': len(raw), 'lines': len(raw.splitlines()),
             'lexical_items': len(re.findall(rb'\w+|[^\w\s]', raw)), 'sha256': digest(raw)}
            for relative, raw in sorted(files.items()) if relative.endswith('.lean')]
    budget = {'scope': 'Every delivered Lean file, including unresolved adapter and Lean script helpers',
        'roots': selection['roots'], 'modules': len(lean), 'lines': sum(r['lines'] for r in lean),
        'bytes': sum(r['bytes'] for r in lean), 'lexical_items': sum(r['lexical_items'] for r in lean),
        'files': lean, 'exported_source_bytes_match_working_sources': True,
        'full_original_proof_assembled': False, 'eventual_submillion_bound_established': False}
    if budget['lines'] > line_cap or budget['bytes'] > byte_cap:
        print(json.dumps({key: budget[key] for key in ['modules', 'lines', 'bytes', 'lexical_items']}), flush=True)
        raise SystemExit('Delivery cap exceeded; no receipt-object scan or destination changes made.')
    checked = acceptance(modules, files)
    current_count = checked['counts'].get('current_local_acceptance', 0)
    incomplete_count = checked['unverified_build_modules']
    assembly = selection.get('candidate_activation', {})
    files['VERIFICATION-STATUS.md'] = (
        '# Verification status of this source snapshot\n\n'
        'This delivery preserves source, explicit mathematical obligations and separately '
        'matched local receipts. Export does not establish proof acceptance. '
        'The full original twelve-square theorem remains unfinished.\n\n'
        f'- {current_count} selected build modules have current matching local acceptance evidence.\n'
        f'- {incomplete_count} selected build modules still require ordinary Lean verification '
        'for these exact source and dependency bytes.\n'
        f'- {len(selection["unresolved_retained_draft_files"])} retained draft files have '
        'explicit missing original dependencies; they are not accepted build roots.\n\n'
        + ('The source was explicitly assembled without requiring pilot acceptance. '
           'That checkpoint creates no Lean acceptance or additional trust assumption.\n\n'
           if assembly.get('unverified_source_assembly') else '')
        + 'Run the normal admission-rejecting verifier on the selected roots before '
        'claiming acceptance of this complete source snapshot. '
        '`evidence/delivery-acceptance.json` records exact per-module matching results; '
        'previous success with different dependencies is labeled separately. '
        'Compiled objects and private local logs are not shipped.\n'
    ).encode()
    files['evidence/delivery-acceptance.json'] = encoded(checked)
    files['evidence/dependency-pins.json'] = encoded(pins())
    files['evidence/delivery-source-budget.json'] = encoded(budget)
    manifest = [{'path': relative, 'bytes': len(raw), 'sha256': digest(raw)}
                for relative, raw in sorted(files.items())]
    files['evidence/delivery-files.json'] = encoded({
        'files': manifest, 'self_excluded_from_hash_list': 'evidence/delivery-files.json',
        'exact_source_paths': sorted(exact_paths),
        'excluded': ['.lake', '.verification', 'vendor duplicates', 'large provenance data/archives',
                     'unactivated proposal source (small manifests retained)',
                     'superseded proof routes', 'standalone diagnostic modules'],
        'note': 'No excluded proof source is imported by the selected roots. Explicitly listed draft adapters retain all present dependencies and record every absent original import.'})
    return files, budget, checked, exact_paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', type=Path, required=True)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--replace-existing', action='store_true')
    parser.add_argument('--line-cap', type=int, default=300000)
    parser.add_argument('--byte-cap', type=int, default=40000000)
    args = parser.parse_args()
    if args.line_cap > 300000 or args.byte_cap > 40000000:
        parser.error('Do not relax delivery limits; simplify the retained proof source.')
    destination = args.destination.absolute()
    resolved = destination.resolve()
    if destination.is_symlink() or resolved.is_relative_to(ROOT.resolve()) or \
            ROOT.resolve().is_relative_to(resolved) or (destination / '.git').exists():
        parser.error('Unsafe destination')
    files, budget, checked, exact_paths = make_payload(args.line_cap, args.byte_cap)
    summary = {'lean_lines': budget['lines'], 'lean_files': budget['modules'],
        'lean_bytes': budget['bytes'], 'total_payload_bytes': sum(map(len, files.values())),
        'receipt_counts': checked['counts'], 'write_requested': args.write}
    print(json.dumps(summary), flush=True)
    if budget['lines'] > args.line_cap or budget['bytes'] > args.byte_cap:
        raise SystemExit('Delivery cap exceeded; no destination changes made.')
    if summary['total_payload_bytes'] > 64 * 1024 * 1024:
        raise SystemExit('Source/document snapshot exceeds 64 MiB; inspect allowlist.')
    if not args.write:
        return
    if shutil.disk_usage(destination.parent).free < 3 * 1024**3 + summary['total_payload_bytes'] + 8 * 1024**2:
        raise SystemExit('Three-GiB free-disk floor including the staged source snapshot.')
    for relative in exact_paths:
        if safe_read(ROOT / relative) != files[relative]:
            raise SystemExit('Source changed during export planning; no destination changes made.')
    if destination.exists() and not args.replace_existing:
        raise SystemExit('Existing delivery requires explicit --replace-existing; no changes made.')
    destination.parent.mkdir(parents=True, exist_ok=True)
    lock = destination.parent / ('.' + destination.name + '.export-lock')
    descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    os.close(descriptor)
    stage, backup = None, None
    def interrupted(signum, frame):
        raise KeyboardInterrupt('Export interrupted')
    signal.signal(signal.SIGTERM, interrupted)
    try:
        stage = Path(tempfile.mkdtemp(prefix='.' + destination.name + '.export-', dir=destination.parent))
        for relative, raw in files.items():
            output = stage / relative
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(raw)
        if destination.exists():
            stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
            backup = destination.with_name(destination.name + '.before-export-' + stamp)
            destination.rename(backup)
        try:
            stage.rename(destination)
            stage = None
        except BaseException:
            if backup is not None and not destination.exists():
                backup.rename(destination)
            raise
        print(json.dumps({'installed': destination.name,
                          'previous_delivery_preserved': backup.name if backup else None}), flush=True)
    finally:
        if stage is not None:
            shutil.rmtree(stage)
        lock.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
