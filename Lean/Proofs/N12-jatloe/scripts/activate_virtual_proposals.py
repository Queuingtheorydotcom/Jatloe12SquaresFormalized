#!/usr/bin/env python3
"""Transactionally activate an authenticated virtual source selection.

Prepared for the parent's explicit serial execution. The default write mode
requires accepted pilots. --assemble-unverified permits a source checkpoint
only; it never creates acceptance evidence or changes accepted registry source.
No Lean, numeric generators, cache deletion, publishing or delivery export.
Old source bytes are backed up before any mutation and restored on failure.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import time
from verify import ROOT, path as module_path, imports, has_admission


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def safe(name):
    path = ROOT / name
    if '..' in path.parts or not path.is_relative_to(ROOT):
        raise ValueError('Path outside working project: ' + str(name))
    cursor = ROOT
    for part in path.relative_to(ROOT).parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise ValueError('Refusing symlink component: ' + str(cursor))
    path = path.resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError('Resolved path outside working project: ' + str(name))
    return path


def atomic(path, raw):
    path = safe(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.activation-tmp')
    if temporary.exists() or temporary.is_symlink():
        raise ValueError('Refusing existing temporary path: ' + str(temporary))
    try:
        temporary.write_bytes(raw)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def restore(receipt_path):
    backup = receipt_path.parent
    archive = ROOT / 'evidence/source-archive'
    if not backup.is_relative_to(archive) or not backup.name.startswith('virtual-activation-'):
        raise ValueError('Not a virtual activation backup')
    receipt = json.loads(receipt_path.read_text())
    planned = []
    for record in receipt['files']:
        if Path(record['path']).is_absolute():
            raise ValueError('Rollback record must use a relative source path')
        target = safe(record['path'])
        if target.suffix != '.lean' and target != ROOT / 'evidence/preferred-delivery-roots.json':
            raise ValueError('Unexpected rollback target: ' + str(target))
        current = target.read_bytes() if target.exists() else None
        current_hash = sha(current) if current is not None else None
        if current_hash not in [record['before_sha256'], record['after_sha256']]:
            raise ValueError('Source has independent later edits; rollback stopped: ' + str(target))
        old = None if record['before_sha256'] is None else safe(backup / record['path']).read_bytes()
        if old is not None and sha(old) != record['before_sha256']:
            raise ValueError('Backup hash mismatch: ' + record['path'])
        planned.append((target, old))
    # Recovery is resumable: every target may be in either authenticated state.
    # A durable small journal records completed restores without repeatedly
    # rewriting the full thousands-file receipt.
    receipt['status'] = 'explicit rollback in progress; safe to resume'
    atomic(receipt_path, (json.dumps(receipt, indent=2) + '\n').encode())
    def interrupted(signum, frame):
        raise RuntimeError('Rollback interrupted; rerun --rollback to resume')
    handlers = {s: signal.signal(s, interrupted) for s in (signal.SIGTERM, signal.SIGINT)}
    try:
        with (backup / 'rollback-progress.jsonl').open('a') as journal:
            for target, old in planned:
                if old is None:
                    target.unlink(missing_ok=True)
                else:
                    atomic(target, old)
                journal.write(json.dumps({'restored': str(target.relative_to(ROOT))}) + '\n')
                journal.flush()
                os.fsync(journal.fileno())
        receipt['status'] = 'explicit rollback restored all original source bytes'
    except BaseException:
        receipt['status'] = 'explicit rollback interrupted; authenticated states allow resumption'
        atomic(receipt_path, (json.dumps(receipt, indent=2) + '\n').encode())
        raise
    finally:
        for s, handler in handlers.items():
            signal.signal(s, handler)
    atomic(receipt_path, (json.dumps(receipt, indent=2) + '\n').encode())
    print(json.dumps({'rollback': str(receipt_path.relative_to(ROOT)), 'files': len(planned)}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path,
        default=Path('evidence/virtual-preferred-source-budget.json'))
    parser.add_argument('--gates', type=Path,
        help='JSON list of required accepted pilot module names; parent chooses the exact scope')
    parser.add_argument('--assemble-unverified', action='store_true',
        help='Assemble source without pilot acceptance; all ordinary Lean verification remains required')
    parser.add_argument('--rollback', type=Path,
        help='Restore an activation receipt after an interruption; requires --run')
    parser.add_argument('--line-cap', type=int, default=300000)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if args.line_cap > 300000 or args.line_cap <= 0:
        parser.error('Keep the complete source cap at or below 300000 lines')
    if args.rollback:
        if not args.run:
            parser.error('Explicit --run is required for rollback')
        restore(safe(args.rollback))
        return
    if args.assemble_unverified and args.gates is not None:
        parser.error('Choose either unverified source assembly or explicit accepted pilot gates')
    if args.gates is None and not args.assemble_unverified:
        parser.error('--gates is required for candidate activation')
    started = time.monotonic()
    report_path = safe(args.report)
    report_raw = report_path.read_bytes()
    report = json.loads(report_raw)
    config_path = safe(report['config'])
    config_raw = config_path.read_bytes()
    if sha(config_raw) != report['config_sha256']:
        raise ValueError('Virtual source selection changed; rerun its census')
    config = json.loads(config_raw)
    preferred_path = safe(config.get('preferred_manifest',
                                     'evidence/preferred-delivery-roots.json'))
    preferred_raw = preferred_path.read_bytes()
    if sha(preferred_raw) != report['preferred_manifest_sha256']:
        raise ValueError('Preferred roots changed; rerun virtual census')
    if report['unexpected_missing_imports']:
        raise ValueError('Unexpected project imports are missing')
    if report['summary']['lines'] > args.line_cap:
        raise ValueError('Complete retained source exceeds the explicit line cap')
    if report['summary']['bytes'] > 40_000_000:
        raise ValueError('Complete retained source exceeds40MB')

    # Pilot logs and objects are real accepted evidence, never supplied by a
    # generated certificate. Full source acceptance is explicitly not inferred.
    gates_raw = b'' if args.assemble_unverified else safe(args.gates).read_bytes()
    gates = [] if args.assemble_unverified else json.loads(gates_raw)
    if not args.assemble_unverified and (not isinstance(gates, list) or not gates):
        raise ValueError('The parent must select nonempty explicit pilot gates')
    index = {} if args.assemble_unverified else json.loads(
        (ROOT / '.verification/checked-modules.json').read_text())
    configuration = sha((ROOT / 'lean-toolchain').read_bytes() +
                        (ROOT / 'lake-manifest.json').read_bytes())
    fingerprints = {}
    active_fingerprints = set()

    def fingerprint(module):
        if module in fingerprints:
            return fingerprints[module]
        if module in active_fingerprints:
            raise ValueError('Pilot import cycle: ' + module)
        active_fingerprints.add(module)
        raw = module_path(module).read_bytes()
        deps = [(d, fingerprint(d)) for d in imports(raw.decode())
                if d.split('.')[0] in {'Compact', 'Completion', 'S12'}]
        value = sha(json.dumps([configuration, sha(raw), deps], sort_keys=True).encode())
        active_fingerprints.remove(module)
        fingerprints[module] = value
        return value
    pilot_receipts = []
    for module in gates:
        if not re.fullmatch(r'[A-Za-z0-9_.]+', module):
            raise ValueError('Invalid pilot module')
        old = index.get(module, {})
        record = old.get('record', {})
        source = module_path(module)
        log = ROOT / '.verification' / (module + '.log')
        obj = ROOT / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
        if record.get('returncode') != 0 or not source.exists() or not log.exists() or not obj.exists():
            raise ValueError('Pilot is not accepted: ' + module)
        log_raw = log.read_bytes()
        if sha(source.read_bytes()) != record.get('source_sha256') or \
                sha(log_raw) != record.get('log_sha256') or has_admission(log_raw.decode()) or \
                sha(obj.read_bytes()) != old.get('object_sha256') or \
                fingerprint(module) != old.get('fingerprint'):
            raise ValueError('Pilot source/log/object no longer matches acceptance: ' + module)
        pilot_receipts.append({'module': module, 'record': record,
                               'object_sha256': old['object_sha256']})

    for overlay in report['overlays_in_priority_order']:
        if sha(safe(overlay['manifest']).read_bytes()) != overlay['manifest_sha256']:
            raise ValueError('Proposal manifest changed: ' + overlay['name'])
    selected = {}
    pending = {}
    target_snapshots = {}
    for source in report['files']:
        actual = safe(source['path'])
        raw = actual.read_bytes()
        if sha(raw) != source['sha256']:
            raise ValueError('Selected source changed: ' + source['path'])
        module = source['module_or_draft']
        if module.endswith('.lean'):
            continue
        selected[module] = raw
        target = safe(module_path(module).relative_to(ROOT))
        current = target.read_bytes() if target.exists() else None
        if module in {'Compact.Assembly.SymbolicRegistry', 'Compact.Assembly.Remaining117'} and current != raw:
            raise ValueError('Source assembly cannot modify the accepted registry: ' + module)
        if actual != target and current != raw:
            pending[target] = raw
            target_snapshots[target] = current

    # Check the actual selected closure again before trusting a source budget.
    # Known missing draft dependencies never become ordinary build assumptions.
    forbidden = config.get('forbidden_module_prefixes', [])
    required_build = set()
    def check_build(module):
        if module in required_build:
            return
        if module not in selected:
            raise ValueError('Missing selected build source: ' + module)
        required_build.add(module)
        for dependency in imports(selected[module].decode()):
            if any(dependency.startswith(p) for p in forbidden):
                raise ValueError('Retired proof route remains imported by ' + module)
            if dependency.split('.')[0] in {'Compact', 'Completion', 'S12'}:
                check_build(dependency)
    for module in report['roots'] + report['explicitly_retained_outside_root_closure']:
        check_build(module)

    # Only explicitly replaced routes are retired. Other useful source and all
    # compiler artifacts remain untouched. The final export has its own census.
    retire = []
    for prefix in forbidden:
        directory = ROOT / Path(*prefix.rstrip('.').split('.')).parent
        if not directory.exists():
            continue
        for candidate in directory.rglob('*.lean'):
            candidate = safe(candidate.relative_to(ROOT))
            relative = candidate.relative_to(ROOT).with_suffix('')
            module = '.'.join(relative.parts)
            if module.startswith(prefix) and module not in selected:
                retire.append(candidate)
    retire = sorted(set(retire))

    preferred = json.loads(preferred_raw)
    # The census deliberately counts production outputs even when they are not
    # reached by a top-level theorem. Preserve these as explicit roots so the
    # later portable export cannot silently discard genuinely retained source.
    preferred['roots'] = list(dict.fromkeys(report['roots'] +
        report['explicitly_retained_outside_root_closure']))
    preferred['explicitly_retained_production_roots'] = report['explicitly_retained_outside_root_closure']
    replacements = {r['old']: r for r in report['root_replacements']}
    for group in preferred.get('root_groups', []):
        changed = [replacements[r] for r in group['roots'] if r in replacements]
        if changed:
            group['roots'] = list(dict.fromkeys(r for old in group['roots']
                for r in replacements.get(old, {'new': [old]})['new']))
            group['role'] += ' (candidate representation replaced)'
            group['validation'] = ' '.join(r['contract_reason'] for r in changed)
    preferred['candidate_activation'] = {'virtual_report_sha256': sha(report_raw),
        'lines': report['summary']['lines'], 'all_candidate_modules_accepted': False,
        'unverified_source_assembly': args.assemble_unverified,
        'accepted_registry_changed': False,
        'note': ('UNVERIFIED SOURCE ASSEMBLY: no pilot gates were required and no Lean acceptance '
                 'or new trust assumption is asserted; full fresh ordinary verification is required.'
                 if args.assemble_unverified else
                 'Exact source selection activated after stated pilots; full ordinary replay remains required.')}
    pending[preferred_path] = (json.dumps(preferred, indent=2) + '\n').encode()
    target_snapshots[preferred_path] = preferred_raw
    changed = list(dict.fromkeys(list(pending) + retire))
    additional_disk = (sum(len(raw) for raw in pending.values()) +
        sum(target.stat().st_size for target in changed if target.exists()) + 8 * 1024**2)
    summary = {'source_files_to_write': len(pending) - 1,
        'retired_source_files': len(retire), 'selected_source': report['summary'],
        'additional_disk_reserve_bytes': additional_disk,
        'pilot_gates': gates, 'unverified_source_assembly': args.assemble_unverified,
        'accepted_registry_changed': False, 'new_trust_assumptions': False,
        'full_candidate_acceptance_claim': False,
        'required_next_action': 'Full fresh source verification using the normal admission-rejecting verifier'}
    if not args.run:
        print(json.dumps({'mode': 'read-only activation plan', **summary}))
        return
    if shutil.disk_usage(ROOT).free < 3 * 1024**3 + additional_disk:
        raise ValueError('Three-GiB free-disk floor including new source and backup reserve')

    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    backup = ROOT / 'evidence/source-archive' / ('virtual-activation-' + stamp + '-' + sha(report_raw)[:10])
    backup.mkdir(parents=True, exist_ok=False)
    old_bytes = {}
    backups = []
    for target in changed:
        if target.is_symlink():
            raise ValueError('Refusing symlink mutation: ' + str(target))
        raw = target.read_bytes() if target.exists() else None
        if target in target_snapshots and raw != target_snapshots[target]:
            raise ValueError('Active source changed before mutation: ' + str(target))
        old_bytes[target] = raw
        if raw is not None:
            destination = backup / target.relative_to(ROOT)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(raw)
        backups.append({'path': str(target.relative_to(ROOT)),
                        'before_sha256': sha(raw) if raw is not None else None,
                        'after_sha256': sha(pending[target]) if target in pending else None})
    receipt = {'status': 'backed up before mutation', 'report_sha256': sha(report_raw),
        'gates_sha256': None if args.assemble_unverified else sha(gates_raw),
        'pilots': pilot_receipts, 'files': backups, **summary}
    receipt_path = backup / 'activation-receipt.json'
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    touched = []
    def interrupted(signum, frame):
        raise RuntimeError('Activation interrupted by signal ' + str(signum))
    previous_handlers = {s: signal.signal(s, interrupted) for s in (signal.SIGTERM, signal.SIGINT)}
    try:
        for target, raw in pending.items():
            touched.append(target)
            atomic(target, raw)
        for target in retire:
            touched.append(target)
            target.unlink()
        for module, expected in selected.items():
            if module_path(module).read_bytes() != expected:
                raise ValueError('Post-activation source differs: ' + module)
        receipt['status'] = ('UNVERIFIED SOURCE ASSEMBLED; no Lean acceptance; full fresh verification required'
            if args.assemble_unverified else 'candidate source activated; full replay pending')
    except BaseException as error:
        for s in previous_handlers:
            signal.signal(s, signal.SIG_IGN)
        rollback_errors = []
        for target in reversed(touched):
            try:
                if old_bytes[target] is None:
                    target.unlink(missing_ok=True)
                else:
                    atomic(target, old_bytes[target])
            except BaseException as rollback_error:
                rollback_errors.append(str(rollback_error))
        receipt.update(status='failed and rollback attempted', error=repr(error),
                       rollback_errors=rollback_errors)
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
        raise
    finally:
        for s, handler in previous_handlers.items():
            signal.signal(s, handler)
    receipt['seconds'] = round(time.monotonic() - started, 3)
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'receipt': str(receipt_path.relative_to(ROOT)), **summary}))


if __name__ == '__main__':
    main()
