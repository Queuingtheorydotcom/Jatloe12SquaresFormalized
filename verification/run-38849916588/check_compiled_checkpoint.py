#!/usr/bin/env python3
"""Authenticate the existing N12 build against the successful run, without Lean.

Uses only Python's standard library, one process, streaming decompression, and
no extraction. The only output file is the requested small JSON report.

Example:
  python3 check_compiled_checkpoint.py --archive CHECKPOINT.zip \
    --evidence SUCCESSFUL_RUN_EVIDENCE --project N12_SOURCE_DIRECTORY \
    --report compiled-checkpoint-verification.json
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import tarfile
import zipfile

EXPECTED_ARCHIVE_SHA256 = '7a20bbdfc76a6f066dc6795e3c50b38c81641c5e99d4dff47536cc6fc1772496'
EXPECTED_ARCHIVE_BYTES = 1033472991
EXPECTED_EVIDENCE_RECEIPTS_SHA256 = 'd70074e3eed105e24633d69bc87798fcd2a0b8f05ae53b3ae1f464a354193b52'
EXPECTED_SUCCESS_REPORT_SHA256 = '483e85130a7b4b31f22241c9d7725fbfc018809c158f23ea250f3c1546458798'
EXPECTED_SOURCE_COMMIT = '1f60d412707aae824b76fbaf11d4e708695451fa'
EXPECTED_CHECKPOINT_COMMIT = '437041a0f00f1ff9166e46b1f7fc93942a441681'
EXPECTED_MODULES = 5377
INDEX = '.verification/checked-modules.json'
MAX_METADATA = 16 * 1024**2
CHUNK = 1024**2


def require(condition, message):
    if not condition:
        raise ValueError(message)


def file_sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(CHUNK), b''):
            digest.update(chunk)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--report', required=True, type=Path)
    args = parser.parse_args()

    require(args.archive.stat().st_size == EXPECTED_ARCHIVE_BYTES, 'Wrong artifact ZIP size')
    require(file_sha256(args.archive) == EXPECTED_ARCHIVE_SHA256, 'Wrong artifact ZIP SHA256')
    print('Artifact ZIP SHA256 verified.', flush=True)

    receipt_file = args.evidence / 'checked-modules.json'
    require(file_sha256(receipt_file) == EXPECTED_EVIDENCE_RECEIPTS_SHA256,
            'Receipt index is not the authenticated successful-run index')
    receipts = json.loads(receipt_file.read_text())
    require(len(receipts) == EXPECTED_MODULES, 'Unexpected receipt count')
    success_file = args.evidence / 'github-replay.json'
    require(file_sha256(success_file) == EXPECTED_SUCCESS_REPORT_SHA256,
            'Success report differs from the authenticated run evidence')
    success = json.loads(success_file.read_text())
    require(success['run_identity'] == {
        'repository': 'EvolvingPrograms/SquaresLean',
        'run_id': '38849916588', 'run_attempt': '1',
        'commit': EXPECTED_SOURCE_COMMIT, 'profile': 'final'}, 'Wrong successful-run identity')
    require(success['compilation_complete'] is True and success['global_optimality_proved'] is True,
            'Final audited success is absent')

    expected_hashes = {}
    for module, receipt in receipts.items():
        require(re.fullmatch(r'(?:S12|Compact|Completion)(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module),
                'Invalid project module name')
        record = receipt['record']
        require(receipt['receipt_version'] == 2 and record['module'] == module
                and record['returncode'] == 0 and record['lean_returncode'] == 0
                and record['rejected_admission'] is False, 'Invalid accepted module receipt: ' + module)
        relative_source = Path(*module.split('.')).with_suffix('.lean')
        source = args.project / ('source' if module.startswith('S12.') else '') / relative_source
        require(file_sha256(source) == record['source_sha256'], 'Source hash mismatch: ' + module)
        expected_hashes['.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'] = receipt['object_sha256']
        expected_hashes['.verification/' + module + '.log'] = record['log_sha256']
    print(f'Authenticated all {len(receipts)} sources and successful receipts.', flush=True)

    expected_paths = set(expected_hashes) | {INDEX}
    seen = set()
    payload_bytes = 0
    log_bytes = 0
    object_bytes = 0
    archive_receipts_sha256 = None
    with zipfile.ZipFile(args.archive) as outer:
        entries = outer.infolist()
        require(len(entries) == 1 and entries[0].filename == 'checkpoint.tar',
                'Artifact ZIP must contain exactly checkpoint.tar')
        tar_bytes = entries[0].file_size
        with outer.open(entries[0]) as compressed:
            with tarfile.open(fileobj=compressed, mode='r|*') as inner:
                first = inner.next()
                require(first is not None and first.name == 'checkpoint.json' and first.isfile()
                        and first.size <= MAX_METADATA, 'Missing or excessive checkpoint metadata')
                metadata = json.load(inner.extractfile(first))
                require(metadata['repository'] == 'EvolvingPrograms/SquaresLean'
                        and metadata['commit'] == EXPECTED_CHECKPOINT_COMMIT
                        and metadata['run_id'] == '38847898861'
                        and str(metadata['run_attempt']) == '1'
                        and metadata['profile'] == 'final'
                        and metadata['modules'] == EXPECTED_MODULES
                        and metadata['schema'] == 1 and metadata['receipt_protocol'] == 2,
                        'Unexpected checkpoint provenance')
                inventory = metadata['files']
                require(set(inventory) == expected_paths,
                        'Checkpoint inventory is not exactly the accepted .olean/log pairs and receipts')
                for name, digest in expected_hashes.items():
                    require(inventory[name]['sha256'] == digest,
                            'Inventory differs from successful receipt: ' + name)
                for member in inner:
                    if member.name == 'checkpoint.json' and member is first:
                        continue
                    require(member.isfile() and member.name in expected_paths and member.name not in seen,
                            'Unexpected, nonregular, or duplicate archive member: ' + member.name)
                    require(member.size == inventory[member.name]['size'], 'Member size mismatch: ' + member.name)
                    if member.name == INDEX:
                        require(member.size <= MAX_METADATA, 'Excessive receipt metadata')
                    hasher = hashlib.sha256()
                    index_chunks = []
                    with inner.extractfile(member) as stream:
                        for chunk in iter(lambda: stream.read(CHUNK), b''):
                            hasher.update(chunk)
                            if member.name == INDEX:
                                index_chunks.append(chunk)
                    actual = hasher.hexdigest()
                    require(actual == inventory[member.name]['sha256'], 'Member SHA256 mismatch: ' + member.name)
                    if member.name == INDEX:
                        archive_receipts_sha256 = actual
                        require(json.loads(b''.join(index_chunks)) == receipts,
                                'Archive receipts differ from successful-run receipts')
                    else:
                        require(actual == expected_hashes[member.name],
                                'Member differs from successful-run receipt: ' + member.name)
                    payload_bytes += member.size
                    if member.name.endswith('.olean'):
                        object_bytes += member.size
                    elif member.name.endswith('.log'):
                        log_bytes += member.size
                    seen.add(member.name)
                    if len(seen) % 1000 == 0:
                        print(f'Authenticated {len(seen)}/{len(expected_paths)} archive payload files.', flush=True)
                require(seen == expected_paths, 'Checkpoint is missing accepted payload files')
            # Reach the ZIP member's EOF to complete its CRC check, including
            # trailing tar padding. No extracted copy is written to disk.
            for _ in iter(lambda: compressed.read(CHUNK), b''):
                pass

    report = {
        'schema_version': 1,
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'artifact': {'repository': 'EvolvingPrograms/SquaresLean', 'artifact_id': 12023379882,
                     'name': 'n12-jatloe-final-checkpoint-1', 'run_id': '38847898861',
                     'run_attempt': 1, 'commit': EXPECTED_CHECKPOINT_COMMIT,
                     'zip_bytes': EXPECTED_ARCHIVE_BYTES, 'zip_sha256': EXPECTED_ARCHIVE_SHA256},
        'authenticated_against_successful_run': {
            'run_id': '38849916588', 'job_id': '116808701733', 'run_attempt': 1,
            'source_commit': EXPECTED_SOURCE_COMMIT,
            'receipt_index_sha256': EXPECTED_EVIDENCE_RECEIPTS_SHA256,
            'success_report_sha256': EXPECTED_SUCCESS_REPORT_SHA256,
            'theorem': 'N12Compact.Final.optimality', 'type': 'S12.packingConstant12 = 4'},
        'archive_contents': {'zip_members': ['checkpoint.tar'], 'tar_bytes': tar_bytes,
                             'metadata_files': 1, 'receipt_index_files': 1,
                             'object_files': EXPECTED_MODULES, 'compiler_log_files': EXPECTED_MODULES,
                             'tar_regular_files': len(seen) + 1, 'payload_bytes': payload_bytes,
                             'object_bytes': object_bytes, 'compiler_log_bytes': log_bytes,
                             'archive_receipt_index_sha256': archive_receipts_sha256,
                             'sidecar_files': 0, 'external_library_files': 0,
                             'compiler_executable_files': 0},
        'checks': {'artifact_zip_sha256': True, 'nested_zip_crc': True,
                   'all_payload_member_sizes_and_sha256': True,
                   'all_5377_source_hashes_match_successful_run': True,
                   'all_5377_object_hashes_match_successful_run': True,
                   'all_5377_log_hashes_match_successful_run': True,
                   'archive_receipts_equal_successful_run_receipts': True,
                   'unexpected_or_missing_files': []},
        'checkpoint_platform': {k: metadata.get(k) for k in
                                ('system', 'machine', 'runner_os', 'runner_arch')},
        'checkpoint_configuration_hashes': metadata['configuration'],
        'verified_compiler_provenance': success['toolchain'],
        'compiled_during_this_check': False,
        'extracted_during_this_check': False,
        'scope': 'The earlier checkpoint objects are byte-identical to all 5377 objects '
                 'authenticated by the later successful final theorem audit. This check '
                 'validates preservation and correspondence, not a new Lean replay. '
                 'The checkpoint contains main .olean files, accepted compiler logs, and receipts; '
                 'Lean 4.35.0 sidecars, external libraries, and compiler binaries are not included. '
                 'Inherited native_decide compiler trust remains.',
    }
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print('PASS: all 5377 source/object/log correspondences authenticated; no extraction or compilation.', flush=True)


if __name__ == '__main__':
    main()
