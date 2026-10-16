#!/usr/bin/env python3
"""Losslessly compress only inactive task-local historical JSON provenance.

Prepared for the parent's serial resource slot; --run is mandatory. Stream
one file at a time, verify the complete decompressed SHA-256 and byte length,
durably journal that verification, and only then unlink the unchanged plain
file. Readers use provenance_source, so logical paths/hashes stay unchanged.
No JSON is executed or parsed, and active data and user archives are excluded.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import os
import resource
import shutil
import signal
import stat
import sys
import tempfile
import time

from provenance_source import compressed_path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'evidence/historical/data'
RECEIPT = ROOT / 'evidence/historical-json-compression'
CHUNK = 65536
TEMP_CAP = 64 * 1024**2


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def signature(info):
    return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns


def sync_directory(path):
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    need(parser.parse_args().run, 'prepared only; parent serial slot and --run required')
    start = time.monotonic()
    need(DATA.is_dir() and not DATA.is_symlink(), 'historical data directory is unavailable')
    need(DATA.resolve().is_relative_to(ROOT), 'data directory leaves the task')
    RECEIPT.mkdir(parents=True, exist_ok=True)
    journal_path = RECEIPT / 'records.jsonl'
    current_temp = None
    counts = {'verified_files': 0, 'removed_plain_files': 0, 'plain_bytes': 0,
              'gzip_bytes': 0, 'skipped_unprofitable': 0}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        rss *= 1 if sys.platform == 'darwin' else 1024
        need(rss < 128 * 1024**2, '128 MiB RSS limit')
        need(time.monotonic() - start < 115, '115-second working deadline')
        need(shutil.disk_usage(DATA).free >= 2 * 1024**3, '2 GiB free disk floor')

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .5, .5)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    def digest_stream(stream):
        digest = hashlib.sha256()
        size = 0
        while block := stream.read(CHUNK):
            guard()
            size += len(block)
            digest.update(block)
        return digest.hexdigest(), size

    def append(record):
        with journal_path.open('a') as journal:
            journal.write(json.dumps(record, separators=(',', ':')) + '\n')
            journal.flush()
            os.fsync(journal.fileno())
        sync_directory(RECEIPT)
        need(journal_path.stat().st_size < 8 * 1024**2, '8 MiB journal cap')

    status, error = 'complete', None
    try:
        files = sorted(DATA.rglob('*.json'), key=lambda path: path.stat().st_size, reverse=True)
        for path in files:
            guard()
            need(not path.is_symlink() and path.resolve().is_relative_to(DATA.resolve()),
                 'refusing symlink or path outside historical data')
            before = path.stat()
            need(stat.S_ISREG(before.st_mode), 'historical JSON is not a regular file')
            target = compressed_path(path)
            need(not target.is_symlink() and target.resolve().is_relative_to(DATA.resolve()),
                 'compressed target leaves historical data')
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                # Safely resume a previous verified compression whose final
                # unlink was interrupted. Existing bytes are never overwritten.
                with path.open('rb') as source:
                    original_hash, original_size = digest_stream(source)
            else:
                fd, temp_name = tempfile.mkstemp(prefix='.n12-json-gzip-', suffix='.part', dir=target.parent)
                current_temp = Path(temp_name)
                original = hashlib.sha256()
                original_size = 0
                with os.fdopen(fd, 'wb') as compressed:
                    with gzip.GzipFile(filename='', mode='wb', compresslevel=6,
                                       fileobj=compressed, mtime=0) as writer:
                        with path.open('rb') as source:
                            while block := source.read(CHUNK):
                                guard()
                                original.update(block)
                                original_size += len(block)
                                writer.write(block)
                                need(compressed.tell() <= TEMP_CAP, '64 MiB temporary-file cap')
                    compressed.flush()
                    os.fsync(compressed.fileno())
                original_hash = original.hexdigest()
                if current_temp.stat().st_size >= original_size:
                    counts['skipped_unprofitable'] += 1
                    current_temp.unlink()
                    current_temp = None
                    continue
            check_path = current_temp if current_temp is not None else target
            with gzip.open(check_path, 'rb') as source:
                recovered_hash, recovered_size = digest_stream(source)
            need(recovered_hash == original_hash and recovered_size == original_size == before.st_size,
                 'compressed round-trip hash/length mismatch; original retained')
            need(signature(path.stat()) == signature(before), 'original changed during compression')
            with check_path.open('rb') as source:
                compressed_hash, compressed_size = digest_stream(source)
            if current_temp is not None:
                os.chmod(current_temp, stat.S_IMODE(before.st_mode))
                os.link(current_temp, target)  # Atomic creation; refuse an existing destination.
                current_temp.unlink()
                current_temp = None
                sync_directory(target.parent)
            record = {'state': 'verified_before_unlink', 'path': str(path.relative_to(ROOT)),
                      'compressed_path': str(target.relative_to(ROOT)),
                      'sha256': original_hash, 'bytes': original_size,
                      'gzip_sha256': compressed_hash, 'gzip_bytes': compressed_size}
            append(record)
            guard()
            need(signature(path.stat()) == signature(before) and not path.is_symlink(),
                 'original changed before unlink; both copies retained')
            path.unlink()
            counts['verified_files'] += 1
            counts['removed_plain_files'] += 1
            counts['plain_bytes'] += original_size
            counts['gzip_bytes'] += compressed_size
    except BaseException as exc:
        status, error = 'stopped; completed files remain verified and readable', str(exc)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        if current_temp is not None:
            current_temp.unlink(missing_ok=True)
        report = {'status': status, 'error': error, 'run_counts': counts,
                  'net_bytes_saved_this_run': counts['plain_bytes'] - counts['gzip_bytes'],
                  'seconds': time.monotonic() - start,
                  'scope': 'Only evidence/historical/data/**/*.json; active certificates and user archives unchanged',
                  'remaining_plain_json_files': sum(1 for _ in DATA.rglob('*.json')),
                  'journal': str(journal_path.relative_to(ROOT)),
                  'trust': 'Original uncompressed hashes and logical paths are preserved; this is storage verification, not proof replay.'}
        temporary_receipt = RECEIPT / 'last-run.json.tmp'
        temporary_receipt.write_text(json.dumps(report, indent=2) + '\n')
        temporary_receipt.replace(RECEIPT / 'last-run.json')
        print(json.dumps(report, indent=2))
    if error is not None:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
