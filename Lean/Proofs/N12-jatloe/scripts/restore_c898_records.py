#!/usr/bin/env python3
"""Authenticated, bounded sequential recovery; never run recovered programs."""
import base64
import gzip
import hashlib
import json
import os
from pathlib import Path
import signal
import ssl
import subprocess
import sys
import tarfile
import threading
import time
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
BASE = Path(os.environ.get('N12_LEGACY_PROJECT', str(ROOT.parent / 'n12-jatloe419'))) / 'provenance'
PLAN = json.loads(Path(sys.argv[1]).read_text()) if len(sys.argv) > 1 else None
OUT = ROOT / 'evidence/C898/raw'
OUT.mkdir(parents=True, exist_ok=True)
CAP_NETWORK = 4_100_000_000
CAP_OUTPUT = PLAN['retained_cap_bytes'] if PLAN else 24 * 1024**2
DEADLINE = 595
TARGETS = {
    'data/region898.json', 'data/batch-Push898-manifest.json',
    'data/case898-input.json', 'S12/DirectSingleDomain.lean',
    'S12/DomainEnumeration.lean', 'S12/MissingCornerBranches.lean',
    'S12/CompactRegionTree.lean', 'S12/CompactFarkasText.lean',
    'S12/CompactPoseText.lean',
}
if PLAN:
    planned = {r['path']: r for r in PLAN['needed']}
    TARGETS = set(planned)
bundle = json.loads((BASE / 'bundle.json').read_text())
manifest_bytes = (BASE / 'source-manifest.json.gz').read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest() == bundle['manifest_sha256']
if PLAN:
    assert PLAN['source_manifest_sha256'] == bundle['manifest_sha256']
rows = {r['path']: r for r in json.loads(gzip.decompress(manifest_bytes))['files']}
del manifest_bytes
assert TARGETS <= rows.keys()
if PLAN:
    assert all(planned[p]['size'] == rows[p]['size'] and
               planned[p]['sha256'] == rows[p]['sha256'] for p in TARGETS)
started = time.monotonic()
stop = threading.Event()
errors = []
receipt = {
    'source_commit': '98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8',
    'manifest_sha256': bundle['manifest_sha256'],
    'full_stream_verified': False, 'fresh_lean_run': False,
    'downloaded_bytes': 0, 'output_bytes': 0, 'parts': [], 'files': [],
    'lean_members': 0, 'lean_bytes': 0, 'lean_newlines': 0,
    'members_seen': 0, 'complete_member_counts_only': True,
    'limits': {'network_bytes': CAP_NETWORK, 'output_bytes': CAP_OUTPUT,
               'seconds_internal': DEADLINE, 'aggregate_rss_mib_external': 384},
}
receipt_path = ROOT / (PLAN['receipt_path'] if PLAN else 'audit/c898-record-restoration.json')
counts_path = ROOT / (PLAN['counts_path'] if PLAN else 'audit/archive-lean-source-counts.tsv')
if PLAN:
    receipt['existing_authenticated_files'] = PLAN['existing']
    receipt['requested_manifest'] = sys.argv[1]
temp_paths = []
recovered = set()


def save():
    receipt['elapsed_seconds'] = round(time.monotonic() - started, 3)
    receipt['missing_targets'] = sorted(TARGETS - recovered)
    receipt['errors'] = errors.copy()
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')


def interrupted(signum, frame):
    stop.set()
    raise KeyboardInterrupt()


signal.signal(signal.SIGTERM, interrupted)
decoder = subprocess.Popen(['/opt/homebrew/bin/zstd', '-q', '-d', '-c', '--memory=128MB'],
                           stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE)


def feed():
    try:
        result = subprocess.run(
            ['git', '-C', str(BASE.parents[2]), 'credential', 'fill'],
            input='protocol=https\nhost=github.com\n\n', text=True,
            capture_output=True, check=True, timeout=20)
        fields = dict(line.split('=', 1) for line in result.stdout.splitlines() if '=' in line)
        auth = 'Basic ' + base64.b64encode(
            (fields['username'] + ':' + fields['password']).encode()).decode()
        del result, fields
        context = ssl.create_default_context(cafile='/etc/ssl/cert.pem')
        whole = hashlib.sha256()
        for index, part in enumerate(bundle['parts']):
            if stop.is_set():
                break
            if time.monotonic() - started > DEADLINE:
                raise TimeoutError('internal deadline')
            if receipt['downloaded_bytes'] + part['size'] > CAP_NETWORK:
                raise RuntimeError('network cap')
            payload = bytearray()
            request = urllib.request.Request(
                'https://api.github.com/repos/EvolvingPrograms/SquaresLean/git/blobs/' + part['git_sha'],
                headers={'Authorization': auth, 'Accept': 'application/vnd.github.raw+json',
                         'User-Agent': 'SquaresLean-bounded-record-recovery'})
            with urllib.request.urlopen(request, context=context, timeout=20) as response:
                while not stop.is_set():
                    chunk = response.read(min(256 * 1024, part['size'] + 1 - len(payload)))
                    if not chunk:
                        break
                    receipt['downloaded_bytes'] += len(chunk)
                    payload.extend(chunk)
                    if len(payload) > part['size']:
                        raise RuntimeError('oversized part')
            if stop.is_set():
                break
            if len(payload) != part['size'] or hashlib.sha256(payload).hexdigest() != part['sha256']:
                raise RuntimeError('part integrity mismatch')
            whole.update(payload)
            receipt['parts'].append(dict(part, index=index))
            for pos in range(0, len(payload), 256 * 1024):
                if stop.is_set():
                    break
                decoder.stdin.write(payload[pos:pos + 256 * 1024])
            del payload
        else:
            receipt['compressed_stream_verified'] = whole.hexdigest() == bundle['compressed_sha256']
            if not receipt['compressed_stream_verified']:
                raise RuntimeError('whole compressed hash mismatch')
    except BrokenPipeError:
        if not stop.is_set():
            errors.append('unexpected broken decoder input')
    except Exception as error:
        errors.append(type(error).__name__)
        receipt['network_error_code'] = getattr(error, 'code', None)
    finally:
        try:
            decoder.stdin.close()
        except OSError:
            pass


worker = threading.Thread(target=feed, daemon=True)
worker.start()
last_report = started
try:
    with counts_path.open('w', buffering=1) as counts, tarfile.open(
            fileobj=decoder.stdout, mode='r|', bufsize=1024 * 1024) as archive:
        header = 'path\tbytes\tnewline_bytes\tsha256\n'
        counts.write(header)
        receipt['output_bytes'] += len(header)
        for member in archive:
            if time.monotonic() - started > DEADLINE:
                raise TimeoutError('internal deadline')
            if not member.isfile() or not member.name.startswith('s12-to117/'):
                raise RuntimeError('unexpected archive member')
            name = member.name[len('s12-to117/'):]
            row = rows.get(name)
            if row is None or member.size != row['size']:
                raise RuntimeError('member metadata mismatch')
            receipt['members_seen'] += 1
            receipt['last_member'] = name
            receipt['last_tar_header_offset'] = member.offset
            if len(archive.members) > 128:
                archive.members.clear()
            selected = name in TARGETS
            count_lean = name.endswith('.lean') and (not PLAN or PLAN['count_all_lean'] or selected)
            if selected or count_lean:
                digest = hashlib.sha256()
                newline_bytes = byte_count = 0
                temporary = None
                if selected:
                    if receipt['output_bytes'] + member.size > CAP_OUTPUT:
                        raise RuntimeError('retained output cap')
                    temporary = OUT / (hashlib.sha256(name.encode()).hexdigest() + '.restoring')
                    temp_paths.append(temporary)
                with archive.extractfile(member) as source:
                    destination = temporary.open('wb') if temporary else None
                    compressed = bool(PLAN and selected and planned[name].get('gzip_storage'))
                    writer = (gzip.GzipFile(filename='', mode='wb', fileobj=destination,
                                           compresslevel=1, mtime=0)
                              if compressed else destination)
                    try:
                        while chunk := source.read(1024 * 1024):
                            digest.update(chunk)
                            newline_bytes += chunk.count(b'\n')
                            byte_count += len(chunk)
                            if writer:
                                writer.write(chunk)
                    finally:
                        if writer is not None and writer is not destination:
                            writer.close()
                        if destination:
                            destination.close()
                if byte_count != row['size'] or digest.hexdigest() != row['sha256']:
                    raise RuntimeError('source integrity mismatch: ' + name)
                if count_lean:
                    line = f'{name}\t{byte_count}\t{newline_bytes}\t{digest.hexdigest()}\n'
                    if receipt['output_bytes'] + len(line.encode()) > CAP_OUTPUT:
                        raise RuntimeError('count output cap')
                    counts.write(line)
                    receipt['output_bytes'] += len(line.encode())
                    receipt['lean_members'] += 1
                    receipt['lean_bytes'] += byte_count
                    receipt['lean_newlines'] += newline_bytes
                if selected:
                    target = ROOT / planned[name]['target'] if PLAN else (
                        (ROOT / 'vendor' / name) if name.endswith('.lean') else OUT / name)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    stored_bytes = temporary.stat().st_size
                    if target.exists():
                        existing_digest = hashlib.sha256()
                        with (gzip.open(target, 'rb') if compressed else target.open('rb')) as existing:
                            for block in iter(lambda: existing.read(1024 * 1024), b''):
                                existing_digest.update(block)
                        if existing_digest.hexdigest() != row['sha256']:
                            raise RuntimeError('existing target mismatch')
                        temporary.unlink()
                    else:
                        os.replace(temporary, target)
                        receipt['output_bytes'] += stored_bytes
                    copied = None
                    if name.endswith('.lean') and (not PLAN or name in PLAN['overlay_only']):
                        if compressed:
                            raise RuntimeError('compressed provenance must not become a proof overlay')
                        overlay = ROOT / 'source' / name
                        if not overlay.exists():
                            if receipt['output_bytes'] + byte_count > CAP_OUTPUT:
                                raise RuntimeError('overlay output cap')
                            overlay.parent.mkdir(parents=True, exist_ok=True)
                            overlay.write_bytes(target.read_bytes())
                            receipt['output_bytes'] += byte_count
                            copied = str(overlay.relative_to(ROOT))
                    receipt['files'].append(dict(row, newline_bytes=newline_bytes,
                                                  retained_path=str(target.relative_to(ROOT)),
                                                  stored_bytes=stored_bytes,
                                                  storage='gzip' if compressed else 'raw',
                                                  restored_overlay=copied))
                    recovered.add(name)
                    if not PLAN or len(recovered) % 100 == 0 or '898' in name or name in PLAN['overlay_only']:
                        print(json.dumps({'recovered': name, 'bytes': byte_count,
                                          'recovered_files': len(recovered)}), flush=True)
                    if not PLAN:
                        save()
            if time.monotonic() - last_report > 20:
                save()
                print(json.dumps({k: receipt[k] for k in ('downloaded_bytes', 'members_seen',
                      'last_member', 'lean_members', 'elapsed_seconds')}), flush=True)
                last_report = time.monotonic()
            if TARGETS <= recovered:
                receipt['stop_reason'] = 'all requested targets recovered'
                break
        else:
            for _ in iter(lambda: decoder.stdout.read(1024 * 1024), b''):
                pass
            worker.join(timeout=3)
            receipt['full_stream_verified'] = bool(receipt.get('compressed_stream_verified'))
except BaseException as error:
    receipt['failure'] = type(error).__name__
finally:
    stop.set()
    if decoder.poll() is None:
        decoder.terminate()
        try:
            decoder.wait(timeout=3)
        except subprocess.TimeoutExpired:
            decoder.kill()
            decoder.wait()
    worker.join(timeout=2)
    receipt['decoder_diagnostic'] = decoder.stderr.read(4096).decode(errors='replace')
    for temporary in temp_paths:
        try:
            temporary.unlink(missing_ok=True)
        except OSError as error:
            errors.append('temporary cleanup: ' + type(error).__name__)
    save()
    print(json.dumps({k: receipt[k] for k in ('downloaded_bytes', 'output_bytes', 'missing_targets',
                      'lean_members', 'lean_bytes', 'lean_newlines', 'elapsed_seconds')}), flush=True)
if receipt.get('failure') or receipt['missing_targets'] or errors:
    raise SystemExit(1)
