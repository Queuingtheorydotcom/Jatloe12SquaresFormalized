#!/usr/bin/env python3
"""Bounded prefix recovery; accepts temporary download URL on stdin, never logs it."""
import hashlib
import base64
import io
import json
import os
from pathlib import Path
import re
import ssl
import subprocess
import sys
import tarfile
import threading
import time
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
CONFIG = json.load(sys.stdin)
INDEX = json.loads((ROOT / 'audit/prefix-small-source-index.json').read_text())
ROOTS = ['Compact.Cases.C981', 'Compact.Assembly.Frontier']
MAX_EXTRACTED = 10_000_000
MAX_CACHE = 16 * 1024 * 1024
started = time.monotonic()
receipt = {'source_commit': '98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8',
           'full_stream_verified': False, 'fresh_lean_run': False,
           'downloaded_bytes': 0, 'parts': [], 'files': [], 'headers': [],
           'retained_bytes': 0, 'cache_peak_bytes': 0}
cache = {}
stop = threading.Event()
errors = []


def source_path(module):
    rel = module.replace('.', '/') + '.lean'
    return ROOT / ('source/' + rel if module.startswith('S12.') else rel)


def closure_missing():
    seen, missing, pending = set(), set(), ROOTS.copy()
    while pending:
        module = pending.pop()
        if module in seen or module.split('.')[0] not in ('S12', 'Completion', 'Compact'):
            continue
        seen.add(module)
        path = source_path(module)
        if not path.exists():
            missing.add(module)
            continue
        pending.extend(re.findall(r'^import\s+(\S+)', path.read_text(), re.M))
    return sorted(missing)


def install_available():
    while True:
        changed = False
        for module in closure_missing():
            rel = module.replace('.', '/') + '.lean'
            if rel not in cache:
                continue
            data = cache[rel]
            if receipt['retained_bytes'] + len(data) > MAX_EXTRACTED:
                raise RuntimeError('retained source limit')
            row = INDEX[rel]
            assert len(data) == row['size']
            assert hashlib.sha256(data).hexdigest() == row['sha256']
            for prefix in ('vendor', 'source'):
                dest = ROOT / prefix / rel
                if dest.exists():
                    if prefix == 'vendor' and dest.read_bytes() != data:
                        raise RuntimeError('vendor source collision')
                    continue
                dest.parent.mkdir(parents=True, exist_ok=True)
                temp = dest.with_suffix('.lean.restoring')
                temp.write_bytes(data)
                os.replace(temp, dest)
            receipt['files'].append(dict(row, lines=data.count(b'\n')))
            receipt['retained_bytes'] += len(data)
            changed = True
        if not changed:
            return


decoder = subprocess.Popen(['/opt/homebrew/bin/zstd', '-d', '-c', '--memory=128MB'],
                           stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE)


def feed():
    try:
        credential = subprocess.run(
            ['git', '-C', os.environ.get('N12_LEGACY_CHECKOUT', str(ROOT)),
             'credential', 'fill'], input='protocol=https\nhost=github.com\n\n',
            text=True, capture_output=True, check=True, timeout=20)
        fields = dict(line.split('=', 1) for line in credential.stdout.splitlines() if '=' in line)
        auth = 'Basic ' + base64.b64encode(
            (fields['username'] + ':' + fields['password']).encode()).decode()
        del credential, fields
        for part in CONFIG['parts']:
            if stop.is_set():
                break
            if receipt['downloaded_bytes'] + part['size'] > CONFIG['download_limit']:
                raise RuntimeError('network byte limit')
            data = bytearray()
            context = ssl.create_default_context(cafile='/etc/ssl/cert.pem')
            request = urllib.request.Request(
                'https://api.github.com/repos/EvolvingPrograms/SquaresLean/git/blobs/' + part['git_sha'],
                headers={'Authorization': auth, 'Accept': 'application/vnd.github.raw+json',
                         'User-Agent': 'SquaresLean-bounded-source-recovery'})
            with urllib.request.urlopen(request, context=context, timeout=20) as response:
                while True:
                    block = response.read(min(65536, part['size'] + 1 - len(data)))
                    if not block:
                        break
                    receipt['downloaded_bytes'] += len(block)
                    data.extend(block)
                    if len(data) > part['size']:
                        raise RuntimeError('oversized part')
            if len(data) != part['size'] or hashlib.sha256(data).hexdigest() != part['sha256']:
                raise RuntimeError('part integrity failure')
            receipt['parts'].append({k: part[k] for k in ('name', 'size', 'sha256', 'git_sha')})
            if len(receipt['parts']) == 1:
                receipt['frame_header_hex'] = data[:18].hex()
            for pos in range(0, len(data), 65536):
                if stop.is_set():
                    break
                decoder.stdin.write(data[pos:pos + 65536])
            del data
    except BrokenPipeError:
        errors.append('decoder closed input')
    except Exception as error:
        # Exception text may contain a signed URL; record its type only.
        errors.append(type(error).__name__)
        receipt['network_error_code'] = getattr(error, 'code', None)
        reason = getattr(error, 'reason', None)
        receipt['network_reason_type'] = type(reason).__name__
        receipt['network_reason_errno'] = getattr(reason, 'errno', None)
    finally:
        try:
            decoder.stdin.close()
        except BrokenPipeError:
            pass


worker = threading.Thread(target=feed, daemon=True)
worker.start()
try:
    with tarfile.open(fileobj=decoder.stdout, mode='r|') as archive:
        for item in archive:
            receipt['members_seen'] = receipt.get('members_seen', 0) + 1
            receipt['last_member'] = item.name
            if len(receipt['headers']) < 12:
                receipt['headers'].append({'name': item.name, 'bytes': item.size})
            rel = item.name.removeprefix('./')
            if rel.startswith('s12-to117/'):
                rel = rel[len('s12-to117/'):]
            if rel.startswith('source/'):
                rel = rel[7:]
            row = INDEX.get(rel)
            if not item.isfile() or row is None or item.size != row['size']:
                continue
            if (ROOT / 'source' / rel).exists():
                continue
            used = sum(map(len, cache.values()))
            if used + item.size > MAX_CACHE:
                continue
            data = archive.extractfile(item).read(item.size)
            if hashlib.sha256(data).hexdigest() != row['sha256']:
                raise RuntimeError('member integrity mismatch')
            cache[rel] = data
            receipt['cache_peak_bytes'] = max(receipt['cache_peak_bytes'], used + len(data))
            install_available()
except (tarfile.ReadError, EOFError, OSError) as error:
    receipt['prefix_end'] = type(error).__name__
except Exception as error:
    receipt['failure'] = type(error).__name__
finally:
    stop.set()
    decoder.terminate()
    try:
        decoder.wait(timeout=3)
    except subprocess.TimeoutExpired:
        decoder.kill()
        decoder.wait()
    worker.join(timeout=3)
    receipt['decoder_diagnostic'] = decoder.stderr.read(4096).decode(errors='replace')
    receipt['missing_source_modules'] = closure_missing()
    receipt['cached_modules'] = len(cache)
    receipt['errors'] = errors
    receipt['elapsed_seconds'] = round(time.monotonic() - started, 3)
    (ROOT / 'audit/prefix-source-restoration.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ('downloaded_bytes', 'retained_bytes',
                      'missing_source_modules', 'members_seen', 'last_member',
                      'elapsed_seconds') if k in receipt}))
