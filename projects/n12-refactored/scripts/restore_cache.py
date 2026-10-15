#!/usr/bin/env python3
"""Restore only exact cache hashes computed by the unchanged pinned cache tool.

Uses the configured runner threads. Never builds Mathlib or fetches ProofWidgets JS.
Transient downloads get five retries, as in the pinned Mathlib cache client.
"""
import http.client
import json
import os
from pathlib import Path
import ssl
import subprocess
import sys
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
BIN = Path.home()/'.elan/toolchains/leanprover--lean4---v4.19.0/bin'
# Keep the endpoint from Mathlib v4.19's Cache/Requests.lean. Newer cache
# containers do not contain these pinned hashes.
CACHE_URL = 'https://lakecache.blob.core.windows.net/mathlib4/f/'
MAX_FILE_BYTES = 8*1024*1024
DOWNLOAD_ATTEMPTS = 6
DOWNLOAD_TIMEOUT = 60


def retryable(error):
    if isinstance(error, urllib.error.HTTPError):
        return error.code in {408, 429} or 500 <= error.code < 600
    if isinstance(error, urllib.error.URLError):
        return not isinstance(error.reason, ssl.SSLCertVerificationError)
    return isinstance(error, (TimeoutError, ConnectionError, ssl.SSLEOFError,
                              http.client.IncompleteRead))


def download_entry(entry, path, context, remaining_bytes):
    """Publish a complete archive atomically; never reuse a partial response."""
    url = CACHE_URL + entry['file']
    label = f"{entry['module']} ({entry['file']})"
    for attempt in range(1, DOWNLOAD_ATTEMPTS+1):
        try:
            with urllib.request.urlopen(url, context=context, timeout=DOWNLOAD_TIMEOUT) as stream:
                data = stream.read(MAX_FILE_BYTES+1)
                expected = stream.headers.get('Content-Length')
                if len(data) > MAX_FILE_BYTES or len(data) > remaining_bytes:
                    raise RuntimeError(f'Cache download budget exceeded for {label}')
                if expected is not None and len(data) != int(expected):
                    raise http.client.IncompleteRead(data, max(0, int(expected)-len(data)))
            break
        except (urllib.error.URLError, TimeoutError, ConnectionError, ssl.SSLEOFError,
                http.client.IncompleteRead) as error:
            if isinstance(error, urllib.error.HTTPError):
                error.close()
            if not retryable(error) or attempt == DOWNLOAD_ATTEMPTS:
                raise RuntimeError(
                    f'Cache download failed for {label} after {attempt} attempt(s): '
                    f'{url}: {error}') from error
            delay = 2**(attempt-1)
            print(f'Cache download {label}: attempt {attempt}/{DOWNLOAD_ATTEMPTS} '
                  f'failed ({error}); retrying in {delay}s', file=sys.stderr, flush=True)
            time.sleep(delay)
    partial = path.with_name(path.name+'.part')
    try:
        partial.write_bytes(data)
        partial.replace(path)
    finally:
        partial.unlink(missing_ok=True)
    return len(data)


def main():
    env = dict(os.environ, MATHLIB_CACHE_DIR=str(ROOT/'.lake/cache'))
    threads = int(os.environ.get('N12_LEAN_THREADS', '1'))
    if threads < 1:
        raise ValueError('N12_LEAN_THREADS must be positive')
    download_limit_mib = int(os.environ.get('N12_CACHE_DOWNLOAD_MIB', '150'))
    if not 1 <= download_limit_mib <= 1024:
        raise ValueError('N12_CACHE_DOWNLOAD_MIB must be between 1 and 1024')
    download_limit = download_limit_mib * 1024 * 1024
    roots = sys.argv[1:] or [
        'Mathlib.Data.Real.Basic', 'Mathlib.Algebra.Order.BigOperators.Ring.Finset',
        'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.Ring', 'Mathlib.Tactic.FieldSimp']
    result = subprocess.run([str(BIN/'lake'), 'env', 'lean', f'-j{threads}', '--run',
                             'scripts/CachePlan.lean', *roots], cwd=ROOT, env=env,
                            capture_output=True, text=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr)
        raise SystemExit(result.returncode)
    plan = json.loads(result.stdout)
    (ROOT/'evidence/mathlib-cache-plan.json').write_text(json.dumps(plan, indent=2)+'\n')
    context = ssl.create_default_context()
    apple_ca = Path('/etc/ssl/cert.pem')
    if apple_ca.is_file():
        context.load_verify_locations(cafile=str(apple_ca))
    (ROOT/'.lake/cache').mkdir(parents=True, exist_ok=True)
    downloaded = 0
    config = []
    print(f'Restoring {len(plan)} pinned cache archives from {CACHE_URL}', flush=True)
    for index, entry in enumerate(plan, 1):
        path = ROOT/'.lake/cache'/entry['file']
        if not path.exists():
            downloaded += download_entry(entry, path, context, download_limit-downloaded)
        item = {'file': str(path)}
        if entry['module'].split('.')[0] == 'Mathlib':
            item['base'] = str(ROOT/'.lake/packages/mathlib')
        config.append(item)
        if index % 100 == 0:
            print(f'Cache archives ready: {index}/{len(plan)}; downloaded {downloaded} bytes',
                  flush=True)
    print(json.dumps({'cached_modules':len(plan),'downloaded_bytes':downloaded}), flush=True)
    lean_tar = ROOT/'.lake/cache/leantar-0.1.15'
    subprocess.run([str(lean_tar) if lean_tar.is_file() else 'leantar',
                    '--jobs', str(threads), '-x', '-j', '-'],
                   input=json.dumps(config), text=True, cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
