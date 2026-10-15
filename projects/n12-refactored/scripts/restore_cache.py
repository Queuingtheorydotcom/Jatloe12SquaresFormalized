#!/usr/bin/env python3
"""Restore only exact cache hashes computed by the unchanged pinned cache tool.

Uses the configured runner threads. Never builds Mathlib or fetches ProofWidgets JS.
"""
import json
import os
from pathlib import Path
import ssl
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
BIN = Path.home()/'.elan/toolchains/leanprover--lean4---v4.19.0/bin'
env = dict(os.environ, MATHLIB_CACHE_DIR=str(ROOT/'.lake/cache'))
threads = int(os.environ.get('N12_LEAN_THREADS', '1'))
if threads < 1:
    raise ValueError('N12_LEAN_THREADS must be positive')
roots = ['Mathlib.Data.Real.Basic', 'Mathlib.Algebra.Order.BigOperators.Ring.Finset',
         'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.Ring', 'Mathlib.Tactic.FieldSimp']
if len(sys.argv) > 1:
    roots = sys.argv[1:]
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
downloaded = 0
download_limit_mib = int(os.environ.get('N12_CACHE_DOWNLOAD_MIB', '150'))
if not 1 <= download_limit_mib <= 1024:
    raise ValueError('N12_CACHE_DOWNLOAD_MIB must be between 1 and 1024')
download_limit = download_limit_mib * 1024 * 1024
config = []
for entry in plan:
    path = ROOT/'.lake/cache'/entry['file']
    if not path.exists():
        url = 'https://lakecache.blob.core.windows.net/mathlib4/f/' + entry['file']
        with urllib.request.urlopen(url, context=context, timeout=30) as stream:
            data = stream.read(8*1024*1024+1)
        if len(data)>8*1024*1024 or downloaded+len(data)>download_limit:
            raise RuntimeError('Cache download budget exceeded')
        downloaded += len(data)
        path.write_bytes(data)
    item = {'file': str(path)}
    if entry['module'].split('.')[0] == 'Mathlib':
        item['base'] = str(ROOT/'.lake/packages/mathlib')
    config.append(item)
print(json.dumps({'cached_modules':len(plan),'downloaded_bytes':downloaded}), flush=True)
lean_tar = ROOT/'.lake/cache/leantar-0.1.15'
subprocess.run([str(lean_tar) if lean_tar.is_file() else 'leantar', '--jobs', str(threads), '-x', '-j', '-'],
               input=json.dumps(config), text=True, cwd=ROOT, check=True)
