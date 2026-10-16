#!/usr/bin/env python3
"""Fetch selected dependencies using the resolved mathlib release's cache CLI."""
import os
import errno
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import sys

ROOT = Path(__file__).resolve().parents[1]


def raise_descriptor_limit():
    """Let leantar unpack large cache closures without the usual 1024-FD ceiling."""
    try:
        import resource
    except ImportError:
        return
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    target = 65536 if hard == resource.RLIM_INFINITY else min(hard, 65536)
    if soft != resource.RLIM_INFINITY and soft < target:
        resource.setrlimit(resource.RLIMIT_NOFILE, (target, hard))
        print(f'Cache file descriptor limit raised from {soft} to {target}', flush=True)


def seed_file(source, destination):
    """Reuse a complete cache file, even when HOME and the project are on different disks."""
    if destination.exists():
        return
    with tempfile.TemporaryDirectory(prefix='.cache-seed-', dir=destination.parent) as directory:
        temporary = Path(directory)/source.name
        try:
            os.link(source, temporary)
        except OSError as error:
            if error.errno != errno.EXDEV:
                raise
            shutil.copy2(source, temporary)
        temporary.replace(destination)


def main():
    raise_descriptor_limit()
    resolved = json.loads((ROOT/'.verification/toolchain.json').read_text())
    env = dict(os.environ, ELAN_TOOLCHAIN=resolved['toolchain'])
    threads = int(os.environ.get('N12_LEAN_THREADS', '1'))
    if threads < 1:
        raise ValueError('N12_LEAN_THREADS must be positive')
    env['LEAN_NUM_THREADS'] = str(threads)
    cache = ROOT/'.lake/cache'
    cache.mkdir(parents=True, exist_ok=True)
    old = Path.home()/'.cache/mathlib'
    for source in old.glob('*.ltar'):
        if source.is_file():
            seed_file(source, cache/source.name)
    for source in old.glob('leantar-*'):
        if source.is_file() and not source.name.endswith('.gz'):
            seed_file(source, cache/source.name)
    env['MATHLIB_CACHE_DIR'] = str(cache)
    # Mathlib checks this file literally, even when elan already selects the
    # exact compiler. Keep the repository's rolling alias outside cache setup.
    toolchain_file = ROOT/'lean-toolchain'
    original = toolchain_file.read_bytes()
    try:
        toolchain_file.write_text(resolved['toolchain'] + '\n')
        subprocess.run(['elan', 'run', resolved['toolchain'], 'lake', 'exe', 'cache', 'get',
                        *sys.argv[1:]], cwd=ROOT, env=env, check=True)
    finally:
        toolchain_file.write_bytes(original)


if __name__ == '__main__':
    main()
