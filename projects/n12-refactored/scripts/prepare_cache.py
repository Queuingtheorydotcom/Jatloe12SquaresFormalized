#!/usr/bin/env python3
"""Build only the five tiny pinned cache-tool modules; no project compilation."""
import os
import errno
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = Path.home()/'.elan/toolchains/leanprover--lean4---v4.19.0/bin/lean'
MATH = ROOT/'.lake/packages/mathlib'
OUT = MATH/'.lake/build/lib/lean'


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
    OUT.joinpath('Cache').mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(OUT))
    threads = int(os.environ.get('N12_LEAN_THREADS', '1'))
    if threads < 1:
        raise ValueError('N12_LEAN_THREADS must be positive')
    for name in ['Lean', 'IO', 'Hashing', 'Requests']:
        subprocess.run([str(LEAN), f'-j{threads}', '-o', str(OUT/'Cache'/f'{name}.olean'),
                        f'Cache/{name}.lean'], cwd=MATH, env=env, check=True)
    cache = ROOT/'.lake/cache'
    cache.mkdir(parents=True, exist_ok=True)
    old = Path.home()/'.cache/mathlib'
    for source in old.glob('*.ltar'):
        if source.is_file():
            seed_file(source, cache/source.name)
    for source in old.glob('leantar-*'):
        if source.is_file() and not source.name.endswith('.gz'):
            seed_file(source, cache/source.name)


if __name__ == '__main__':
    main()
