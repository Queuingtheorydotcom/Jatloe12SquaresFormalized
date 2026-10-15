#!/usr/bin/env python3
"""Restore pinned public dependency sources, with a hard extracted-byte limit.

No caches, generated proof corpus, Git history, or toolchains are downloaded.
This writes only .lake/packages under this project, and rejects tar links.
"""
import json
from pathlib import Path, PurePosixPath
import ssl
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
LIMIT = 256 * 1024 * 1024

def restore(url, rev, name):
    destination = ROOT / '.lake/packages' / name
    marker = destination / '.source-pin'
    if marker.exists():
        if marker.read_text().strip() != rev:
            raise ValueError('Existing source pin differs')
        return
    if destination.exists():
        raise ValueError('Incomplete destination requires manual inspection')
    destination.mkdir(parents=True)
    archive = url.replace('https://github.com/', 'https://codeload.github.com/')
    if archive.endswith('.git'):
        archive = archive[:-4]
    archive += '/tar.gz/' + rev
    context = ssl.create_default_context()
    # The platform default is used on Linux and on configured Python installs.
    # Apple's system store is also available to an otherwise unconfigured Python.
    apple_ca = Path('/etc/ssl/cert.pem')
    if apple_ca.is_file():
        context.load_verify_locations(cafile=str(apple_ca))
    size = 0
    with urllib.request.urlopen(archive, context=context, timeout=45) as stream:
        with tarfile.open(fileobj=stream, mode='r|gz') as tar:
            for member in tar:
                parts = PurePosixPath(member.name).parts[1:]
                if not parts or '..' in parts or member.name.startswith('/'):
                    continue
                if not member.isfile():
                    continue
                relative = Path(*parts)
                if any(p in ('.git', 'node_modules', '.lake') for p in parts):
                    continue
                size += member.size
                if size > LIMIT:
                    raise ValueError('Source archive exceeds extraction budget')
                output = destination / relative
                output.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(member) as source, output.open('xb') as target:
                    while data := source.read(1024 * 1024):
                        target.write(data)
    marker.write_text(rev + '\n')
    print(json.dumps({'package': name, 'source_bytes': size}), flush=True)

def main():
    restore('https://github.com/leanprover-community/mathlib4', PIN, 'mathlib')
    package_root = ROOT / '.lake/packages/mathlib'
    manifest = json.loads((package_root / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        restore(package['url'], package['rev'], package['name'])
    packages = []
    for name in ['mathlib'] + [p['name'] for p in manifest['packages']]:
        directory = ROOT / '.lake/packages' / name
        config = 'lakefile.toml' if (directory / 'lakefile.toml').exists() else 'lakefile.lean'
        packages.append({'type': 'path', 'name': name, 'dir': str(directory.relative_to(ROOT)),
                         'scope': '', 'inherited': name != 'mathlib',
                         'configFile': config, 'manifestFile': 'lake-manifest.json'})
    (ROOT / 'lake-manifest.json').write_text(json.dumps({
        'version': '1.1.0', 'name': 'n12_compact', 'lakeDir': '.lake',
        'packagesDir': '.lake/packages', 'packages': packages}, indent=2) + '\n')

if __name__ == '__main__':
    main()
