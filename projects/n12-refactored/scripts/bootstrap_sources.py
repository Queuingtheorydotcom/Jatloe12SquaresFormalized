#!/usr/bin/env python3
"""Restore pinned public dependency sources, with a hard extracted-byte limit.

No caches, generated proof corpus, Git history, or toolchains are downloaded.
Downloads are staged under .lake and published only when complete. Unmarked
older destinations are preserved under .lake/source-backups before retrying.
"""
import http.client
import json
from pathlib import Path, PurePosixPath
import ssl
import sys
import tarfile
import tempfile
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
LIMIT = 256 * 1024 * 1024
DOWNLOAD_ATTEMPTS = 3


def retryable(error):
    if isinstance(error, urllib.error.HTTPError):
        return error.code in {408, 429} or 500 <= error.code < 600
    if isinstance(error, urllib.error.URLError):
        return not isinstance(error.reason, ssl.SSLCertVerificationError)
    return isinstance(error, (TimeoutError, ConnectionError, ssl.SSLEOFError,
                              http.client.IncompleteRead, tarfile.ReadError, EOFError))


def extract(archive, destination, context):
    size = 0
    with urllib.request.urlopen(archive, context=context, timeout=60) as stream:
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
    return size


def restore(url, rev, name):
    if name in {'', '.', '..'} or Path(name).name != name:
        raise ValueError('Invalid dependency package name')
    destination = ROOT / '.lake/packages' / name
    if destination.is_symlink():
        raise ValueError('Dependency destination is a symlink; inspect it before restoring')
    marker = destination / '.source-pin'
    if marker.exists():
        if marker.read_text().strip() != rev:
            raise ValueError('Existing source pin differs')
        return
    if destination.exists():
        # A prior interrupted version wrote directly into the destination.
        # Preserve all unmarked contents, including any user edits, elsewhere.
        backups = ROOT / '.lake/source-backups'
        backups.mkdir(parents=True, exist_ok=True)
        backup = Path(tempfile.mkdtemp(prefix=name+'-incomplete-', dir=backups)) / name
        destination.replace(backup)
        print(json.dumps({'package': name, 'preserved_incomplete_source':
                          str(backup.relative_to(ROOT))}), flush=True)
    destination.parent.mkdir(parents=True, exist_ok=True)
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
    staging = ROOT / '.lake/source-staging'
    staging.mkdir(parents=True, exist_ok=True)
    for attempt in range(1, DOWNLOAD_ATTEMPTS+1):
        try:
            with tempfile.TemporaryDirectory(prefix=name+'-', dir=staging) as directory:
                stage = Path(directory) / name
                stage.mkdir()
                size = extract(archive, stage, context)
                (stage / '.source-pin').write_text(rev + '\n')
                stage.replace(destination)
            break
        except (urllib.error.URLError, TimeoutError, ConnectionError, ssl.SSLEOFError,
                http.client.IncompleteRead, tarfile.ReadError, EOFError) as error:
            if isinstance(error, urllib.error.HTTPError):
                error.close()
            if not retryable(error) or attempt == DOWNLOAD_ATTEMPTS:
                raise RuntimeError(f'Dependency {name} download failed after '
                                   f'{attempt} attempt(s): {archive}: {error}') from error
            delay = 2**(attempt-1)
            print(f'Dependency {name}: download attempt {attempt} failed; '
                  f'retrying in {delay}s ({error})', file=sys.stderr, flush=True)
            time.sleep(delay)
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
    manifest_path = ROOT / 'lake-manifest.json'
    temporary = manifest_path.with_suffix('.json.tmp')
    temporary.write_text(json.dumps({
        'version': '1.1.0', 'name': 'n12_compact', 'lakeDir': '.lake',
        'packagesDir': '.lake/packages', 'packages': packages}, indent=2) + '\n')
    temporary.replace(manifest_path)

if __name__ == '__main__':
    main()
