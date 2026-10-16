#!/usr/bin/env python3
"""Restore the verified, pinned Lean/mathlib pair and bounded public dependencies.

Install the exact resolved compiler through elan. Source downloads are staged
under .lake and published only when complete. Older destinations, including
their builds and user edits, are preserved under .lake/source-backups.
"""
import http.client
import json
import os
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
import ssl
import sys
import tarfile
import tempfile
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
LIMIT = 256 * 1024 * 1024
DOWNLOAD_ATTEMPTS = 3


def github_json(path):
    headers = {'User-Agent': 'n12-source-bootstrap', 'Accept': 'application/vnd.github+json'}
    if os.environ.get('GITHUB_TOKEN'):
        headers['Authorization'] = 'Bearer ' + os.environ['GITHUB_TOKEN']
    request = urllib.request.Request('https://api.github.com/repos/' + path, headers=headers)
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def resolve_latest():
    """Require mathlib for the latest stable Lean; never fall back to an older pair."""
    lean = github_json('leanprover/lean4/releases/latest')
    tag = lean['tag_name']
    if lean.get('prerelease') or lean.get('draft') or not re.fullmatch(r'v\d+\.\d+\.\d+', tag):
        raise RuntimeError('Latest Lean release is not a stable version')
    try:
        mathlib = github_json('leanprover-community/mathlib4/releases/tags/' + tag)
    except urllib.error.HTTPError as error:
        if error.code == 404:
            error.close()
            raise RuntimeError(f'Latest Lean {tag} has no matching stable mathlib release; refusing an older compiler') from error
        raise
    if mathlib.get('prerelease') or mathlib.get('draft') or mathlib['tag_name'] != tag:
        raise RuntimeError(f'Mathlib release for latest Lean {tag} is not stable')
    revision = github_json('leanprover-community/mathlib4/commits/' + tag)['sha']
    if not re.fullmatch(r'[0-9a-f]{40}', revision):
        raise RuntimeError('Invalid resolved mathlib commit')
    return {'toolchain': 'leanprover/lean4:' + tag,
            'lean_release': lean['html_url'],
            'mathlib': {'tag': tag, 'revision': revision, 'release': mathlib['html_url']},
            'resolved_at': datetime.now(timezone.utc).isoformat()}


def resolve_pinned():
    """Load the checked-in verified runtime without resolving mutable release tags."""
    lock = ROOT/'verification/toolchain-lock.json'
    try:
        resolved = json.loads(lock.read_text())
        toolchain = resolved['toolchain']
        mathlib = resolved['mathlib']
        tag = toolchain.removeprefix('leanprover/lean4:')
        if (not re.fullmatch(r'leanprover/lean4:v\d+\.\d+\.\d+', toolchain)
                or mathlib['tag'] != tag
                or not re.fullmatch(r'[0-9a-f]{40}', mathlib['revision'])):
            raise ValueError('invalid compiler or mathlib pin')
        if (ROOT/'lean-toolchain').read_text().strip() != toolchain:
            raise ValueError('lean-toolchain does not match the verified runtime lock')
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        raise RuntimeError(f'Invalid verified runtime lock: {error}') from error
    return resolved


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
    if marker.exists() and marker.read_text().strip() == rev:
        return
    if destination.exists():
        # Preserve previous releases and interrupted downloads, including edits.
        backups = ROOT / '.lake/source-backups'
        backups.mkdir(parents=True, exist_ok=True)
        backup = Path(tempfile.mkdtemp(prefix=name+'-', dir=backups)) / name
        destination.replace(backup)
        print(json.dumps({'package': name, 'preserved_previous_source':
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

def restore_git(url, rev, name):
    """Lake requires actual git checkouts for dependencies declared as git."""
    if name in {'', '.', '..'} or Path(name).name != name:
        raise ValueError('Invalid dependency package name')
    destination = ROOT/'.lake/packages'/name
    if destination.is_symlink():
        raise ValueError('Dependency destination is a symlink; inspect it before restoring')
    if (destination/'.git').is_dir():
        current = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=destination,
                                          text=True).strip()
        if current == rev:
            (destination/'.source-pin').write_text(rev + '\n')
            return
    staging = ROOT/'.lake/source-staging'
    staging.mkdir(parents=True, exist_ok=True)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=name+'-', dir=staging) as directory:
        stage = Path(directory)/name
        stage.mkdir()
        for arguments in (['init', '--quiet'], ['remote', 'add', 'origin', url],
                          ['fetch', '--depth=1', 'origin', rev],
                          ['checkout', '--quiet', '--detach', 'FETCH_HEAD']):
            subprocess.run(['git', *arguments], cwd=stage, check=True)
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=stage,
                                         text=True).strip()
        if actual != rev:
            raise RuntimeError(f'Dependency {name} checkout does not match resolved revision')
        (stage/'.source-pin').write_text(rev + '\n')
        if destination.exists():
            backups = ROOT/'.lake/source-backups'
            backups.mkdir(parents=True, exist_ok=True)
            backup = Path(tempfile.mkdtemp(prefix=name+'-', dir=backups))/name
            destination.replace(backup)
            print(json.dumps({'package': name, 'preserved_previous_source':
                              str(backup.relative_to(ROOT))}), flush=True)
        stage.replace(destination)
    print(json.dumps({'package': name, 'git_revision': rev}), flush=True)


def dependency_manifest(manifest):
    """Retain upstream git identities required by mathlib's cache validation."""
    directory = ROOT/'.lake/packages/mathlib'
    config = 'lakefile.toml' if (directory/'lakefile.toml').exists() else 'lakefile.lean'
    packages = [{'type': 'path', 'name': 'mathlib', 'dir': '.lake/packages/mathlib',
                 'scope': '', 'inherited': False,
                 'configFile': config, 'manifestFile': 'lake-manifest.json'}]
    packages.extend(dict(package, inherited=True) for package in manifest['packages'])
    # This is our generated path-dependency manifest, whose schema is 1.1.0;
    # the upstream manifest's format version does not describe this document.
    return {'version': '1.1.0', 'name': 'n12_compact', 'lakeDir': '.lake',
            'packagesDir': '.lake/packages', 'packages': packages}


def main():
    resolved = resolve_pinned()
    subprocess.run(['elan', 'toolchain', 'install', resolved['toolchain']], cwd=ROOT, check=True)
    # The checked-in selector is already exact; preserve it during bootstrap.
    previous = ROOT/'.lake/packages/mathlib/.source-pin'
    if previous.exists() and previous.read_text().strip() != resolved['mathlib']['revision']:
        build = ROOT/'.lake/build'
        if build.exists():
            backups = ROOT/'.lake/source-backups'
            backups.mkdir(parents=True, exist_ok=True)
            build.replace(Path(tempfile.mkdtemp(prefix='project-build-', dir=backups))/'build')
    restore('https://github.com/leanprover-community/mathlib4', resolved['mathlib']['revision'], 'mathlib')
    package_root = ROOT / '.lake/packages/mathlib'
    if (package_root/'lean-toolchain').read_text().strip() != resolved['toolchain']:
        raise RuntimeError('Pinned mathlib does not use the verified Lean toolchain')
    manifest = json.loads((package_root / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        restore_git(package['url'], package['rev'], package['name'])
    manifest_path = ROOT / 'lake-manifest.json'
    temporary = manifest_path.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(dependency_manifest(manifest), indent=2) + '\n')
    temporary.replace(manifest_path)
    record = ROOT/'.verification/toolchain.json'
    record.parent.mkdir(parents=True, exist_ok=True)
    temporary = record.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(resolved, indent=2) + '\n')
    temporary.replace(record)
    print(json.dumps(resolved), flush=True)

if __name__ == '__main__':
    main()
