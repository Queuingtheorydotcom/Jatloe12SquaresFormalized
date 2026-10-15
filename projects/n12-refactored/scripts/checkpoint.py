#!/usr/bin/env python3
"""Package accepted N12 objects, or restore a same-branch GitHub Actions checkpoint.

Restoration is an optimization, never proof acceptance: verify.py rechecks every
receipt, source, dependency fingerprint, object and log before reusing an object.
No toolchain, library cache, source, or global-success report is restored.
"""
import argparse
import datetime
import hashlib
import importlib.util
import io
import itertools
import json
import math
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.error
import urllib.parse
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 1
RECEIPT_PROTOCOL = 2
MAX_METADATA = 16 * 1024**2
MODULE = re.compile(r'(?:Compact|Completion|S12)(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
CONFIG_FILES = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean')
INDEX = '.verification/checked-modules.json'
META = 'checkpoint.json'


def storage_allowance():
    """Use the runner's project allocation, plus tar headers; default is local-only."""
    gib = float(os.environ.get('N12_PROJECT_GIB', '16'))
    if not math.isfinite(gib) or gib <= 0:
        raise ValueError('N12_PROJECT_GIB must be a positive finite number')
    return int(gib * 1024**3) + 64*1024**2


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1024**2), b''):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    os.replace(temporary, path)


def git(root, *arguments):
    return subprocess.check_output(['git', '-c', 'protocol.allow=never', *arguments],
                                   cwd=root, text=True, stderr=subprocess.PIPE).strip()


def configuration(root):
    return {name: sha256(root/name) for name in CONFIG_FILES if (root/name).is_file()}


def provenance(root, profile):
    repository = os.environ.get('GITHUB_REPOSITORY', '')
    if not repository:
        remote = git(root, 'remote', 'get-url', 'origin')
        match = re.search(r'github\.com[:/]([^/]+/[^/]+?)(?:\.git)?$', remote)
        if not match:
            raise ValueError('Cannot identify GitHub repository for checkpoint provenance')
        repository = match.group(1)
    branch = os.environ.get('GITHUB_REF_NAME') or git(root, 'branch', '--show-current')
    if not branch:
        raise ValueError('Checkpoint requires an identifiable source branch')
    return {'schema': SCHEMA, 'receipt_protocol': RECEIPT_PROTOCOL,
            'repository': repository, 'commit': git(root, 'rev-parse', 'HEAD'),
            'branch': branch, 'profile': profile, 'configuration': configuration(root),
            'system': platform.system(), 'machine': platform.machine(),
            'runner_os': os.environ.get('RUNNER_OS', platform.system()),
            'runner_arch': os.environ.get('RUNNER_ARCH', platform.machine()),
            'run_id': os.environ.get('GITHUB_RUN_ID'),
            'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
            'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat()}


def load_script(root, name):
    spec = importlib.util.spec_from_file_location('checkpoint_' + name,
                                                 root/'scripts'/f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def module_paths(module):
    if not MODULE.fullmatch(module):
        raise ValueError('Invalid project module: ' + module)
    return ('.lake/build/lib/lean/' + module.replace('.', '/') + '.olean',
            '.verification/' + module + '.log')


def accepted_receipts(root, modules, verify):
    """Keep a dependency-complete subset with intact success receipts.

    verify.py recomputes its compiler/configuration fingerprint before reuse;
    packaging need not run Lean (setup itself might have failed or timed out).
    """
    index = root/INDEX
    checked = json.loads(index.read_text()) if index.exists() else {}
    accepted, files = {}, {}
    for module in modules:  # dependency-first order from verify.closure
        try:
            entry = checked[module]
            record = entry['record']
            if not isinstance(entry, dict) or not isinstance(record, dict):
                continue
            obj, log = module_paths(module)
            source = verify.path(module)
            dependencies = [dep for dep in verify.imports(source.read_text())
                            if dep.split('.')[0] in {'Compact', 'Completion', 'S12'}]
            if any(dep not in accepted for dep in dependencies):
                continue
            if (record.get('returncode') != 0 or record.get('rejected_admission', False)
                    or record.get('module') != module
                    or record.get('source_sha256') != sha256(source)
                    or entry.get('object_sha256') != sha256(root/obj)
                    or record.get('log_sha256') != sha256(root/log)
                    or verify.has_admission((root/log).read_text())
                    or not entry.get('fingerprint')):
                continue
            for name in (obj, log):
                safe_destination(root, name)
                files[name] = {'sha256': sha256(root/name), 'size': (root/name).stat().st_size}
            accepted[module] = entry
        except (KeyError, FileNotFoundError, UnicodeError, TypeError):
            continue
    return accepted, files


def add_bytes(archive, name, payload):
    info = tarfile.TarInfo(name)
    info.size = len(payload)
    info.mode = 0o644
    archive.addfile(info, io.BytesIO(payload))


def package(root, profile):
    replay = load_script(root, 'github_replay')
    verify = load_script(root, 'verify')
    modules = verify.closure(replay.roots_for(profile))
    receipts, files = accepted_receipts(root, modules, verify)
    index = (json.dumps(receipts, indent=2, sort_keys=True) + '\n').encode()
    files[INDEX] = {'sha256': hashlib.sha256(index).hexdigest(), 'size': len(index)}
    metadata = dict(provenance(root, profile), modules=len(receipts), files=files)
    output = root/'.verification/artifacts/checkpoint.tar'
    output.parent.mkdir(parents=True, exist_ok=True)
    required = sum(item['size'] for item in files.values())
    if required > storage_allowance() or shutil.disk_usage(output.parent).free < required + 256*1024**2:
        raise ValueError('Insufficient checkpoint disk allowance; accepted objects remain on runner')
    temporary = output.with_suffix('.tar.tmp')
    try:
        with tarfile.open(temporary, 'w|') as archive:
            add_bytes(archive, META, json.dumps(metadata, sort_keys=True).encode())
            add_bytes(archive, INDEX, index)
            for name in sorted(files):
                if name != INDEX:
                    archive.add(root/name, arcname=name, recursive=False)
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    report = {'status': 'packaged', 'profile': profile, 'accepted_modules': len(receipts),
              'artifact': str(output.relative_to(root)), 'bytes': output.stat().st_size,
              'global_optimality_proved': False}
    atomic_json(root/'.verification/checkpoint-package.json', report)
    return report


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if urllib.parse.urlsplit(req.full_url)[:2] != urllib.parse.urlsplit(newurl)[:2]:
            redirected.remove_header('Authorization')
        return redirected


class GitHub:
    def __init__(self, repository, token):
        self.repository = repository
        self.base = os.environ.get('GITHUB_API_URL', 'https://api.github.com').rstrip('/')
        self.token = token
        self.opener = urllib.request.build_opener(SafeRedirect())

    def open(self, path):
        url = self.base + '/repos/' + self.repository + path
        request = urllib.request.Request(url, headers={
            'Authorization': 'Bearer ' + self.token, 'Accept': 'application/vnd.github+json',
            'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'SquaresLean-N12-checkpoint'})
        return self.opener.open(request, timeout=60)

    def get(self, path):
        with self.open(path) as response:
            return json.load(response)

    def is_ancestor(self, older, newer):
        if older == newer:
            return True
        comparison = self.get('/compare/' + urllib.parse.quote(older + '...' + newer, safe='.'))
        return comparison.get('status') in {'ahead', 'identical'}

    def download(self, artifact_id, target):
        with self.open('/actions/artifacts/' + str(int(artifact_id)) + '/zip') as response:
            written = 0
            with target.open('wb') as output:
                for chunk in iter(lambda: response.read(1024**2), b''):
                    written += len(chunk)
                    if written > storage_allowance() or shutil.disk_usage(target.parent).free < len(chunk) + 256*1024**2:
                        raise ValueError('Checkpoint download exceeds disk allowance')
                    output.write(chunk)


def compatible(metadata, current):
    if not isinstance(metadata, dict):
        raise ValueError('Invalid checkpoint metadata')
    for name in ('schema', 'receipt_protocol', 'repository', 'branch', 'profile',
                 'configuration', 'system', 'machine', 'runner_os', 'runner_arch'):
        if metadata.get(name) != current.get(name):
            raise ValueError('Incompatible checkpoint ' + name)


def allowed_path(name):
    if name == INDEX:
        return True
    if name.startswith('.lake/build/lib/lean/') and name.endswith('.olean'):
        module = name[len('.lake/build/lib/lean/'):-len('.olean')].replace('/', '.')
        return bool(MODULE.fullmatch(module)) and name == module_paths(module)[0]
    if name.startswith('.verification/') and name.endswith('.log'):
        module = name[len('.verification/'):-len('.log')]
        return bool(MODULE.fullmatch(module)) and name == module_paths(module)[1]
    return False


def safe_destination(root, name):
    if not allowed_path(name) or PurePosixPath(name).is_absolute() or '..' in PurePosixPath(name).parts:
        raise ValueError('Disallowed checkpoint path: ' + name)
    target = root/name
    cursor = target
    while cursor != root:
        if cursor.is_symlink():
            raise ValueError('Symlink in checkpoint destination: ' + name)
        cursor = cursor.parent
    return target


def restore_tar(root, archive_path, current, expected_commit, require_nonempty=False):
    """Validate in staging, copy objects/logs, atomically publish receipts last."""
    with tempfile.TemporaryDirectory(prefix='checkpoint-stage-', dir=root/'.verification') as temp:
        stage = Path(temp)
        tar_input = {'fileobj': archive_path} if hasattr(archive_path, 'read') else {'name': archive_path}
        with tarfile.open(mode='r|*', **tar_input) as archive:
            first = archive.next()
            if not first or first.name != META or not first.isfile() or first.size > MAX_METADATA:
                raise ValueError('Checkpoint metadata must be the first regular file')
            metadata = json.load(archive.extractfile(first))
            compatible(metadata, current)
            if metadata.get('commit') != expected_commit:
                raise ValueError('Artifact source commit differs from its workflow run')
            files = metadata.get('files', {})
            if not isinstance(files, dict) or INDEX not in files or len(files) > 30000:
                raise ValueError('Invalid checkpoint file inventory')
            expected_size = 0
            for name, receipt in files.items():
                safe_destination(root, name)
                if not isinstance(receipt, dict):
                    raise ValueError('Invalid checkpoint inventory entry')
                size = receipt.get('size')
                if (not isinstance(receipt.get('sha256'), str)
                        or not re.fullmatch(r'[0-9a-f]{64}', receipt['sha256'])):
                    raise ValueError('Invalid checkpoint file hash')
                if name == INDEX and isinstance(size, int) and size > MAX_METADATA:
                    raise ValueError('Checkpoint receipts exceed metadata allowance')
                if not isinstance(size, int) or size < 0:
                    raise ValueError('Invalid checkpoint file size')
                expected_size += size
            # ZIP is streamed into one staging tree. os.replace below moves on
            # the same filesystem; there is no expanded tar or second object copy.
            if expected_size > storage_allowance() or shutil.disk_usage(stage).free < expected_size + 256*1024**2:
                raise ValueError('Checkpoint extraction exceeds disk allowance')
            seen = set()
            for member in archive:
                if member.name == META and member is first:
                    continue
                if member.name in seen or member.name not in files or not member.isfile():
                    raise ValueError('Unexpected, duplicate, or nonregular checkpoint member')
                receipt = files[member.name]
                if member.size != receipt['size']:
                    raise ValueError('Checkpoint member size differs from inventory')
                destination = stage/member.name
                destination.parent.mkdir(parents=True, exist_ok=True)
                digest = hashlib.sha256()
                with archive.extractfile(member) as source, destination.open('wb') as output:
                    for chunk in iter(lambda: source.read(1024**2), b''):
                        digest.update(chunk)
                        output.write(chunk)
                if digest.hexdigest() != receipt['sha256']:
                    raise ValueError('Checkpoint hash mismatch: ' + member.name)
                seen.add(member.name)
            if seen != set(files):
                raise ValueError('Checkpoint has missing members')
        receipts = json.loads((stage/INDEX).read_text())
        if not isinstance(receipts, dict) or len(receipts) != metadata.get('modules'):
            raise ValueError('Checkpoint receipt count differs from metadata')
        if require_nonempty and not receipts:
            raise ValueError('Empty checkpoint skipped while seeking reusable progress')
        required = {INDEX}
        for module, entry in receipts.items():
            obj, log = module_paths(module)
            required.update((obj, log))
            if not isinstance(entry, dict) or not isinstance(entry.get('record'), dict):
                raise ValueError('Invalid accepted module receipt')
            record = entry['record']
            if (obj not in files or log not in files or record.get('module') != module
                    or record.get('returncode') != 0 or record.get('rejected_admission', False)
                    or entry.get('object_sha256') != files[obj]['sha256']
                    or record.get('log_sha256') != files[log]['sha256']):
                raise ValueError('Checkpoint objects or logs disagree with accepted receipts')
        if required != set(files):
            raise ValueError('Checkpoint contains files without accepted receipts')
        for name in sorted(files):
            if name == INDEX:
                continue
            target = safe_destination(root, name)
            target.parent.mkdir(parents=True, exist_ok=True)
            os.replace(stage/name, target)
        target = safe_destination(root, INDEX)
        target.parent.mkdir(parents=True, exist_ok=True)
        os.replace(stage/INDEX, target)
    return len(receipts)


def restore_zip(root, zip_path, current, commit, require_nonempty=False):
    with zipfile.ZipFile(zip_path) as archive:
        entries = archive.infolist()
        if len(entries) != 1 or entries[0].filename != 'checkpoint.tar':
            raise ValueError('Artifact must contain only checkpoint.tar')
        if entries[0].file_size > storage_allowance():
            raise ValueError('Checkpoint tar exceeds disk allowance')
        with archive.open(entries[0]) as source:
            return restore_tar(root, source, current, commit, require_nonempty=require_nonempty)


def candidate_artifacts(api, current, run):
    name = 'n12-' + current['profile'] + '-checkpoint'
    matches_name = re.compile(re.escape(name) + r'(?:-[1-9][0-9]*)?\Z').fullmatch
    if run != 'auto':
        run_id = int(run)
        if str(run_id) == str(current.get('run_id')):
            raise ValueError('Cannot resume the currently running workflow')
        result = api.get(f'/actions/runs/{run_id}/artifacts?per_page=100')
        for artifact in sorted(result['artifacts'], key=lambda item: item['id'], reverse=True):
            if matches_name(artifact['name']) and not artifact['expired']:
                yield artifact, run_id
        return
    for page in itertools.count(1):
        query = urllib.parse.urlencode({'per_page': 100, 'page': page})
        artifacts = api.get('/actions/artifacts?' + query)['artifacts']
        for artifact in sorted(artifacts, key=lambda item: item['id'], reverse=True):
            source = artifact.get('workflow_run', {})
            if (matches_name(artifact['name']) and not artifact['expired']
                    and source.get('head_branch') == current['branch']
                    and str(source.get('id')) != str(current.get('run_id'))):
                yield artifact, source['id']
        if len(artifacts) < 100:
            break


def restore(root, profile, run, api=None):
    report = {'status': 'cold_start', 'profile': profile, 'requested_run': run,
              'attempts': [], 'global_optimality_proved': False}
    directory = root/'.verification'
    directory.mkdir(parents=True, exist_ok=True)
    report_path = directory/'checkpoint-restore.json'
    if run == 'none':
        report['status'] = 'disabled'
        atomic_json(report_path, report)
        return report
    try:
        current = provenance(root, profile)
        if api is None:
            token = os.environ.get('GH_TOKEN') or os.environ.get('GITHUB_TOKEN')
            if not token:
                raise ValueError('GH_TOKEN is unavailable; starting without a checkpoint')
            api = GitHub(current['repository'], token)
        for artifact, run_id in candidate_artifacts(api, current, run):
            attempt = {'run_id': run_id, 'artifact_id': artifact['id']}
            report['attempts'].append(attempt)
            try:
                source = api.get(f'/actions/runs/{run_id}')
                workflow = source.get('path', '').split('@')[0]
                if (workflow not in {'.github/workflows/verify.yml', '.github/workflows/n12.yml'}
                        or source.get('repository', {}).get('full_name') != current['repository']
                        or source.get('head_repository', {}).get('full_name') != current['repository']
                        or source.get('head_branch') != current['branch']):
                    raise ValueError('Checkpoint run is not a matching N12 branch workflow')
                if not api.is_ancestor(source['head_sha'], current['commit']):
                    raise ValueError('Checkpoint commit is not an ancestor of the current source')
                with tempfile.TemporaryDirectory(prefix='checkpoint-download-', dir=directory) as temp:
                    archive = Path(temp)/'checkpoint.zip'
                    api.download(artifact['id'], archive)
                    count = restore_zip(root, archive, current, source['head_sha'],
                                        require_nonempty=(run == 'auto'))
                attempt['status'] = 'restored'
                report.update(status='restored', accepted_modules=count, source_run=run_id,
                              source_commit=source['head_sha'])
                break
            except (ValueError, OSError, KeyError, TypeError, tarfile.TarError, zipfile.BadZipFile) as error:
                attempt.update(status='rejected', reason=str(error))
        if report['status'] != 'restored':
            report['reason'] = 'No available compatible checkpoint; replay starts from source'
    except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        report['reason'] = str(error)
    atomic_json(report_path, report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest='command', required=True)
    for command in ('package', 'restore'):
        subparser = subparsers.add_parser(command)
        subparser.add_argument('--profile', choices=('final', 'registered', 'selected'), required=True)
        if command == 'restore':
            subparser.add_argument('--run', default='auto', help='auto, none, or a prior run ID')
    args = parser.parse_args()
    if args.command == 'package':
        try:
            report = package(ROOT, args.profile)
        except (ValueError, OSError, subprocess.CalledProcessError) as error:
            report = {'status': 'package_failed', 'reason': str(error)}
            atomic_json(ROOT/'.verification/checkpoint-package.json', report)
            print(json.dumps(report), flush=True)
            raise SystemExit(1)
    else:
        if args.run not in {'auto', 'none'} and not args.run.isdecimal():
            parser.error('--run must be auto, none, or a numeric workflow run ID')
        report = restore(ROOT, args.profile, args.run)
    print(json.dumps(report), flush=True)
    if args.command == 'restore' and args.run not in {'auto', 'none'} and report['status'] != 'restored':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
