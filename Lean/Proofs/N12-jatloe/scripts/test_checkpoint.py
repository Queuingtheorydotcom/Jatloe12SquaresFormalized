#!/usr/bin/env python3
"""Offline checkpoint tests: no Lean, network, or repository mutations."""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import tarfile
import tempfile
import types
import unittest
from unittest.mock import patch
import zipfile

spec = importlib.util.spec_from_file_location('checkpoint', Path(__file__).with_name('checkpoint.py'))
checkpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checkpoint)


def digest(payload):
    return hashlib.sha256(payload).hexdigest()


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root/'.verification').mkdir()
        self.current = dict(schema=checkpoint.SCHEMA, receipt_protocol=checkpoint.RECEIPT_PROTOCOL,
                            repository='owner/repo', commit='a'*40, branch='n12', profile='final',
                            configuration={'lean-toolchain': 'abc'}, system='Linux', machine='x86_64',
                            runner_os='Linux', runner_arch='X64', run_id='123')
        self.verify = types.SimpleNamespace(path=self.source,
            imports=lambda text: [line[7:] for line in text.splitlines() if line.startswith('import ')],
            has_admission=lambda log: 'sorryAx' in log or "declaration uses 'sorry'" in log)
        self.modules = ['Compact.Base', 'Compact.Final']
        self.receipts = {}
        self.write_module('Compact.Base', 'theorem base := True\n')
        self.write_module('Compact.Final', 'import Compact.Base\ntheorem final := True\n')
        checkpoint.atomic_json(self.root/checkpoint.INDEX, self.receipts)

    def tearDown(self):
        self.temporary.cleanup()

    def source(self, module):
        return self.root/(module.replace('.', '/') + '.lean')

    def write_module(self, module, source):
        path = self.source(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        obj, log = checkpoint.module_paths(module)
        for name, payload in ((obj, b'fake olean ' + module.encode()), (log, b'accepted\n')):
            target = self.root/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
        self.receipts[module] = {'fingerprint': 'opaque', 'receipt_version': 2,
            'object_sha256': checkpoint.sha256(self.root/obj),
            'record': {'module': module, 'returncode': 0,
                       'source_sha256': checkpoint.sha256(path),
                       'log_sha256': checkpoint.sha256(self.root/log)}}

    def archive(self, mutate=None, extras=()):
        receipts, files = checkpoint.accepted_receipts(self.root, self.modules, self.verify)
        index = json.dumps(receipts).encode()
        payloads = {name: (self.root/name).read_bytes() for name in files}
        payloads[checkpoint.INDEX] = index
        files[checkpoint.INDEX] = {'sha256': digest(index), 'size': len(index)}
        metadata = dict(self.current, files=files, modules=len(receipts))
        if mutate:
            mutate(metadata, payloads)
        output = self.root/'test.tar'
        with tarfile.open(output, 'w') as archive:
            checkpoint.add_bytes(archive, checkpoint.META, json.dumps(metadata).encode())
            for name, payload in payloads.items():
                checkpoint.add_bytes(archive, name, payload)
            for member in extras:
                archive.addfile(member)
        return output

    def test_package_excludes_partial_and_stale_dependencies(self):
        (self.root/checkpoint.module_paths('Compact.Base')[0]).write_bytes(b'partial')
        accepted, files = checkpoint.accepted_receipts(self.root, self.modules, self.verify)
        self.assertEqual(accepted, {})
        self.assertEqual(files, {})

    def test_package_excludes_changed_sources_and_admissions(self):
        self.source('Compact.Base').write_text('changed\n')
        accepted, _ = checkpoint.accepted_receipts(self.root, self.modules, self.verify)
        self.assertEqual(accepted, {})
        self.write_module('Compact.Base', 'theorem base := True\n')
        log = self.root/checkpoint.module_paths('Compact.Final')[1]
        log.write_text("declaration uses 'sorry'\n")
        self.receipts['Compact.Final']['record']['log_sha256'] = checkpoint.sha256(log)
        checkpoint.atomic_json(self.root/checkpoint.INDEX, self.receipts)
        accepted, _ = checkpoint.accepted_receipts(self.root, self.modules, self.verify)
        self.assertEqual(list(accepted), ['Compact.Base'])

    def test_package_and_restore_round_trip(self):
        replay = types.SimpleNamespace(roots_for=lambda profile: self.modules)
        self.verify.closure = lambda roots: roots
        with patch.object(checkpoint, 'load_script', side_effect=lambda root, name:
                          replay if name == 'github_replay' else self.verify), \
                patch.object(checkpoint, 'provenance', return_value=self.current):
            report = checkpoint.package(self.root, 'final')
        self.assertEqual(report['accepted_modules'], 2)
        archive = self.root/report['artifact']
        target = self.root/'destination'
        (target/'.verification').mkdir(parents=True)
        sentinel = target/'untouched.lean'
        sentinel.write_text('do not change')
        count = checkpoint.restore_tar(target, archive, self.current, self.current['commit'])
        self.assertEqual(count, 2)
        self.assertEqual(json.loads((target/checkpoint.INDEX).read_text()), self.receipts)
        self.assertEqual(sentinel.read_text(), 'do not change')
        self.assertFalse((target/'.verification/github-replay.json').exists())

    def assert_rejected_without_index_change(self, archive):
        before = (self.root/checkpoint.INDEX).read_bytes()
        with self.assertRaises((ValueError, tarfile.TarError)):
            checkpoint.restore_tar(self.root, archive, self.current, self.current['commit'])
        self.assertEqual((self.root/checkpoint.INDEX).read_bytes(), before)

    def test_reject_corrupt_hash_before_installation(self):
        def corrupt(metadata, payloads):
            obj = checkpoint.module_paths('Compact.Final')[0]
            payloads[obj] = b'x' * len(payloads[obj])
        self.assert_rejected_without_index_change(self.archive(corrupt))

    def test_reject_traversal_and_links(self):
        for name in ('../escape', '/absolute', '.verification/../../escape'):
            with self.subTest(name=name):
                def add_invalid(metadata, payloads):
                    payloads[name] = b''
                    metadata['files'][name] = {'size': 0, 'sha256': digest(b'')}
                self.assert_rejected_without_index_change(self.archive(add_invalid))
        link = tarfile.TarInfo('.verification/Compact.Bad.log')
        link.type = tarfile.SYMTYPE
        link.linkname = '/etc/passwd'
        self.assert_rejected_without_index_change(self.archive(extras=[link]))

    def test_reject_destination_symlink(self):
        archive = self.archive()
        log = self.root/checkpoint.module_paths('Compact.Base')[1]
        log.unlink()
        log.symlink_to(self.root/'outside')
        self.assert_rejected_without_index_change(archive)

    def test_reject_missing_duplicate_and_extra_files(self):
        def missing(metadata, payloads):
            del payloads[checkpoint.module_paths('Compact.Base')[0]]
        self.assert_rejected_without_index_change(self.archive(missing))
        extra = tarfile.TarInfo(checkpoint.module_paths('Compact.Base')[1])
        self.assert_rejected_without_index_change(self.archive(extras=[extra]))
        def extra_allowed(metadata, payloads):
            name = '.verification/Compact.Extra.log'
            payloads[name] = b''
            metadata['files'][name] = {'sha256': digest(b''), 'size': 0}
        self.assert_rejected_without_index_change(self.archive(extra_allowed))

    def test_reject_incompatible_provenance(self):
        for field in ('schema', 'receipt_protocol', 'repository', 'branch', 'profile',
                      'configuration', 'system', 'machine', 'runner_os', 'runner_arch', 'commit'):
            with self.subTest(field=field):
                self.assert_rejected_without_index_change(self.archive(
                    lambda metadata, payloads: metadata.update({field: 'wrong'})))

    def test_zip_rejects_unrelated_files(self):
        output = self.root/'test.zip'
        with zipfile.ZipFile(output, 'w') as archive:
            archive.writestr('../escape', b'bad')
        with self.assertRaises(ValueError):
            checkpoint.restore_zip(self.root, output, self.current, self.current['commit'])

    def fake_api(self, artifact_zip, branch='n12', workflow='verify.yml', ancestor=True):
        artifact = dict(id=12, name='n12-final-checkpoint-2', expired=False,
                        workflow_run=dict(id=99, head_branch=branch))
        run = dict(path='.github/workflows/'+workflow, repository={'full_name': 'owner/repo'},
                   head_repository={'full_name': 'owner/repo'}, head_branch=branch,
                   head_sha=self.current['commit'])
        return types.SimpleNamespace(
            get=lambda path: run if path == '/actions/runs/99' else {'artifacts': [artifact]},
            is_ancestor=lambda older, newer: ancestor,
            download=lambda artifact_id, target: shutil.copyfile(artifact_zip, target))

    def test_auto_accepts_forwarding_workflow_and_attempt_suffix(self):
        archive = self.archive()
        zipped = self.root/'artifact.zip'
        with zipfile.ZipFile(zipped, 'w') as output:
            output.write(archive, 'checkpoint.tar')
        with patch.object(checkpoint, 'provenance', return_value=self.current):
            report = checkpoint.restore(self.root, 'final', 'auto', self.fake_api(zipped))
        self.assertEqual(report['status'], 'restored')
        self.assertEqual(report['source_run'], 99)
        self.assertFalse(report['global_optimality_proved'])

    def test_auto_rejects_wrong_branch_workflow_and_history(self):
        for kwargs in ({'branch': 'main'}, {'workflow': 'unrelated.yml'}, {'ancestor': False}):
            with self.subTest(kwargs=kwargs), \
                    patch.object(checkpoint, 'provenance', return_value=self.current):
                report = checkpoint.restore(self.root, 'final', 'auto', self.fake_api(None, **kwargs))
                self.assertEqual(report['status'], 'cold_start')
                self.assertTrue((self.root/'.verification/checkpoint-restore.json').is_file())

    def test_auto_skips_empty_checkpoint_and_accepts_ancestor(self):
        zipped = self.root/'accepted.zip'
        ancestor = 'b'*40
        archive = self.archive(lambda metadata, payloads: metadata.update(commit=ancestor))
        with zipfile.ZipFile(zipped, 'w') as output:
            output.write(archive, 'checkpoint.tar')
        checkpoint.atomic_json(self.root/checkpoint.INDEX, {})
        empty = self.root/'empty.zip'
        with zipfile.ZipFile(empty, 'w') as output:
            output.write(self.archive(), 'checkpoint.tar')
        artifacts = [dict(id=13, name='n12-final-checkpoint-1', expired=False,
                          workflow_run=dict(id=100, head_branch='n12')),
                     dict(id=12, name='n12-final-checkpoint-2', expired=False,
                          workflow_run=dict(id=99, head_branch='n12'))]
        def get(path):
            if path.startswith('/actions/artifacts?'):
                return {'artifacts': artifacts}
            run_id = int(path.rsplit('/', 1)[1])
            return dict(path='.github/workflows/n12.yml', repository={'full_name': 'owner/repo'},
                        head_repository={'full_name': 'owner/repo'}, head_branch='n12',
                        head_sha=ancestor if run_id == 99 else self.current['commit'])
        api = types.SimpleNamespace(get=get, is_ancestor=lambda old, new: True,
            download=lambda artifact_id, target: shutil.copyfile(
                empty if artifact_id == 13 else zipped, target))
        with patch.object(checkpoint, 'provenance', return_value=self.current):
            report = checkpoint.restore(self.root, 'final', 'auto', api)
        self.assertEqual(report['status'], 'restored')
        self.assertEqual(report['source_run'], 99)
        self.assertEqual(report['source_commit'], ancestor)
        self.assertIn('Empty checkpoint', report['attempts'][0]['reason'])

    def test_storage_allowance_uses_runner_allocation(self):
        with patch.dict(os.environ, {'N12_PROJECT_GIB': '80'}):
            self.assertGreater(checkpoint.storage_allowance(), 80*1024**3)
        for invalid in ('-1', '0', 'nan', 'inf', 'no'):
            with self.subTest(invalid=invalid), patch.dict(os.environ, {'N12_PROJECT_GIB': invalid}):
                with self.assertRaises(ValueError):
                    checkpoint.storage_allowance()

    def test_disabled_does_not_need_git_or_network(self):
        with patch.object(checkpoint, 'provenance', side_effect=AssertionError('not needed')):
            self.assertEqual(checkpoint.restore(self.root, 'final', 'none')['status'], 'disabled')

    def test_redirect_does_not_forward_token_to_storage(self):
        request = checkpoint.urllib.request.Request('https://api.github.com/repos/a/b',
                                                    headers={'Authorization': 'Bearer SECRET'})
        redirected = checkpoint.SafeRedirect().redirect_request(
            request, None, 302, '', {}, 'https://storage.example/artifact')
        self.assertFalse(redirected.has_header('Authorization'))


if __name__ == '__main__':
    unittest.main()
