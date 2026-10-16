#!/usr/bin/env python3
"""Offline dependency/bootstrap fixtures; no network or Lean compiler runs."""
import contextlib
import errno
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import urllib.error


def load(name):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(name+'.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


bootstrap = load('bootstrap_sources')
REVISION = 'a' * 40
prepare = load('prepare_cache')


class PinnedRuntimeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root/'verification').mkdir()
        self.lock = self.root/'verification/toolchain-lock.json'
        self.record = {'toolchain': 'leanprover/lean4:v4.35.0',
                       'mathlib': {'tag': 'v4.35.0', 'revision': REVISION}}
        self.lock.write_text(json.dumps(self.record))
        (self.root/'lean-toolchain').write_text(self.record['toolchain']+'\n')
        self.addCleanup(patch.stopall)
        patch.object(bootstrap, 'ROOT', self.root).start()
        self.fetch = patch.object(bootstrap, 'github_json', side_effect=AssertionError('network')).start()

    def test_uses_exact_pin_without_latest_release_request(self):
        self.assertEqual(bootstrap.resolve_pinned(), self.record)
        self.fetch.assert_not_called()

    def test_missing_lock_fails_closed(self):
        self.lock.unlink()
        with self.assertRaisesRegex(RuntimeError, 'Invalid verified runtime lock'):
            bootstrap.resolve_pinned()
        self.fetch.assert_not_called()

    def test_rejects_mutable_revision_and_mismatched_versions(self):
        for field, value in [('revision', 'main'), ('tag', 'v4.36.0')]:
            record = json.loads(json.dumps(self.record))
            record['mathlib'][field] = value
            self.lock.write_text(json.dumps(record))
            with self.assertRaisesRegex(RuntimeError, 'invalid compiler or mathlib pin'):
                bootstrap.resolve_pinned()

    def test_rejects_stable_selector(self):
        (self.root/'lean-toolchain').write_text('leanprover/lean4:stable\n')
        with self.assertRaisesRegex(RuntimeError, 'does not match'):
            bootstrap.resolve_pinned()

    def test_rejects_non_object_lock(self):
        self.lock.write_text('[]')
        with self.assertRaisesRegex(RuntimeError, 'Invalid verified runtime lock'):
            bootstrap.resolve_pinned()


class LatestReleaseTests(unittest.TestCase):
    def test_descriptor_limit_respects_hard_limit(self):
        import resource
        with patch.object(resource, 'getrlimit', return_value=(1024, 4096)), \
                patch.object(resource, 'setrlimit') as set_limit, contextlib.redirect_stdout(io.StringIO()):
            prepare.raise_descriptor_limit()
        set_limit.assert_called_once_with(resource.RLIMIT_NOFILE, (4096, 4096))

    def test_descriptor_limit_does_not_lower_existing_limit(self):
        import resource
        with patch.object(resource, 'getrlimit', return_value=(100000, 100000)), \
                patch.object(resource, 'setrlimit') as set_limit:
            prepare.raise_descriptor_limit()
        set_limit.assert_not_called()

    def test_git_dependency_reuses_exact_existing_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root/'.lake/packages/batteries'
            (package/'.git').mkdir(parents=True)
            with patch.object(bootstrap, 'ROOT', root), \
                    patch.object(bootstrap.subprocess, 'check_output', return_value=REVISION+'\n'), \
                    patch.object(bootstrap.subprocess, 'run') as run:
                bootstrap.restore_git('https://example/batteries', REVISION, 'batteries')
            run.assert_not_called()
            self.assertEqual((package/'.source-pin').read_text(), REVISION+'\n')

    def test_failed_git_fetch_preserves_old_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root/'.lake/packages/batteries'
            package.mkdir(parents=True)
            (package/'user.lean').write_text('preserve')
            with patch.object(bootstrap, 'ROOT', root), \
                    patch.object(bootstrap.subprocess, 'run', side_effect=RuntimeError('fetch failed')):
                with self.assertRaisesRegex(RuntimeError, 'fetch failed'):
                    bootstrap.restore_git('https://example/batteries', REVISION, 'batteries')
            self.assertEqual((package/'user.lean').read_text(), 'preserve')
            self.assertEqual(list((root/'.lake/source-staging').iterdir()), [])

    def test_manifest_preserves_upstream_git_identity(self):
        package = {'type': 'git', 'name': 'batteries', 'rev': REVISION,
                   'url': 'https://github.com/leanprover-community/batteries',
                   'inputRev': 'main', 'inherited': False, 'scope': 'leanprover-community',
                   'configFile': 'lakefile.lean', 'manifestFile': 'lake-manifest.json'}
        manifest = bootstrap.dependency_manifest({'version': '1.3.0', 'packages': [package]})
        self.assertEqual(manifest['version'], '1.1.0')
        self.assertEqual(manifest['packages'][1], dict(package, inherited=True))
        self.assertFalse(package['inherited'])
        replay = load('github_replay')
        with patch.object(replay, 'ROOT', Path('/project')):
            configs = replay.package_config_paths(manifest)
        self.assertIn(Path('/project/.lake/packages/batteries/lakefile.lean'), configs)

    def test_resolves_exact_latest_pair(self):
        release = {'tag_name': 'v4.35.0', 'html_url': 'https://example/release'}
        with patch.object(bootstrap, 'github_json', side_effect=[release, release, {'sha': REVISION}]):
            result = bootstrap.resolve_latest()
        self.assertEqual(result['toolchain'], 'leanprover/lean4:v4.35.0')
        self.assertEqual(result['mathlib']['revision'], REVISION)

    def test_missing_matching_mathlib_does_not_fall_back(self):
        release = {'tag_name': 'v4.36.0', 'html_url': 'https://example/release'}
        error = urllib.error.HTTPError('https://example', 404, 'missing', {}, None)
        with patch.object(bootstrap, 'github_json', side_effect=[release, error]) as fetch:
            with self.assertRaisesRegex(RuntimeError, 'refusing an older compiler'):
                bootstrap.resolve_latest()
        self.assertEqual(fetch.call_count, 2)

    def test_rejects_prerelease(self):
        with patch.object(bootstrap, 'github_json', return_value={'tag_name': 'v4.36.0-rc1'}):
            with self.assertRaisesRegex(RuntimeError, 'not a stable version'):
                bootstrap.resolve_latest()

    def test_cache_cli_uses_record_and_selected_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'.verification').mkdir()
            (root/'lean-toolchain').write_text('leanprover/lean4:stable\n')
            (root/'.verification/toolchain.json').write_text(json.dumps({'toolchain': 'leanprover/lean4:v4.35.0'}))
            with patch.object(prepare, 'ROOT', root), patch.object(Path, 'home', return_value=root), \
                    patch.object(prepare.sys, 'argv', ['prepare_cache.py', 'Mathlib.Data.Real.Basic']), \
                    patch.object(prepare.subprocess, 'run') as run:
                prepare.main()
            self.assertEqual(run.call_args.args[0], ['elan', 'run', 'leanprover/lean4:v4.35.0',
                'lake', 'exe', 'cache', 'get', 'Mathlib.Data.Real.Basic'])
            self.assertEqual(run.call_args.kwargs['env']['ELAN_TOOLCHAIN'], 'leanprover/lean4:v4.35.0')
            self.assertEqual((root/'lean-toolchain').read_text(), 'leanprover/lean4:stable\n')

    def test_cache_restores_alias_after_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'.verification').mkdir()
            (root/'lean-toolchain').write_text('leanprover/lean4:stable\n')
            (root/'.verification/toolchain.json').write_text(json.dumps({'toolchain': 'leanprover/lean4:v4.35.0'}))
            def fail(*args, **kwargs):
                self.assertEqual((root/'lean-toolchain').read_text(), 'leanprover/lean4:v4.35.0\n')
                raise RuntimeError('cache failed')
            with patch.object(prepare, 'ROOT', root), patch.object(Path, 'home', return_value=root), \
                    patch.object(prepare.subprocess, 'run', side_effect=fail):
                with self.assertRaisesRegex(RuntimeError, 'cache failed'):
                    prepare.main()
            self.assertEqual((root/'lean-toolchain').read_text(), 'leanprover/lean4:stable\n')


def archive(files=None):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode='w:gz') as tar:
        for name, data in (files or {'lakefile.lean': b'-- pinned source\n'}).items():
            item = tarfile.TarInfo('package-revision/'+name)
            item.size = len(data)
            tar.addfile(item, io.BytesIO(data))
    return io.BytesIO(output.getvalue())


class BootstrapTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.destination = self.root/'.lake/packages/mathlib'
        self.addCleanup(patch.stopall)
        patch.object(bootstrap, 'ROOT', self.root).start()
        self.open = patch.object(bootstrap.urllib.request, 'urlopen').start()
        self.sleep = patch.object(bootstrap.time, 'sleep').start()
        patch.object(bootstrap.sys, 'stderr', io.StringIO()).start()

    def restore(self):
        with contextlib.redirect_stdout(io.StringIO()):
            bootstrap.restore('https://github.com/leanprover-community/mathlib4',
                              REVISION, 'mathlib')

    def assert_no_staging(self):
        staging = self.root/'.lake/source-staging'
        self.assertEqual(list(staging.iterdir()), [])

    def test_timeout_retries_then_publishes_pinned_complete_source(self):
        self.open.side_effect = [TimeoutError('timed out'), archive()]
        self.restore()
        self.assertEqual((self.destination/'lakefile.lean').read_bytes(), b'-- pinned source\n')
        self.assertEqual((self.destination/'.source-pin').read_text().strip(), REVISION)
        self.assertIn('/tar.gz/'+REVISION, self.open.call_args.args[0])
        self.sleep.assert_called_once_with(1)
        self.assert_no_staging()

    def test_mid_extraction_failure_does_not_pollute_retry(self):
        def interrupted(url, destination, context):
            (destination/'partial.lean').write_text('incomplete')
            raise TimeoutError('interrupted stream')
        self.open.return_value = archive()
        with patch.object(bootstrap, 'extract', side_effect=interrupted):
            with self.assertRaisesRegex(RuntimeError, 'after 3 attempt'):
                # Repeated failures leave no visible package or staged directory.
                self.restore()
        self.assertFalse(self.destination.exists())
        self.assert_no_staging()
        self.restore()
        self.assertFalse((self.destination/'partial.lean').exists())
        self.assertTrue((self.destination/'.source-pin').is_file())

    def test_legacy_unmarked_destination_is_preserved_outside_packages(self):
        self.destination.mkdir(parents=True)
        (self.destination/'user-edits.lean').write_text('keep my edits')
        self.open.return_value = archive()
        self.restore()
        backups = list((self.root/'.lake/source-backups').glob('*/mathlib/user-edits.lean'))
        self.assertEqual(len(backups), 1)
        self.assertEqual(backups[0].read_text(), 'keep my edits')
        self.assertFalse((self.destination/'user-edits.lean').exists())
        self.assertEqual([p.name for p in self.destination.parent.iterdir()], ['mathlib'])

    def test_completed_pin_is_reused_and_changed_pin_is_not_overwritten(self):
        self.destination.mkdir(parents=True)
        marker = self.destination/'.source-pin'
        marker.write_text(REVISION+'\n')
        self.restore()
        self.open.assert_not_called()
        marker.write_text('different revision\n')
        self.open.return_value = archive()
        self.restore()
        self.assertEqual(marker.read_text(), REVISION+'\n')
        backups = list((self.root/'.lake/source-backups').glob('*/mathlib/.source-pin'))
        self.assertEqual([p.read_text() for p in backups], ['different revision\n'])

    def test_interrupt_before_publish_leaves_no_accepted_package(self):
        self.open.return_value = archive()
        with patch.object(Path, 'replace', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.restore()
        self.assertFalse(self.destination.exists())
        self.assert_no_staging()

    def test_archive_byte_limit_is_not_retried_or_published(self):
        self.open.return_value = archive()
        with patch.object(bootstrap, 'LIMIT', 1):
            with self.assertRaisesRegex(ValueError, 'extraction budget'):
                self.restore()
        self.sleep.assert_not_called()
        self.assertFalse(self.destination.exists())
        self.assert_no_staging()

    def test_permanent_http_failure_does_not_retry(self):
        self.open.side_effect = urllib.error.HTTPError('https://example.invalid', 404,
                                                      'missing', {}, None)
        with self.assertRaisesRegex(RuntimeError, 'after 1 attempt'):
            self.restore()
        self.sleep.assert_not_called()
        self.assertFalse(self.destination.exists())
        self.assert_no_staging()

    def test_archive_paths_cannot_escape_staging(self):
        self.open.return_value = archive({'../outside': b'bad', '.git/secret': b'bad',
                                          'lakefile.lean': b'good'})
        self.restore()
        self.assertFalse((self.root/'outside').exists())
        self.assertFalse((self.destination/'.git').exists())
        self.assertEqual((self.destination/'lakefile.lean').read_bytes(), b'good')


class CacheSeedTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.source = self.root/'old-cache'/'leantar-0.1.15'
        self.source.parent.mkdir()
        self.source.write_bytes(b'complete cached file')
        self.source.chmod(0o755)
        self.destination = self.root/'new-cache'/self.source.name
        self.destination.parent.mkdir()

    def test_cross_filesystem_copy_preserves_contents_and_executable_mode(self):
        with patch.object(prepare.os, 'link', side_effect=OSError(errno.EXDEV, 'different filesystem')):
            prepare.seed_file(self.source, self.destination)
        self.assertEqual(self.destination.read_bytes(), self.source.read_bytes())
        self.assertEqual(self.destination.stat().st_mode & 0o777, 0o755)
        self.assertEqual(list(self.destination.parent.iterdir()), [self.destination])

    def test_same_filesystem_keeps_hardlink_and_existing_files_are_reused(self):
        prepare.seed_file(self.source, self.destination)
        self.assertEqual(self.destination.stat().st_ino, self.source.stat().st_ino)
        with patch.object(prepare.os, 'link') as link:
            prepare.seed_file(self.source, self.destination)
        link.assert_not_called()

    def test_interrupted_copy_is_never_published(self):
        def interrupted(source, destination):
            destination.write_bytes(b'partial')
            raise KeyboardInterrupt('interrupted cache copy')
        with patch.object(prepare.os, 'link', side_effect=OSError(errno.EXDEV, 'different filesystem')), \
                patch.object(prepare.shutil, 'copy2', side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                prepare.seed_file(self.source, self.destination)
        self.assertFalse(self.destination.exists())
        self.assertEqual(list(self.destination.parent.iterdir()), [])
        self.assertEqual(self.source.read_bytes(), b'complete cached file')

    def test_permission_failures_are_not_disguised_as_cross_device_copies(self):
        with patch.object(prepare.os, 'link', side_effect=PermissionError(errno.EACCES, 'denied')), \
                patch.object(prepare.shutil, 'copy2') as copy:
            with self.assertRaises(PermissionError):
                prepare.seed_file(self.source, self.destination)
        copy.assert_not_called()
        self.assertFalse(self.destination.exists())


if __name__ == '__main__':
    unittest.main()
