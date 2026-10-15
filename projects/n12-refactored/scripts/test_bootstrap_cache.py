#!/usr/bin/env python3
"""Offline dependency/bootstrap fixtures; no network or Lean compiler runs."""
import contextlib
import errno
import importlib.util
import io
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
prepare = load('prepare_cache')


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
                              bootstrap.PIN, 'mathlib')

    def assert_no_staging(self):
        staging = self.root/'.lake/source-staging'
        self.assertEqual(list(staging.iterdir()), [])

    def test_timeout_retries_then_publishes_pinned_complete_source(self):
        self.open.side_effect = [TimeoutError('timed out'), archive()]
        self.restore()
        self.assertEqual((self.destination/'lakefile.lean').read_bytes(), b'-- pinned source\n')
        self.assertEqual((self.destination/'.source-pin').read_text().strip(), bootstrap.PIN)
        self.assertIn('/tar.gz/'+bootstrap.PIN, self.open.call_args.args[0])
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
        marker.write_text(bootstrap.PIN+'\n')
        self.restore()
        self.open.assert_not_called()
        marker.write_text('different revision\n')
        with self.assertRaisesRegex(ValueError, 'source pin differs'):
            self.restore()
        self.assertEqual(marker.read_text(), 'different revision\n')

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
