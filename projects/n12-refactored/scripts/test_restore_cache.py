#!/usr/bin/env python3
"""Offline cache-download regression tests; never invoke Lean or the network."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import ssl
import subprocess
import tempfile
import unittest
from unittest.mock import MagicMock, patch
import urllib.error

spec = importlib.util.spec_from_file_location('restore_cache',
                                             Path(__file__).with_name('restore_cache.py'))
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


def response(data=b'archive', length=None):
    stream = io.BytesIO(data)
    stream.headers = {'Content-Length': str(len(data) if length is None else length)}
    return stream


class DownloadTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.path = Path(temporary.name)/'0123456789abcdef.ltar'
        self.entry = {'module': 'Mathlib.Data.Real.Basic', 'file': self.path.name}
        self.addCleanup(patch.stopall)
        self.open = patch.object(cache.urllib.request, 'urlopen').start()
        self.sleep = patch.object(cache.time, 'sleep').start()
        self.errors = io.StringIO()
        # Keep expected simulated failures out of the test runner output.
        patch.object(cache.sys, 'stderr', self.errors).start()

    def download(self, remaining=100):
        return cache.download_entry(self.entry, self.path, None, remaining)

    def test_timeout_retries_then_publishes_complete_archive(self):
        self.open.side_effect = [urllib.error.URLError(TimeoutError('timed out')), response()]
        self.assertEqual(self.download(), 7)
        self.assertEqual(self.path.read_bytes(), b'archive')
        self.assertFalse(self.path.with_suffix('.ltar.part').exists())
        self.sleep.assert_called_once_with(1)
        self.assertIn(self.entry['module'], self.errors.getvalue())
        self.assertEqual(self.open.call_args.args[0], cache.CACHE_URL+self.path.name)
        self.assertEqual(self.open.call_args.kwargs['timeout'], 60)

    def test_read_timeout_retries(self):
        stream = MagicMock()
        stream.__enter__.return_value = stream
        stream.read.side_effect = TimeoutError('read timed out')
        self.open.side_effect = [stream, response()]
        self.download()
        self.assertEqual(self.path.read_bytes(), b'archive')
        stream.__exit__.assert_called_once()

    def test_abrupt_tls_disconnect_retries(self):
        self.open.side_effect = [ssl.SSLEOFError('connection closed'), response()]
        self.download()
        self.assertEqual(self.path.read_bytes(), b'archive')
        self.sleep.assert_called_once_with(1)

    def test_transient_http_statuses_retry(self):
        for status in [408, 429, 500, 502, 503, 504]:
            with self.subTest(status=status):
                self.open.side_effect = [urllib.error.HTTPError(
                    cache.CACHE_URL, status, 'temporary', {}, None), response()]
                self.assertEqual(self.download(), 7)

    def test_missing_object_is_not_retried(self):
        self.open.side_effect = urllib.error.HTTPError(cache.CACHE_URL, 404, 'missing', {}, None)
        with self.assertRaisesRegex(RuntimeError, 'after 1 attempt'):
            self.download()
        self.assertEqual(self.open.call_count, 1)
        self.sleep.assert_not_called()
        self.assertFalse(self.path.exists())

    def test_invalid_certificate_is_not_retried(self):
        self.open.side_effect = urllib.error.URLError(ssl.SSLCertVerificationError('invalid'))
        with self.assertRaisesRegex(RuntimeError, 'after 1 attempt'):
            self.download()
        self.sleep.assert_not_called()

    def test_exhausted_retries_report_module_and_url(self):
        self.open.side_effect = TimeoutError('timed out')
        with self.assertRaisesRegex(RuntimeError, 'after 6 attempt') as caught:
            self.download()
        self.assertIn(self.entry['module'], str(caught.exception))
        self.assertIn(cache.CACHE_URL+self.path.name, str(caught.exception))
        self.assertEqual(self.open.call_count, 6)
        self.assertEqual([call.args[0] for call in self.sleep.call_args_list], [1, 2, 4, 8, 16])
        self.assertFalse(self.path.exists())

    def test_truncated_body_is_retried(self):
        self.open.side_effect = [response(b'ar', length=7), response()]
        self.download()
        self.assertEqual(self.path.read_bytes(), b'archive')
        self.sleep.assert_called_once_with(1)

    def test_size_and_total_budget_limits_are_preserved(self):
        for limit, remaining in [(4, 100), (100, 4)]:
            with self.subTest(limit=limit, remaining=remaining), \
                    patch.object(cache, 'MAX_FILE_BYTES', limit):
                self.open.return_value = response()
                with self.assertRaisesRegex(RuntimeError, 'budget exceeded'):
                    self.download(remaining)
                self.assertFalse(self.path.exists())
                self.sleep.assert_not_called()

    def test_interrupted_publish_does_not_leave_an_accepted_file(self):
        self.open.return_value = response()
        with patch.object(Path, 'replace', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.download()
        self.assertFalse(self.path.exists())
        self.assertFalse(self.path.with_suffix('.ltar.part').exists())

    def test_main_preserves_cache_plan_reuse_and_extraction(self):
        root = self.path.parent
        (root/'evidence').mkdir()
        cachedir = root/'.lake/cache'
        cachedir.mkdir(parents=True)
        (cachedir/self.path.name).write_bytes(b'existing')
        plan = [self.entry, {'module': 'Batteries.Basic', 'file': 'fedcba9876543210.ltar'}]
        self.open.return_value = response()
        with patch.object(cache, 'ROOT', root), \
                patch.object(cache.sys, 'argv', ['restore_cache.py', 'Mathlib.Data.Real.Basic']), \
                patch.dict(cache.os.environ, {'N12_LEAN_THREADS': '8', 'N12_CACHE_DOWNLOAD_MIB': '1'}), \
                patch.object(cache.subprocess, 'run', side_effect=[
                    subprocess.CompletedProcess([], 0, json.dumps(plan)),
                    subprocess.CompletedProcess([], 0)]) as run, \
                contextlib.redirect_stdout(io.StringIO()):
            cache.main()
        self.assertEqual(self.open.call_count, 1)
        self.assertEqual((cachedir/self.path.name).read_bytes(), b'existing')
        self.assertEqual(json.loads((root/'evidence/mathlib-cache-plan.json').read_text()), plan)
        self.assertIn('-j8', run.call_args_list[0].args[0])
        config = json.loads(run.call_args.kwargs['input'])
        self.assertEqual(config[0]['base'], str(root/'.lake/packages/mathlib'))
        self.assertNotIn('base', config[1])
        self.assertEqual(run.call_args.args[0], ['leantar', '--jobs', '8', '-x', '-j', '-'])


if __name__ == '__main__':
    unittest.main()
