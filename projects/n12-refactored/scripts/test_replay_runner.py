#!/usr/bin/env python3
"""Exercise replay/resume semantics with a fake compiler; never invoke Lean."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import types
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('verify', Path(__file__).with_name('verify.py'))
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)
checkpoint_spec = importlib.util.spec_from_file_location('checkpoint', Path(__file__).with_name('checkpoint.py'))
checkpoint = importlib.util.module_from_spec(checkpoint_spec)
checkpoint_spec.loader.exec_module(checkpoint)


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.bin = self.root/'bin'
        self.bin.mkdir()
        (self.bin/'lean').write_text('fake compiler binary')
        (self.root/'lean-toolchain').write_text('pinned toolchain')
        (self.root/'lake-manifest.json').write_text('{}')
        (self.root/'lakefile.toml').write_text('name = "test"')
        (self.root/'Compact').mkdir()
        (self.root/'Compact/Base.lean').write_text('def x := 1\n')
        (self.root/'Compact/Final.lean').write_text('import Compact.Base\ndef y := x\n')
        self.calls = []
        self.reject = None
        self.fail = None
        self.interrupt = None
        self.addCleanup(patch.stopall)
        patch.object(verify, 'ROOT', self.root).start()
        patch.object(verify, 'BIN', self.bin).start()
        patch.object(verify.subprocess, 'check_output', return_value='{}').start()
        patch.object(verify.subprocess, 'run', side_effect=self.compile).start()

    def compile(self, command, **kwargs):
        source = Path(command[-1])
        self.calls.append((source.stem, command, kwargs['env']))
        output = Path(command[command.index('-o')+1])
        output.write_text(source.read_text())
        if source.stem == self.interrupt:
            raise KeyboardInterrupt('simulated five-hour interruption')
        if source.stem == self.reject:
            kwargs['stdout'].write("warning: declaration uses 'sorry'\n")
        return subprocess.CompletedProcess(command, 1 if source.stem == self.fail else 0)

    def replay(self, *arguments):
        with patch('sys.argv', ['verify.py', '--jobs', '8', *arguments, 'Compact.Final']), \
                contextlib.redirect_stdout(io.StringIO()):
            verify.main()

    def receipts(self):
        return json.loads((self.root/'.verification/checked-modules.json').read_text())

    def test_threads_and_reuse(self):
        self.replay()
        self.assertEqual([c[0] for c in self.calls], ['Base', 'Final'])
        self.assertTrue(all('-j8' in c[1] and c[2]['LEAN_NUM_THREADS']=='8' for c in self.calls))
        self.calls.clear()
        self.replay()
        self.assertEqual(self.calls, [])
        self.assertEqual(len(self.receipts()), 2)

    def test_changed_dependency_invalidates_descendants(self):
        self.replay()
        self.calls.clear()
        (self.root/'Compact/Base.lean').write_text('def x := 2\n')
        self.replay()
        self.assertEqual([c[0] for c in self.calls], ['Base', 'Final'])

    def test_changed_compiler_invalidates_receipts(self):
        self.replay()
        self.calls.clear()
        (self.bin/'lean').write_text('different compiler')
        self.replay()
        self.assertEqual(len(self.calls), 2)

    def test_tampered_object_or_log_recompiled(self):
        self.replay()
        self.calls.clear()
        (self.root/'.lake/build/lib/lean/Compact/Base.olean').write_text('tampered')
        (self.root/'.verification/Compact.Final.log').write_text('tampered')
        self.replay()
        self.assertEqual(len(self.calls), 2)

    def test_fresh_replays_every_module(self):
        self.replay()
        self.calls.clear()
        self.replay('--fresh')
        self.assertEqual(len(self.calls), 2)

    def test_admission_never_accepted(self):
        self.reject = 'Final'
        with self.assertRaises(SystemExit):
            self.replay()
        self.assertEqual(list(self.receipts()), ['Compact.Base'])
        self.assertFalse((self.root/'.lake/build/lib/lean/Compact/Final.olean').exists())

    def test_compile_error_keeps_prior_progress(self):
        self.fail = 'Final'
        with self.assertRaises(SystemExit):
            self.replay()
        self.assertEqual(list(self.receipts()), ['Compact.Base'])
        self.assertFalse((self.root/'.lake/build/lib/lean/Compact/Final.pending.olean').exists())

    def test_interrupted_compile_preserves_completed_receipt(self):
        self.interrupt = 'Final'
        with self.assertRaises(KeyboardInterrupt):
            self.replay()
        self.assertEqual(list(self.receipts()), ['Compact.Base'])
        self.assertFalse((self.root/'.lake/build/lib/lean/Compact/Final.olean').exists())
        self.interrupt = None
        self.calls.clear()
        self.replay()
        self.assertEqual([c[0] for c in self.calls], ['Final'])

    def test_interrupted_receipt_write_leaves_previous_json(self):
        target = self.root/'receipt.json'
        verify.write_json(target, {'completed': 1})
        with patch.object(Path, 'replace', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                verify.write_json(target, {'completed': 2})
        self.assertEqual(json.loads(target.read_text()), {'completed': 1})

    def test_checkpoint_roundtrip_reuses_real_runner_receipts(self):
        self.replay()
        current = dict(schema=checkpoint.SCHEMA, receipt_protocol=checkpoint.RECEIPT_PROTOCOL,
                       repository='owner/repo', commit='a'*40, branch='n12', profile='final',
                       configuration=checkpoint.configuration(self.root), system='Linux', machine='x86_64',
                       runner_os='Linux', runner_arch='X64', run_id='123')
        replay = types.SimpleNamespace(roots_for=lambda profile: ['Compact.Final'])
        with patch.object(checkpoint, 'load_script', side_effect=lambda root, name: verify if name=='verify' else replay), \
                patch.object(checkpoint, 'provenance', return_value=current):
            saved = checkpoint.package(self.root, 'final')
        for module in self.receipts():
            for name in checkpoint.module_paths(module):
                (self.root/name).unlink()
        (self.root/checkpoint.INDEX).unlink()
        checkpoint.restore_tar(self.root, self.root/saved['artifact'], current, current['commit'])
        self.calls.clear()
        self.replay()
        self.assertEqual(self.calls, [])


if __name__ == '__main__':
    unittest.main()
