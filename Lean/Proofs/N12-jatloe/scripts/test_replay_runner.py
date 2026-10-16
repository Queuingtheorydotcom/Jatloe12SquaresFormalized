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
import threading
import time
import sys
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('verify', Path(__file__).with_name('verify.py'))
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)
checkpoint_spec = importlib.util.spec_from_file_location('checkpoint', Path(__file__).with_name('checkpoint.py'))
checkpoint = importlib.util.module_from_spec(checkpoint_spec)
checkpoint_spec.loader.exec_module(checkpoint)


class ReplayTests(unittest.TestCase):
    def test_resolved_toolchain_selects_actual_compiler(self):
        directory = self.root/'.verification'
        directory.mkdir()
        (directory/'toolchain.json').write_text(json.dumps({'toolchain': 'leanprover/lean4:v4.35.0'}))
        with patch.object(verify, 'BIN', None), patch.dict(verify.os.environ, {}, clear=True), \
                patch.object(verify.subprocess, 'check_output', return_value=str(self.bin/'lean')):
            self.assertEqual(verify.compiler_bin(), self.bin.resolve())
            self.assertEqual(verify.os.environ['ELAN_TOOLCHAIN'], 'leanprover/lean4:v4.35.0')

    def test_explicit_toolchain_override_is_preserved(self):
        directory = self.root/'.verification'
        directory.mkdir()
        (directory/'toolchain.json').write_text(json.dumps({'toolchain': 'older'}))
        with patch.object(verify, 'BIN', None), \
                patch.dict(verify.os.environ, {'ELAN_TOOLCHAIN': 'requested'}, clear=True), \
                patch.object(verify.subprocess, 'check_output', return_value=str(self.bin/'lean')):
            self.assertEqual(verify.compiler_bin(), self.bin.resolve())
            self.assertEqual(verify.os.environ['ELAN_TOOLCHAIN'], 'requested')

    def test_failure_excerpt_bounds_cascading_diagnostics(self):
        log = ''.join(f'File.lean:{i}:0: error: root or cascading failure\ncontext\n' for i in range(1000))
        excerpt = verify.failure_excerpt(log)
        self.assertIn('1000 error diagnostics; first 3:', excerpt)
        self.assertLess(len(excerpt), 1000)
        self.assertIn('File.lean:0:0:', excerpt)

    def test_parallel_siblings_finish_before_consumer_and_reuse_receipts(self):
        (self.root/'Compact/Other.lean').write_text('def z := 3\n')
        (self.root/'Compact/Final.lean').write_text('import Compact.Base Compact.Other\n')
        barrier = threading.Barrier(2, timeout=5)
        original = self.compile
        def compile_parallel(command, **kwargs):
            source = Path(command[-1])
            if source.stem in {'Base', 'Other'}:
                barrier.wait()
            else:
                self.assertEqual({c[0] for c in self.calls}, {'Base', 'Other'})
            return original(command, **kwargs)
        with patch.object(self, 'compiler', side_effect=compile_parallel):
            self.replay('--module-jobs', '2')
        self.assertEqual(len(self.receipts()), 3)
        self.calls.clear()
        self.replay('--module-jobs', '2')
        self.assertEqual(self.calls, [])

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
        self.compiler = self.compile
        self.addCleanup(patch.stopall)
        patch.object(verify, 'ROOT', self.root).start()
        patch.object(verify, 'BIN', self.bin).start()
        patch.object(verify.subprocess, 'check_output', return_value='{}').start()
        case = self
        class FakeCompiler:
            def __init__(self, command, **kwargs):
                self.command, self.kwargs = command, kwargs
                self.returncode = None

            def wait(self, timeout=None):
                if self.returncode is None:
                    try:
                        self.returncode = case.compiler(self.command, **self.kwargs).returncode
                    except BaseException:
                        self.returncode = 130
                        raise
                return self.returncode

            def poll(self):
                return self.returncode

            def terminate(self):
                self.returncode = -15

            def kill(self):
                self.returncode = -9
        patch.object(verify.subprocess, 'Popen', side_effect=FakeCompiler).start()

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

    def test_keep_going_checks_independent_failures_and_blocks_dependents(self):
        (self.root/'Compact/Other.lean').write_text('def z := 3\n')
        (self.root/'Compact/Child.lean').write_text('import Compact.Base\n')
        (self.root/'Compact/Final.lean').write_text('import Compact.Child Compact.Other\n')
        self.fail = 'Base'
        self.reject = 'Other'
        with self.assertRaises(SystemExit):
            self.replay('--keep-going', '--module-jobs', '2')
        self.assertEqual({call[0] for call in self.calls}, {'Base', 'Other'})
        report = json.loads((self.root/'.verification/latest-replay.json').read_text())
        self.assertFalse(report['complete'])
        self.assertEqual(sum(r.get('returncode', 0) != 0 for r in report['records']), 2)
        self.assertEqual({r['module'] for r in report['records'] if r.get('status') == 'blocked'},
                         {'Compact.Child', 'Compact.Final'})
        self.fail = self.reject = None
        self.calls.clear()
        self.replay('--keep-going')
        self.assertEqual(len(self.receipts()), 4)

    def test_default_stops_before_independent_work(self):
        (self.root/'Compact/Other.lean').write_text('def z := 3\n')
        (self.root/'Compact/Final.lean').write_text('import Compact.Base Compact.Other\n')
        self.fail = 'Base'
        with self.assertRaises(SystemExit):
            self.replay()
        self.assertEqual([call[0] for call in self.calls], ['Base'])

    def test_stdout_contains_only_accepted_module_progress(self):
        for fresh in (True, False):
            output = io.StringIO()
            with patch('sys.argv', ['verify.py', 'Compact.Final']), contextlib.redirect_stdout(output):
                verify.main()
            self.assertEqual(output.getvalue(), 'module 1/2\nmodule 2/2\n')
            if fresh:
                self.calls.clear()
        self.assertEqual(self.calls, [])

    def test_terminated_compiler_is_not_counted_as_a_proof_failure(self):
        original = self.compile
        def terminate(command, **kwargs):
            result = original(command, **kwargs)
            if Path(command[-1]).stem == 'Final':
                result.returncode = -15
            return result
        self.compiler = terminate
        output = io.StringIO()
        with patch('sys.argv', ['verify.py', 'Compact.Final']), contextlib.redirect_stdout(output):
            with self.assertRaises(SystemExit):
                verify.main()
        self.assertEqual(output.getvalue(), 'module 1/2\n')
        summary = json.loads((self.root/'.verification/failure-summary.json').read_text())
        self.assertEqual((summary['failed'], summary['terminated']), (0, 1))

    def test_failed_module_does_not_advance_progress_and_log_is_saved(self):
        self.reject = 'Final'
        output = io.StringIO()
        with patch('sys.argv', ['verify.py', 'Compact.Final']), contextlib.redirect_stdout(output):
            with self.assertRaises(SystemExit):
                verify.main()
        self.assertEqual(output.getvalue(), 'module 1/2\n')
        summary = json.loads((self.root/'.verification/failure-summary.json').read_text())
        self.assertEqual(summary['failed_modules'], ['Compact.Final'])
        self.assertEqual((summary['accepted'], summary['failed']), (1, 1))
        self.assertIn("declaration uses 'sorry'", (self.root/'.verification/Compact.Final.log').read_text())
        report = json.loads((self.root/'.verification/latest-replay.json').read_text())
        self.assertFalse(report['complete'])
        self.assertEqual(report['records'][-1]['returncode'], 1)

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


class ParallelAbortTests(unittest.TestCase):
    def test_failure_terminates_running_compiler_before_scheduler_returns(self):
        compilers = verify.CompilerProcesses()
        started = threading.Event()
        children = []
        original_popen = subprocess.Popen
        def launch(command, **kwargs):
            child = original_popen(command, **kwargs)
            children.append(child)
            started.set()
            return child
        def check(module):
            if module == 'failed':
                self.assertTrue(started.wait(timeout=3))
                raise RuntimeError('simulated compiler failure')
            return compilers.run([sys.executable, '-c', 'import time; time.sleep(60)'],
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        begin = time.monotonic()
        try:
            with patch.object(verify.subprocess, 'Popen', side_effect=launch):
                with self.assertRaisesRegex(RuntimeError, 'simulated compiler failure'):
                    verify.schedule(['failed', 'running'], {'failed': [], 'running': []},
                                    check, workers=2, abort=compilers.abort)
            self.assertLess(time.monotonic()-begin, 5)
            self.assertEqual(len(children), 1)
            self.assertIsNotNone(children[0].poll())
            with self.assertRaisesRegex(RuntimeError, 'Replay cancelled'):
                compilers.run([sys.executable, '-c', 'pass'])
        finally:
            compilers.abort()


if __name__ == '__main__':
    unittest.main()
