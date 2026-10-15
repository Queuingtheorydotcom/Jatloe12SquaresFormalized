#!/usr/bin/env python3
"""Offline checks against stale success on reused runners; never invoke Lean."""
import json
import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import types
import unittest
from unittest.mock import patch

import replay_state as state
import github_replay as replay


class RunStateTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.directory = self.root/'.verification'
        self.directory.mkdir()
        patcher = patch.dict(state.os.environ, {
            'GITHUB_REPOSITORY': 'owner/repo', 'GITHUB_RUN_ID': '123',
            'GITHUB_RUN_ATTEMPT': '1', 'GITHUB_SHA': 'abc',
            'N12_REPLAY_PROFILE': 'final', 'CHECKPOINT_UPLOAD': 'success'}, clear=True)
        patcher.start()
        self.addCleanup(patcher.stop)

    def write_report(self, **changes):
        report = dict(profile='final', compilation_complete=True,
                      global_optimality_proved=True, run_identity=state.identity())
        report.update(changes)
        (self.directory/'github-replay.json').write_text(json.dumps(report))

    def test_reset_removes_success_but_preserves_verified_module_receipts(self):
        self.write_report()
        (self.directory/'checked-modules.json').write_text('{"saved":true}')
        state.reset(self.root)
        self.assertFalse((self.directory/'github-replay.json').exists())
        self.assertEqual((self.directory/'checked-modules.json').read_text(), '{"saved":true}')
        self.assertIn('incomplete', state.summary(self.root))

    def test_only_exact_current_run_can_report_success(self):
        self.write_report()
        self.assertIn('final theorem compiled', state.summary(self.root))
        for field in state.identity():
            with self.subTest(field=field):
                stale = state.identity()
                stale[field] = 'different'
                self.write_report(run_identity=stale)
                self.assertIn('incomplete', state.summary(self.root))

    def test_legacy_or_malformed_report_is_not_success(self):
        for value in ('{', '[]', '{"global_optimality_proved":true}'):
            with self.subTest(value=value):
                (self.directory/'github-replay.json').write_text(value)
                self.assertIn('incomplete', state.summary(self.root))

    def test_missing_identity_cannot_authenticate_a_report(self):
        with patch.dict(state.os.environ, {}, clear=True):
            self.write_report()
            self.assertIn('incomplete', state.summary(self.root))

    def test_final_audit_must_finish_before_success(self):
        self.write_report(global_optimality_proved=False)
        self.assertIn('incomplete', state.summary(self.root))

    def test_component_success_stays_scoped(self):
        with patch.dict(state.os.environ, {'N12_REPLAY_PROFILE': 'registered'}):
            self.write_report(profile='registered', global_optimality_proved=False)
            self.assertIn('Selected N12 components compiled', state.summary(self.root))

    def test_quiet_verification_saves_driver_diagnostics(self):
        output = io.StringIO()
        def command(*args, **kwargs):
            kwargs['stderr'].write('saved compiler driver detail\n')
        with patch.object(replay, 'ROOT', self.root), \
                patch.object(replay.subprocess, 'run', side_effect=command), \
                contextlib.redirect_stdout(output):
            replay.run('fake-compiler', announce=False)
        self.assertEqual(output.getvalue(), '')
        self.assertIn('driver detail', (self.directory/'replay-driver.log').read_text())

    def test_lake_warning_does_not_corrupt_audit_environment(self):
        def environment(*args, **kwargs):
            kwargs['stderr'].write('harmless Lake warning\n')
            return '{}'
        verify = types.SimpleNamespace(has_admission=lambda log: False)
        result = subprocess.CompletedProcess([], 0,
            "N12Compact.Final.optimality depends on axioms: [propext]\n")
        with patch.object(replay, 'ROOT', self.root), \
                patch.object(replay.subprocess, 'check_output', side_effect=environment), \
                patch.object(replay.subprocess, 'run', return_value=result):
            self.assertEqual(replay.audit_global(verify), ['propext'])
        self.assertIn('Lake warning', (self.directory/'replay-driver.log').read_text())


if __name__ == '__main__':
    unittest.main()
