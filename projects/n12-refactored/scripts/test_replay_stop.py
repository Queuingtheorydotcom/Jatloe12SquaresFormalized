#!/usr/bin/env python3
"""Offline fixtures for guarded replay failure classification."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest

from replay_stop import classify


class StopTests(unittest.TestCase):
    def receipt(self, reason=None, **extra):
        return dict(stop_reason=reason, remaining_processes=[], cleanup_errors=[], **extra)

    def test_only_clean_time_limits_become_checkpoint_success(self):
        for reason in ('deadline_reached', 'elapsed_time_limit'):
            result = classify(124, self.receipt(reason))
            self.assertEqual(result['workflow_exit_code'], 0)
            self.assertTrue(result['checkpointed'])
            self.assertFalse(result['global_optimality_proved'])
        receipt = self.receipt('deadline_reached')
        receipt['remaining_processes'] = [123]
        self.assertEqual(classify(124, receipt)['workflow_exit_code'], 124)

    def test_interruption_is_failed_including_legacy_exit_124(self):
        for code in (124, 130, 143):
            result = classify(code, self.receipt('interrupted', interrupt_signal=signal.SIGTERM))
            self.assertEqual(result['status'], 'interrupted')
            self.assertEqual(result['workflow_exit_code'], code)
            self.assertIn('SIGTERM', result['message'])
            self.assertFalse(result['checkpointed'])

    def test_resource_stops_keep_the_reason_and_measurements(self):
        for reason in ('aggregate_rss_limit', 'aggregate_physical_footprint_limit', 'free_disk_floor'):
            result = classify(124, self.receipt(reason, peak_group_rss_kib=1024,
                                               minimum_free_bytes=2048, limits={'free_gib': 3}))
            self.assertEqual(result['status'], 'resource_limit')
            self.assertEqual(result['workflow_exit_code'], 124)
            self.assertEqual(result['minimum_free_bytes'], 2048)
            self.assertEqual(result['limits'], {'free_gib': 3})

    def test_command_and_guard_errors_remain_failed(self):
        self.assertEqual(classify(1, self.receipt())['status'], 'command_failed')
        self.assertEqual(classify(124, self.receipt('monitor_error'))['status'], 'guard_failed')
        self.assertEqual(classify(124, self.receipt())['workflow_exit_code'], 124)
        self.assertEqual(classify(0, self.receipt('monitor_error'))['workflow_exit_code'], 1)

    def test_success_does_not_claim_a_global_theorem(self):
        result = classify(0, self.receipt())
        self.assertEqual(result['workflow_exit_code'], 0)
        self.assertFalse(result['global_optimality_proved'])

    def test_cli_saves_diagnostic_and_summary_without_assertion_traceback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            receipt = root/'receipt.json'
            output, summary, workflow_output = root/'output.json', root/'summary', root/'workflow-output'
            receipt.write_text(json.dumps(self.receipt('interrupted', interrupt_signal=15)))
            result = subprocess.run([sys.executable, str(Path(__file__).with_name('replay_stop.py')),
                                     '--exit-code', '143', '--receipt', str(receipt), '--output', str(output)],
                                    env=dict(os.environ, GITHUB_STEP_SUMMARY=str(summary), GITHUB_OUTPUT=str(workflow_output)),
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 143)
            self.assertEqual(result.stderr, '')
            self.assertEqual(json.loads(output.read_text())['status'], 'interrupted')
            self.assertIn('SIGTERM', summary.read_text())
            self.assertEqual(workflow_output.read_text(), 'checkpointed=false\n')

    def test_missing_receipt_fails_even_when_command_reports_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root/'output.json'
            env = {k: v for k, v in os.environ.items() if k not in {'GITHUB_STEP_SUMMARY', 'GITHUB_OUTPUT'}}
            result = subprocess.run([sys.executable, str(Path(__file__).with_name('replay_stop.py')),
                                     '--exit-code', '0', '--receipt', str(root/'missing'), '--output', str(output)],
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertEqual(json.loads(output.read_text())['status'], 'receipt_error')


if __name__ == '__main__':
    unittest.main()
