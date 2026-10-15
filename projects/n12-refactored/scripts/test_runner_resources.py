#!/usr/bin/env python3
"""Small fixture tests only: no Lean, network, or repository build artifacts."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

import runner_resources as resources


class ResourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.proc = self.root/'proc'
        self.group = self.root/'cgroup'
        (self.proc/'self').mkdir(parents=True)
        self.group.mkdir()

    def write(self, path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_v2_affinity_cpuset_and_parent_quota(self):
        self.write(self.proc/'self/cgroup', '0::/job/task\n')
        self.write(self.group/'cpu.max', 'max 100000')
        self.write(self.group/'job/cpu.max', '250000 100000')
        self.write(self.group/'job/task/cpu.max', 'max 100000')
        self.write(self.group/'job/cpuset.cpus.effective', '2-7')
        groups = resources.cgroup_directories(self.proc, self.group)
        cpus, report = resources.detect_cpu(groups, count=32, affinity=set(range(8)))
        self.assertEqual(cpus, 3)
        self.assertEqual(report['allowed_cpu_ids'], list(range(2, 8)))

    def test_v1_controller_mounts(self):
        self.write(self.proc/'self/cgroup', '2:cpu,cpuacct:/job\n3:memory:/job\n4:cpuset:/job\n')
        self.write(self.group/'cpu,cpuacct/job/cpu.cfs_quota_us', '100000')
        self.write(self.group/'cpu,cpuacct/job/cpu.cfs_period_us', '100000')
        self.write(self.group/'cpuset/job/cpuset.cpus', '0-7')
        groups = resources.cgroup_directories(self.proc, self.group)
        cpus, _ = resources.detect_cpu(groups, count=16, affinity=set(range(16)))
        self.assertEqual(cpus, 1)

    def test_namespace_mount_root(self):
        self.write(self.proc/'self/cgroup', '0::/docker/job/task\n')
        self.write(self.proc/'self/mountinfo',
                   '30 20 0:1 /docker/job /sys/fs/cgroup rw - cgroup2 cgroup rw\n')
        self.write(self.group/'task/cpu.max', '200000 100000')
        groups = resources.cgroup_directories(self.proc, self.group)
        cpus, _ = resources.detect_cpu(groups, count=16, affinity=set(range(16)))
        self.assertEqual(cpus, 2)

    def test_memory_minimum_includes_parent_remaining(self):
        self.write(self.proc/'meminfo', 'MemTotal: 16777216 kB\nMemAvailable: 12582912 kB\n')
        self.write(self.proc/'self/cgroup', '0::/job/task\n')
        self.write(self.group/'memory.max', 'max')
        self.write(self.group/'job/memory.max', str(8*resources.GIB))
        self.write(self.group/'job/memory.current', str(3*resources.GIB))
        self.write(self.group/'job/task/memory.max', str(6*resources.GIB))
        self.write(self.group/'job/task/memory.current', str(resources.GIB))
        available, _ = resources.detect_memory(
            resources.cgroup_directories(self.proc, self.group), self.proc)
        self.assertEqual(available, 5*resources.GIB)

    def test_v1_memory_current_not_only_limit(self):
        self.write(self.proc/'meminfo', 'MemTotal: 16777216 kB\nMemAvailable: 12582912 kB\n')
        self.write(self.proc/'self/cgroup', '2:memory:/job\n')
        self.write(self.group/'memory/job/memory.limit_in_bytes', str(4*resources.GIB))
        self.write(self.group/'memory/job/memory.usage_in_bytes', str(resources.GIB))
        available, _ = resources.detect_memory(
            resources.cgroup_directories(self.proc, self.group), self.proc)
        self.assertEqual(available, 3*resources.GIB)

    def test_all_cpus_and_ninety_percent_memory(self):
        plan = resources.make_plan(64, 64*resources.GIB, 200*resources.GIB, 2*resources.GIB)
        self.assertEqual(plan['N12_LEAN_THREADS'], '64')
        self.assertEqual(plan['LEAN_NUM_THREADS'], '64')
        self.assertLessEqual(int(plan['N12_RSS_MIB']), .90*64*1024)
        self.assertGreater(int(plan['N12_RSS_MIB']), .89*64*1024)
        self.assertEqual(plan['N12_CACHE_DOWNLOAD_MIB'], '1024')
        self.assertGreater(float(plan['N12_PROJECT_GIB']), 10)
        project = float(plan['N12_PROJECT_GIB'])
        self.assertLessEqual(project*2+8, 202)
        self.assertGreaterEqual(float(plan['N12_FREE_GIB']), project+8)
        self.assertEqual(float(plan['N12_RESTORE_FREE_GIB']), 8)
        self.assertLess(float(plan['N12_RESTORE_FREE_GIB']), float(plan['N12_FREE_GIB']))

    def test_explicit_jobs_are_capped(self):
        args = (8, 8*resources.GIB, 40*resources.GIB, resources.GIB)
        self.assertEqual(resources.make_plan(*args, jobs='4')['N12_LEAN_THREADS'], '4')
        self.assertEqual(resources.make_plan(*args, jobs='64')['N12_LEAN_THREADS'], '8')
        for value in ('0', '-1', 'many'):
            with self.assertRaises(ValueError):
                resources.make_plan(*args, jobs=value)

    def test_low_resources_fail_closed(self):
        with self.assertRaises(RuntimeError):
            resources.make_plan(4, 128*resources.MIB, 20*resources.GIB, resources.GIB)
        with self.assertRaises(RuntimeError):
            resources.make_plan(4, 4*resources.GIB, resources.GIB, resources.GIB)


class BoundedTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root/'scripts').mkdir()
        self.script = self.root/'scripts/bounded.py'
        shutil.copyfile(Path(__file__).with_name('bounded.py'), self.script)
        self.receipt = self.root/'receipt.json'

    def run_child(self, code, *limits):
        return subprocess.run([sys.executable, str(self.script), '--rss-mib', '512',
                               '--free-gib', '0', '--seconds', '10',
                               '--receipt', str(self.receipt), *map(str, limits), '--',
                               sys.executable, '-c', code], cwd=self.root,
                              capture_output=True, text=True, timeout=15)

    def test_default_is_one_thread_and_override_reaches_child(self):
        for threads in (1, 3):
            flags = [] if threads == 1 else ['--threads', str(threads)]
            result = self.run_child('import os; print(os.environ["LEAN_NUM_THREADS"])', *flags)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), str(threads))
            report = json.loads(self.receipt.read_text())
            self.assertEqual(report['limits']['threads'], threads)

    def test_expired_deadline_does_not_launch(self):
        marker = self.root/'launched'
        result = self.run_child('from pathlib import Path; Path("launched").touch()',
                                '--deadline', time.time()-1)
        self.assertEqual(result.returncode, 124, result.stderr)
        self.assertFalse(marker.exists())
        report = json.loads(self.receipt.read_text())
        self.assertFalse(report['launched'])
        self.assertEqual(report['stop_reason'], 'deadline_reached')

    def test_deadline_stops_descendants_and_preserves_receipt(self):
        result = self.run_child('import subprocess, sys; '
                               'subprocess.run([sys.executable, "-c", "import time; time.sleep(60)"])',
                               '--deadline', time.time()+.6)
        self.assertEqual(result.returncode, 124, result.stderr)
        report = json.loads(self.receipt.read_text())
        self.assertEqual(report['stop_reason'], 'deadline_reached')
        self.assertEqual(report['remaining_processes'], [])
        self.assertEqual(report['cleanup_errors'], [])
        self.assertLess(report['elapsed_seconds'], 8)

    def test_pause_still_blocks_launch(self):
        (self.root/'PAUSED.json').write_text('{}')
        result = self.run_child('raise RuntimeError("must not launch")')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('paused', result.stderr)
        self.assertFalse(self.receipt.exists())


if __name__ == '__main__':
    unittest.main()
