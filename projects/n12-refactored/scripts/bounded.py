#!/usr/bin/env python3
"""Run one process group under aggregate RSS, elapsed-time and free-disk limits."""
import argparse
import ctypes
import errno
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

# macOS RSS omits compressed/private pages. Count the kernel's physical
# footprint too, so a compressing process cannot evade the aggregate limit.
# Layout is rusage_info_v2 from the installed SDK's sys/resource.h.
class RUsageInfoV2(ctypes.Structure):
    _fields_ = [('uuid', ctypes.c_uint8 * 16)] + [
        (name, ctypes.c_uint64) for name in (
            'user_time', 'system_time', 'pkg_idle_wkups', 'interrupt_wkups',
            'pageins', 'wired_size', 'resident_size', 'phys_footprint',
            'proc_start_abstime', 'proc_exit_abstime', 'child_user_time',
            'child_system_time', 'child_pkg_idle_wkups', 'child_interrupt_wkups',
            'child_pageins', 'child_elapsed_abstime', 'diskio_bytesread',
            'diskio_byteswritten')]

if sys.platform == 'darwin':
    _libproc = ctypes.CDLL('/usr/lib/libproc.dylib', use_errno=True)
    _pid_rusage = _libproc.proc_pid_rusage
    _pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
    _pid_rusage.restype = ctypes.c_int

def footprint_kib(pid):
    if sys.platform != 'darwin':
        return 0
    info = RUsageInfoV2()
    if _pid_rusage(pid, 2, ctypes.byref(info)):
        error = ctypes.get_errno()
        if error == errno.ESRCH:
            return 0  # The process exited after the accounting snapshot.
        raise OSError(error, 'Cannot monitor physical footprint', str(pid))
    return (info.phys_footprint + 1023) // 1024

def processes():
    result = subprocess.run(['ps', '-axo', 'pid=,pgid=,rss=,stat='],
                            capture_output=True, text=True, check=True)
    return [tuple(map(int, fields[:3])) for line in result.stdout.splitlines()
            if (fields := line.split()) and 'Z' not in fields[3]]

def stopped_process_details(pgid):
    """One stop-time snapshot; comm excludes command arguments."""
    result = subprocess.run(['ps', '-axo', 'pid=,pgid=,rss=,stat=,comm='],
                            capture_output=True, text=True, check=True, timeout=1)
    details = []
    for line in result.stdout.splitlines():
        fields = line.split(None, 4)
        if len(fields) == 5 and int(fields[1]) == pgid and 'Z' not in fields[3]:
            details.append({'pid': int(fields[0]), 'pgid': int(fields[1]),
                            'rss_kib': int(fields[2]),
                            'comm': os.path.basename(fields[4])})
    return sorted(details, key=lambda item: item['rss_kib'], reverse=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rss-mib', type=int, default=1200)
    parser.add_argument('--footprint-mib', type=int,
                        help='macOS physical footprint cap; defaults to the RSS cap')
    parser.add_argument('--seconds', type=int, default=180)
    parser.add_argument('--threads', type=int, default=1,
                        help='Lean worker threads; local default remains one')
    parser.add_argument('--deadline', type=float,
                        help='absolute Unix deadline shared across setup and replay')
    parser.add_argument('--free-gib', type=float, default=4)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.threads < 1 or args.seconds <= 0:
        parser.error('--threads and --seconds must be positive')
    if args.deadline is not None and not math.isfinite(args.deadline):
        parser.error('--deadline must be a finite Unix timestamp')
    checkpoint_root = Path(__file__).resolve().parents[1]
    if (checkpoint_root/'PAUSED.json').exists():
        raise SystemExit('Computation is paused. Read PAUSED.json; clear it only after an explicit request to resume.')
    footprint_limit = args.footprint_mib if args.footprint_mib is not None else args.rss_mib
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('A command is required')
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    deadline_remaining = args.deadline-time.time() if args.deadline is not None else None
    effective_seconds = min(args.seconds, deadline_remaining) if deadline_remaining is not None else args.seconds
    time_limit_reason = ('deadline_reached' if deadline_remaining is not None and
                         deadline_remaining <= args.seconds else 'elapsed_time_limit')
    peak = 0
    peak_footprint = 0
    minimum_free_bytes = shutil.disk_usage('.').free
    reason = None
    child = None
    cleanup_errors = []
    peak_group_processes = []
    stop_group_processes = []
    stop_snapshot_error = None
    def interrupt(signum, frame):
        raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM, interrupt)
    try:
        if effective_seconds <= 0:
            reason = 'deadline_reached'
            raise RuntimeError('Shared replay deadline reached before launch')
        processes()  # Fail closed before launching if monitoring is unavailable.
        footprint_kib(os.getpid())
        if shutil.disk_usage('.').free < args.free_gib * 1024**3:
            reason = 'free_disk_floor'
            raise RuntimeError('Free-disk floor reached before launch')
        if time.monotonic()-started >= effective_seconds:
            reason = time_limit_reason
            raise RuntimeError('Time allowance reached before launch')
        child = subprocess.Popen(command, start_new_session=True,
                                 env=dict(os.environ, OMP_NUM_THREADS='1',
                                          OPENBLAS_NUM_THREADS='1', LEAN_NUM_THREADS=str(args.threads)))
        while child.poll() is None:
            group = [(pid, pgid, r) for pid, pgid, r in processes() if pgid == child.pid]
            rss = sum(r for _, _, r in group)
            footprint = sum(footprint_kib(pid) for pid, _, _ in group)
            peak_footprint = max(peak_footprint, footprint)
            if rss > peak:
                peak = rss
                # Reuse the normal accounting sample; do not add polling work.
                peak_group_processes = [
                    {'pid': pid, 'pgid': pgid, 'rss_kib': r}
                    for pid, pgid, r in sorted(group, key=lambda item: item[2], reverse=True)]
            free_bytes = shutil.disk_usage('.').free
            minimum_free_bytes = min(minimum_free_bytes, free_bytes)
            if rss > args.rss_mib * 1024:
                reason = 'aggregate_rss_limit'
            elif footprint > footprint_limit * 1024:
                reason = 'aggregate_physical_footprint_limit'
            elif time.monotonic() - started >= effective_seconds:
                reason = time_limit_reason
            elif free_bytes < args.free_gib * 1024**3:
                reason = 'free_disk_floor'
            if reason:
                try:
                    stop_group_processes = stopped_process_details(child.pid)
                except (OSError, subprocess.SubprocessError, ValueError) as error:
                    # Diagnostics must never bypass the existing group cleanup.
                    stop_snapshot_error = str(error)
                print(json.dumps({'stopping':reason,'minimum_free_bytes':minimum_free_bytes,'peak_group_rss_kib':peak,
                    'peak_group_physical_footprint_kib':peak_footprint}),flush=True)
                break
            time.sleep(0.25)
    except KeyboardInterrupt:
        reason = 'interrupted'
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        reason = reason or 'monitor_error'
        stop_snapshot_error = str(error)
    finally:
        if child is not None:
            try:
                if child.poll() is None:
                    os.killpg(child.pid, signal.SIGTERM)
                    child.wait(timeout=3)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
                except ProcessLookupError:
                    pass
                except PermissionError as error:
                    cleanup_errors.append(str(error))
            except ProcessLookupError:
                pass
            except PermissionError as error:
                cleanup_errors.append(str(error))
            remaining = [pid for pid, pgid, _ in processes() if pgid == child.pid]
            # On macOS the process leader can exit before its descendants
            # finish handling TERM. Allow their short shutdown/reap window.
            cleanup_deadline = time.monotonic() + 3
            while remaining and time.monotonic() < cleanup_deadline:
                time.sleep(0.1)
                remaining = [pid for pid, pgid, _ in processes() if pgid == child.pid]
            if remaining:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                    time.sleep(0.1)
                except ProcessLookupError:
                    pass
                except PermissionError as error:
                    cleanup_errors.append(str(error))
            if remaining:
                time.sleep(0.5)
            args.receipt.write_text(json.dumps({
                'command': command, 'returncode': child.returncode, 'stop_reason': reason,
                'limits': {'rss_mib': args.rss_mib, 'physical_footprint_mib': footprint_limit,
                           'seconds': args.seconds, 'free_gib': args.free_gib,
                           'threads': args.threads, 'deadline_epoch': args.deadline,
                           'effective_seconds': max(0, effective_seconds)},
                'elapsed_seconds': round(time.monotonic()-started, 3),
                'minimum_free_bytes': minimum_free_bytes,
                'peak_group_rss_kib': peak,
                'peak_group_physical_footprint_kib': peak_footprint,
                'peak_group_processes': peak_group_processes,
                'stop_group_processes': stop_group_processes,
                'stop_snapshot_error': stop_snapshot_error,
                'cleanup_errors':cleanup_errors,
                'remaining_processes': [pid for pid, pgid, _ in processes() if pgid == child.pid]
            }, indent=2) + '\n')
    if child is None:
        report = {
            'command': command, 'returncode': None, 'stop_reason': reason,
            'launched': False,
            'limits': {'rss_mib': args.rss_mib, 'physical_footprint_mib': footprint_limit,
                       'seconds': args.seconds, 'free_gib': args.free_gib,
                       'threads': args.threads, 'deadline_epoch': args.deadline,
                       'effective_seconds': max(0, effective_seconds)},
            'elapsed_seconds': round(time.monotonic()-started, 3),
            'minimum_free_bytes': minimum_free_bytes,
            'monitor_error': stop_snapshot_error,
            'cleanup_errors': [], 'remaining_processes': []}
        args.receipt.write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps({'stopping': reason, 'launched': False,
                          'minimum_free_bytes': minimum_free_bytes}), flush=True)
    raise SystemExit(124 if reason else child.returncode)

if __name__ == '__main__':
    main()
