#!/usr/bin/env python3
"""Size the N12 GitHub replay to its runner; --plan is read-only and local-safe.

The runtime guard keeps a modest RAM reserve and enough free disk to stage a
checkpoint. These settings do not change the conservative local build defaults.
"""
import argparse
import json
import math
import os
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
MIB = 1024**2
GIB = 1024**3


def read_text(path):
    try:
        return path.read_text().strip()
    except (OSError, UnicodeError):
        return ''


def cpu_set(text):
    result = set()
    for item in text.split(','):
        if not item:
            continue
        bounds = item.split('-')
        first, last = int(bounds[0]), int(bounds[-1])
        if len(bounds) > 2 or first < 0 or last < first:
            raise ValueError('Invalid CPU set')
        result.update(range(first, last+1))
    return result


def cgroup_directories(proc=Path('/proc'), cgroup=Path('/sys/fs/cgroup')):
    """Read the current cgroup and ancestors, including v1 controller mounts.

    Mount roots handle cgroup namespaces where /proc lists a host-relative path.
    The conventional mount locations are also checked for restricted /proc.
    """
    memberships = []
    for line in read_text(proc/'self/cgroup').splitlines():
        fields = line.split(':', 2)
        if len(fields) == 3:
            memberships.append((set(filter(None, fields[1].split(','))), fields[2]))
    groups = {name: set() for name in ('cpu', 'cpuset', 'memory')}

    def add(controller_names, mount, current):
        if not current.is_relative_to(mount):
            return
        while True:
            if current.is_dir():
                for name in controller_names:
                    groups[name].add(current)
            if current == mount:
                break
            current = current.parent

    for line in read_text(proc/'self/mountinfo').splitlines():
        parts = line.split(' - ', 1)
        if len(parts) != 2:
            continue
        left, right = parts[0].split(), parts[1].split()
        if len(left) < 5 or len(right) < 3 or right[0] not in {'cgroup', 'cgroup2'}:
            continue
        mount_root = Path(left[3])
        mount = Path(left[4])
        if mount.is_relative_to('/sys/fs/cgroup'):
            mount = cgroup/mount.relative_to('/sys/fs/cgroup')
        controllers = set(right[2].split(','))
        for names, member in memberships:
            selected = set(groups) if right[0] == 'cgroup2' and not names else names & controllers & set(groups)
            if not selected:
                continue
            member_path = Path(member)
            # Reject traversal components from namespace-relative proc paths.
            if '..' not in member_path.parts and member_path.is_relative_to(mount_root):
                add(selected, mount, mount/member_path.relative_to(mount_root))
            add(selected, mount, mount)
    for names, member in memberships:
        if '..' in Path(member).parts:
            member = '/'
        if not names:
            add(set(groups), cgroup, cgroup/member.lstrip('/'))
        else:
            for name in names & set(groups):
                mounts = [cgroup/name]
                if name == 'cpu':
                    mounts.append(cgroup/'cpu,cpuacct')
                for mount in mounts:
                    add({name}, mount, mount/member.lstrip('/'))
    # cgroup v2 root constraints remain useful even without readable membership.
    add(set(groups), cgroup, cgroup)
    return {name: sorted(paths) for name, paths in groups.items()}


def detect_cpu(groups, count=None, affinity=None):
    count = count or os.cpu_count() or 1
    if affinity is None:
        try:
            affinity = os.sched_getaffinity(0)
        except (AttributeError, OSError):
            affinity = set(range(count))
    allowed = set(affinity)
    quotas = []
    for directory in groups['cpuset']:
        raw = read_text(directory/'cpuset.cpus.effective') or read_text(directory/'cpuset.cpus')
        if raw:
            allowed &= cpu_set(raw)
    for directory in groups['cpu']:
        raw = read_text(directory/'cpu.max').split()
        if len(raw) == 2 and raw[0] != 'max':
            quotas.append(int(raw[0])/int(raw[1]))
        else:
            quota = read_text(directory/'cpu.cfs_quota_us')
            period = read_text(directory/'cpu.cfs_period_us')
            if quota and period and int(quota) > 0:
                quotas.append(int(quota)/int(period))
    limits = [count, len(allowed)]
    if quotas:
        # A fractional core still needs one worker to make full use of its time.
        limits.append(math.ceil(min(quotas)))
    available = max(1, min(limits))
    return available, {'host_logical_cpus': count, 'allowed_cpu_ids': sorted(allowed),
                       'cgroup_cpu_quotas': quotas, 'available_cpus': available}


def detect_memory(groups, proc=Path('/proc')):
    values = {}
    for line in read_text(proc/'meminfo').splitlines():
        fields = line.split()
        if len(fields) >= 2:
            values[fields[0].rstrip(':')] = int(fields[1])*1024
    if 'MemTotal' not in values:
        raise RuntimeError('Cannot determine Linux runner memory from /proc/meminfo')
    available = values.get('MemAvailable', sum(values.get(k, 0)
                           for k in ('MemFree', 'Buffers', 'Cached')))
    available = min(available, values['MemTotal'])
    constraints = []
    for directory in groups['memory']:
        limit = read_text(directory/'memory.max') or read_text(directory/'memory.limit_in_bytes')
        current = read_text(directory/'memory.current') or read_text(directory/'memory.usage_in_bytes')
        if limit and limit != 'max':
            if not current:
                raise RuntimeError('Cannot read usage for a limited memory cgroup: '+str(directory))
            remaining = max(0, int(limit)-int(current))
            available = min(available, remaining)
            constraints.append({'path': str(directory), 'limit_bytes': int(limit),
                                'current_bytes': int(current), 'available_bytes': remaining})
    return available, {'host_memory_bytes': values['MemTotal'],
                       'host_available_bytes': values.get('MemAvailable', available),
                       'cgroup_memory_limits': constraints, 'available_bytes': available}


def project_bytes(root):
    size = 0
    for directory, _, files in os.walk(root):
        for name in files:
            file = Path(directory)/name
            if not file.is_symlink():
                size += file.stat().st_size
    return size


def make_plan(available_cpus, available_memory, free_disk, current_project, jobs='auto'):
    try:
        requested = available_cpus if jobs == 'auto' else int(jobs)
    except ValueError as error:
        raise ValueError('--jobs must be auto or a positive integer') from error
    if requested < 1:
        raise ValueError('--jobs must be auto or a positive integer')
    threads = min(requested, available_cpus)
    memory_mib = available_memory//MIB
    memory_reserve_mib = max(256, math.ceil(memory_mib*.1))
    rss_mib = memory_mib-memory_reserve_mib
    if rss_mib < 128:
        raise RuntimeError('Runner has too little available RAM for a guarded replay')
    # At the full project budget, at least one project-sized archive plus this
    # OS reserve still fits. Round the project allowance down, the floor up.
    disk_reserve = max(3*GIB, min(8*GIB, math.ceil(free_disk*.05)))
    project_gib = math.floor((free_disk+current_project-disk_reserve)/2/GIB*10)/10
    free_gib = math.ceil((project_gib+disk_reserve/GIB)*10)/10
    if project_gib*GIB <= current_project or free_gib*GIB >= free_disk:
        raise RuntimeError('Runner has too little free disk to build and stage a checkpoint')
    return {'N12_LEAN_THREADS': str(threads), 'LEAN_NUM_THREADS': str(threads),
            'N12_RSS_MIB': str(rss_mib), 'N12_PROJECT_GIB': str(project_gib),
            'N12_CACHE_DOWNLOAD_MIB': str(min(1024, max(1, rss_mib//8))),
            # Restoration temporarily holds its ZIP plus staged objects. The
            # compilation phase separately reserves a new checkpoint archive.
            'N12_RESTORE_FREE_GIB': str(math.ceil(disk_reserve/GIB*10)/10),
            'N12_FREE_GIB': str(free_gib)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', default='auto', help='auto or a positive thread count, capped by available CPUs')
    parser.add_argument('--plan', action='store_true', help='show settings without writing files or GitHub environment')
    args = parser.parse_args()
    if not args.plan and os.environ.get('GITHUB_ACTIONS') != 'true':
        parser.error('Applying runner settings is GitHub-only; use --plan for local inspection')
    if sys.platform != 'linux':
        parser.error('Runner resource detection requires Linux; local defaults are unchanged')
    if not args.plan and not os.environ.get('GITHUB_ENV'):
        parser.error('GITHUB_ENV is required when applying runner settings')
    groups = cgroup_directories()
    cpus, cpu_report = detect_cpu(groups)
    memory, memory_report = detect_memory(groups)
    free_disk = shutil.disk_usage(ROOT).free
    current_project = project_bytes(ROOT)
    try:
        environment = make_plan(cpus, memory, free_disk, current_project, args.jobs)
    except (ValueError, RuntimeError) as error:
        parser.error(str(error))
    report = {'cpu': cpu_report, 'memory': memory_report,
              'disk': {'free_bytes': free_disk, 'current_project_bytes': current_project,
                       'checkpoint_policy': 'reserve one full project-sized archive plus OS headroom'},
              'requested_jobs': args.jobs, 'environment': environment,
              'replay_deadline_epoch': os.environ.get('N12_REPLAY_DEADLINE')}
    if not args.plan:
        directory = ROOT/'.verification'
        directory.mkdir(exist_ok=True)
        (directory/'runner-resources.json').write_text(json.dumps(report, indent=2)+'\n')
        with Path(os.environ['GITHUB_ENV']).open('a') as output:
            for name, value in environment.items():
                output.write(name+'='+value+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
