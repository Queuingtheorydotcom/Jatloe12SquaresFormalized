#!/usr/bin/env python3
"""Dependency-scheduled source-to-object replay, with atomic receipts.

Use bounded.py around this runner. Library cache is read, never rebuilt.
An accepted conditional module is not an accepted global packing theorem.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import sys
import threading
sys.path.insert(0, str(next(parent for parent in Path(__file__).resolve().parents
                          if (parent/'ci/scheduler.py').is_file())))
from ci.scheduler import schedule

ROOT = Path(__file__).resolve().parents[1]
BIN = None
RECEIPT_VERSION = 2


def compiler_bin():
    """Resolve the selected compiler itself, rather than hashing the elan proxy."""
    global BIN
    if BIN is None:
        resolved = ROOT/'.verification/toolchain.json'
        if resolved.exists() and 'ELAN_TOOLCHAIN' not in os.environ:
            os.environ['ELAN_TOOLCHAIN'] = json.loads(resolved.read_text())['toolchain']
        elan = Path.home()/'.elan/bin/elan'
        compiler = subprocess.check_output(
            [str(elan), 'which', 'lean'], cwd=ROOT, text=True).strip()
        BIN = Path(compiler).resolve().parent
    return BIN


def failure_excerpt(log):
    """Keep CI output bounded; the complete diagnostic stays in its module log."""
    lines = log.splitlines()
    errors = [i for i, line in enumerate(lines) if re.search(r': error(?:\([^)]*\))?:', line)]
    if not errors:
        return '\n'.join(lines[:12])
    excerpt = [f'{len(errors)} error diagnostics; first {min(3, len(errors))}:']
    for index in errors[:3]:
        excerpt.extend(line[:500] for line in lines[index:index + 3])
    return '\n'.join(excerpt)


class CompilerProcesses:
    """Stop active compilers when one parallel check fails.

    Children stay in bounded.py's process group so aggregate accounting and
    deadline cleanup continue to cover them and any compiler descendants.
    """
    def __init__(self):
        self.lock = threading.Lock()
        self.children = set()
        self.cancelled = False

    def run(self, command, **kwargs):
        with self.lock:
            if self.cancelled:
                raise RuntimeError('Replay cancelled after another module failed')
            child = subprocess.Popen(command, **kwargs)
            self.children.add(child)
        try:
            return subprocess.CompletedProcess(command, child.wait())
        finally:
            # Retain interrupted children until abort() can terminate them.
            if child.poll() is not None:
                with self.lock:
                    self.children.discard(child)

    def abort(self):
        with self.lock:
            self.cancelled = True
            children = list(self.children)
            for child in children:
                if child.poll() is None:
                    try:
                        child.terminate()
                    except ProcessLookupError:
                        pass
        deadline = time.monotonic() + 3
        for child in children:
            try:
                child.wait(timeout=max(0, deadline-time.monotonic()))
            except subprocess.TimeoutExpired:
                try:
                    child.kill()
                except ProcessLookupError:
                    pass
                child.wait()


def write_json(path, value):
    """A deadline must leave either the old complete receipt or the new one."""
    temporary = path.with_name(path.name+'.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def configuration_fingerprint():
    inputs = [(name, hashlib.sha256((ROOT/name).read_bytes()).hexdigest())
              for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']
              if (ROOT/name).is_file()]
    # Restored receipts cannot silently carry over a different compiler binary.
    inputs.append(('lean', hashlib.sha256((compiler_bin()/'lean').read_bytes()).hexdigest()))
    return hashlib.sha256(json.dumps([RECEIPT_VERSION, inputs]).encode()).hexdigest()


def module_fingerprint(configuration, source_hash, dependencies):
    return hashlib.sha256(json.dumps([configuration, source_hash, dependencies],
                                    sort_keys=True).encode()).hexdigest()

def has_admission(log):
    return 'sorryAx' in log or "declaration uses 'sorry'" in log

def path(module):
    relative = Path(*module.split('.')).with_suffix('.lean')
    return ROOT/'source'/relative if module.startswith('S12.') else ROOT/relative

def imports(source):
    # Sources here use ordinary top-level imports; comments are removed first.
    source = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    return [m for line in re.findall(r'^\s*import\s+([^\n]+)', source, re.M)
            for m in line.split()]

def closure(roots):
    ordered, seen, active = [], set(), set()
    def visit(module):
        if module in seen or module.split('.')[0] not in {'Compact','Completion','S12'}:
            return
        if module in active:
            raise ValueError('Import cycle at '+module)
        active.add(module)
        for dep in imports(path(module).read_text()):
            visit(dep)
        active.remove(module); seen.add(module); ordered.append(module)
    for root in roots:
        visit(root)
    return ordered

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules',nargs='+')
    parser.add_argument('--plan',action='store_true')
    parser.add_argument('--jobs',type=int,
                        default=int(os.environ.get('N12_LEAN_THREADS', '1')))
    parser.add_argument('--fresh',action='store_true')
    parser.add_argument('--keep-going', action='store_true',
                        help='Check independent modules after failures; skip their dependents')
    parser.add_argument("--module-jobs", type=int, default=1)
    args=parser.parse_args()
    if args.jobs < 1 or args.module_jobs < 1:
        parser.error('--jobs must be positive')
    modules=closure(args.modules)
    if args.plan:
        print(json.dumps({'modules':modules,'source_bytes':sum(path(m).stat().st_size for m in modules)}));return
    if (ROOT/'PAUSED.json').exists():
        raise SystemExit('Proof work is paused. Read handoff/CONTINUATION-2026-10-14.txt; clear PAUSED.json only after an explicit user resume.')
    verification=ROOT/'.verification';verification.mkdir(exist_ok=True)
    out=ROOT/'.lake/build/lib/lean';out.mkdir(parents=True,exist_ok=True)
    compiler_bin()
    # Lake only computes the environment; it is never asked to build dependencies.
    env=json.loads(subprocess.check_output([str(BIN/'lake'),'env','python3','-c',
        'import os,json;print(json.dumps(dict(os.environ)))'],cwd=ROOT,text=True))
    env['LEAN_PATH']=str(out)+os.pathsep+env.get('LEAN_PATH','')
    env['LEAN_NUM_THREADS']=str(args.jobs)
    index_path=verification/'checked-modules.json'
    checked=json.loads(index_path.read_text()) if index_path.exists() and not args.fresh else {}
    if args.fresh:
        write_json(index_path, checked)
    configuration=configuration_fingerprint()
    fingerprints={}
    records=[]
    unsuccessful = set()
    accepted = 0
    failed = 0
    terminated = 0
    blocked = 0
    lock = threading.RLock()
    compilers = CompilerProcesses()
    write_json(verification/'latest-replay.json', {'records':records,
        'roots':args.modules,'complete':False,'global_optimality_proved':False})
    selected = set(modules)
    dependencies = {m: [d for d in imports(path(m).read_text()) if d in selected] for m in modules}
    def progress():
        print(f'module {accepted}/{len(modules)}', flush=True)

    def check_module(module):
        nonlocal accepted, failed, blocked, terminated
        with lock:
            blocked_by = [dep for dep in dependencies[module] if dep in unsuccessful]
            if blocked_by:
                unsuccessful.add(module)
                blocked += 1
                records.append({'module': module, 'status': 'blocked', 'blocked_by': blocked_by})
                write_json(verification/'latest-replay.json', {'records': records,
                    'roots': args.modules, 'complete': False, 'global_optimality_proved': False})
                return
        source=path(module); target=out/Path(*module.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        source_hash=hashlib.sha256(source.read_bytes()).hexdigest()
        fingerprint=module_fingerprint(configuration,source_hash,
            [(dep,fingerprints[dep]) for dep in imports(source.read_text())
             if dep in fingerprints])
        old=checked.get(module,{})
        old_log=verification/(module+'.log')
        if old.get('receipt_version')==RECEIPT_VERSION and \
            old.get('fingerprint')==fingerprint and target.exists() and \
            old.get('object_sha256')==hashlib.sha256(target.read_bytes()).hexdigest() and \
            old.get('record',{}).get('returncode')==0 and old_log.exists() and \
            old.get('record',{}).get('log_sha256')==hashlib.sha256(old_log.read_bytes()).hexdigest() and \
            not has_admission(old_log.read_text()):
            fingerprints[module]=fingerprint
            with lock:
                records.append(dict(old['record'],reused_verified_object=True))
                accepted += 1
                progress()
            return

        started=time.monotonic()
        log_path=verification/(module+'.log')
        temporary_target=target.with_name(target.stem+'.pending.olean')
        temporary_target.unlink(missing_ok=True)
        # Preserve diagnostics even if the resource guard terminates the group.
        with log_path.open('w') as log_file:
            # This pinned Lean rejects -M as an unknown max_memory option.
            # bounded.py enforces aggregate RSS and physical footprint instead.
            result=compilers.run([str(BIN/'lean'),f'-j{args.jobs}','-o',str(temporary_target),str(source)],
                cwd=ROOT,env=env,stdout=log_file,stderr=subprocess.STDOUT,text=True)
        log=log_path.read_text()
        # Lean can exit successfully after accepting an admission. Such an
        # object is never accepted or reused by this project runner.
        rejected_admission=has_admission(log)
        returncode=result.returncode or (1 if rejected_admission else 0)
        record={'module':module,'source_sha256':source_hash,
                'elapsed_seconds':round(time.monotonic()-started,3),'returncode':returncode,
                'lean_threads':args.jobs,
                'lean_returncode':result.returncode,'rejected_admission':rejected_admission,
                'log_sha256':hashlib.sha256(log.encode()).hexdigest()}
        with lock:
            records.append(record)
            if returncode == 0:
                temporary_target.replace(target)
                fingerprints[module]=fingerprint
                checked[module]={'receipt_version':RECEIPT_VERSION,
                    'fingerprint':fingerprint,'record':record,
                    'object_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
                write_json(index_path, checked)
                accepted += 1
            else:
                unsuccessful.add(module)
                if returncode < 0:
                    terminated += 1
                else:
                    failed += 1
                temporary_target.unlink(missing_ok=True)
                checked.pop(module, None)
                write_json(index_path, checked)
            write_json(verification/'latest-replay.json', {'records':records,
                'roots':args.modules,'complete':False,
                'global_optimality_proved':False})
            if returncode == 0:
                progress()
        if returncode and not args.keep_going:
            raise SystemExit(returncode)
    def failure_summary():
        # The console is reserved for the accepted-module counter. Compiler
        # diagnostics and failure categories remain in downloadable evidence.
        write_json(verification/'failure-summary.json', {
            'accepted': accepted, 'total': len(modules), 'failed': failed,
            'blocked': blocked, 'terminated': terminated,
            'failed_modules': [record['module'] for record in records
                               if record.get('returncode', 0) > 0]})

    try:
        schedule(modules, dependencies, check_module, workers=args.module_jobs,
                 abort=compilers.abort)
    except BaseException:
        # The scheduler has joined terminated workers before returning here.
        failure_summary()
        raise
    if unsuccessful:
        failure_summary()
        raise SystemExit(1)
    write_json(verification/'latest-replay.json', {'records':records,
        'roots':args.modules,'complete':True,'global_optimality_proved':False})

if __name__=='__main__':main()
