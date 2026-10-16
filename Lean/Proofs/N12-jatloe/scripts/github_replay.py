#!/usr/bin/env python3
"""Explicit GitHub-only N12 replay. --plan is safe without Lean or networking.

Registered/selected profiles compile source components and remain scoped.
The final profile requires a separate unconditional theorem and a type/axiom
audit. This runner never invokes the unrelated parent N11 workflow.
"""
import argparse
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import traceback

ROOT = Path(__file__).resolve().parents[1]
BIN = Path.home()/'.elan/bin'
FINAL_MODULE = 'Compact.Assembly.Final'
FINAL_THEOREM = 'N12Compact.Final.optimality'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def load_script(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def roots_for(profile):
    roots = ['Compact.Assembly.ContinuousRemaining']
    if profile == 'selected':
        roots += ['Compact.Assembly.C981Progress']
        roots += ['.'.join(f.relative_to(ROOT).with_suffix('').parts)
                  for f in sorted((ROOT/'Compact/Completion').rglob('*.lean'))]
    elif profile == 'final':
        final = ROOT/Path(*FINAL_MODULE.split('.')).with_suffix('.lean')
        if not final.is_file():
            raise ValueError('Unconditional final source is absent; global proof is unfinished')
        roots = [FINAL_MODULE]
    return sorted(set(roots))


def package_config_paths(manifest):
    return [ROOT/(item['dir'] if item['type'] == 'path'
                  else str(Path(manifest['packagesDir'])/item['name']))/item['configFile']
            for item in manifest['packages'] if item['configFile'].endswith('.lean')]


def disk_preflight():
    free_gib = float(os.environ.get('N12_FREE_GIB', '3'))
    project_gib = float(os.environ.get('N12_PROJECT_GIB', '10'))
    if shutil.disk_usage(ROOT).free < free_gib*1024**3:
        raise RuntimeError(f'N12 replay needs at least {free_gib:g} GiB free for checkpointing')
    size = sum(f.stat().st_size for f in ROOT.rglob('*') if f.is_file())
    if size > project_gib*1024**3:
        raise RuntimeError(f'N12 project exceeds its {project_gib:g} GiB storage budget')


def run(*args, env=None, announce=True):
    if announce:
        print('Running: ' + ' '.join(map(str, args)), flush=True)
        subprocess.run(list(map(str, args)), cwd=ROOT, env=env, check=True)
        print('Completed: ' + ' '.join(map(str, args)), flush=True)
    else:
        with (ROOT/'.verification/replay-driver.log').open('a') as diagnostics:
            subprocess.run(list(map(str, args)), cwd=ROOT, env=env, check=True,
                           stderr=diagnostics)


def audit_global(verify, jobs=1):
    """Compilation checks the exact unconditional type, not a printed name."""
    directory = ROOT/'.verification'
    source = directory/'GlobalTypeAudit.lean'
    source.write_text(f'import {FINAL_MODULE}\n'
                      f'example : S12.packingConstant12 = 4 := {FINAL_THEOREM}\n'
                      f'set_option pp.fullNames true in\n#print axioms {FINAL_THEOREM}\n')
    with (directory/'replay-driver.log').open('a') as diagnostics:
        env = json.loads(subprocess.check_output(
            [str(BIN/'lake'), 'env', 'python3', '-c',
             'import json,os;print(json.dumps(dict(os.environ)))'], cwd=ROOT, text=True,
            stderr=diagnostics))
    env['LEAN_PATH'] = str(ROOT/'.lake/build/lib/lean')+os.pathsep+env.get('LEAN_PATH', '')
    env['LEAN_NUM_THREADS'] = str(jobs)
    result = subprocess.run([str(BIN/'lean'), f'-j{jobs}', str(source)], cwd=ROOT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (directory/'global-type-axiom-audit.log').write_text(result.stdout)
    if result.returncode or verify.has_admission(result.stdout):
        raise RuntimeError('Unconditional final theorem type audit failed; see saved log')
    match = re.search(re.escape(FINAL_THEOREM)+r"'? depends on axioms:\s*\[([^]]*)\]",
                      result.stdout, re.S)
    if match:
        axioms = {s.strip() for s in match.group(1).split(',') if s.strip()}
    elif FINAL_THEOREM in result.stdout and 'does not depend on any axioms' in result.stdout:
        axioms = set()
    else:
        raise RuntimeError('Final axiom output was not recognized; no success is asserted')
    from audit_native_axioms import closure, validate_runtime
    manifest = json.loads((ROOT/'audit/approved-native-axioms.json').read_text())
    validated = validate_runtime(closure(FINAL_MODULE), manifest, axioms)
    (directory/'global-native-axiom-audit.json').write_text(json.dumps(validated, indent=2)+'\n')
    return sorted(axioms)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', choices=['registered', 'selected', 'final'],
                        default='registered')
    parser.add_argument('--plan', action='store_true')
    parser.add_argument('--jobs', type=int, default=int(os.environ.get('N12_LEAN_THREADS', '1')))
    parser.add_argument('--resume-run', choices=['none'], default='none',
                        help='Resume uses the workflow build cache; old checkpoints omit Lean 4.35 sidecars')
    parser.add_argument('--module-jobs', type=int, default=1)
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--keep-going', action='store_true')
    args = parser.parse_args()
    if args.jobs < 1 or args.module_jobs < 1:
        parser.error('--jobs must be positive')
    if not args.plan:
        if os.environ.get('GITHUB_ACTIONS') != 'true':
            parser.error('Replay is GitHub-only; local use is restricted to --plan')
        run_identity = load_script('replay_state').reset(ROOT, args.profile)
    try:
        roots = roots_for(args.profile)
    except ValueError as error:
        parser.error(str(error))
    verify = load_script('verify')
    project = verify.closure(roots)
    if args.plan:
        print(json.dumps({'profile':args.profile, 'roots':roots,
                          'project_modules':len(project), 'compiled':False,
                          'global_optimality_proved':False}, indent=2))
        return
    from runner_resources import cgroup_directories, detect_cpu
    cpus, _ = detect_cpu(cgroup_directories())
    args.module_jobs = min(args.module_jobs, max(1, cpus // args.jobs))
    print(f'Parallel compilation: {args.module_jobs} modules × {args.jobs} Lean threads; {cpus} CPUs available.', flush=True)
    os.environ['N12_LEAN_THREADS'] = str(args.jobs)
    os.environ['LEAN_NUM_THREADS'] = str(args.jobs)
    disk_preflight()
    run('python3', 'scripts/bootstrap_sources.py')
    resolved = json.loads((ROOT/'.verification/toolchain.json').read_text())
    os.environ['ELAN_TOOLCHAIN'] = resolved['toolchain']
    global BIN
    BIN = Path(subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, text=True).strip()).parent
    census = load_script('source_census')
    with contextlib.redirect_stdout(io.StringIO()):
        census.main(roots)
    packages = [f for f in (ROOT/'.lake/packages').iterdir() if f.is_dir()]
    external, missing = census.external_closure([verify.path(m) for m in project], packages)
    if missing:
        raise RuntimeError('Missing dependency sources: '+', '.join(sorted(missing)))
    setup_sources = [ROOT/'.lake/packages/mathlib/Cache/Main.lean']
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    package_configs = package_config_paths(manifest)
    setup_sources += package_configs
    setup_external, setup_missing = census.external_closure(setup_sources, packages)
    setup_external.add('Cache.Main')
    if setup_missing:
        raise RuntimeError('Missing cache-tool sources: '+', '.join(sorted(setup_missing)))
    # Runtime entries, compiled Lake package configurations and their entire
    # dependency union count too; none is assumed to be in the proof closure.
    audit_modules = int(args.profile == 'final')
    total_modules = len(project)+len(package_configs)+audit_modules+len(external | setup_external)
    if total_modules > 10000:
        raise RuntimeError('Proof and cache setup exceed the hard 10000-module cap')
    # Core Lean/Std/Lake are provided by the resolved compiler. Mathlib's own
    # cache executable selects compatible archives for the remaining imports.
    cache_roots = sorted({m for module in project
        for m in census.header_imports(verify.path(module))
        if m.split('.')[0] not in {'Compact','Completion','S12','Init','Lean','Std','Lake','Cache'}})
    if not cache_roots:
        raise RuntimeError('Unexpected empty external cache root set')
    env = dict(os.environ, MATHLIB_CACHE_DIR=str(ROOT/'.lake/cache'))
    run('python3', 'scripts/prepare_cache.py', *cache_roots, env=env)
    disk_preflight()
    run('python3', 'scripts/verify.py', '--jobs', str(args.jobs),
        '--module-jobs', str(args.module_jobs),
        *(['--fresh'] if args.fresh else []),
        *(['--keep-going'] if args.keep_going else []), *roots, announce=False)
    report = {'profile':args.profile, 'roots':roots, 'compilation_complete':True,
              'run_identity':run_identity,
              'project_modules':len(project), 'external_modules':len(external),
              'cache_setup_project_modules':0,
              'toolchain':resolved,
              'compiled_package_configs':[str(p.relative_to(ROOT)) for p in package_configs],
              'global_type_audit_modules':audit_modules,
              'lean_threads':args.jobs,
              'cache_setup_extra_external_modules':sorted(setup_external-external),
              'combined_modules_including_cache_setup':total_modules,
              'global_optimality_proved':False}
    if args.profile == 'final':
        report['final_axioms'] = audit_global(verify, args.jobs)
        report['inherited_native_compiler_trust'] = bool(set(report['final_axioms']) - STANDARD_AXIOMS)
        report['global_optimality_proved'] = True
    verify.write_json(ROOT/'.verification/github-replay.json', report)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        directory = ROOT/'.verification'
        directory.mkdir(exist_ok=True)
        with (directory/'replay-error.log').open('w') as diagnostics:
            traceback.print_exc(file=diagnostics)
            if isinstance(error, subprocess.CalledProcessError) and error.output:
                diagnostics.write(str(error.output)+'\n')
        sys.exit(error.returncode if isinstance(error, subprocess.CalledProcessError)
                 and error.returncode > 0 else 1)
