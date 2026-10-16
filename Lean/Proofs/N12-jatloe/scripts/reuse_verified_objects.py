#!/usr/bin/env python3
"""Reuse only unchanged, receipt- and hash-validated checkpoint objects.

This does not assert a fresh replay. verify.py recomputes the complete local
dependency fingerprint before consuming any copied object. Package manifests
and toolchain declarations must match; neither the source checkpoint nor its
shared library cache is modified.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('local_verify', ROOT/'scripts/verify.py')
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-dir', type=Path, required=True)
    parser.add_argument('--max-bytes', type=int, default=100*1024*1024)
    parser.add_argument('modules', nargs='+')
    args = parser.parse_args()
    cache = args.cache_dir.resolve()
    for name in ['lean-toolchain','lake-manifest.json']:
        if (ROOT/name).read_bytes() != (cache/name).read_bytes():
            raise SystemExit('Checkpoint configuration mismatch: '+name)
    old = json.loads((cache/'.verification/checked-modules.json').read_text())
    index_path = ROOT/'.verification/checked-modules.json'
    current = json.loads(index_path.read_text()) if index_path.exists() else {}
    configuration = hashlib.sha256((ROOT/'lean-toolchain').read_bytes()+
        (ROOT/'lake-manifest.json').read_bytes()).hexdigest()
    fingerprints = {}
    copied, total = [], 0
    for module in VERIFY.closure(args.modules):
        source = VERIFY.path(module)
        source_hash = digest(source)
        fingerprint = hashlib.sha256(json.dumps([configuration,source_hash,
            [(dep,fingerprints[dep]) for dep in VERIFY.imports(source.read_text())
                if dep in fingerprints]],sort_keys=True).encode()).hexdigest()
        fingerprints[module] = fingerprint
        candidate = old.get(module, {})
        relative = Path(*module.split('.')).with_suffix('.olean')
        target = ROOT/'.lake/build/lib/lean'/relative
        log_target = ROOT/'.verification'/(module+'.log')
        accepted = current.get(module, {})
        if accepted.get('fingerprint') == fingerprint and target.exists() and \
                accepted.get('object_sha256') == digest(target) and log_target.exists() and \
                accepted.get('record',{}).get('log_sha256') == digest(log_target):
            continue
        obj = cache/'.lake/build/lib/lean'/relative
        log = cache/'.verification'/(module+'.log')
        record = candidate.get('record', {})
        if candidate.get('fingerprint') != fingerprint or record.get('returncode') != 0 or \
                record.get('source_sha256') != source_hash or not obj.exists() or \
                candidate.get('object_sha256') != digest(obj) or not log.exists() or \
                record.get('log_sha256') != digest(log) or VERIFY.has_admission(log.read_text()):
            continue
        if total+obj.stat().st_size > args.max_bytes:
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(obj, target)
        shutil.copyfile(log, log_target)
        current[module] = candidate
        total += obj.stat().st_size
        copied.append(module)
    index_path.write_text(json.dumps(current,indent=2)+'\n')
    receipt = {'checkpoint':str(cache),'copied_modules':copied,'copied_bytes':total,
        'roots':args.modules,'fresh_replay':False,'global_optimality_proved':False}
    (ROOT/'.verification/latest-object-reuse.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'copied_modules':len(copied),'copied_bytes':total}))

if __name__=='__main__':
    main()
