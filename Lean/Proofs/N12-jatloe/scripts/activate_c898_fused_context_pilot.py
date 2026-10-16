#!/usr/bin/env python3
"""Parent-only activation of one new authentic C898 context-fusion pilot.

Does not replace any production context or terminal theorem. The two exact
records are copied from authenticated proposals into an isolated namespace:
one cyclic nonterminal context and one explicit terminal fan. No Lean runs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import signal
import time

ROOT = Path(__file__).resolve().parents[1]
TARGET = 'Compact/Cases/C898/FusedContextPilot.lean'
RECEIPT = 'evidence/c898-fused-context-pilot-activation.json'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def regular(relative):
    path = ROOT / relative
    if not path.is_relative_to(ROOT) or '..' in Path(relative).parts:
        raise ValueError('Path outside project')
    for component in (path, *path.parents):
        if component == ROOT:
            break
        if component.is_symlink():
            raise ValueError('Symlink refused: ' + str(component))
    return path


def proposal(name, module):
    folder = regular('evidence/proposals/' + name)
    manifest_raw = (folder / 'manifest.json').read_bytes()
    manifest = json.loads(manifest_raw)
    raw = (folder / module).read_bytes()
    expected = manifest['output_files'][module]
    assert sha(raw) == expected['sha256']
    assert len(raw) == expected['bytes'] and raw.count(b'\n') == expected['lines']
    # Check pinned original inputs before importing a newly generated view.
    for relative, expected_hash in manifest['inputs'].items():
        assert sha(regular(relative).read_bytes()) == expected_hash, relative
    return raw.decode(), manifest, {'proposal': name,
        'manifest_sha256': sha(manifest_raw), 'source': module,
        'source_sha256': sha(raw)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('The parent must schedule --run explicitly')
    started = time.monotonic()
    cycle, cycle_manifest, cycle_evidence = proposal('C898FusedContexts',
        'Compact/Cases/C898/CachedPairs/Contexts00.lean')
    terminal, _, terminal_evidence = proposal('C898TerminalContexts',
        'Compact/Cases/C898/PairStep14CachedContexts.lean')
    helper = 'Compact/Cases/C898/FusedContextSyntax.lean'
    assert sha(regular(helper).read_bytes()) == cycle_manifest['output_files'][helper]['sha256']
    first = re.findall(r'(?ms)^checked_c898_fan route0 commonRaw0 :=\n.*?(?=\n\nchecked_c898_fan)', cycle)
    second = re.findall(r'(?ms)^checked_c898_fan cachedPose0 TerminalCommon\.terminalRawContext0 :=\n.*?(?=\n\nchecked_c898_fan)', terminal)
    assert len(first) == len(second) == 1
    source = '''import Compact.Cases.C898.FusedContextSyntax
import Compact.Cases.C898.CachedPairs.CyclicDirections

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

/-! Two exact original contexts test both supported certificate encodings.
This module changes no production theorem or context binding. -/
namespace N12Compact.C898Cached.FusionPilot
open C898Shared CachedSupportFan AllPairs
noncomputable section

''' + first[0] + '\n\n' + second[0] + '''

theorem cycle_original_pose : route0.pose = 1191 := rfl
theorem terminal_original_pose : cachedPose0.pose = 3301 := rfl

#print axioms route0_raw_checked
#print axioms commonRaw0_exact
#print axioms cachedPose0_raw_checked
#print axioms TerminalCommon.terminalRawContext0_exact
end
end N12Compact.C898Cached.FusionPilot
'''
    raw = source.encode()
    assert len(raw) < 16 * 1024
    target = regular(TARGET)
    receipt = regular(RECEIPT)
    temporary = target.with_suffix('.lean.fusion-pilot-tmp')
    receipt_temporary = receipt.with_suffix('.json.fusion-pilot-tmp')
    assert not temporary.exists() and not receipt_temporary.exists()
    if target.exists():
        assert target.read_bytes() == raw, 'Refusing a differing existing pilot'
        assert receipt.exists(), 'Existing pilot has no activation receipt'
        old = json.loads(receipt.read_text())
        if old['output']['sha256'] != sha(raw):
            repair = json.loads(regular('evidence/c898-fused-pilot-section-repair.json').read_text())
            assert repair['source'] == TARGET
            assert repair['old_sha256'] == old['output']['sha256']
            assert repair['new_sha256'] == sha(raw)
        print(json.dumps({'already_present': TARGET, 'bytes': len(raw)}))
        return
    assert not receipt.exists(), 'Refusing existing unrelated receipt'
    record = {'scope': 'Two original contexts only; new isolated source; ordinary Lean replay pending.',
        'lean_checked': False, 'production_sources_changed': False,
        'inputs': [cycle_evidence, terminal_evidence],
        'helper_sha256': sha(regular(helper).read_bytes()),
        'output': {'path': TARGET, 'sha256': sha(raw), 'bytes': len(raw),
            'lines': raw.count(b'\n')}}
    written = []
    def interrupted(signum, frame):
        raise RuntimeError('Pilot activation interrupted: ' + str(signum))
    previous = {s: signal.signal(s, interrupted) for s in (signal.SIGTERM, signal.SIGINT)}
    try:
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary.write_bytes(raw)
        written.append((target, sha(raw)))
        os.replace(temporary, target)
        record['seconds'] = time.monotonic() - started
        receipt_raw = (json.dumps(record, indent=2) + '\n').encode()
        receipt_temporary.write_bytes(receipt_raw)
        written.append((receipt, sha(receipt_raw)))
        os.replace(receipt_temporary, receipt)
    except BaseException:
        for signum in previous:
            signal.signal(signum, signal.SIG_IGN)
        for path, expected in reversed(written):
            if path.exists() and sha(path.read_bytes()) == expected:
                path.unlink()
        raise
    finally:
        temporary.unlink(missing_ok=True)
        receipt_temporary.unlink(missing_ok=True)
        for signum, handler in previous.items():
            signal.signal(signum, handler)
    print(json.dumps({'module': TARGET[:-5].replace('/', '.'),
        'bytes': len(raw), 'lines': raw.count(b'\n'), 'seconds': record['seconds']}))


if __name__ == '__main__':
    main()
