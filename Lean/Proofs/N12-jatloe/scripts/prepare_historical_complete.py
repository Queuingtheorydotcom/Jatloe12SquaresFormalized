#!/usr/bin/env python3
"""Assemble the six exact original case conclusions from concrete adapters.

Coordinator-only source producer: no search, Lean execution, or activation.
The seven output modules require every entrance, direct-pruning, overlap,
and chord module to compile; an incomplete dependency cannot become a proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import resource
import shutil
import signal
import sys
import time

from prepare_historical_direct_pruning import CASES, original_fields

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
DEST = ROOT / 'evidence/proposals/HistoricalComplete'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def source(case, original, pair_steps):
    fields = original_fields(original)
    initials = [int(name[7:]) for name, _ in fields if name.startswith('initial')]
    stages = {int(name[4:]) for name, _ in fields if name.startswith('step')}
    need(len(initials) + len(stages) == len(fields), 'unknown original field')
    need(set(pair_steps) <= stages, 'pair stage is absent from original graph')
    chords = sorted(stages - set(pair_steps))
    need((case != 713) or chords == [5], 'unexpected C713 height replacement')
    imports = [f'Compact.Cases.C{case}.DirectPruning.All']
    imports += [f'Compact.HistoricalCommon.C{case}.Step{step:02}' for step in pair_steps]
    if case == 713:
        imports += ['Compact.Assembly.RowIdentity']
    else:
        imports += [f'Compact.Cases.C{case}.RecipeInitial.Entry']
        imports += [f'Compact.Preservation.Chords.C{case}Step{step:02}' for step in chords]
    namespace = f'N12Compact.Preservation.Complete.C{case}'
    text = '\n'.join('import ' + item for item in imports) + f'''

/-! Exact original case composition. Acceptance requires all imported
numerical and original-packing adapters; this source contains no new premise. -/
namespace {namespace}
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem overlaps : C{case}DirectPruning.BlockOverlaps :=
  {{
'''
    for step in pair_steps:
        text += f'    step{step} := HistoricalCommon.C{case}.Step{step:02}.block_overlaps\n'
    text += '  }\n\n'
    if case == 713:
        row = re.search(r'\(RowIdentity\.rowAt (\d+)\)\.originalId = 713', original)
        need(row is not None, 'authenticated original row identity absent')
        index = int(row[1])
        text += f'''private theorem row_checked :
    (RowIdentity.rowAt {index}).originalId = 713 ∧
    (RowIdentity.rowAt {index}).groups = case713Family := by decide +kernel

theorem excludes_case : ExcludesCase 713 := by
  intro r hr hid p hf
  apply C713DirectPruning.family_impossible_of_block_overlaps overlaps p
  exact hf.trans (RowIdentity.family_at {index} 713 case713Family row_checked r hr hid)
'''
    else:
        text += f'private theorem remaining : C{case}DirectPruning.Remaining :=\n  {{\n'
        for name, _ in fields:
            if name.startswith('initial'):
                text += f'    {name} := C{case}Entry.owner{name[7:]}_cover\n'
            elif int(name[4:]) in chords:
                text += f'    {name} := Preservation.Chords.C{case}Step{int(name[4:]):02}.packing_sound\n'
        text += f'''  }}

theorem excludes_case : ExcludesCase {case} :=
  C{case}DirectPruning.excludes_case_of_remaining overlaps remaining
'''
    text += f'\n#print axioms excludes_case\n\nend\nend {namespace}\n'
    return text, {'case': case, 'initial_owners': initials,
                  'pair_steps': pair_steps, 'original_chord_steps': chords,
                  'height_replacement': case == 713}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    need(args.run, 'coordinator serial slot and --run required')
    stage = DEST.with_name(DEST.name + '.staging')
    need(not DEST.exists() and not stage.exists(), 'refusing existing proposal')
    started = time.monotonic()
    hashes = {}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        rss *= 1 if sys.platform == 'darwin' else 1024
        need(rss < 128 * 1024**2 and time.monotonic() - started < 25,
             '128 MiB / 25 second source-only limit')

    def read(path, expected=None):
        guard()
        need(path.stat().st_size < 8 * 1024**2, 'oversized metadata input')
        raw = path.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        need(expected is None or digest == expected, 'source hash mismatch: ' + str(path))
        hashes[str(path.relative_to(ROOT))] = digest
        return raw.decode()

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    stage.mkdir(parents=True)
    try:
        manifest = json.loads(read(BASE / 'manifest.json'))
        expected = {item['path']: item['sha256'] for item in manifest['output_files']}
        outputs, cases = {}, []
        for case in CASES:
            data = json.loads(read(BASE / f'C{case}.json', expected[f'C{case}.json']))
            original = read(ROOT / f'Compact/Preservation/C{case}.lean')
            text, metadata = source(case, original, sorted(map(int, data['pair_steps'])))
            outputs[f'Compact/Preservation/Complete/C{case}.lean'] = text
            cases.append(metadata)
        need(sum(len(case['pair_steps']) for case in cases) == 113,
             'incomplete original pair-stage partition')
        need(sum(len(case['original_chord_steps']) for case in cases) == 21,
             'incomplete original chord-stage partition')
        outputs['Compact/Preservation/Complete/All.lean'] = '\n'.join(
            f'import Compact.Preservation.Complete.C{case}' for case in CASES) + '''

/-! Six original case exclusions assembled from concrete checked adapters.
There are no outstanding contract parameters in these theorem statements.
This aggregate is accepted only after its entire dependency closure passes. -/
'''
        records = []
        for relative, text in outputs.items():
            raw = text.encode()
            path = stage / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            records.append({'path': relative, 'sha256': hashlib.sha256(raw).hexdigest(),
                            'bytes': len(raw), 'lines': text.count('\n')})
        report = {'status': 'source assembly only; all imported adapters require Lean acceptance',
                  'lean_checked': False, 'cases': cases, 'input_sha256': hashes,
                  'output_files': records, 'lean_modules': len(records),
                  'lean_lines': sum(record['lines'] for record in records),
                  'lean_bytes': sum(record['bytes'] for record in records),
                  'elapsed_seconds': time.monotonic() - started}
        need(report['lean_bytes'] < 256 * 1024, '256 KiB source output cap')
        (stage / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        stage.rename(DEST)
        print(json.dumps({key: report[key] for key in
              ['status', 'lean_modules', 'lean_lines', 'lean_bytes', 'elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
