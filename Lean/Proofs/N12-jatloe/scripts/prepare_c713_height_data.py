#!/usr/bin/env python3
"""Prepare the 108 exact original C713 occupied-row transfers.

Parent-only --run: 256 MiB, 60 seconds, 8 MiB atomic proposal output.
No compiler, subprocess, network, or active-source mutation. Numerical tests
see materialized row lists; all cache equalities and the original-angle
radius checks remain independent ordinary Lean kernel obligations.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse, hashlib, json, re, resource, shutil, signal, sys, time

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'evidence/proposals/C713Height'
NS = 'N12Compact.C713HeightData'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(65536), b''):
            h.update(block)
    return h.hexdigest()


def rational(value):
    value = Q(value)
    return str(value.numerator) if value.denominator == 1 else f'({value.numerator}/{value.denominator})'


def header(imports):
    return '\n'.join('import ' + name for name in imports) + f'''

namespace {NS}
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''


def footer():
    return f'\nend {NS}\n'


def entry_source(index, record, radius):
    height = Q(record['height'])
    target = 'none' if record['target'] is None else 'some ' + str(record['target'])
    name = f'entry{index}'
    return f'''def {name} : Entry :=
  ⟨⟨{record['source']}, ⟨0,{height.denominator},{-height.numerator},false⟩, {target}⟩,
   ⟨{rational(radius[0])},{rational(radius[1])}⟩⟩

private def base{index} : List Row :=
  materialize_rows% ({name}.spec.base C713Shared.dictionary)
private def target{index} : List Row :=
  materialize_rows% ({name}.spec.targets C713Shared.dictionary)

private theorem base{index}_exact :
    base{index} = {name}.spec.base C713Shared.dictionary := by decide +kernel
private theorem target{index}_exact :
    target{index} = {name}.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric{index} :
    PlanarVertexSparse.UnorderedCheck base{index} [] target{index} := by decide +kernel

theorem {name}_checked : {name}.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base{index}_exact, ← target{index}_exact] using numeric{index}
  · change {name}.TargetCheck
    decide +kernel

'''


def all_source(count, modules):
    source = header(modules + ['Compact.Cases.C713.SharedDomains'])
    source += 'private def checkedRecords : Array {entry : Entry // entry.Check} := #[\n'
    source += ',\n'.join(f'  ⟨entry{i},entry{i}_checked⟩' for i in range(count)) + ']\n\n'
    source += f'''def record (i : Fin {count}) : Entry :=
  (checkedRecords[i.val]'(by change i.val < {count}; exact i.isLt)).val

theorem record_checked (i : Fin {count}) : (record i).Check :=
  (checkedRecords[i.val]'(by change i.val < {count}; exact i.isLt)).property

theorem source_ids :
    (List.finRange {count}).map (fun i => (record i).spec.source) =
      C713Shared.continuousScout713Domain7_0Ids := by rfl

theorem target_ids :
    (List.finRange {count}).flatMap (fun i => (record i).spec.target.toList) =
      C713Shared.continuousScout713Domain7_6Ids := by rfl

#print axioms record_checked
'''
    return source + footer()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('prepared only; parent serial slot and --run required')
    start = time.monotonic()
    stage = DEST.with_name(DEST.name + '.staging')
    need(not DEST.exists() and not stage.exists(), 'refusing existing proposal')

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(time.monotonic() - start < 55 and rss < 256 * 1024**2, '256 MiB/55-second resource limit')

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    stage.mkdir(parents=True)
    try:
        audit_path = ROOT / 'evidence/c713-height-slice-audit.json'
        data_path = ROOT / 'evidence/historical-compact-data/C713.json'
        radius_path = ROOT / 'vendor/S12/AngleChordRadiusData.lean'
        receipt_path = ROOT / 'evidence/inherited/evidence/C713/case-replay.json'
        audit = json.loads(audit_path.read_text())
        selected = audit['targets']['continuousScout713Domain7_6']
        need(audit['status'].startswith('complete exact finite audit') and
             selected['passed'] == 108 and not selected['failed'], 'incomplete exact height audit')
        data = json.loads(data_path.read_text())
        for path, expected in audit['sources'].items():
            need(sha(ROOT / path) == expected, 'audit source changed: ' + path)
        receipt = json.loads(receipt_path.read_text())['local_source_sha256']
        radius_hash = sha(radius_path)
        need(radius_hash == receipt['S12.AngleChordRadiusData'] == audit['radius_source_sha256'],
             'radius provenance mismatch')
        radii = {int(i): (Q(upper.strip('()')), Q(radius.strip('()')))
                 for i, upper, radius in re.findall(
                     r'def angleChordRadius128_(\d+) : AngleChordRadiusCertificate := '
                     r'⟨⟨angle128_\d+,angle128_\d+_checked⟩,([^,]+),([^⟩]+)⟩',
                     radius_path.read_text())}
        need(set(radii) == set(range(128)), 'incomplete original radius grid')
        records = selected['roots']
        need(len(records) == 108, 'wrong source count')
        need([r['source'] for r in records] == data['domains']['continuousScout713Domain7_0'],
             'original source domain mismatch')
        need([r['target'] for r in records if r['target'] is not None] ==
             data['domains']['continuousScout713Domain7_6'], 'original target domain mismatch')
        for record in records:
            need(Q(record['height']) == Q(87, 50) + radii[record['angle']][1],
                 'cut/radius mismatch')
        outputs = {}
        modules = []
        for batch, offset in enumerate(range(0, 108, 8)):
            module = f'Compact.Cases.C713.HeightData.Batch{batch:02}'
            modules.append(module)
            source = header(['Compact.Cases.C713.HeightCore', 'Compact.Core.RowMaterializeSyntax'])
            for index in range(offset, min(offset + 8, 108)):
                source += entry_source(index, records[index], radii[records[index]['angle']])
            outputs[module.replace('.', '/') + '.lean'] = source + footer()
        outputs['Compact/Cases/C713/HeightData/All.lean'] = all_source(108, modules)
        total = sum(len(source.encode()) for source in outputs.values())
        need(total < 8 * 1024**2, '8 MiB output limit')
        for name, source in outputs.items():
            path = stage / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        report = {
            'status': 'complete source proposal; Lean replay pending', 'case': 713,
            'source_poses': 108, 'target_poses': 102,
            'empty_target_records': sum(r['target'] is None for r in records),
            'closed_empty_sources': selected['empty'],
            'height': '87/50 + original certified angle radius',
            'numerical_claim': 'ordinary kernel vertex checks required for every source',
            'geometric_claim': 'C713OccupiedRow.above_radius, separately checked in original model',
            'inputs': {str(p.relative_to(ROOT)): sha(p) for p in
                       [audit_path, data_path, radius_path, receipt_path]},
            'lean_modules': len(outputs), 'lean_lines': sum(s.count('\n') for s in outputs.values()),
            'lean_bytes': total,
            'outputs': [{'path': name, 'sha256': hashlib.sha256(source.encode()).hexdigest(),
                         'lines': source.count('\n'), 'bytes': len(source.encode())}
                        for name, source in outputs.items()],
            'elapsed_seconds': time.monotonic() - start}
        (stage / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        stage.rename(DEST)
        print(json.dumps({key: report[key] for key in ['status', 'source_poses', 'target_poses',
            'empty_target_records', 'lean_modules', 'lean_lines', 'lean_bytes', 'elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
