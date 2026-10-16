#!/usr/bin/env python3
"""Reencode existing six-case fans by original pose/block/cycle references.

Parent-run only. No geometry search, Lean invocation or active source mutation.
Every source JSON is authenticated against the completed original fan audit;
each recipe must reproduce its exact input list, angle and integer reference.
Existing context IDs, chunk boundaries, cycles, directions and numeric Check
statements are preserved. The one empty context remains in its original path.
The proposal uses 256 MiB RSS, 115 seconds and at most 16 MiB output.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from math import lcm
from pathlib import Path
import re
import resource
import shutil
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FAMILY = 'C701_713_717_973_978_979'
PREFIX = Path('Compact/HistoricalFans') / FAMILY
OLD = ROOT / 'evidence/historical-fans-701-713-717-973-978-979-cycles'
DEST = ROOT / 'evidence/proposals/HistoricalPoseFanRecipes'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    need(args.run, 'explicit parent-run --run required')
    stage = DEST.with_name(DEST.name + '.staging')
    need(not DEST.exists() and not stage.exists(), 'refusing existing proposal')
    started = time.monotonic()
    written = 0
    sources = {}
    files = []

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        need(rss < 256 * 1024**2, '256 MiB RSS guard')
        need(time.monotonic() - started < 115, '115 second guard')

    def stop(*_):
        raise InterruptedError('termination requested')

    def read(path, expected=None):
        raw = path.read_bytes()
        sha = digest(raw)
        if expected is not None:
            need(sha == expected, f'authenticated input changed: {path.name}')
        sources[str(path.relative_to(ROOT))] = sha
        return raw

    def write(relative, text):
        nonlocal written
        raw = text.encode()
        written += len(raw)
        need(written <= 16 * 1024**2, '16 MiB output guard')
        path = stage / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        info = {'path': str(relative), 'lines': raw.count(b'\n'),
                'bytes': len(raw), 'sha256': digest(raw)}
        files.append(info)
        guard()
        return info

    signal.signal(signal.SIGALRM, guard)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    stage.mkdir(parents=True)
    try:
        old_manifest = json.loads(read(OLD / 'manifest.json'))
        need(old_manifest['all_selected_pairs_pass'] and
             old_manifest['failure_count'] == 0 and
             old_manifest['boundary_cycles'], 'original fan audit incomplete')
        old_files = {item['path']: item for item in old_manifest['files']}
        fans = json.loads(read(OLD / 'fans.json', old_files['fans.json']['sha256']))

        def original(name):
            path = f'evidence/historical-compact-data/{name}.json'
            return json.loads(read(ROOT / path, old_manifest['sources'][path]))

        poses, blocks = original('poses'), original('blocks')
        contexts, refs = original('contexts'), original('references')
        need(len(refs) == 192, 'reference grid changed')
        for values in (poses, blocks, contexts):
            need(all(item['index'] == i for i, item in enumerate(values)),
                 'dictionary indices changed')
        counts = read(ROOT / 'Compact/HistoricalData/Counts.lean').decode()
        row_match = re.search(r'(?:def|abbrev) rowCount\s*:\s*Nat\s*:=\s*(\d+)', counts)
        need(row_match is not None, 'missing original row count')
        row_count = int(row_match.group(1))
        need(all(0 <= row < row_count for block in blocks for row in block['rows']),
             'block row outside actual dictionary')

        # The Lean helper derives these five integers from the original
        # rational AngleEnclosure, not from an independent reference table.
        declarations = {}
        for grid in (64, 128):
            source = read(ROOT / f'source/S12/AngleData{grid}.lean').decode()
            for name, body in re.findall(
                    r'def (angle(?:64|128)_\d+) : AngleEnclosure := ⟨([^⟩]+)⟩', source):
                values = [Fraction(s.strip().strip('()')) for s in body.split(',')]
                need(len(values) == 7, f'angle shape: {name}')
                c, s, inner = values[2], values[3], values[5]
                d = lcm(c.denominator, s.denominator)
                declarations[name] = [c.numerator * (d // c.denominator),
                    s.numerator * (d // s.denominator), d,
                    inner.numerator, inner.denominator]
        for i, reference in enumerate(refs):
            expected_name = f'angle64_{i}' if i < 64 else f'angle128_{i-64}'
            need(reference['name'] == expected_name, 'original angle order changed')
            fields = [reference[key] for key in
                ('c', 's', 'denominator', 'sideNumerator', 'sideDenominator')]
            need(declarations[expected_name] == fields,
                 f'derived reference differs: {expected_name}')

        bindings = {}

        def matches(cid, pose, block):
            p, c = poses[pose], contexts[cid]
            inputs = ([] if block is None else blocks[block]['rows']) + p['rows']
            return p['angle'] == c['angle'] and inputs == c['inputs']

        # Prefer actual source/block assignments recorded in the old plans.
        # Equivalent repeated assignments may share a context, but all are
        # compared with the exact ordered original input list.
        for plan in fans['plans']:
            cid, pose, block = plan['source'], plan['source_pose'], plan['block']
            need(matches(cid, pose, block), f'original source mismatch: {cid}')
            bindings.setdefault(cid, (pose, block))
        pose_by_content = {}
        for pose in poses:
            pose_by_content.setdefault((pose['angle'], tuple(pose['rows'])), pose['index'])
        for plan in fans['plans']:
            for cid in plan['neighbors']:
                c = contexts[cid]
                pose = pose_by_content.get((c['angle'], tuple(c['inputs'])))
                need(pose is not None and matches(cid, pose, None),
                     f'neighbor is not an actual complete pose: {cid}')
                bindings.setdefault(cid, (pose, None))
        del pose_by_content

        records = {record['context']: record for record in fans['context_records']}
        need(len(records) == len(fans['context_records']), 'duplicate fan context')
        empty = {int(cid) for cid in fans['empty_contexts']}
        active = sorted(cid for cid in records if cid not in empty)
        need(len(active) == 12932 and len(empty) == 1, 'original scope changed')
        need(all(cid in bindings for cid in active), 'unbound original fan context')
        for cid in active:
            recipe = records[cid]
            need(recipe['boundary_cycle'] and
                 all(row in contexts[cid]['inputs'] for row in recipe['boundary_cycle']),
                 f'absent/foreign cyclic boundary: {cid}')
            need(matches(cid, *bindings[cid]), f'recipe input mismatch: {cid}')

        # One shared original block dictionary replaces repeated source-prefix
        # lists. Reuse the accepted balanced sparse literal parser with a
        # dummy angle; no geometry or unchecked proof is added by that parser.
        block_lines = ['import Compact.Core.SparseLiteral',
            'import Compact.HistoricalData.Counts', '',
            'namespace N12Compact.HistoricalData', 'set_option Elab.async false',
            'noncomputable def fanBlockData : SparseLiteral.Tree (Fin 1 × List (Fin rowCount)) :=',
            f'  sparse_poses% 1 {row_count} "']
        block_lines += [f"{b['index']}:0;" + ','.join(map(str, b['rows'])) for b in blocks]
        block_lines += ['"', 'noncomputable def fanBlockRows (i : Nat) : List (Fin rowCount) :=',
            '  (SparseLiteral.lookup (0, []) fanBlockData i).2',
            'end N12Compact.HistoricalData', '']
        write(Path('lean/Compact/HistoricalData/SharedFanBlocks.lean'), '\n'.join(block_lines))

        bank_lines = [
            'import Compact.Bridge.HistoricalPoseFanRecipe',
            'import Compact.Cases.C713.SharedDictionary',
            'import Compact.HistoricalData.SharedFanBlocks',
            f'import Compact.HistoricalFans.{FAMILY}.Directions', '',
            f'namespace N12Compact.HistoricalFans.{FAMILY}',
            'open HistoricalData VertexFanTable', 'set_option Elab.async false',
            'noncomputable def poseFan (pose : Fin poseCount) (block : Option Nat)',
            '    (cycle : List (Fin rowCount)) : RawContext rowCount :=',
            '  HistoricalPoseFanRecipe.Recipe.raw ⟨pose, block, cycle⟩',
            '    C713Shared.dictionary fanBlockRows directions',
            f'end N12Compact.HistoricalFans.{FAMILY}', '']
        write(Path('lean') / PREFIX / 'RecipeBank.lean', '\n'.join(bank_lines))

        before_lines, before_bytes = 0, 0
        mapping = []
        for chunk in range((len(active) + 31) // 32):
            selected = active[chunk*32:(chunk+1)*32]
            relative = PREFIX / f'Contexts{chunk:03}.lean'
            expected = old_files['lean/' + str(relative)]['sha256']
            old_raw = read(ROOT / relative, expected)
            before_lines += old_raw.count(b'\n')
            before_bytes += len(old_raw)
            lines = [f'import Compact.HistoricalFans.{FAMILY}.RecipeBank', '',
                f'namespace N12Compact.HistoricalFans.{FAMILY}',
                'open N12Compact.HistoricalData N12Compact.VertexFanTable',
                'set_option Elab.async false',
                'set_option maxRecDepth 20000',
                f'def contexts{chunk:03} : Array (RawContext rowCount) := #[']
            for offset, cid in enumerate(selected):
                pose, block = bindings[cid]
                block_text = 'none' if block is None else f'(some {block})'
                cycle = records[cid]['boundary_cycle']
                lines.append(f'  materialize_boundary_fan% (poseFan {pose} {block_text} [' +
                    ','.join(map(str, cycle)) + ']),')
                mapping.append({'context': cid, 'chunk': chunk, 'offset': offset,
                    'pose': pose, 'block': block, 'angle': contexts[cid]['angle']})
            lines += [']', f'theorem contexts{chunk:03}_checked (i : Fin {len(selected)}) :',
                f"    (contexts{chunk:03}[i.val]'(by change i.val < {len(selected)}; exact i.isLt)).Check rows := by",
                '  revert i', '  decide +kernel',
                f'end N12Compact.HistoricalFans.{FAMILY}', '']
            write(Path('lean') / relative, '\n'.join(lines))

        # These shared interfaces are not regenerated or semantically changed.
        for name in ('Directions.lean', 'All.lean'):
            relative = PREFIX / name
            expected = old_files.get('lean/' + str(relative), {}).get('sha256')
            raw = read(ROOT / relative, expected)
            before_lines += raw.count(b'\n')
            before_bytes += len(raw)
            write(Path('lean') / relative, raw.decode())
        write(Path('bindings.json'), json.dumps(mapping, separators=(',', ':')) + '\n')
        lean_files = [f for f in files if f['path'].endswith('.lean')]
        helper = read(ROOT / 'Compact/Bridge/HistoricalPoseFanRecipe.lean')
        report = {
            'status': 'exact pose/block/cycle reencoding; Lean replay pending',
            'lean_checked': False, 'whole_cases_proved': False,
            'active_contexts': len(active), 'empty_contexts_unchanged': sorted(empty),
            'original_requested_pairs_unchanged': old_manifest['requested_pairs'],
            'same_materializer_with_exact_original_arguments': True,
            'boundary_cycles_and_direction_array_unchanged': True,
            'all_input_lists_angles_and_references_exact': True,
            'source_context_bindings_checked': len(fans['plans']),
            'reference_encodings_checked': len(refs),
            'shared_blocks': len(blocks), 'sources': sources, 'files': files,
            'before_fan_lines': before_lines, 'before_fan_bytes': before_bytes,
            'after_fan_and_block_lines': sum(f['lines'] for f in lean_files),
            'after_fan_and_block_bytes': sum(f['bytes'] for f in lean_files),
            'generic_helper_lines': helper.count(b'\n'),
            'total_new_scope_lines': sum(f['lines'] for f in lean_files) + helper.count(b'\n'),
            'limits': {'rss_mib': 256, 'seconds': 115, 'output_mib': 16},
            'elapsed_seconds': time.monotonic() - started,
            'remaining': ['ordinary Lean replay of the new helper and context tables',
                'all original unaccepted entrance, pair, relaxation and chord obligations']}
        # Do not include manifest.json in its own file list/hash.
        write(Path('manifest.json'), json.dumps(report, indent=2) + '\n')
        stage.rename(DEST)
        print(json.dumps({k: report[k] for k in ('status', 'active_contexts',
            'before_fan_lines', 'after_fan_and_block_lines', 'generic_helper_lines',
            'total_new_scope_lines', 'elapsed_seconds')}))
    except BaseException:
        if stage.exists():
            shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
