#!/usr/bin/env python3
"""Render proposal-only sparse dictionaries from the audited active closure.

No active Lean file is changed. Original IDs and all selected values remain
exact; missing IDs intentionally use explicit harmless defaults and cannot
be referenced by the audited production closure. Root runs serially with
--run under128MiB/60sec/8MiB. No Lean, subprocess, archive or network access.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import signal
import time

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / 'Compact/Cases/C898'
OUT = ROOT / 'evidence/proposals/C898Sparse'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    if not parser.parse_args().run:
        parser.error('Prepared only; root must supply --run in the bounded serial slot.')
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('60sec deadline')))
    signal.alarm(60)
    started = time.monotonic()
    manifest_path = ROOT / 'evidence/c898-active-dictionary.json'
    manifest_bytes = manifest_path.read_bytes()
    assert len(manifest_bytes) < 8 * 1024**2
    manifest = json.loads(manifest_bytes)
    exact = manifest['exact_values']
    assert sha(json.dumps(exact, separators=(',', ':')).encode()) == manifest['exact_values_sha256']
    originals = {name: (CASE / name).read_bytes() for name in ['SharedRows.lean', 'SharedPoses.lean']}
    for name, original in originals.items():
        path = str((CASE / name).relative_to(ROOT))
        assert sha(original) == manifest['input_hashes'][path]['sha256'], (name, 'changed after audit')
    row_ids = [r['original_id'] for r in exact['rows']]
    pose_ids = [p['original_id'] for p in exact['poses']]
    assert row_ids == sorted(set(row_ids)) == manifest['selected_row_ids']
    assert pose_ids == sorted(set(pose_ids)) == manifest['selected_pose_ids']
    row_set = set(row_ids)
    assert all(r in row_set for p in exact['poses'] for r in p['rows'])

    row_source = originals['SharedRows.lean'].decode()
    row_match = re.search(r'noncomputable def rowData : Array \(Array \(Row × Nat\)\) := row_text% "\n.*?\n"',
                          row_source, re.S)
    assert row_match
    row_lines = [f'{r["original_id"]}:' + ','.join(map(str, r['integers'])) + ',' +
                 str(r['strict']).lower() + ',' + str(r['denominator'] - 1)
                 for r in exact['rows']]
    replacement = 'noncomputable def rowData : SparseLiteral.Tree (Row × Nat) := sparse_rows% "\n' + \
                  '\n'.join(row_lines) + '\n"'
    row_source = row_source[:row_match.start()] + replacement + row_source[row_match.end():]
    assert 'import Compact.Core.RowSyntax' in row_source
    row_source = row_source.replace('import Compact.Core.RowSyntax', 'import Compact.Core.SparseLiteral')
    assert row_source.count('RowSyntax.lookup rowData i.val') == 2
    row_source = row_source.replace('RowSyntax.lookup rowData i.val',
                                    'SparseLiteral.lookup (⟨0,0,0,false⟩,0) rowData i.val')

    pose_source = originals['SharedPoses.lean'].decode()
    pose_match = re.search(r'noncomputable def poseData : Array \(Array \(Fin 64 × List \(Fin rowCount\)\)\) := '
                           r'pose_text% 64 26026 "\n.*?\n"', pose_source, re.S)
    assert pose_match
    pose_lines = [f'{p["original_id"]}:{p["angle"]};' + ','.join(map(str, p['rows']))
                  for p in exact['poses']]
    replacement = 'noncomputable def poseData : SparseLiteral.Tree (Fin 64 × List (Fin rowCount)) := ' + \
                  'sparse_poses% 64 26026 "\n' + '\n'.join(pose_lines) + '\n"'
    pose_source = pose_source[:pose_match.start()] + replacement + pose_source[pose_match.end():]
    assert pose_source.count('PoseSyntax.lookup poseData (0, []) i.val') == 2
    pose_source = pose_source.replace('PoseSyntax.lookup poseData (0, []) i.val',
                                      'SparseLiteral.lookup (0, []) poseData i.val')
    pose_set = set(pose_ids)
    removed_aliases = []
    def preserve_alias(match):
        if int(match[2]) in pose_set:
            return match[0]
        removed_aliases.append({'name': match[1], 'original_id': int(match[2])})
        return ''
    pose_source = re.sub(r'^noncomputable def (\w+) : PoseLeaf := poses (\d+)\n',
                         preserve_alias, pose_source, flags=re.M)
    assert len(removed_aliases) == manifest['removed_pose_count']
    outputs = {'SharedRows.lean': row_source, 'SharedPoses.lean': pose_source}
    assert sum(len(s.encode()) for s in outputs.values()) < 8 * 1024**2
    OUT.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = OUT / name
        temporary = path.with_suffix('.lean.tmp')
        try:
            temporary.write_text(source)
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)
    client_changes = []
    for directory in [CASE / 'RecipeInitial']:
        for path in sorted(directory.glob('*.lean')):
            source = path.read_text()
            count = source.count('row_subset% N12Compact.C898Shared.rowData')
            if count:
                client_changes.append({'path': str(path.relative_to(ROOT)), 'occurrences': count,
                                       'old_sha256': sha(source.encode()),
                                       'required_change': 'row_subset% becomes sparse_rows_subset%; arguments unchanged'})
    report = {
        'scope': 'Proposal only. No active Lean changes and no sparse dictionary replay claimed.',
        'manifest_sha256': sha(manifest_bytes),
        'preserved_public_row_count': manifest['original_row_count'],
        'preserved_public_pose_count': manifest['original_pose_count'],
        'retained_rows': len(row_ids), 'retained_poses': len(pose_ids),
        'removed_aliases': removed_aliases, 'client_activation_changes': client_changes,
        'outputs': {str((OUT/name).relative_to(ROOT)): {'bytes': len(source.encode()),
                    'lines': source.count('\n'), 'sha256': sha(source.encode()),
                    'old_bytes': len(originals[name]), 'old_lines': originals[name].count(b'\n')}
                    for name, source in outputs.items()},
        'retained_values': 'Exact original ID, angle, row order, integer coefficients, strict bits and denominators.',
        'missing_id_behavior': 'Missing row: zero nonstrict form with denominator1; missing pose: angle0 with no constraints. '
                               'Only inactive IDs change, as separately audited; final original entry/exit checks still must replay.',
        'activation_gate': 'Accept SparseLiteral; review exact selector/proposal hashes; switch the two data files '
                           'and every listed pool client atomically; regenerate/replay actual production closure.',
        'seconds': time.monotonic() - started,
    }
    report_path = ROOT / 'evidence/c898-sparse-dictionary-proposal.json'
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['retained_rows','retained_poses','outputs','seconds']}, indent=2))


if __name__ == '__main__':
    main()
