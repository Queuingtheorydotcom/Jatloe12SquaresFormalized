#!/usr/bin/env python3
"""Select the exact dictionary closure of the unfused compact C898 proof.

Preparation only: this writes an evidence manifest, never active Lean files.
Original IDs, row values, pose angles and row order are preserved. The root
agent must run this serially with --run. No Lean, search, or subprocesses.
The report is an encoder audit, not proof acceptance or a compiled-size claim.
"""
from collections import Counter, defaultdict
from pathlib import Path
import argparse
import hashlib
import json
import re
import resource
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / 'Compact/Cases/C898'
OUT = ROOT / 'evidence/c898-active-dictionary.json'
MIB = 1024 ** 2


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('Prepared only; --run requires the parent serial slot.')
    started = time.monotonic()
    inputs, total_read = {}, 0

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic() - started > 120 or rss > 256 * MIB:
            raise RuntimeError('Active-ID selector exceeded 120 seconds or 256 MiB RSS')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .1, .1)

    def read(path):
        nonlocal total_read
        data = path.read_bytes()
        total_read += len(data)
        require(total_read <= 48 * MIB, 'Input reads exceeded 48 MiB')
        inputs[str(path.relative_to(ROOT))] = {
            'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
        return data.decode()

    def load(name):
        return json.loads(read(ROOT / 'evidence' / name))

    manifest = load('c898-shared-pose-map.json')
    domains = load('c898-domain-map.json')['domains']
    plans = load('c898-pair-pruning-plan-map.json')['plans']
    all_links = load('c898-relaxation-two-index-witnesses.json')
    chord = load('c898-chord-window-supports.json')
    rows, poses, blocks = manifest['rows'], manifest['poses'], manifest['blocks']
    require(len(rows) == manifest['row_count'] == 26026, 'Unexpected row count')
    require(len(poses) == manifest['pose_count'] == 3317, 'Unexpected pose count')
    require([p['index'] for p in poses] == list(range(len(poses))), 'Pose IDs not dense original order')
    require([b['index'] for b in blocks] == list(range(500)), 'Unexpected block IDs')
    require(len(domains) == 26 and len(plans) == 601, 'Unexpected domain/plan count')
    require({p['step'] for p in plans} == set(range(15)) - {9, 10}, 'Missing pair step')
    links = [w for w in all_links if not w['name'].startswith('incoming898ToScout898Link')]
    require(len(all_links) == 2048 and len(links) == 927, 'Unexpected retained relaxation count')
    require(len(chord['plans']) == 105, 'Unexpected chord plan count')

    pose_reasons, row_reasons = defaultdict(set), defaultdict(set)

    def add_pose(index, reason):
        require(type(index) is int and 0 <= index < len(poses), f'Invalid pose ID: {index}')
        pose_reasons[index].add(reason)

    def add_row(index, reason):
        require(type(index) is int and 0 <= index < len(rows), f'Invalid row ID: {index}')
        row_reasons[index].add(reason)

    initial = [p for p in poses if re.fullmatch(r'continuousScout898Initial\d+_\d+', p['name'])]
    require(len(initial) == 630, 'Expected exactly 630 direct output poses')
    for name, ids in domains.items():
        for index in ids:
            add_pose(index, 'actual_domains')
    owners = {int(re.fullmatch(r'continuousScout898Initial(\d+)_\d+', p['name'])[1]) for p in initial}
    for owner in owners:
        owner_poses = sorted((p for p in initial if p['name'].startswith(f'continuousScout898Initial{owner}_')),
                             key=lambda p: p['angle'])
        require([p['index'] for p in owner_poses] == domains[f'continuousScout898Domain{owner}_0'],
                f'Direct output differs from original initial domain {owner}')
        for pose in owner_poses:
            add_pose(pose['index'], 'direct_initial_outputs')

    used_blocks = []
    for plan in plans:
        add_pose(plan['source'], 'pair_sources')
        for index in domains[plan['neighbors_name']]:
            add_pose(index, 'complete_pair_neighbor_domains')
        for index in plan['pieces']:
            add_pose(index, 'pair_pieces')
        if plan['block'] is not None:
            used_blocks.append(plan['block'])
            for index in blocks[plan['block']]['rows']:
                add_row(index, 'pair_blocks')
    require(sorted(used_blocks) == list(range(500)), 'Every original pair block must occur exactly once')

    # Preserve only the complements actually queried by complete pair plans.
    complement_text = read(CASE / 'PairComplements.lean')
    complement_body = complement_text.split(':= #[', 1)[1].split(']', 1)[0]
    require(re.fullmatch(r'[\d,\s]*', complement_body) is not None, 'Unknown complement literal schema')
    complements = list(map(int, re.findall(r'\d+', complement_body)))
    require(len(complements) == len(rows), 'Complement dictionary was already changed; re-audit explicitly')
    used_keys = sorted({i for block in blocks for i in block['rows']})
    require(len(used_keys) == 725, 'Unexpected pair-complement key count')
    for index in used_keys:
        other = complements[index]
        add_row(other, 'used_pair_complements')
        a, b = rows[index], rows[other]
        require(b['integers'] == [-v for v in a['integers']] and
                b['strict'] is not a['strict'] and b['denominator'] == a['denominator'],
                f'Complement not exact at row {index}')

    for link in links:
        source, target = poses[link['source']], poses[link['target']]
        add_pose(source['index'], 'retained_relaxation_sources')
        add_pose(target['index'], 'retained_relaxation_targets')
        require([p[0] for p in link['proofs']] == target['rows'], f'Target order differs: {link["name"]}')
        for proof in link['proofs']:
            add_row(proof[0], 'retained_relaxation_targets')
            if len(proof) == 2 and proof[1] == 'alias':
                require(proof[0] in source['rows'], f'Alias missing in source: {link["name"]}')
            else:
                require(len(proof) == 3 and all(i in source['rows'] for i in proof[1:]),
                        f'Support missing in source: {link["name"]}')
                for index in proof[1:]:
                    add_row(index, 'retained_relaxation_supports')

    for neighbor in chord['neighbors']:
        add_pose(neighbor['pose'], 'chord_neighbors')
        require(neighbor['angle'] == poses[neighbor['pose']]['angle'], 'Chord angle changed')
        for support in neighbor['supports']:
            require(all(i in poses[neighbor['pose']]['rows'] for i in support['rows']), 'Chord support not in pose')
            for index in support['rows']:
                add_row(index, 'chord_neighbor_supports')
    for plan in chord['plans']:
        add_pose(plan['source'], 'chord_sources')
        require(len(plan['branches']) == 2, 'Chord branch coverage incomplete')
        for branch in plan['branches']:
            if 'piece' in branch:
                add_pose(branch['piece'], 'chord_pieces')
            else:
                require(len(branch['excluded_by']) == 2 and
                        all(i in poses[plan['source']]['rows'] for i in branch['excluded_by']),
                        'Chord closing support missing from source')
                for index in branch['excluded_by']:
                    add_row(index, 'chord_close_supports')

    for index in pose_reasons:
        for row in poses[index]['rows']:
            add_row(row, 'selected_pose_rows')
    raw_ids = {p['index'] for p in poses if p['name'].startswith('leaf898_')}
    require(len(raw_ids) == 1121 and not raw_ids.intersection(pose_reasons), 'An obsolete raw pose remains live')

    # The current active literal dictionaries must match the source metadata,
    # not merely the translator's historical recorded output hashes.
    row_source = read(CASE / 'SharedRows.lean')
    body = row_source.split('row_text% "', 1)[1].split('"', 1)[0]
    parsed_rows = []
    for line in body.strip().splitlines():
        x, y, c, strict, pred = line.strip().split(',')
        require(strict in ('true', 'false'), 'Invalid row strictness')
        parsed_rows.append({'integers': list(map(int, (x, y, c))),
                            'strict': strict == 'true', 'denominator': int(pred) + 1})
    require(parsed_rows == rows, 'Active row table differs from authenticated map')
    del parsed_rows, body
    pose_source = read(CASE / 'SharedPoses.lean')
    body = re.split(r'pose_text%\s+64\s+26026\s+"', pose_source, maxsplit=1)[1].split('"', 1)[0]
    parsed_poses = []
    for line in body.strip().splitlines():
        angle, ids = line.strip().split(';')
        parsed_poses.append((int(angle), list(map(int, ids.split(','))) if ids else []))
    require(parsed_poses == [(p['angle'], p['rows']) for p in poses], 'Active pose table differs from map')
    del parsed_poses, body

    # Independent checks of present cached contexts and target pools. These
    # cannot add unexpected IDs: any mismatch stops the producer.
    cache_counts = Counter()
    for path in sorted(CASE.glob('PairStep[0-9][0-9]CachedData.lean')):
        source = read(path)
        context = None
        for line in source.splitlines():
            m = re.fullmatch(r'(?:noncomputable )?def cachedInputs(\d+) : List \(Fin rowCount\) := (.*)', line)
            if m:
                shape = re.fullmatch(r'(?:blockRows (\d+) \+\+ )?poseRows (\d+)', m[2])
                require(shape is not None, f'Unknown cached input schema in {path.name}')
                pose_id = int(shape[2])
                require(pose_id in pose_reasons, f'Unselected cached pose {pose_id}')
                context = poses[pose_id]['rows'][:]
                if shape[1] is not None:
                    context = blocks[int(shape[1])]['rows'] + context
                require(all(i in row_reasons for i in context), 'Unselected cached input row')
                cache_counts['contexts'] += 1
            m = re.match(r'\s*⟨\d+, (\d+), (\d+), ⟨⟨', line)
            if m:
                require(context is not None and all(int(i) in context for i in m.groups()),
                        f'Cached basis row missing from context in {path.name}')
                cache_counts['basis_entries'] += 1
        cache_counts['source_files'] += 1
    for path in sorted((CASE / 'RecipeInitial').glob('Data[0-9][0-9].lean')):
        source = read(path)
        for body in re.findall(r'row_subset%\s+N12Compact\.C898Shared\.rowData\s+"([^"]*)"', source):
            ids = [int(s.strip()) for s in body.split(',') if s.strip()]
            require(all(i in row_reasons for i in ids), f'Unselected direct target pool row in {path.name}')
            cache_counts['target_pools'] += 1
            cache_counts['target_pool_memberships'] += len(ids)

    selected_rows, selected_poses = sorted(row_reasons), sorted(pose_reasons)
    row_literal = lambda r: ','.join(map(str, r['integers'])) + ',' + str(r['strict']).lower() + ',' + str(r['denominator'] - 1) + '\n'
    pose_literal = lambda p: str(p['angle']) + ';' + ','.join(map(str, p['rows'])) + '\n'
    old_row_bytes = sum(len(row_literal(r).encode()) for r in rows)
    new_row_bytes = sum(len(row_literal(rows[i]).encode()) for i in selected_rows)
    old_pose_bytes = sum(len(pose_literal(p).encode()) for p in poses)
    new_pose_bytes = sum(len(pose_literal(poses[i]).encode()) for i in selected_poses)
    selected = {
        'rows': [{'original_id': i, 'slot': slot, **rows[i]} for slot, i in enumerate(selected_rows)],
        'poses': [{'original_id': i, 'slot': slot, **poses[i]} for slot, i in enumerate(selected_poses)]}
    selected_bytes = json.dumps(selected, separators=(',', ':')).encode()
    report = {
        'scope': 'Exact pre-fusion C898 dictionary closure. Encoder audit only; sparse replacement and Lean replay pending.',
        'original_row_count': len(rows), 'original_pose_count': len(poses),
        'selected_row_count': len(selected_rows), 'selected_pose_count': len(selected_poses),
        'removed_row_count': len(rows) - len(selected_rows), 'removed_pose_count': len(poses) - len(selected_poses),
        'removed_raw_pose_count': len(raw_ids),
        'selected_row_ids': selected_rows, 'selected_pose_ids': selected_poses,
        'removed_row_ids': sorted(set(range(len(rows))) - set(selected_rows)),
        'removed_pose_ids': sorted(set(range(len(poses))) - set(selected_poses)),
        'row_reason_counts': dict(Counter(reason for reasons in row_reasons.values() for reason in reasons)),
        'pose_reason_counts': dict(Counter(reason for reasons in pose_reasons.values() for reason in reasons)),
        'original_to_compact_layout': 'The rows/poses entries provide original_id and compact slot; public IDs must remain original_id.',
        'exact_values': selected, 'exact_values_sha256': hashlib.sha256(selected_bytes).hexdigest(),
        'used_complements': [[i, complements[i]] for i in used_keys],
        'coverage_counts': {'actual_domains': len(domains), 'direct_output_poses': len(initial),
                            'pair_plans': len(plans), 'pair_blocks': len(used_blocks),
                            'retained_relaxation_links': len(links), 'chord_plans': len(chord['plans']),
                            'chord_neighbor_records': len(chord['neighbors'])},
        'independent_current_source_checks': dict(cache_counts),
        'literal_payload_bytes': {'original_rows': old_row_bytes, 'selected_rows': new_row_bytes,
                                  'original_poses': old_pose_bytes, 'selected_poses': new_pose_bytes,
                                  'saved_before_sparse_key_overhead': old_row_bytes + old_pose_bytes - new_row_bytes - new_pose_bytes,
                                  'sparse_decimal_key_bytes': sum(len(str(i)) + 1 for i in selected_rows + selected_poses)},
        'selected_pose_row_memberships': sum(len(poses[i]['rows']) for i in selected_poses),
        'limitations': ['No future chord fusion savings included.',
                        'No compiled object, replay-time or global seven-case saving is claimed.',
                        'Derived direct base/forbidden rows are exact formula caches, not shared dictionary IDs.',
                        'Cached source coverage records only files present at this audit; complete structural closure uses all original plans/domains.',
                        'Original unused IDs may change only outside this live closure; downstream ordinary checks must still replay.'],
        'input_hashes': inputs, 'input_bytes_read': total_read, 'seconds': time.monotonic() - started}
    encoded = (json.dumps(report, separators=(',', ':')) + '\n').encode()
    require(len(encoded) <= 8 * MIB, 'Evidence output exceeds 8 MiB')
    guard()
    temporary = OUT.with_suffix('.json.tmp')
    try:
        temporary.write_bytes(encoded)
        temporary.replace(OUT)
    finally:
        temporary.unlink(missing_ok=True)
        signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: report[key] for key in (
        'selected_row_count', 'selected_pose_count', 'removed_row_count', 'removed_pose_count',
        'removed_raw_pose_count', 'coverage_counts', 'literal_payload_bytes', 'seconds')}, indent=2))


if __name__ == '__main__':
    main()
