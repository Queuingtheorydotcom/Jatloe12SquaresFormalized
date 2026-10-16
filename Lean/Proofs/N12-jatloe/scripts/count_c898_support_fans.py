#!/usr/bin/env python3
"""Count exact shared basis lists from all previously audited C898 witnesses.

No search, Lean run, or new geometric assertion. Does not modify active source.
Explicit --run required; designed to use one small bounded audit slot.
"""
from pathlib import Path
from collections import Counter, defaultdict
import argparse
import hashlib
import json
import resource
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', action='store_true')
    args = ap.parse_args()
    if not args.run:
        ap.error('Prepared only: explicit --run required.')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic() - started > 30 or rss > 128 * 1024**2:
            raise RuntimeError('30-second/128-MiB audit cap reached')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.1, 0.1)
    source = ROOT / 'evidence/c898-shared-pose-map.json'
    witnesses = ROOT / 'evidence/c898-all-pair-four-index-witnesses.jsonl'
    m = json.loads(source.read_text())
    poses = {p['name']: p for p in m['poses']}
    blocks = {b['name']: b for b in m['blocks']}
    contexts, context_ids, fans = [], {}, defaultdict(set)
    usages = defaultdict(set)
    direction_requests = defaultdict(set)
    unique_bases = set()
    counts = Counter()
    witness_hash = hashlib.sha256()

    def context(rows):
        # Membership premises are identical after sorting/deduplicating rows.
        key = tuple(sorted(set(rows)))
        if key not in context_ids:
            context_ids[key] = len(contexts)
            contexts.append(key)
        return context_ids[key]

    with witnesses.open('rb') as f:
        for raw in f:
            witness_hash.update(raw)
            record = json.loads(raw)
            assert not record['fallbacks'] and len(record['supports']) == 8
            source_pose, neighbor_pose = poses[record['source']], poses[record['neighbor']]
            block = blocks[record['block']]
            A, B = block['rows'] + source_pose['rows'], neighbor_pose['rows']
            ai, bi = context(A), context(B)
            usages[ai].add(('source', source_pose['index'], block['index']))
            usages[bi].add(('neighbor', neighbor_pose['index'], -1))
            for axis, (i, j, k, l) in enumerate(record['supports']):
                key = [0, 2, 1, 3][axis % 4] * 64 + record['angles'][0 if axis < 4 else 1]
                direction_requests[ai].add(key)
                direction_requests[bi].add((key + 128) % 256)
                ab, bb = tuple(sorted((A[i], A[j]))), tuple(sorted((B[k], B[l])))
                assert ab[0] != ab[1] and bb[0] != bb[1]
                fans[ai].add(ab); fans[bi].add(bb)
                unique_bases.add(ab); unique_bases.add(bb)
                counts['basis_occurrences_in_old_witnesses'] += 2
            counts['pair_records'] += 1
    assert counts['pair_records'] == 25843
    counts['contexts'] = len(contexts)
    counts['global_unique_two_row_bases'] = len(unique_bases)
    counts['context_basis_memberships'] = sum(map(len, fans.values()))
    counts['max_bases_per_context'] = max(map(len, fans.values()))
    counts['distinct_context_direction_requests'] = sum(map(len, direction_requests.values()))
    counts['max_directions_per_context'] = max(map(len, direction_requests.values()))
    payload = {
        'scope': 'Exact all-C898 counts from existing audited four-index witnesses; no new Lean acceptance.',
        'counts': dict(counts),
        'bases_per_context_histogram': dict(sorted(Counter(map(len, fans.values())).items())),
        'source_pose_map_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'witness_jsonl_sha256': witness_hash.hexdigest(),
        'contexts': [{'id': i, 'rows': list(rows), 'bases': sorted(fans[i]), 'uses': sorted(usages[i])}
                     for i, rows in enumerate(contexts)],
        'semantic_boundary': [
            'A basis proves a directional bound only after its determinant, nonnegative multipliers, row membership, and strictness are checked.',
            'Every old witness basis is present. No claim that an arbitrary first basis works, or that a full polygon fan is already proved.',
            'An existential/minimum-support checker can recover all old witnesses, but runtime requires a bounded pilot.',
            'Source/neighbor coverage, initial entry, chord steps, and final emptiness remain mandatory.',
        ],
        'elapsed_seconds': time.monotonic() - started,
    }
    signal.setitimer(signal.ITIMER_REAL, 0)
    output = ROOT / 'evidence/c898-support-fan-counts.json'
    encoded = json.dumps(payload, separators=(',', ':')) + '\n'
    assert len(encoded.encode()) < 8 * 1024**2
    output.write_text(encoded)
    print(json.dumps({'counts': dict(counts), 'elapsed_seconds': payload['elapsed_seconds']}))


if __name__ == '__main__':
    main()
