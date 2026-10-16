#!/usr/bin/env python3
"""Audit exact dictionary consumers without changing or duplicating the bank.

Parent-only --run, inside the serial 256 MiB/120-second resource guard.
Output is at most 8 MiB and contains ID selections and provenance, not Lean.
The original closure keeps every retained relaxation, including unfinished
chords. A separate, explicitly conditional candidate removes only link IDs
whose every authenticated name belongs to the replaced C713 step 5.

This is an ID/reachability audit, not a numerical check or Lean acceptance.
It does not assert that the remaining chord/region contracts are converted.
"""
from collections import Counter
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

from prepare_historical_graphs import read_case

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
FANS = ROOT / 'evidence/historical-fans-701-713-717-973-978-979-cycles'
CASES = (701, 713, 717, 973, 978, 979)
OUT_CAP = 8 * 1024**2
TAGS = (
    'semantic_domain', 'direct_entrance_target', 'pair_source',
    'complete_pair_neighbor', 'pair_piece', 'pair_target',
    'pair_relaxation_endpoint', 'chord_relaxation_endpoint',
    'other_retained_relaxation_endpoint', 'chord_source_or_target',
    'c713_height_source_or_target', 'actual_pruning_block',
    'fan_context_input', 'fan_basis_or_cycle', 'empty_certificate_row',
    'strict_block_complement', 'other_current_domain',
)
BIT = {tag: 1 << i for i, tag in enumerate(TAGS)}


def need(condition, message):
    if not condition:
        raise ValueError(message)


class JSONStream:
    """Decode one small value at a time; never load the full fan document."""
    def __init__(self, path, guard):
        self.file = path.open('r')
        self.guard = guard
        self.buffer = ''
        self.position = 0
        self.decoder = json.JSONDecoder()
        self.eof = False

    def refill(self):
        self.guard()
        self.buffer = self.buffer[self.position:]
        self.position = 0
        block = self.file.read(65536)
        self.eof = not block
        self.buffer += block
        need(len(self.buffer) <= 2 * 1024**2, 'single JSON value exceeds 2 MiB')

    def peek(self):
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position].isspace():
                self.position += 1
            if self.position < len(self.buffer):
                return self.buffer[self.position]
            if self.eof:
                return None
            self.refill()

    def punctuation(self, expected):
        need(self.peek() == expected, 'unexpected streamed JSON punctuation')
        self.position += 1

    def value(self):
        need(self.peek() is not None, 'truncated JSON value')
        while True:
            try:
                result, end = self.decoder.raw_decode(self.buffer, self.position)
                self.position = end
                return result
            except json.JSONDecodeError:
                need(not self.eof, 'invalid/truncated streamed JSON value')
                self.refill()

    def array(self):
        self.punctuation('[')
        first = True
        while self.peek() != ']':
            if not first:
                self.punctuation(',')
            first = False
            yield self.value()
        self.punctuation(']')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--output', default='evidence/historical-bank-reachability')
    args = parser.parse_args()
    need(args.run, 'prepared only; parent serial slot and --run required')
    output = (ROOT / args.output).resolve()
    need(output.is_relative_to(ROOT / 'evidence'), 'output must be under evidence')
    stage = output.with_name(output.name + '.staging')
    need(not stage.exists() and not output.exists(), 'refusing existing output')
    start = time.monotonic()
    provenance = {}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        rss *= 1 if sys.platform == 'darwin' else 1024
        need(rss < 256 * 1024**2 and time.monotonic() - start < 115,
             '256 MiB / 115-second working guard')

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    def authenticate(path, expected=None):
        h = hashlib.sha256()
        with path.open('rb') as file:
            for block in iter(lambda: file.read(65536), b''):
                guard()
                h.update(block)
        digest = h.hexdigest()
        need(expected is None or digest == expected, 'source hash mismatch: ' + str(path))
        provenance[str(path.relative_to(ROOT))] = digest
        return digest

    def load(path, expected=None):
        authenticate(path, expected)
        need(path.stat().st_size < 16 * 1024**2, 'metadata file exceeds bounded load')
        with path.open() as file:
            result = json.load(file)
        guard()
        return result

    def records(path):
        stream = JSONStream(path, guard)
        try:
            yield from stream.array()
            need(stream.peek() is None, 'trailing JSON array content')
        finally:
            stream.file.close()

    stage.mkdir(parents=True)
    try:
        manifest = load(BASE / 'manifest.json')
        need(manifest['status'].startswith('data assembled'), 'incomplete source extraction')
        need(tuple(manifest['scope']) == CASES, 'wrong extraction scope')
        expected = {entry['path']: entry['sha256'] for entry in manifest['output_files']}
        def data(name):
            return load(BASE / name, expected[name])
        counts = manifest['unique_objects']
        poses, blocks, links, contexts = [data(name + 's.json') for name in ('pose', 'block', 'link', 'context')]
        for name, values in (('pose', poses), ('block', blocks), ('link', links), ('context', contexts)):
            need(len(values) == counts[name] and all(v['index'] == i for i, v in enumerate(values)),
                 'noncanonical ' + name + ' IDs')
        row_count = counts['row']
        for pose in poses:
            need(0 <= pose['angle'] < 192 and all(0 <= r < row_count for r in pose['rows']),
                 'invalid original pose record')
        pose_masks = [0] * len(poses)
        row_masks = [0] * row_count
        pair_links, selected_blocks = set(), set()
        expected_fan_plans = {}

        def mark_pose(pid, reason, destination=pose_masks):
            need(type(pid) is int and 0 <= pid < len(poses), 'invalid live pose ID')
            destination[pid] |= BIT[reason]

        def mark_row(rid, reason):
            need(type(rid) is int and 0 <= rid < row_count, 'invalid live row ID')
            row_masks[rid] |= BIT[reason]

        direct = load(ROOT / 'evidence/historical-direct-cover-audit.json')['cases']
        cover_path = ROOT / 'vendor/S12/CoverData.lean'
        authenticate(cover_path)
        cover_rows = [(int(cid), tuple(map(int, values.split(',')))) for cid, values in
                      re.findall(r'⟨(\d+),\{([0-9,]+)\}', cover_path.read_text())]
        need(len(cover_rows) == 577, 'original family table differs')
        graph_summary, chord_steps, active_steps = [], set(), set()
        for case in CASES:
            graph = read_case(case, manifest, next(a for a in direct if a['case'] == case),
                              cover_rows, provenance, guard)
            case_data = data(f'C{case}.json')
            steps = {entry['step'] for entry in graph['stages']}
            active_steps.update((case, step) for step in steps)
            for name, domain in graph['domains'].items():
                for pid in domain:
                    mark_pose(pid, 'semantic_domain')
                    if name in graph['initials']:
                        mark_pose(pid, 'direct_entrance_target')
            for name, domain in case_data['domains'].items():
                for pid in domain:
                    mark_pose(pid, 'other_current_domain')
            for entry in graph['stages']:
                if entry['kind'] != 'PruningCoverCheck':
                    chord_steps.add((case, entry['step']))
                    for name in [entry['source'], entry['target']]:
                        for pid in graph['domains'][name]:
                            mark_pose(pid, 'chord_source_or_target')
            if case == 713:
                for name in ('continuousScout713Domain7_0', 'continuousScout713Domain7_6'):
                    for pid in case_data['domains'][name]:
                        mark_pose(pid, 'c713_height_source_or_target')
            for plan in case_data['plans']:
                need(plan['step'] in steps, 'plan outside active graph; review before pruning')
                mark_pose(plan['source'], 'pair_source')
                for pid in case_data['domains'][plan['neighbors_name']]:
                    mark_pose(pid, 'complete_pair_neighbor')
                for pid in plan['pieces']:
                    mark_pose(pid, 'pair_piece')
                for pid in plan['targets']:
                    mark_pose(pid, 'pair_target')
                pair_links.update(plan['links'])
                if plan['block'] is not None:
                    selected_blocks.add(plan['block'])
                    key = (case, plan['step'], plan['name'])
                    need(key not in expected_fan_plans, 'duplicate fan plan occurrence')
                    expected_fan_plans[key] = (plan['source'], plan['block'],
                        tuple(case_data['domains'][plan['neighbors_name']]))
            graph_summary.append({k: graph[k] for k in ('case', 'initials', 'terminal', 'unused_steps')} |
                                 {'stages': len(graph['stages']), 'domains': len(graph['domains'])})
            del graph, case_data
        need(len(active_steps) == 134, 'active graph changed; review stage count')

        # Keep all old relaxation endpoints, even when their proof is unfinished.
        # A candidate may discard a step-5-only C713 link only after the new
        # original-packing height adapter is accepted. Shared IDs are protected.
        link_names = [0] * len(links)
        link_outside_height = [False] * len(links)
        chord_links = set()
        names_path = BASE / 'names.jsonl'
        authenticate(names_path, expected['names.jsonl'])
        with names_path.open() as file:
            for line in file:
                entry = json.loads(line)
                if entry['kind'] != 'link':
                    continue
                index = entry['index']
                need(0 <= index < len(links), 'named link outside original table')
                link_names[index] += 1
                m = re.match(r'continuousScout(\d+)Step(\d+)', entry['name'])
                stage_key = (int(m[1]), int(m[2])) if m else None
                if stage_key in chord_steps:
                    chord_links.add(index)
                if stage_key != (713, 5):
                    link_outside_height[index] = True
        candidate_pose_masks = pose_masks.copy()
        retired_height_links = []
        for index, link in enumerate(links):
            need(link_names[index] > 0, 'unnamed retained link; cannot infer its scope')
            reason = ('pair_relaxation_endpoint' if index in pair_links else
                      'chord_relaxation_endpoint' if index in chord_links else
                      'other_retained_relaxation_endpoint')
            for pid in (link['source'], link['target']):
                mark_pose(pid, reason)
            obsolete = index not in pair_links and not link_outside_height[index]
            if obsolete:
                retired_height_links.append(index)
            else:
                for pid in (link['source'], link['target']):
                    mark_pose(pid, reason, candidate_pose_masks)
        for bid in selected_blocks:
            need(0 <= bid < len(blocks), 'block ID outside original table')
            for rid in blocks[bid]['rows']:
                mark_row(rid, 'actual_pruning_block')

        fan_manifest = load(FANS / 'manifest.json')
        need(fan_manifest['all_selected_pairs_pass'] and fan_manifest['cases'] == list(CASES),
             'fan audit incomplete or wrong scope')
        for path, digest in fan_manifest['sources'].items():
            if path not in provenance:
                source_path = (ROOT / path).resolve()
                need(source_path.parent == BASE and expected.get(source_path.name) == digest,
                     'fan source lacks authenticated extraction provenance: ' + path)
                authenticate(source_path, digest)
            need(provenance.get(path) == digest, 'fan source differs from selected source: ' + path)
        fan_file = next(entry for entry in fan_manifest['files'] if entry['path'] == 'fans.json')
        authenticate(FANS / 'fans.json', fan_file['sha256'])
        seen_contexts, seen_plans, requested_contexts = set(), set(), set()
        fan_pair_occurrences = 0
        def activate_context(cid, empty=False):
            need(type(cid) is int and 0 <= cid < len(contexts), 'invalid fan context ID')
            need(cid not in seen_contexts, 'duplicate emitted context')
            seen_contexts.add(cid)
            for rid in contexts[cid]['inputs']:
                mark_row(rid, 'fan_context_input')
            return contexts[cid]
        stream = JSONStream(FANS / 'fans.json', guard)
        try:
            stream.punctuation('{')
            keys_seen = set()
            while stream.peek() != '}':
                if keys_seen:
                    stream.punctuation(',')
                key = stream.value()
                need(key not in keys_seen, 'duplicate fan JSON field')
                keys_seen.add(key)
                stream.punctuation(':')
                if key == 'context_records':
                    for record in stream.array():
                        context = activate_context(record['context'])
                        inputs = set(context['inputs'])
                        for entry in record['entries']:
                            for rid in entry[1:3]:
                                need(rid in inputs, 'basis row not in actual context')
                                mark_row(rid, 'fan_basis_or_cycle')
                        for rid in record['boundary_cycle'] or []:
                            need(rid in inputs, 'boundary row not in actual context')
                            mark_row(rid, 'fan_basis_or_cycle')
                elif key == 'empty_contexts':
                    for cid, certificate in stream.value().items():
                        context = activate_context(int(cid), empty=True)
                        for rid in certificate['rows']:
                            need(rid in context['inputs'], 'empty witness row outside actual context')
                            mark_row(rid, 'empty_certificate_row')
                elif key == 'plans':
                    for plan in stream.array():
                        identifier = (plan['case'], plan['step'], plan['name'])
                        need(identifier not in seen_plans, 'duplicate fan plan')
                        seen_plans.add(identifier)
                        source, block, neighbors = expected_fan_plans[identifier]
                        need(source == plan['source_pose'] and block == plan['block'],
                             'fan source or block differs from original plan')
                        source_context = contexts[plan['source']]
                        requested_contexts.add(plan['source'])
                        need(source_context['angle'] == poses[source]['angle'] and
                             source_context['inputs'] == blocks[block]['rows'] + poses[source]['rows'],
                             'fan source context differs from exact original rows')
                        need(len(neighbors) == len(plan['neighbors']), 'neighbor coverage length differs')
                        for pid, cid in zip(neighbors, plan['neighbors']):
                            requested_contexts.add(cid)
                            context = contexts[cid]
                            need(context['angle'] == poses[pid]['angle'] and
                                 context['inputs'] == poses[pid]['rows'], 'actual neighbor context differs')
                        fan_pair_occurrences += len(neighbors)
                elif key == 'angle_order':
                    need(sorted(stream.value()) == list(range(192)), 'reference key permutation differs')
                else:
                    raise ValueError('unknown fan field: ' + str(key))
            stream.punctuation('}')
            need(stream.peek() is None, 'trailing fan JSON content')
        finally:
            stream.file.close()
        need(seen_plans == set(expected_fan_plans), 'fan plan occurrence coverage incomplete')
        need(seen_contexts == requested_contexts and
             len(seen_contexts) == fan_manifest['requested_contexts'] and
             fan_pair_occurrences == fan_manifest['requested_pairs'], 'fan scope count differs')

        # Original block complements are exact rational/strict negations. Missing
        # dictionary values are reported as future data obligations, never filled
        # with zero defaults or silently omitted from a purported complete proof.
        row_path = BASE / 'rows.json'
        authenticate(row_path, expected['rows.json'])
        block_rows = {rid for bid in selected_blocks for rid in blocks[bid]['rows']}
        opposite_keys = {}
        row_record_bytes = [0] * row_count
        for i, row in enumerate(records(row_path)):
            need(row['index'] == i and row['denominator'] > 0 and
                 len(row['integers']) == 3 and type(row['strict']) is bool, 'invalid original row')
            if i in block_rows:
                opposite = (*(-x for x in row['integers']), not row['strict'], row['denominator'])
                opposite_keys.setdefault(opposite, []).append(i)
            row_record_bytes[i] = len((f'{i}:' + ','.join(map(str, row['integers'])) + ',' +
                str(row['strict']).lower() + ',' + str(row['denominator'] - 1) + '\n').encode())
        need(i + 1 == row_count, 'row count mismatch')
        found_opposites = {}
        for row in records(row_path):
            key = (*row['integers'], row['strict'], row['denominator'])
            if key in opposite_keys:
                mark_row(row['index'], 'strict_block_complement')
                for original in opposite_keys[key]:
                    found_opposites[original] = row['index']
        missing_opposites = sorted(block_rows - found_opposites.keys())
        original_rows, candidate_rows = row_masks.copy(), row_masks.copy()
        for pid, pose in enumerate(poses):
            for rid in pose['rows']:
                original_rows[rid] |= pose_masks[pid]
                candidate_rows[rid] |= candidate_pose_masks[pid]

        contracts_path = BASE / 'remaining-contracts.jsonl'
        authenticate(contracts_path, expected['remaining-contracts.jsonl'])
        contracts = Counter()
        with contracts_path.open() as file:
            for line in file:
                entry = json.loads(line)
                contracts[entry['kind']] += 1
        # No per-record proof source is deleted, and no unparsed contract is
        # treated as established just because all its old endpoint IDs survive.
        def summary(pmask, rmask):
            return {'poses': sum(bool(x) for x in pmask), 'rows': sum(bool(x) for x in rmask),
                'pose_reasons': {tag: sum(bool(x & BIT[tag]) for x in pmask) for tag in TAGS},
                'row_reasons': {tag: sum(bool(x & BIT[tag]) for x in rmask) for tag in TAGS}}
        removed_rows = [i for i, mask in enumerate(candidate_rows) if not mask]
        removed_poses = [i for i, mask in enumerate(candidate_pose_masks) if not mask]
        pose_record_bytes = [len((f'{p["index"]}:{p["angle"]};' +
                             ','.join(map(str, p['rows'])) + '\n').encode()) for p in poses]
        report = {
            'status': 'complete ID-consumer audit; no active changes or Lean claims',
            'scope': list(CASES), 'sources': provenance,
            'limits': {'rss_mib': 256, 'seconds': 120, 'output_mib': 8},
            'original_dictionary': {'rows': row_count, 'poses': len(poses)},
            'original_route': summary(pose_masks, original_rows),
            'after_c713_height_candidate': summary(candidate_pose_masks, candidate_rows),
            'candidate_requires': 'Accept the complete C713 original-packing ChordDirect adapter and all its numeric records before dropping its old step-5-only links.',
            'candidate_retired_links': retired_height_links,
            'candidate_removed_rows': removed_rows, 'candidate_removed_poses': removed_poses,
            'candidate_data_record_lines_saved': len(removed_rows) + len(removed_poses),
            'candidate_data_record_bytes_saved': sum(row_record_bytes[i] for i in removed_rows) +
                                                  sum(pose_record_bytes[i] for i in removed_poses),
            'size_boundary': 'Record savings only. Shared-bank scaffolding and whole-proof line count require a new concrete source census; no whole 300k or 1M bound is asserted.',
            'graphs': graph_summary, 'pair_links': len(pair_links), 'retained_links': len(links),
            'selected_blocks': len(selected_blocks), 'fan_contexts': len(seen_contexts),
            'fan_plan_occurrences': len(seen_plans), 'pair_occurrences': fan_pair_occurrences,
            'missing_exact_complement_rows': missing_opposites,
            'unconverted_contract_inventory': dict(contracts),
            'unfinished_contract_policy': 'All original semantic domains, all retained chord-link endpoints, pair pieces and targets remain represented. Unparsed chord/region contracts remain explicit obligations; this report does not convert or count their future proof source.',
            'seconds': time.monotonic() - start,
        }
        retired_height_set = set(retired_height_links)
        selection = {'row_ids': [i for i, mask in enumerate(candidate_rows) if mask],
                     'pose_ids': [i for i, mask in enumerate(candidate_pose_masks) if mask],
                     'block_ids': sorted(selected_blocks),
                     'link_ids': [i for i in range(len(links)) if i not in retired_height_set],
                     'context_ids': sorted(seen_contexts),
                     'exact_complements': found_opposites,
                     'conditional_on': report['candidate_requires']}
        written = 0
        for name, value in [('manifest.json', report), ('selection.json', selection)]:
            blob = (json.dumps(value, separators=(',', ':'), ensure_ascii=False) + '\n').encode()
            written += len(blob)
            need(written <= OUT_CAP, '8 MiB output cap')
            (stage / name).write_bytes(blob)
        guard()
        stage.rename(output)
        print(json.dumps({key: report[key] for key in ('status', 'original_dictionary',
            'original_route', 'after_c713_height_candidate', 'candidate_data_record_lines_saved',
            'candidate_data_record_bytes_saved', 'seconds')}, indent=2))
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
