#!/usr/bin/env python3
"""Parent-run reachability and optional isolated bank for direct pair pruning.

No active source changes. All original global IDs stay fixed. Every current
semantic domain, fan input/basis/empty witness, actual block, outgoing target,
and all 21 original chord stages survive. Pair-only raw pieces and relaxation
links are no longer consumers ONLY after the separately checked direct-plan
replacement. This does not certify the pending Lean instances.

Run --run [--emit] in the parent's 200 MiB/60-second serial slot. The internal
guard stops at 190 MiB/55 seconds; transactional output is capped at 16 MiB.
"""
from collections import Counter, defaultdict
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

from audit_historical_bank_reachability import JSONStream
from prepare_historical_graphs import read_case

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
FANS = ROOT / 'evidence/historical-fans-701-713-717-973-978-979-cycles'
DIRECT = ROOT / 'evidence/historical-outside-coverage'
CASES = (701, 713, 717, 973, 978, 979)
TAGS = ('semantic_domain', 'direct_entrance_target', 'original_current_domain',
        'pair_source', 'pair_neighbor', 'pair_final_target', 'direct_branch_target',
        'chord_stage_pose', 'chord_link_endpoint', 'chord_named_pose',
        'actual_pruning_block', 'chord_named_block', 'fan_context_input',
        'fan_basis_or_cycle', 'empty_certificate_row')
BIT = {name: 1 << i for i, name in enumerate(TAGS)}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sparse_sources(rows, poses, live_rows, live_poses, row_count, guard):
    """Exact selected original records, bounded balanced leaves, unchanged API."""
    outputs = {}
    chunks = []
    outputs['Compact/HistoricalData/Counts.lean'] = f'''namespace N12Compact.HistoricalData
abbrev rowCount : Nat := {row_count}
abbrev poseCount : Nat := {len(poses)}
end N12Compact.HistoricalData
'''
    def value(kind, index):
        if kind == 'Rows':
            row = rows[index]
            return '(⟨' + ','.join(map(str, row['integers'])) + ',' + str(row['strict']).lower() + \
                f'⟩,{row["denominator"] - 1})'
        return f'({poses[index]["angle"]}, [' + ','.join(map(str, poses[index]['rows'])) + '])'
    def record(kind, index):
        if kind == 'Rows':
            row = rows[index]
            return f'{index}:' + ','.join(map(str, row['integers'])) + ',' + \
                str(row['strict']).lower() + ',' + str(row['denominator'] - 1)
        return f'{index}:{poses[index]["angle"]};' + ','.join(map(str, poses[index]['rows']))
    def build(kind, ids):
        guard()
        if not ids:
            return '.empty'
        if len(ids) <= 2048:
            name = f'part{ids[0]:06}'
            namespace = f'N12Compact.HistoricalData.{kind}Chunks'
            module = f'Compact.HistoricalData.{kind}Chunks.Part{ids[0]:06}'
            path = module.replace('.', '/') + '.lean'
            typ = 'SparseLiteral.Tree (IntegerSupport.Row × Nat)' if kind == 'Rows' else \
                'SparseLiteral.Tree (Fin 192 × List (Fin rowCount))'
            parser = 'sparse_rows%' if kind == 'Rows' else f'sparse_poses% 192 {row_count}'
            outputs[path] = '\n'.join(['import Compact.Core.SparseLiteral',
                'import Compact.HistoricalData.Counts', '', f'namespace {namespace}',
                'set_option Elab.async false', f'noncomputable def {name} : {typ} := {parser} "',
                *(record(kind, i) for i in ids), '"', f'end {namespace}', ''])
            chunks.append({'kind': kind, 'module': module, 'path': path,
                           'first': ids[0], 'last': ids[-1], 'records': len(ids)})
            return f'{kind}Chunks.{name}'
        mid = len(ids) // 2
        left = build(kind, ids[:mid])
        right = build(kind, ids[mid+1:])
        return f'(.node {ids[mid]} {value(kind, ids[mid])}\n  {left}\n  {right})'
    rt = build('Rows', live_rows)
    pt = build('Poses', live_poses)
    ri = ['import ' + c['module'] for c in chunks if c['kind'] == 'Rows']
    pi = ['import ' + c['module'] for c in chunks if c['kind'] == 'Poses']
    outputs['Compact/HistoricalData/SharedRows.lean'] = '\n'.join(ri) + f'''

/-! Original global IDs, restricted to the exact direct-pruning consumer closure.
Unused IDs have the ordinary sparse fallback; no active consumer may use them.
This bank is a proposal until all replacement contracts and bindings replay. -/
namespace N12Compact.HistoricalData
open IntegerSupport
set_option Elab.async false
noncomputable def rowData : SparseLiteral.Tree (Row × Nat) :=
  {rt}
noncomputable def rowPair (index : Nat) : Row × Nat :=
  SparseLiteral.lookup (⟨0,0,0,false⟩,0) rowData index
noncomputable def rows (i : Fin rowCount) : Row := (rowPair i.val).1
noncomputable def denominators (i : Fin rowCount) : Nat := (rowPair i.val).2+1
theorem positive_denominators (i : Fin rowCount) : 0 < denominators i := Nat.zero_lt_succ _
end N12Compact.HistoricalData
'''
    outputs['Compact/HistoricalData/SharedPoses.lean'] = '\n'.join([
        'import Compact.HistoricalData.SharedRows', 'import S12.OwnerEnclosure', *pi]) + f'''

namespace N12Compact.HistoricalData
open S12
set_option Elab.async false
noncomputable def poseData : SparseLiteral.Tree (Fin 192 × List (Fin rowCount)) :=
  {pt}
noncomputable def poseRecord (index : Nat) : Fin 192 × List (Fin rowCount) :=
  SparseLiteral.lookup (0,[]) poseData index
noncomputable def poseAngle (i : Fin poseCount) : Fin 192 := (poseRecord i.val).1
noncomputable def poseRows (i : Fin poseCount) : List (Fin rowCount) := (poseRecord i.val).2
noncomputable def poses (angles : Fin 192 → {{w : AngleEnclosure // w.Check}})
    (i : Fin poseCount) : PoseLeaf :=
  ⟨angles (poseAngle i), (poseRows i).map (fun r => (rows r).normalized (denominators r))⟩
end N12Compact.HistoricalData
'''
    return outputs, chunks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--emit', action='store_true')
    parser.add_argument('--output', default='evidence/historical-direct-bank')
    args = parser.parse_args()
    need(args.run, 'parent serial slot and --run required')
    dest = (ROOT / args.output).resolve()
    need(dest.is_relative_to(ROOT / 'evidence'), 'output must remain under evidence')
    staging = dest.with_name(dest.name + '.staging')
    need(not dest.exists() and not staging.exists(), 'refusing existing output')
    start = time.monotonic()
    provenance = {}
    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 190 * 1024**2 and time.monotonic() - start < 55, '190 MiB/55-second working guard')
    def stopped(*_):
        raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stopped)
    signal.signal(signal.SIGINT, stopped)
    def authenticate(path, expected=None):
        h = hashlib.sha256()
        with path.open('rb') as file:
            for block in iter(lambda: file.read(65536), b''):
                guard()
                h.update(block)
        result = h.hexdigest()
        need(expected is None or result == expected, 'source hash mismatch: ' + str(path))
        provenance[str(path.relative_to(ROOT))] = result
        return result
    def load(path, expected=None):
        authenticate(path, expected)
        need(path.stat().st_size < 16 * 1024**2, 'oversized metadata load')
        with path.open() as file:
            result = json.load(file)
        guard()
        return result
    def array(path):
        stream = JSONStream(path, guard)
        try:
            yield from stream.array()
            need(stream.peek() is None, 'trailing JSON')
        finally:
            stream.file.close()
    staging.mkdir(parents=True)
    try:
        manifest = load(BASE / 'manifest.json')
        need(tuple(manifest['scope']) == CASES and manifest['status'].startswith('data assembled'),
             'incomplete or incorrect extraction')
        expected = {x['path']: x['sha256'] for x in manifest['output_files']}
        def data(name):
            return load(BASE / name, expected[name])
        audit = load(DIRECT / 'manifest.json')
        need(audit['completed_cases'] == list(CASES) and audit['all_outside_contexts_visited'] and
             not audit['failure_samples'] and audit['counts']['outside_branches'] ==
             audit['counts']['direct_final_target'] == 16896, 'direct replacement audit incomplete')
        for path, digest in audit['input_sha256'].items():
            authenticate(ROOT / path, digest)
        authenticate(DIRECT / 'branches.jsonl', audit['branches_sha256'])
        counts = manifest['unique_objects']
        poses, blocks, links, contexts = [data(name + 's.json') for name in ('pose', 'block', 'link', 'context')]
        for kind, values in (('pose', poses), ('block', blocks), ('link', links), ('context', contexts)):
            need(len(values) == counts[kind] and all(v['index'] == i for i, v in enumerate(values)),
                 'noncanonical original ' + kind + ' IDs')
        pm = [0] * len(poses)
        rm = [0] * counts['row']
        def pose(pid, reason):
            need(type(pid) is int and 0 <= pid < len(pm), 'invalid live pose ID')
            pm[pid] |= BIT[reason]
        def row(rid, reason):
            need(type(rid) is int and 0 <= rid < len(rm), 'invalid live row ID')
            rm[rid] |= BIT[reason]
        direct_initial = load(ROOT / 'evidence/historical-direct-cover-audit.json')['cases']
        cover_path = ROOT / 'vendor/S12/CoverData.lean'
        authenticate(cover_path)
        cover_rows = [(int(cid), tuple(map(int, values.split(',')))) for cid, values in
                      re.findall(r'⟨(\d+),\{([0-9,]+)\}', cover_path.read_text())]
        need(len(cover_rows) == 577, 'original family table differs')
        chord_steps, pair_steps, pair_links, selected_blocks = set(), set(), set(), set()
        pair_raw_poses = set()
        expected_fans = {}
        graph_records = []
        branch_count = plan_count = zero_count = 0
        with (DIRECT / 'branches.jsonl').open() as branch_file:
            for case in CASES:
                graph = read_case(case, manifest, next(a for a in direct_initial if a['case'] == case),
                                  cover_rows, provenance, guard)
                cdata = data(f'C{case}.json')
                for name, domain in graph['domains'].items():
                    for pid in domain:
                        pose(pid, 'semantic_domain')
                        if name in graph['initials']:
                            pose(pid, 'direct_entrance_target')
                for domain in cdata['domains'].values():
                    for pid in domain:
                        pose(pid, 'original_current_domain')
                for step in graph['stages']:
                    if step['kind'] != 'PruningCoverCheck':
                        chord_steps.add((case, step['step']))
                        for name in [step['source'], step['target'], *step['neighbors']]:
                            for pid in graph['domains'][name]:
                                pose(pid, 'chord_stage_pose')
                by_stage = defaultdict(list)
                for ordinal, plan in enumerate(cdata['plans']):
                    by_stage[plan['step']].append((ordinal, plan))
                need(set(by_stage) == set(map(int, cdata['pair_steps'])), 'pair scope mismatch')
                for step, names in cdata['pair_steps'].items():
                    step = int(step)
                    pair_steps.add((case, step))
                    sources, neighbors, targets = [cdata['domains'][name] for name in names]
                    target_set = set(targets)
                    need([p['source'] for _, p in by_stage[step]] == sources, 'original source coverage changed')
                    for ordinal, plan in by_stage[step]:
                        plan_count += 1
                        source, bid = plan['source'], plan['block']
                        pose(source, 'pair_source')
                        need(cdata['domains'][plan['neighbors_name']] == neighbors, 'original neighbors changed')
                        for pid in neighbors:
                            pose(pid, 'pair_neighbor')
                        for pid in plan['targets']:
                            need(pid in target_set, 'plan target outside original stage')
                            pose(pid, 'pair_final_target')
                        pair_links.update(plan['links'])
                        pair_raw_poses.update(plan['pieces'])
                        if bid is None:
                            faces = 1
                        else:
                            need(0 <= bid < len(blocks), 'invalid actual block')
                            selected_blocks.add(bid)
                            faces = len(blocks[bid]['rows'])
                            expected_fans[(case, step, plan['name'])] = (source, bid, tuple(neighbors))
                        if faces == 0:
                            zero_count += 1
                            need(bid is not None and not blocks[bid]['rows'] and not plan['pieces'],
                                 'zero branch requires the empty blocked conjunction')
                        for face in range(faces):
                            line = branch_file.readline()
                            need(bool(line), 'missing audited outside branch')
                            branch = json.loads(line)
                            need(branch[:4] == [case, ordinal, face, 0], 'audited original branch order/scope differs')
                            pid = branch[4]
                            need(pid in plan['targets'] and pid in target_set and
                                 poses[pid]['angle'] == poses[source]['angle'], 'audited final target differs')
                            pose(pid, 'direct_branch_target')
                            branch_count += 1
                graph_records.append({'case': case, 'stages': graph['stages'],
                                      'initials': graph['initials'], 'terminal': graph['terminal']})
                del graph, cdata, by_stage
            need(not branch_file.read(1), 'unexpected extra audited branch')
        need((plan_count, branch_count, zero_count, len(pair_steps), len(chord_steps)) ==
             (9166, 16896, 2153, 113, 21), 'full original scope changed')
        chord_links = set()
        named_links = set()
        authenticate(BASE / 'names.jsonl', expected['names.jsonl'])
        with (BASE / 'names.jsonl').open() as file:
            for line in file:
                entry = json.loads(line)
                m = re.match(r'continuousScout(\d+)Step(\d+)', entry['name'])
                key = (int(m[1]), int(m[2])) if m else None
                if entry['kind'] == 'link':
                    named_links.add(entry['index'])
                    if key in chord_steps:
                        chord_links.add(entry['index'])
                elif key in chord_steps and entry['kind'] == 'pose':
                    pose(entry['index'], 'chord_named_pose')
                elif key in chord_steps and entry['kind'] == 'block':
                    for rid in blocks[entry['index']]['rows']:
                        row(rid, 'chord_named_block')
        need(named_links == set(range(len(links))), 'unknown unnamed retained link')
        need(pair_links | chord_links == named_links, 'unclassified original link must remain explicit')
        for index in chord_links:
            for pid in (links[index]['source'], links[index]['target']):
                pose(pid, 'chord_link_endpoint')
        for bid in selected_blocks:
            for rid in blocks[bid]['rows']:
                row(rid, 'actual_pruning_block')
        fan_manifest = load(FANS / 'manifest.json')
        need(fan_manifest['all_selected_pairs_pass'] and fan_manifest['cases'] == list(CASES), 'fan scope incomplete')
        for path, digest in fan_manifest['sources'].items():
            need(provenance.get(path) == digest or
                 (Path(path).parent == BASE.relative_to(ROOT) and expected.get(Path(path).name) == digest),
                 'fan source differs from authenticated extraction')
            if provenance.get(path) != digest:
                authenticate(ROOT / path, digest)
        fan_entry = next(x for x in fan_manifest['files'] if x['path'] == 'fans.json')
        authenticate(FANS / 'fans.json', fan_entry['sha256'])
        seen_contexts, requested, seen_plans = set(), set(), set()
        pair_occurrences = 0
        def activate_context(cid):
            need(0 <= cid < len(contexts) and cid not in seen_contexts, 'invalid/duplicate fan context')
            seen_contexts.add(cid)
            for rid in contexts[cid]['inputs']:
                row(rid, 'fan_context_input')
            return contexts[cid]
        stream = JSONStream(FANS / 'fans.json', guard)
        try:
            stream.punctuation('{')
            seen_keys = set()
            while stream.peek() != '}':
                if seen_keys:
                    stream.punctuation(',')
                key = stream.value()
                need(key not in seen_keys, 'duplicate fan JSON key')
                seen_keys.add(key)
                stream.punctuation(':')
                if key == 'context_records':
                    for record in stream.array():
                        context = activate_context(record['context'])
                        inputs = set(context['inputs'])
                        for entry in record['entries']:
                            for rid in entry[1:3]:
                                need(rid in inputs, 'fan basis outside actual input')
                                row(rid, 'fan_basis_or_cycle')
                        for rid in record['boundary_cycle'] or []:
                            need(rid in inputs, 'fan cycle outside actual input')
                            row(rid, 'fan_basis_or_cycle')
                elif key == 'empty_contexts':
                    for cid, certificate in stream.value().items():
                        context = activate_context(int(cid))
                        for rid in certificate['rows']:
                            need(rid in context['inputs'], 'empty witness outside actual input')
                            row(rid, 'empty_certificate_row')
                elif key == 'plans':
                    for plan in stream.array():
                        key_plan = (plan['case'], plan['step'], plan['name'])
                        need(key_plan not in seen_plans and key_plan in expected_fans, 'fan occurrence differs')
                        seen_plans.add(key_plan)
                        source, block, neighbors = expected_fans[key_plan]
                        need(source == plan['source_pose'] and block == plan['block'], 'fan source/block differs')
                        cid = plan['source']
                        requested.add(cid)
                        need(contexts[cid]['angle'] == poses[source]['angle'] and
                             contexts[cid]['inputs'] == blocks[block]['rows'] + poses[source]['rows'],
                             'fan blocked source rows differ')
                        need(len(neighbors) == len(plan['neighbors']), 'fan neighbors incomplete')
                        for pid, cid in zip(neighbors, plan['neighbors']):
                            requested.add(cid)
                            need(contexts[cid]['angle'] == poses[pid]['angle'] and
                                 contexts[cid]['inputs'] == poses[pid]['rows'], 'fan neighbor rows differ')
                        pair_occurrences += len(neighbors)
                elif key == 'angle_order':
                    need(sorted(stream.value()) == list(range(192)), 'angle permutation differs')
                else:
                    raise ValueError('unknown fan field ' + str(key))
            stream.punctuation('}')
            need(stream.peek() is None, 'trailing fan data')
        finally:
            stream.file.close()
        need(seen_plans == set(expected_fans) and seen_contexts == requested and
             pair_occurrences == 639066 and len(seen_contexts) == fan_manifest['requested_contexts'],
             'complete original fan coverage differs')
        del expected_fans, contexts, blocks, links
        for pid, record in enumerate(poses):
            need(0 <= record['angle'] < 192, 'invalid original angle')
            for rid in record['rows']:
                need(0 <= rid < len(rm), 'invalid original row ID')
                rm[rid] |= pm[pid]
        live_rows = [i for i, mask in enumerate(rm) if mask]
        live_poses = [i for i, mask in enumerate(pm) if mask]
        removed_rows = [i for i, mask in enumerate(rm) if not mask]
        removed_poses = [i for i, mask in enumerate(pm) if not mask]
        need(set(removed_poses) <= pair_raw_poses,
             'candidate drops a pose that is not an authenticated pair-only intermediate')
        retired_pose_rows = {rid for pid in removed_poses for rid in poses[pid]['rows']}
        need(set(removed_rows) <= retired_pose_rows,
             'candidate drops a row outside the retired pair-pose closure')
        kept_rows = {}
        record_bytes_saved = sum(len((f'{i}:{poses[i]["angle"]};' +
            ','.join(map(str, poses[i]['rows'])) + '\n').encode()) for i in removed_poses)
        row_path = BASE / 'rows.json'
        authenticate(row_path, expected['rows.json'])
        for i, record in enumerate(array(row_path)):
            need(record['index'] == i and record['denominator'] > 0 and len(record['integers']) == 3
                 and type(record['strict']) is bool, 'invalid original row')
            if rm[i]:
                if args.emit:
                    kept_rows[i] = record
            else:
                record_bytes_saved += len((f'{i}:' + ','.join(map(str, record['integers'])) + ',' +
                    str(record['strict']).lower() + ',' + str(record['denominator'] - 1) + '\n').encode())
        need(i + 1 == len(rm), 'row count differs')
        authenticate(BASE / 'remaining-contracts.jsonl', expected['remaining-contracts.jsonl'])
        contracts = Counter()
        with (BASE / 'remaining-contracts.jsonl').open() as file:
            for line in file:
                contracts[json.loads(line)['kind']] += 1
        outputs, chunks = ({}, [])
        if args.emit:
            outputs, chunks = sparse_sources(kept_rows, poses, live_rows, live_poses, len(rm), guard)
        condition = ('Accept every concrete direct Plan.Check and exact stage source/output binding, '
            'then replace all pair-only old piece/link imports. Keep all original 21 chord contracts '
            'and all their selected endpoints. Replay every importing theorem before activation.')
        report = {
            'status': 'complete conditional direct-route ID audit; no active changes or new Lean claims',
            'scope': list(CASES), 'sources': provenance,
            'original_dictionary': {'rows': len(rm), 'poses': len(pm)},
            'direct_route': {'rows': len(live_rows), 'poses': len(live_poses),
                'row_reasons': {tag: sum(bool(x & BIT[tag]) for x in rm) for tag in TAGS},
                'pose_reasons': {tag: sum(bool(x & BIT[tag]) for x in pm) for tag in TAGS}},
            'removed_rows': removed_rows, 'removed_poses': removed_poses,
            'record_lines_saved': len(removed_rows) + len(removed_poses),
            'record_bytes_saved': record_bytes_saved,
            'direct_plans': plan_count, 'outside_contexts': branch_count,
            'empty_block_plans': zero_count, 'pair_stages': len(pair_steps), 'chord_stages': len(chord_steps),
            'retained_chord_links': len(chord_links), 'retired_pair_only_links': len(pair_links - chord_links),
            'fan_contexts': len(seen_contexts), 'pair_occurrences': pair_occurrences,
            'graphs': graph_records, 'original_contract_inventory': dict(contracts),
            'required_before_activation': condition,
            'strict_complements': 'Derived Row values, never missing/default dictionary IDs.',
            'size_boundary': 'Exact data-record savings only until optional emission; final retained import census still required.',
            'proposal': {'emitted': args.emit, 'modules': len(outputs),
                'lines': sum(s.count('\n') for s in outputs.values()),
                'bytes': sum(len(s.encode()) for s in outputs.values()), 'chunks': chunks},
            'limits': {'rss_mib': 200, 'seconds': 60, 'output_mib': 16},
            'seconds': time.monotonic() - start,
        }
        selection = {'row_ids': live_rows, 'pose_ids': live_poses,
                     'block_ids': sorted(selected_blocks), 'link_ids': sorted(chord_links),
                     'context_ids': sorted(seen_contexts), 'conditional_on': condition}
        written = 0
        hashes = {}
        for name, source in outputs.items():
            guard()
            blob = source.encode()
            written += len(blob)
            need(written <= 16 * 1024**2, '16 MiB output cap')
            path = staging / 'proposal' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(blob)
            need(path.read_bytes() == blob, 'source write verification failed')
            hashes[name] = hashlib.sha256(blob).hexdigest()
        report['proposal']['sha256'] = hashes
        for name, value in [('manifest.json', report), ('selection.json', selection)]:
            blob = (json.dumps(value, separators=(',', ':')) + '\n').encode()
            written += len(blob)
            need(written <= 16 * 1024**2, '16 MiB output cap')
            (staging / name).write_bytes(blob)
        guard()
        staging.rename(dest)
        print(json.dumps({k: report[k] for k in ('status', 'original_dictionary', 'direct_route',
            'record_lines_saved', 'record_bytes_saved', 'retained_chord_links',
            'retired_pair_only_links', 'seconds')}, indent=2))
        print(json.dumps({k: report['proposal'][k] for k in ('emitted', 'modules', 'lines', 'bytes')}))
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
