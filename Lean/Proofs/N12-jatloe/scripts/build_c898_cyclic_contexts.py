#!/usr/bin/env python3
"""Prepare exact cyclic replacements for C898's existing cached contexts.

Parent-run only: 256 MiB RSS, 115 seconds, 8 MiB output, no Lean/subprocess.
The producer never changes active Lean. It emits the SAME ContextsNN module
and routeN names in an isolated proposal, leaving all pair/stage/relaxation
obligations in place. Every selected nonterminal pair is rechecked on all
eight actual axes. The separately accepted terminal stage14 is left alone.

Cycles are only lookup hints. Materialization emits ordinary constructor
terms; recipe.Check still proves original row membership, exact vertices and
reference identity, and the unchanged pair modules check every actual axis.
An unsupported cycle keeps its exact original two-row fan and records the
reason. A missing original pair or failed support check aborts the proposal.
"""
from bisect import bisect_right
from collections import defaultdict
from fractions import Fraction
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

from boundary_fan_cycle import compact_cycle
from build_c898_pair_fan_pilot import cramer, direction, axis_key, target_constant
from build_c898_cached_pair_pilot import vertex, ref_text

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'evidence/proposals/C898CyclicContexts'
LEAN = Path('Compact/Cases/C898/CachedPairs')


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def begin(imports):
    return [*[f'import {module}' for module in imports], '',
            'set_option Elab.async false', 'set_option maxRecDepth 10000', '',
            'namespace N12Compact.C898Cached.AllPairs',
            'open C898Shared CachedSupportFan S12', 'noncomputable section', '']


def finish(lines):
    return '\n'.join(lines + ['', 'end', 'end N12Compact.C898Cached.AllPairs', ''])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--raw-numeric', action='store_true',
                        help='also materialize routeNRaw for the existing raw pair interface')
    args = parser.parse_args()
    need(args.run, 'parent bounded slot and explicit --run required')
    stage = DEST.with_name(DEST.name + '.staging')
    need(not DEST.exists() and not stage.exists(), 'refusing an existing proposal')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        need(time.monotonic() - started < 115 and rss < 256 * 1024**2,
             '115-second/256-MiB guard reached')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    input_hashes = {}

    def load(name):
        path = ROOT / name
        raw = path.read_bytes()
        input_hashes[name] = digest(raw)
        return json.loads(raw)

    try:
        data = load('evidence/c898-shared-pose-map.json')
        audit = load('evidence/c898-support-fan-counts.json')
        record_doc = load('evidence/c898-pair-record-map.json')
        plan_doc = load('evidence/c898-pair-pruning-plan-map.json')
        domain_doc = load('evidence/c898-domain-map.json')
        previous = load('evidence/c898-all-cached-pairs.json')
        need(input_hashes['evidence/c898-shared-pose-map.json'] ==
             audit['source_pose_map_sha256'], 'support audit refers to another pose bank')
        for label, name in [('poses', 'c898-shared-pose-map.json'),
                            ('fans', 'c898-support-fan-counts.json'),
                            ('records', 'c898-pair-record-map.json'),
                            ('plans', 'c898-pair-pruning-plan-map.json'),
                            ('domains', 'c898-domain-map.json')]:
            need(previous['input_sha256'][label] == input_hashes['evidence/' + name],
                 'cached context route manifest is stale: ' + label)
        references_path = ROOT / 'Compact/Cases/C898/References.lean'
        references_raw = references_path.read_bytes()
        input_hashes[str(references_path.relative_to(ROOT))] = digest(references_raw)
        need(previous['references_sha256'] == digest(references_raw),
             'cached route references differ')
        refs = [tuple(map(int, match)) for match in re.findall(
            r'⟨(-?\d+), (-?\d+), (\d+), (-?\d+), (\d+)⟩,', references_raw.decode())]
        need(len(refs) == 64, 'the original 64 reference frames are required')
        directions = [direction(key, refs) for key in range(256)]
        rows, poses, blocks = data['rows'], data['poses'], data['blocks']
        records, plans = record_doc['records'], plan_doc['plans']
        need(len(records) == 25843, 'original pair count changed')
        stages = {int(key): value for key, value in domain_doc['pair_steps'].items()}
        need(len(stages) == 13 and 14 in stages, 'original stage scope changed')
        contexts = {context['id']: context for context in audit['contexts']}
        by_rows = {tuple(context['rows']): context['id'] for context in audit['contexts']}
        routes, route_ids, requests = [], {}, defaultdict(set)
        grouped = defaultdict(list)

        def route(pose, block):
            key = pose, block
            if key not in route_ids:
                inputs = ([] if block is None else blocks[block]['rows']) + poses[pose]['rows']
                context = by_rows[tuple(sorted(set(inputs)))]
                route_ids[key] = len(routes)
                routes.append({'pose': pose, 'block': block, 'angle': poses[pose]['angle'],
                               'context': context, 'inputs': inputs})
            return route_ids[key]

        for record in records:
            if record['step'] == 14:
                continue
            source = route(record['source'], record['block'])
            neighbor = route(record['neighbor'], None)
            grouped[record['step']].append((record, source, neighbor))
            a, b = routes[source], routes[neighbor]
            for axis in range(8):
                key = axis_key(a['angle'], b['angle'], axis)
                requests[a['context']].add(key)
                requests[b['context']].add((key + 128) % 256)
        need(routes == previous['routes'], 'route identifiers or original inputs changed')
        need(len(requests) == previous['contexts'] == 1002,
             'the exact 1002 nonterminal context scope changed')

        # Check the complete source-plan x actual-neighbor products before
        # replacing any representation; no records may vanish in filtering.
        for step, (source_domain, neighbor_domain, _) in sorted(stages.items()):
            if step == 14:
                continue
            selected = sorted((plan for plan in plans if plan['step'] == step),
                              key=lambda plan: plan['pose'])
            need([plan['source'] for plan in selected] == domain_doc['domains'][source_domain],
                 f'step{step}: original source cover mismatch')
            need(all(plan['neighbors_name'] == neighbor_domain for plan in selected),
                 f'step{step}: original neighbor cover mismatch')
            expected = [(plan['source'], neighbor, plan['block'])
                        for plan in selected if plan['block'] is not None
                        for neighbor in domain_doc['domains'][neighbor_domain]]
            actual = [(record['source'], record['neighbor'], record['block'])
                      for record, _, _ in sorted(grouped[step], key=lambda item: item[0]['index'])]
            need(expected == actual, f'step{step}: incomplete Cartesian pair coverage')

        cycles, fans, fallbacks, old_entries_count = {}, {}, {}, 0
        for cid, requested in sorted(requests.items()):
            guard()
            old_entries = []
            for key in sorted(requested):
                x, y = directions[key]
                candidates = []
                for first, second in contexts[cid]['bases']:
                    need(first in contexts[cid]['rows'] and second in contexts[cid]['rows'],
                         f'context{cid}: original support row not in original inputs')
                    value = cramer(rows[first], rows[second], x, y)
                    if value is not None:
                        candidates.append((Fraction(value[3], value[2]), not value[4],
                                           first, second))
                need(bool(candidates), f'context{cid}: missing original key{key}')
                _, _, first, second = min(candidates)
                if not old_entries or old_entries[-1][1:3] != [first, second]:
                    old_entries.append([key if old_entries else 0, first, second,
                                        *vertex(rows[first], rows[second])])
            old_entries_count += len(old_entries)
            candidate = compact_cycle(rows, old_entries, directions, requested)
            if candidate['cycle'] is None:
                fallbacks[cid] = candidate['reason']
                fans[cid] = old_entries
            else:
                cycles[cid], fans[cid] = candidate['cycle'], candidate['entries']
            need(len(fans[cid]) < 65536, '16-step binary lookup bound exceeded')
        starts = {cid: [entry[0] for entry in entries] for cid, entries in fans.items()}

        def select(cid, key):
            return fans[cid][max(0, bisect_right(starts[cid], key) - 1)]

        # Replay all actual axis arithmetic after cycle substitution. The
        # dominance check above is useful but is not used to skip this audit.
        pairs_checked = axes_checked = 0
        for step in sorted(grouped):
            for record, source, neighbor in grouped[step]:
                a, b = routes[source], routes[neighbor]
                for axis in range(8):
                    key = axis_key(a['angle'], b['angle'], axis)
                    A = select(a['context'], key)
                    B = select(b['context'], (key + 128) % 256)
                    x, y = directions[key]
                    left = cramer(rows[A[1]], rows[A[2]], x, y)
                    right = cramer(rows[B[1]], rows[B[2]], -x, -y)
                    need(left is not None and right is not None,
                         f'{record["name"]}: cycle lost actual cone{axis}')
                    scale, constant = target_constant(refs[a['angle']], refs[b['angle']], x, y)
                    lhs = scale * (left[3] * right[2] + right[3] * left[2])
                    rhs = left[2] * right[2] * constant
                    need(lhs < rhs or lhs == rhs and (left[4] or right[4]),
                         f'{record["name"]}: cycle lost strict overlap axis{axis}')
                    axes_checked += 1
                pairs_checked += 1
            guard()
        need(pairs_checked == 25419 and axes_checked == 203352,
             'not every nonterminal original pair/axis was checked')
        need(sum(record['step'] == 14 for record in records) == 424,
             'accepted terminal pair scope changed')

        outputs = {}
        lines = begin(['Compact.Cases.C898.CachedPairFan', 'Compact.Core.BoundaryFanSyntax'])
        lines += ['def cyclicDirections : Array ReferenceAxis.Direction := #[']
        lines += [f'  ⟨{x},{y},1⟩,' for x, y in directions]
        lines += [']']
        outputs[str(LEAN / 'CyclicDirections.lean')] = finish(lines)
        by_context = defaultdict(list)
        for rid, item in enumerate(routes):
            by_context[item['context']].append(rid)
        ordered = sorted(fans)
        for chunk in range((len(ordered) + 63) // 64):
            chosen = ordered[chunk * 64:(chunk + 1) * 64]
            route_order = [rid for cid in chosen for rid in by_context[cid]]
            lines = begin(['Compact.Cases.C898.CachedPoseRecipe',
                           'Compact.Cases.C898.CachedPairs.CyclicDirections',
                           'Compact.Core.BasisMaterializeSyntax',
                           'Compact.Core.FiniteCheckChunks'])
            for cid in chosen:
                # Only .entries is used. Membership is checked against each
                # actual recipe input list, never against an invented polygon.
                if cid in cycles:
                    reference = refs[routes[by_context[cid][0]]['angle']]
                    cycle = '[' + ','.join(map(str, cycles[cid])) + ']'
                    lines += [f'def fan{cid} : Array (Entry rowCount) :=',
                              f'  (materialize_boundary_fan% (BoundaryFan.context rows [] {ref_text(reference)}',
                              f'    cyclicDirections {cycle})).entries', '']
                else:
                    lines += [f'/-- Exact original support fan retained: {fallbacks[cid]}. -/',
                              f'def fan{cid} : Array (Entry rowCount) := #[']
                    for key, first, second, _, _, _ in fans[cid]:
                        lines += [f'  ⟨{key},{first},{second},materialize_basis% '
                                  f'VertexSupport.Basis.fromRowsPrimitive (rows {first}) (rows {second})⟩,']
                    lines += [']', '']
            prefix = f'cyclicRecipes{chunk:02}'
            lines += [f'def {prefix} : Array ContextRecipe := #[']
            for rid in route_order:
                item = routes[rid]
                block = 'none' if item['block'] is None else f'some {item["block"]}'
                lines += [f'  ⟨{item["pose"]},{block},{item["angle"]},'
                          f'{ref_text(refs[item["angle"]])},fan{item["context"]}⟩,']
            size = len(route_order)
            lines += [']', '', f'def {prefix}Get (i : Fin {size}) : ContextRecipe :=',
                      f"  {prefix}[i.val]'(by change i.val < {size}; exact i.isLt)", '']
            count = (size + 7) // 8
            for block in range(count):
                lines += [f'theorem {prefix}_batch{block} :',
                          f'    FiniteCheckChunks.Check (fun i : Fin {size} => ({prefix}Get i).Check) {block} := by',
                          '  decide +kernel', '']
            lines += [f'theorem {prefix}_checked (i : Fin {size}) : ({prefix}Get i).Check := by',
                      f'  refine FiniteCheckChunks.sound (fun j : Fin {size} => ({prefix}Get j).Check)',
                      f'    (count := {count}) (by decide) ?_ i',
                      '  intro block', '  fin_cases block']
            lines += [f'  · exact {prefix}_batch{block}' for block in range(count)]
            lines += ['']
            for local, rid in enumerate(route_order):
                lines += [f'def route{rid} : PoseContext :=',
                          f'  ({prefix}Get {local}).certify ({prefix}_checked {local})']
                if args.raw_numeric:
                    lines += [f'def route{rid}Raw : RawSupportFan.Context :=',
                              f'  materialize_raw_fan% (route{rid}.context.numeric)',
                              f'theorem route{rid}Raw_exact : route{rid}Raw = route{rid}.context.numeric := rfl']
            outputs[str(LEAN / f'Contexts{chunk:02}.lean')] = finish(lines)
        need(sum(len(source.encode()) for source in outputs.values()) < 8 * 1024**2,
             '8-MiB output cap exceeded')
        report = {'scope': 'Exact cycle substitution proposal; Lean acceptance pending',
                  'lean_checked': False, 'whole_case_proved': False,
                  'contexts': len(fans), 'cyclic_contexts': len(cycles), 'routes': len(routes),
                  'original_nonterminal_pairs': pairs_checked, 'axes_checked': axes_checked,
                  'accepted_terminal_pairs_unchanged': 424,
                  'cycle_fallbacks': len(fallbacks), 'fallback_reasons': fallbacks,
                  'old_fan_entries': old_entries_count,
                  'boundary_row_ids': sum(map(len, cycles.values())),
                  'derived_entries': sum(map(len, fans.values())),
                  'raw_numeric': args.raw_numeric, 'input_sha256': input_hashes,
                  'lean_modules': len(outputs),
                  'lean_lines': sum(source.count('\n') for source in outputs.values()),
                  'lean_bytes': sum(len(source.encode()) for source in outputs.values()),
                  'outputs': {name: {'sha256': digest(source.encode()),
                                    'lines': source.count('\n'), 'bytes': len(source.encode())}
                              for name, source in outputs.items()},
                  'remaining': ['All emitted recipe and pair checks in Lean',
                                'Original pruning/relaxation, entrance and final case replay'],
                  'seconds': time.monotonic() - started}
        stage.mkdir(parents=True)
        for name, source in outputs.items():
            guard()
            path = stage / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        (stage / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        stage.rename(DEST)
        print(json.dumps({key: value for key, value in report.items()
                          if key not in ('outputs', 'input_sha256')}, indent=2))
    except BaseException:
        if stage.exists():
            shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
