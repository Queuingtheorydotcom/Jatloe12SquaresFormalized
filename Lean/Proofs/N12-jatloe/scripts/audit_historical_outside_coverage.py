#!/usr/bin/env python3
"""Audit every whole first-failed-face context of the six current pair routes.

Parent-only serial 256 MiB / 120 second slot; four MiB total output. This is
exact integer certificate discovery, not Lean acceptance or a case exclusion.
No compiler, source mutation, subprocess, floating point, or inferred empty
branch. Every target row needs a 0/1/2-row implication; a closed branch needs
an explicit at-most-three-row strict Farkas witness. Unsupported whole-context
coverage remains a gap even when the old subdivision may prove it.

The output records direct final target IDs and sparse local hint positions.
Omitted hints mean literal row copies, reconstructed by first occurrence.
All source contexts are derived in the precise outsideRows order, including
strict opposite rows that have no existing global row identifier.
"""
from collections import Counter, OrderedDict, defaultdict
from itertools import combinations
from math import gcd
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

from audit_historical_bank_reachability import JSONStream

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/historical-compact-data'
CASES = (701, 713, 717, 973, 978, 979)
OUTPUT_CAP = 4 * 1024**2


class BudgetStop(RuntimeError):
    pass


def need(test, message):
    if not test:
        raise ValueError(message)


def opposite(row):
    return (-row[0], -row[1], -row[2], not row[3])


def normalized(row):
    divisor = gcd(gcd(abs(row[0]), abs(row[1])), abs(row[2])) or 1
    return (row[0] // divisor, row[1] // divisor, row[2] // divisor, row[3])


def pair_hint(a, b, target):
    ax, ay, ac, ast = a
    bx, by, bc, bst = b
    tx, ty, tc, tst = target
    determinant = ax * by - ay * bx
    if not determinant:
        return False
    sign = 1 if determinant > 0 else -1
    left = sign * (tx * by - ty * bx)
    right = sign * (ax * ty - ay * tx)
    if left < 0 or right < 0:
        return False
    slack = abs(determinant) * tc - left * ac - right * bc
    return slack >= 0 and (not tst or slack > 0 or
                           left > 0 and ast or right > 0 and bst)


def single_hint(source, target):
    sx, sy, sc, strict = source
    tx, ty, tc, target_strict = target
    pivot, component = (sx, tx) if sx else (sy, ty)
    if not pivot:
        return False
    scale = abs(pivot)
    weight = component if pivot > 0 else -component
    slack = scale * tc - weight * sc
    return weight >= 0 and weight * sx == scale * tx and weight * sy == scale * ty and \
        slack >= 0 and (not target_strict or slack > 0 or weight > 0 and strict)


class Context:
    """Local positions are retained even when equal source rows repeat."""
    def __init__(self, rows):
        self.rows = tuple(rows)
        self.positions = {}
        for i, row in enumerate(self.rows):
            self.positions.setdefault(row, i)
        self.unique = tuple(self.positions.values())
        self.hints = {}

    def hint(self, target):
        if target in self.positions:
            return ('copy', self.positions[target])
        if target in self.hints:
            return self.hints[target]
        result = None
        if target[:2] == (0, 0) and target[2] >= 0 and (not target[3] or target[2] > 0):
            result = (0,)
        if result is None:
            result = next(((1, i) for i in self.unique if single_hint(self.rows[i], target)), None)
        if result is None:
            result = next(((2, i, j) for i, j in combinations(self.unique, 2)
                           if pair_hint(self.rows[i], self.rows[j], target)), None)
        self.hints[target] = result
        return result

    def cover(self, target):
        sparse = []
        for position, row in enumerate(target):
            hint = self.hint(row)
            if hint is None:
                return None, position
            if hint[0] != 'copy':
                sparse.append((position,) + hint)
        return sparse, None

    def empty(self):
        def valid(indices, weights):
            if not any(weights) or any(w < 0 for w in weights):
                return None
            values = [sum(w * self.rows[i][j] for i, w in zip(indices, weights)) for j in range(3)]
            strict = any(w > 0 and self.rows[i][3] for i, w in zip(indices, weights))
            if values[:2] != [0, 0] or not (values[2] < 0 or values[2] == 0 and strict):
                return None
            divisor = 0
            for weight in weights:
                divisor = gcd(divisor, weight)
            return [(i, w // divisor) for i, w in zip(indices, weights) if w]
        for i in self.unique:
            witness = valid((i,), (1,))
            if witness:
                return witness
        for i, j in combinations(self.unique, 2):
            a, b = self.rows[i], self.rows[j]
            pivot = 0 if a[0] or b[0] else 1
            witness = valid((i, j), (abs(b[pivot]), abs(a[pivot])))
            if witness:
                return witness
        for i, j, k in combinations(self.unique, 3):
            a, b, c = self.rows[i], self.rows[j], self.rows[k]
            weights = (b[0]*c[1]-b[1]*c[0], c[0]*a[1]-c[1]*a[0], a[0]*b[1]-a[1]*b[0])
            witness = valid((i, j, k), weights) or valid((i, j, k), tuple(-w for w in weights))
            if witness:
                return witness
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--output', default='evidence/historical-outside-coverage')
    args = parser.parse_args()
    need(args.run, 'prepared only; parent serial slot and --run required')
    output = (ROOT / args.output).resolve()
    need(output.is_relative_to(ROOT / 'evidence'), 'output must remain under evidence')
    stage = output.with_name(output.name + '.staging')
    need(not output.exists() and not stage.exists(), 'refusing existing audit output')
    started = time.monotonic()
    provenance, counts, case_counts, failures = {}, Counter(), {}, []
    failure_hash = hashlib.sha256()
    link_witness_hash = hashlib.sha256()
    report = {'status': 'incomplete', 'scope': list(CASES), 'completed_cases': [],
              'certificate_status': 'Exact integer audit only; all new Lean checks remain pending.'}
    written = 0
    current = {'phase': 'load'}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        if rss >= 256 * 1024**2 or time.monotonic() - started >= 114:
            raise BudgetStop('256 MiB / 114-second working limit; only completed records retained')

    def stop(*_):
        raise BudgetStop('termination requested; only completed records retained')

    def authenticate(path, expected=None):
        value = hashlib.sha256()
        with path.open('rb') as stream:
            for block in iter(lambda: stream.read(65536), b''):
                guard()
                value.update(block)
        actual = value.hexdigest()
        need(expected is None or actual == expected, 'authenticated input changed: ' + str(path))
        provenance[str(path.relative_to(ROOT))] = actual

    def load(path, expected=None):
        authenticate(path, expected)
        need(path.stat().st_size <= 16 * 1024**2, 'metadata load exceeds16MiB')
        with path.open() as stream:
            result = json.load(stream)
        guard()
        return result

    def entries(path, expected):
        authenticate(path, expected)
        stream = JSONStream(path, guard)
        try:
            yield from stream.array()
            need(stream.peek() is None, 'trailing JSON content')
        finally:
            stream.file.close()

    def record_failure(failure):
        raw = json.dumps(failure, separators=(',', ':')).encode()
        failure_hash.update(raw + b'\n')
        counts['unsupported_branches'] += 1
        if len(failures) < 100:
            failures.append(failure)

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    stage.mkdir(parents=True)
    outcome_path = stage / 'branches.jsonl'
    try:
        with outcome_path.open('wb') as outcomes:
            def emit(value):
                nonlocal written
                raw = json.dumps(value, separators=(',', ':')).encode() + b'\n'
                if written + len(raw) >= OUTPUT_CAP - 512 * 1024:
                    raise BudgetStop('four MiB output budget; completed branch records retained')
                outcomes.write(raw)
                written += len(raw)

            try:
                manifest = load(BASE / 'manifest.json')
                need(manifest['status'].startswith('data assembled') and tuple(manifest['scope']) == CASES,
                     'wrong or incomplete authenticated extraction')
                expected = {item['path']: item['sha256'] for item in manifest['output_files']}
                quantities = manifest['unique_objects']
                rows = []
                for row in entries(BASE / 'rows.json', expected['rows.json']):
                    need(row['index'] == len(rows) and row['denominator'] > 0, 'invalid row record')
                    need(type(row['strict']) is bool and len(row['integers']) == 3, 'invalid integer row')
                    rows.append(tuple(row['integers']) + (row['strict'],))
                poses = []
                for pose in entries(BASE / 'poses.json', expected['poses.json']):
                    need(pose['index'] == len(poses) and 0 <= pose['angle'] < 192, 'invalid pose')
                    need(all(0 <= r < len(rows) for r in pose['rows']), 'invalid pose row ID')
                    poses.append((pose['angle'], tuple(pose['rows'])))
                blocks = []
                for block in entries(BASE / 'blocks.json', expected['blocks.json']):
                    need(block['index'] == len(blocks) and all(0 <= r < len(rows) for r in block['rows']),
                         'invalid block ID')
                    blocks.append(tuple(block['rows']))
                links = []
                for link in entries(BASE / 'links.json', expected['links.json']):
                    need(link['index'] == len(links) and all(0 <= link[key] < len(poses) for key in ('source', 'target')),
                         'invalid retained link')
                    links.append((link['source'], link['target']))
                need((len(rows), len(poses), len(blocks), len(links)) ==
                     tuple(quantities[k] for k in ('row', 'pose', 'block', 'link')), 'dictionary count mismatch')
                current['phase'] = 'outside contexts'
                selected_links, pair_steps = set(), set()
                # Small bounded cache only; global pose lists themselves remain compact IDs.
                contexts = OrderedDict()
                def context(values):
                    values = tuple(values)
                    found = contexts.get(values)
                    if found is not None:
                        contexts.move_to_end(values)
                        return found
                    result = Context(values)
                    contexts[values] = result
                    if len(contexts) > 128:
                        contexts.popitem(last=False)
                    return result

                for case in CASES:
                    data = load(BASE / f'C{case}.json', expected[f'C{case}.json'])
                    need(data['case'] == case, 'case identity differs')
                    cc = Counter()
                    case_counts[case] = cc
                    stage_plans = defaultdict(list)
                    for ordinal, plan in enumerate(data['plans']):
                        stage_plans[plan['step']].append((ordinal, plan))
                    need(set(map(int, data['pair_steps'])) == set(stage_plans), 'pair-stage scope mismatch')
                    for step, names in data['pair_steps'].items():
                        step = int(step)
                        source_name, neighbor_name, target_name = names
                        source_domain, neighbor_domain, target_domain = [data['domains'][name] for name in names]
                        original_plans = stage_plans[step]
                        need([p['source'] for _, p in original_plans] == source_domain,
                             f'C{case} step{step}: source order/coverage differs')
                        pair_steps.add((case, step))
                        cc['pair_stages'] += 1
                        target_members = set(target_domain)
                        for ordinal, plan in original_plans:
                            guard()
                            current = {'phase': 'outside contexts', 'case': case, 'step': step, 'plan': ordinal}
                            need(plan['case'] == case and plan['step'] == step, 'wrong plan occurrence')
                            need(data['domains'][plan['neighbors_name']] == neighbor_domain,
                                 'complete original neighbor domain differs')
                            need(all(t in target_members for t in plan['targets']), 'outgoing target outside stage')
                            need([links[i][0] for i in plan['links']] == plan['pieces'], 'raw-piece/link order differs')
                            need(all(links[i][1] in plan['targets'] for i in plan['links']), 'link target outside plan')
                            selected_links.update(plan['links'])
                            source = plan['source']
                            angle, source_ids = poses[source]
                            need(all(poses[p][0] == angle for p in plan['pieces'] + plan['targets']),
                                 'original plan changes angle')
                            block = plan['block']
                            need(block is None or 0 <= block < len(blocks), 'block outside dictionary')
                            need(plan['historical_pair_count'] == (len(neighbor_domain) if block is not None else 0),
                                 'original pair witness scope differs')
                            old_pieces = [(pid, tuple(rows[r] for r in poses[pid][1])) for pid in plan['pieces']]
                            literal = defaultdict(list)
                            normal = defaultdict(list)
                            unordered = defaultdict(list)
                            for pid, values in old_pieces:
                                literal[values].append(pid)
                                forms = tuple(map(normalized, values))
                                normal[forms].append(pid)
                                unordered[tuple(sorted(forms))].append(pid)
                            inputs = tuple(rows[r] for r in source_ids)
                            branches = [(0, inputs)] if block is None else []
                            if block is not None:
                                for position, rid in enumerate(blocks[block]):
                                    branches.append((position, (opposite(rows[rid]),) + inputs))
                                    inputs = (rows[rid],) + inputs
                            counts['plans'] += 1
                            cc['plans'] += 1
                            if not plan['pieces']:
                                cc['zero_piece_plans'] += 1
                            if block is not None and not blocks[block]:
                                cc['empty_block_conjunction_plans'] += 1
                            covered_raw_pieces = set()
                            complete_plan = True
                            for face, values in branches:
                                current['face'] = face
                                guard()
                                local = context(values)
                                cc['outside_branches'] += 1
                                counts['outside_branches'] += 1
                                exact = literal.get(values, [])
                                scaled = normal.get(tuple(map(normalized, values)), [])
                                permuted = unordered.get(tuple(sorted(map(normalized, values))), [])
                                match = 'literal_raw_piece' if exact else 'scaled_ordered_raw_piece' if scaled else \
                                    'scaled_permuted_raw_piece' if permuted else 'no_equal_raw_piece'
                                cc[match] += 1
                                covered_raw_pieces.update(exact or scaled or permuted)
                                priorities = [links[i][1] for i in plan['links'] if links[i][0] in (exact or scaled or permuted)]
                                candidates = list(dict.fromkeys(priorities + plan['targets']))
                                selected, missing = None, []
                                for target in candidates:
                                    hints, bad = local.cover(tuple(rows[r] for r in poses[target][1]))
                                    if hints is not None:
                                        selected = (target, hints)
                                        break
                                    if len(missing) < 8:
                                        missing.append([target, bad, poses[target][1][bad]])
                                if selected is not None:
                                    target, hints = selected
                                    emit([case, ordinal, face, 0, target, hints])
                                    cc['direct_final_target'] += 1
                                    counts['direct_final_target'] += 1
                                    cc['noncopy_hint_occurrences'] += len(hints)
                                else:
                                    empty = local.empty()
                                    if empty is not None:
                                        emit([case, ordinal, face, 1, empty])
                                        cc['checked_empty'] += 1
                                        counts['checked_empty'] += 1
                                    else:
                                        complete_plan = False
                                        # This can reveal an old subdivision, but it is not a
                                        # proof that its union covers this entire new context.
                                        implications = []
                                        for pid, old_rows in old_pieces:
                                            hints, _ = local.cover(old_rows)
                                            if hints is not None:
                                                implications.append(pid)
                                        failure = {'case': case, 'step': step, 'plan': ordinal,
                                            'name': plan['name'], 'origin': plan['origin'], 'face': face,
                                            'block': block, 'source': source, 'raw_pieces': plan['pieces'],
                                            'targets': plan['targets'], 'first_unsupported_rows': missing,
                                            'implied_old_pieces': implications,
                                            'reason': 'No single final target or <=3-row contradiction certified; retain original subdivision.'}
                                        record_failure(failure)
                                        emit([case, ordinal, face, 2])
                                        cc['unsupported_branches'] += 1
                            cc['complete_plans' if complete_plan else 'plans_requiring_original_subdivision'] += 1
                            cc['raw_piece_occurrences'] += len(plan['pieces'])
                            cc['raw_piece_ids_without_equal_outside_context'] += len(set(plan['pieces']) - covered_raw_pieces)
                    report['completed_cases'].append(case)
                need(len(pair_steps) == 113, 'complete pair-stage count differs from authenticated scope')
                counts['pair_stages'] = len(pair_steps)
                counts['selected_pair_links'] = len(selected_links)
                counts['retained_links_total'] = len(links)
                report['all_outside_contexts_visited'] = True
                current = {'phase': 'all retained original relaxation links'}
                link_failures = []
                for index, (source, target) in enumerate(links):
                    current['link'] = index
                    guard()
                    need(poses[source][0] == poses[target][0], 'retained relaxation changes angle')
                    local = context(tuple(rows[r] for r in poses[source][1]))
                    hints, missing = local.cover(tuple(rows[r] for r in poses[target][1]))
                    counts['retained_links_visited'] += 1
                    if hints is None:
                        counts['unsupported_retained_links'] += 1
                        if len(link_failures) < 100:
                            link_failures.append({'link': index, 'source': source, 'target': target,
                                                  'target_position': missing, 'target_row': poses[target][1][missing]})
                    else:
                        counts['retained_links_with_exact_hints'] += 1
                        link_witness_hash.update(json.dumps([index, hints], separators=(',', ':')).encode() + b'\n')
                report['retained_link_failure_samples'] = link_failures
                report['all_retained_links_visited'] = True
                report['status'] = 'complete exact audit; unresolved branches retained' if counts['unsupported_branches'] or \
                    counts['unsupported_retained_links'] else 'complete exact audit; all direct branches certified; Lean replay pending'
            except BudgetStop as stopped:
                signal.setitimer(signal.ITIMER_REAL, 0)
                report['status'] = 'partial audit; resource/output limit reached'
                report['stopped_because'] = str(stopped)
        signal.setitimer(signal.ITIMER_REAL, 0)
        report.update({'last_position': current, 'counts': dict(counts),
            'case_counts': {str(case): dict(value) for case, value in case_counts.items()},
            'failure_samples': failures, 'all_failure_records_sha256': failure_hash.hexdigest(),
            'successful_link_witnesses_sha256': link_witness_hash.hexdigest(),
            'input_sha256': provenance,
            'outside_semantics': 'opposite(current row) :: reversed(true prefix) ++ original source rows; strictness is flipped',
            'branch_record_schema': {'keep': '[case, planOrdinal, face, 0, targetPoseId, sparseHints]',
                'close': '[case, planOrdinal, face, 1, [[localRowPosition, positiveWeight],...]]',
                'unresolved': '[case, planOrdinal, face, 2]',
                'sparseHints': '[targetRowPosition, 0] constant; [...,1,sourcePosition] single; [...,2,left,right] pair; omitted positions are exact copies'},
            'strict_complement_ids': 'Never required: complements are exact derived Row values.',
            'trust_boundary': 'Authenticated compact extraction and exact integer arithmetic; no historical subtree omitted on failure; numerical audit is not a Lean theorem.',
            'elapsed_seconds': time.monotonic() - started,
            'peak_rss_bytes': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)})
        report['branches_sha256'] = hashlib.sha256(outcome_path.read_bytes()).hexdigest()
        report['branches_bytes'] = outcome_path.stat().st_size
        raw = (json.dumps(report, indent=2) + '\n').encode()
        need(len(raw) + outcome_path.stat().st_size < OUTPUT_CAP, 'final audit exceeds four MiB')
        (stage / 'manifest.json').write_bytes(raw)
        stage.rename(output)
        print(json.dumps({key: report[key] for key in ('status', 'counts', 'elapsed_seconds', 'peak_rss_bytes')}))
    except BaseException:
        shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
