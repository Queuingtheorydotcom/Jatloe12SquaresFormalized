#!/usr/bin/env python3
"""Bounded, authenticated source inventory; explicit --run is required.

Reads gzip sources in place and the existing raw vendor fallback. Never writes
Lean, invokes Lean, runs recovered programs, or expands an archive to disk.
The counts are exact within the reported completed scope, not a global theorem
or an inferred bound on the unfinished proof. SQLite deduplication compares full
canonical values, not truncated hashes.
"""
from provenance_source import read_bytes, read_text, text_stream
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import argparse
import gzip
import hashlib
import heapq
import json
import math
import re
import resource
import signal
import sqlite3
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CASES = (701, 713, 717, 898, 973, 978, 979)
DECL = re.compile(r'^(?:noncomputable )?(?:def|theorem|lemma) (\w+)', re.M)
EXPLICIT_ROW = re.compile(r'⟨⟨!\[([^,\]]+),([^\]]+)\],([^⟩]+)⟩,(true|false)⟩')


class Limit(Exception):
    pass


def classify_declaration(text):
    """Fixed vocabulary: no declaration names or proposition-specific keys."""
    head = text.split(':=', 1)[0]
    prefix = 'theorem' if re.match(r'(?:theorem|lemma)\b', text) else 'definition'
    categories = (
        ('PoseLeaf', 'pose'), ('PoseRoot', 'pose_root'),
        ('AngleEnclosure', 'angle'), ('RegionTree', 'region_tree'),
        ('RelaxationLink', 'relaxation'), ('Pruning', 'pruning'),
        ('Chord', 'chord'), ('Farkas', 'farkas'),
        ('LinearConstraint', 'linear_constraint'), ('LocalQuery', 'local_query'),
        ('DomainSpec', 'domain'), ('OwnedHullPoint', 'hull_point'),
    )
    for token, category in categories:
        if token in head:
            return prefix + '/' + category
    if prefix == 'theorem':
        return 'theorem/check' if '.Check' in head or '_checked' in head else 'theorem/other'
    if re.search(r':\s*(?:List|Array|Finset)\b', head):
        return 'definition/finite_data'
    return 'definition/other'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', action='store_true', help='required explicit execution flag')
    ap.add_argument('--seconds', type=int, default=120)
    ap.add_argument('--memory-mib', type=int, default=256)
    ap.add_argument('--scratch-mib', type=int, default=64)
    ap.add_argument('--verify-pairs', action='store_true',
                    help='second pass: check every recognized original pair witness and reconstruct supports')
    ap.add_argument('--output', default='evidence/seven-source-inventory.json')
    args = ap.parse_args()
    if not args.run:
        ap.error('Prepared only. Pass --run after recovery is stable and the compute slot is granted.')
    assert 1 <= args.seconds <= 600 and 32 <= args.memory_mib <= 384
    assert 8 <= args.scratch_mib <= 256
    started = time.monotonic()
    out = ROOT / args.output
    scratch = out.with_suffix('.scratch.sqlite')
    assert not scratch.exists(), f'refusing to overwrite {scratch}'
    report = {'scope': 'Receipt-matched original accepted-seven source union only; no fresh Lean acceptance.',
              'global_under_1m_bound_established': False,
              'assembly_under_300k_bound_established': False,
              'status': 'incomplete', 'limits': vars(args), 'files': [], 'missing': [],
              'unsupported': [], 'pair_failures': [], 'deduplication': 'full canonical value comparison',
              'caveat': 'Structural data counts exclude unconverted coverage/entry/terminal adapters; no leaf extrapolation.'}
    counts = Counter()
    kinds = Counter()
    untranslated_kinds = Counter()
    largest_untranslated = []
    expected, owners = {}, {}
    for case in CASES:
        receipt = json.loads((ROOT / f'evidence/inherited/evidence/C{case}/case-replay.json').read_text())
        for module, sha in receipt['local_source_sha256'].items():
            if module.startswith('S12.'):
                assert expected.setdefault(module, sha) == sha
                owners.setdefault(module, []).append(case)
    report['expected_modules'] = len(expected)
    report['receipt_cases'] = list(CASES)

    def guard(*_):
        if time.monotonic() - started > args.seconds:
            raise Limit('wall-clock cap reached')
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if rss > args.memory_mib * 1024**2:
            raise Limit('RSS cap reached')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.2, 0.2)
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(Limit('termination requested')))
    db = sqlite3.connect(scratch)
    db.execute('PRAGMA page_size=4096')
    db.execute(f'PRAGMA max_page_count={args.scratch_mib * 256}')
    db.execute('PRAGMA journal_mode=OFF')
    db.execute('PRAGMA cache_size=-8192')
    db.execute('PRAGMA temp_store=FILE')
    db.execute('CREATE TABLE objects (kind TEXT, value TEXT, ident INTEGER, PRIMARY KEY(kind,value)) WITHOUT ROWID')
    db.execute('CREATE TABLE names (name TEXT PRIMARY KEY, kind TEXT, ident INTEGER, value TEXT) WITHOUT ROWID')
    db.execute('CREATE TABLE row_rays (row_id INTEGER PRIMARY KEY, ray_id INTEGER)')
    sequences = Counter()

    def intern(kind, value):
        value = json.dumps(value, separators=(',', ':'))
        prior = db.execute('SELECT ident FROM objects WHERE kind=? AND value=?', (kind, value)).fetchone()
        if prior:
            return prior[0]
        index = sequences[kind]
        sequences[kind] += 1
        db.execute('INSERT INTO objects VALUES (?,?,?)', (kind, value, index))
        return index

    @lru_cache(maxsize=8192)
    def intern_row(fields):
        assert len(fields) == 4
        values = [Q(t.replace('(', '').replace(')', '').strip()) for t in fields[:3]]
        assert fields[3] in ('0', '1', 'false', 'true')
        strict = fields[3] in ('1', 'true')
        identity = intern('row', [str(q) for q in values] + [strict])
        denominator = math.lcm(*(q.denominator for q in values))
        numerators = [int(q * denominator) for q in values]
        divisor = math.gcd(*numerators)
        # gcd is nonnegative. Never flip the ray or discard strictness.
        primitive = [n // divisor for n in numerators] if divisor else [0, 0, 0]
        ray = intern('primitive_row', primitive + [strict])
        db.execute('INSERT OR IGNORE INTO row_rays VALUES (?,?)', (identity, ray))
        return identity

    def row(fields):
        return intern_row(tuple(fields))

    @lru_cache(maxsize=8192)
    def row_ray(index):
        return db.execute('SELECT ray_id FROM row_rays WHERE row_id=?', (index,)).fetchone()[0]

    @lru_cache(maxsize=8192)
    def ray_value(index):
        value = db.execute('SELECT value FROM objects WHERE kind=? AND ident=?', ('primitive_row', index)).fetchone()
        return tuple(json.loads(value[0]))

    def rows(text):
        return [row(t.split(',')) for t in text.split(';')] if text else []

    def terms(text):
        result = []
        for term in text.split(';'):
            fields = term.split(',')
            assert len(fields) == 5
            result.append((str(Q(fields[0])), row(fields[1:])))
        counts['weighted_row_occurrences'] += len(result)
        return intern('weighted_rows', result)

    empty_basis_sizes = Counter()
    empty_failures = []

    def empty_basis(text):
        """Try only cited rows; validate the new certificate over exact integers."""
        active = []
        old_terms = []
        for term in text.split(';'):
            fields = term.split(',')
            weight = Q(fields[0])
            assert weight >= 0
            index = row(fields[1:])
            old_terms.append((weight, index))
            if weight:
                active.append(row_ray(index))
        active = sorted(set(active))
        old_values = [(weight, row_value(index)) for weight, index in old_terms]
        assert all(sum(w * r[i] for w, r in old_values) == 0 for i in range(3))
        assert any(w > 0 and r[3] for w, r in old_values)
        counts['empty_original_exact_checks'] += 1

        def accepted(ids, weights):
            values = [ray_value(i) for i in ids]
            if not any(w > 0 for w in weights) or any(w < 0 for w in weights):
                return False
            if any(sum(w * r[j] for w, r in zip(weights, values)) for j in range(2)):
                return False
            constant = sum(w * r[2] for w, r in zip(weights, values))
            return constant < 0 or (constant == 0 and any(w > 0 and r[3] for w, r in zip(weights, values)))

        def found(ids, weights):
            support = [i for i, w in zip(ids, weights) if w > 0]
            empty_basis_sizes[len(support)] += 1
            counts['empty_small_basis_checks'] += 1
            return intern('empty_row_basis', support)

        for i in active:
            if accepted([i], [1]):
                return found([i], [1])
        for i, j in combinations(active, 2):
            a, b = ray_value(i), ray_value(j)
            weights = [abs(b[0]), abs(a[0])] if a[0] or b[0] else [abs(b[1]), abs(a[1])]
            if accepted([i, j], weights):
                return found([i, j], weights)
        for ids in combinations(active, 3):
            a, b, c = [ray_value(i) for i in ids]
            weights = [b[0]*c[1]-b[1]*c[0], c[0]*a[1]-c[1]*a[0], a[0]*b[1]-a[1]*b[0]]
            for sign in (1, -1):
                signed = [sign * w for w in weights]
                if accepted(ids, signed):
                    return found(ids, signed)
        counts['empty_small_basis_unconverted'] += 1
        if len(empty_failures) < 100:
            empty_failures.append(active)
        return None

    def save_name(name, kind, identity, value):
        value = json.dumps(value, separators=(',', ':'))
        prior = db.execute('SELECT kind,ident,value FROM names WHERE name=?', (name,)).fetchone()
        assert prior is None or prior == (kind, identity, value), name
        db.execute('INSERT OR IGNORE INTO names VALUES (?,?,?,?)', (name, kind, identity, value))

    def load_name(name):
        value = db.execute('SELECT kind,ident,value FROM names WHERE name=?', (name,)).fetchone()
        if value is None:
            raise ValueError(f'unresolved source name: {name}')
        return value[0], value[1], json.loads(value[2])

    @lru_cache(maxsize=2048)
    def row_value(index):
        value = db.execute('SELECT value FROM objects WHERE kind=? AND ident=?', ('row', index)).fetchone()
        assert value
        a = json.loads(value[0])
        return tuple(map(Q, a[:3])) + (a[3],)

    # Avoid repeated full-table scans when reconstructing supports.
    db.execute('CREATE INDEX object_ids ON objects(kind,ident)')
    verified = []
    angles = {}

    def declarations(module, sha, record):
        rel = module.replace('.', '/') + '.lean'
        path = ROOT / 'evidence/historical/source-gzip' / (rel + '.gz')
        raw_path = ROOT / 'vendor' / rel
        if path.exists():
            with gzip.open(path, 'rb') as f:
                raw = f.read(8 * 1024**2 + 1)
                assert len(raw) <= 8 * 1024**2, 'single-source size cap'
        elif raw_path.exists() or raw_path.with_name(raw_path.name + '.gz').exists():
            raw = read_bytes(raw_path)
            assert len(raw) <= 8 * 1024**2, 'single-source size cap'
            path = raw_path
        else:
            if record:
                report['missing'].append(module)
            return
        assert hashlib.sha256(raw).hexdigest() == sha, f'authentication mismatch: {module}'
        if record:
            report['files'].append({'module': module, 'path': str(path.relative_to(ROOT)),
                                    'sha256': sha, 'bytes': len(raw), 'lines': raw.count(b'\n'),
                                    'cases': owners[module]})
            counts['source_bytes'] += len(raw)
            counts['source_lines'] += raw.count(b'\n')
            verified.append((module, sha))
        text = raw.decode()
        matches = list(DECL.finditer(text))
        for i, match in enumerate(matches):
            guard()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
            yield match[1], text[match.start():end]

    def unsupported(module, name, reason):
        counts['unsupported_declarations'] += 1
        if len(report['unsupported']) < 500:
            report['unsupported'].append([module, name, reason])

    try:
        for module, sha in sorted(expected.items()):
            for name, d in declarations(module, sha, True):
                head = d.split(':=', 1)[0]
                counts['declarations'] += 1
                declaration_kind = classify_declaration(d)
                kinds[declaration_kind] += 1
                recognized = False
                angle = re.fullmatch(r'angle(\d+)_(\d+)', name)
                if angle and ': AngleEnclosure :=' in d:
                    values = [Q(s.replace('(', '').replace(')', '')) for s in d.split('⟨', 1)[1].split('⟩', 1)[0].split(',')]
                    angles[angle.group(0)] = (values[2], values[3], values[5])
                if re.search(r' : PoseLeaf :=', d[:250]):
                    m = re.search(r'⟨⟨(angle\d+_\d+),\w+⟩,regionConstraintsFromText "([^"\n]*)"', d)
                    if m:
                        ids = rows(m[2]); value = [m[1], ids]
                        save_name(name, 'pose', intern('pose', value), value)
                        intern('primitive_pose', [m[1], sorted({row_ray(i) for i in ids})])
                        counts['pose_occurrences'] += 1
                        counts['pose_row_occurrences'] += len(ids)
                        recognized = True
                    else:
                        unsupported(module, name, 'PoseLeaf is not the known literal schema')
                if name.endswith('BlockRows') and ':=' in d:
                    expr = d.split('\n')[0].split(':=', 1)[1].strip()
                    fields = EXPLICIT_ROW.findall(expr)
                    if expr == '[]' or (fields and len(fields) == expr.count('⟨⟨![')):
                        ids = [row(list(f)) for f in fields]
                        save_name(name, 'block', intern('block', ids), ids)
                        counts['block_occurrences'] += 1
                        recognized = True
                    else:
                        unsupported(module, name, 'BlockRows is not the known explicit schema')
                trees = re.findall(r'regionTreeFromText "([^"\n]*)"', d)
                for tree in trees:
                    nodes = []
                    for line in tree.split('\\n'):
                        fields = line.split('|'); kind = fields[0]
                        counts['tree_node_occurrences_' + kind] += 1
                        if kind == 'L' and len(fields) == 1:
                            node = ['L']
                        elif kind == 'E' and len(fields) == 2:
                            node = ['E', terms(fields[1])]
                            empty_basis(fields[1])
                        elif kind == 'C' and len(fields) == 4:
                            yes, no = int(fields[2]), int(fields[3])
                            assert 0 <= yes < len(nodes) and 0 <= no < len(nodes)
                            node = ['C', row(fields[1].split(',')), nodes[yes], nodes[no]]
                        elif kind == 'F' and len(fields) == 3:
                            node = ['F', rows(fields[1]), [terms(t) for t in fields[2].split('~')]]
                        else:
                            raise ValueError(f'unknown compact tree node {module}:{name}:{kind}')
                        nodes.append(intern('tree_syntax_node', node))
                    assert nodes
                    intern('tree_syntax_root', nodes[-1])
                    counts['tree_root_occurrences'] += 1
                    recognized = True
                if 'axisOverlapForms a.val b.val' in d:
                    counts['pair_candidate_declarations'] += 1
                    recognized = True
                if not recognized:
                    counts['untranslated_source_lines'] += d.count('\n')
                    untranslated_kinds[declaration_kind] += d.count('\n')
                    heapq.heappush(largest_untranslated,
                                  (len(d.encode()), d.count('\n'), module, name, declaration_kind))
                    if len(largest_untranslated) > 50:
                        heapq.heappop(largest_untranslated)
                else:
                    counts['recognized_source_lines'] += d.count('\n')
            db.commit()
        report['source_inventory_complete'] = not report['missing']
        # A second optional pass resolves named leaves before checking pair records.
        if args.verify_pairs:
            for module, sha in verified:
                for name, d in declarations(module, sha, False):
                    if 'axisOverlapForms a.val b.val' not in d:
                        continue
                    try:
                        bound = re.findall(r'let [ab] : .*?(angle\d+_\d+)\.reference', d)
                        match = re.search(r'let ia := (\w+BlockRows)\s*\+\+\s*(\w+)\.inputs', d)
                        neighbor = re.search(r'let ib := (\w+)\.inputs', d)
                        proof = re.search(r'\(axisOverlapForms a.val b.val\) "([^"\n]*)"', d)
                        if len(bound) != 2 or not match or not neighbor or not proof:
                            raise ValueError('unsupported pair binding/schema')
                        _, block_id, block = load_name(match[1])
                        _, pose_id, pose = load_name(match[2])
                        _, other_id, other = load_name(neighbor[1])
                        assert pose[0] == bound[0] and other[0] == bound[1]
                        a_ids, b_ids = block + pose[1], other[1]
                        A, B = [row_value(i) for i in a_ids], [row_value(i) for i in b_ids]
                        a, b = angles[bound[0]], angles[bound[1]]
                        axes = [(a[0], a[1]), (-a[1], a[0]), (b[0], b[1]), (-b[1], b[0])]
                        directions = [(u, v) for x, y in axes for u, v in [(x, y), (-x, -y)]]
                        proofs = proof[1].split(';'); assert len(proofs) == 8
                        support_records = []
                        for text, (nx, ny) in zip(proofs, directions):
                            guard()
                            radius = sum(t[2] / 2 * (abs(nx*t[0]+ny*t[1]) + abs(-nx*t[1]+ny*t[0])) for t in (a, b))
                            all_rows = [(-nx, -ny, nx, ny, -radius, False)]
                            all_rows += [(x,y,Q(0),Q(0),z,s) for x,y,z,s in A]
                            all_rows += [(Q(0),Q(0),x,y,z,s) for x,y,z,s in B]
                            weights = [(Q(t.split(':')[0]), int(t.split(':')[1])) for t in text.split(',')]
                            assert all(w >= 0 and 0 <= i < len(all_rows) for w,i in weights)
                            assert all(sum(w*all_rows[i][j] for w,i in weights) == 0 for j in range(5))
                            assert any(w > 0 and all_rows[i][5] for w,i in weights)
                            counts['pair_original_axis_checks'] += 1
                            counts['pair_weight_text_bytes'] += len(text)
                            active_a = sorted({i-1 for w,i in weights if w and 0 < i <= len(A) and (A[i-1][0] or A[i-1][1])})
                            active_b = sorted({i-1-len(A) for w,i in weights if w and i > len(A) and (B[i-1-len(A)][0] or B[i-1-len(A)][1])})

                            def best(rr, active, x, y):
                                if len(active) < 2:
                                    active = sorted(set(active) | {i for i,t in enumerate(rr) if t[0] or t[1]})
                                result = None
                                for i,j in combinations(active, 2):
                                    x1,y1,z1,_ = rr[i]; x2,y2,z2,_ = rr[j]
                                    det = x1*y2-y1*x2
                                    if not det:
                                        continue
                                    u,v = (x*y2-y*x2)/det, (x1*y-y1*x)/det
                                    if u < 0 or v < 0:
                                        continue
                                    candidate = (u*z1+v*z2, (i,j), (u,v))
                                    if result is None or candidate[0] < result[0]:
                                        result = candidate
                                return result

                            aa, bb = best(A, active_a, nx, ny), best(B, active_b, -nx, -ny)
                            assert aa is not None and bb is not None, 'no independent support pair'
                            constant = -radius + aa[0] + bb[0]
                            strict = constant < 0 or any(w > 0 and t[3] for w,t in zip(aa[2]+bb[2], [A[i] for i in aa[1]] + [B[i] for i in bb[1]]))
                            assert constant <= 0 and strict, 'reconstructed strict bound failed'
                            support_records.append([a_ids[i] for i in aa[1]] + [b_ids[i] for i in bb[1]])
                            counts['pair_four_index_axis_checks'] += 1
                        intern('pair_record', [pose_id, other_id, block_id, support_records])
                        counts['pair_records_reconstructed'] += 1
                    except (ValueError, AssertionError, KeyError) as exc:
                        counts['pair_unconverted'] += 1
                        if len(report['pair_failures']) < 500:
                            report['pair_failures'].append([module, name, str(exc)])
                db.commit()
        report['status'] = 'source inventory completed within scope'
    except (Limit, MemoryError, sqlite3.Error, OSError, ValueError, AssertionError) as exc:
        report['status'] = 'stopped safely; partial scope only'
        report['stop_reason'] = f'{type(exc).__name__}: {exc}'
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        report['counts'] = dict(counts)
        report['unique_structures'] = dict(sequences)
        report['empty_basis_size_histogram'] = dict(empty_basis_sizes)
        report['empty_basis_failures'] = empty_failures
        report['primitive_row_interpretation'] = (
            'Positive rational scaling only: clear denominators, divide the positive gcd of all three coefficients; '
            'strictness and ray sign are preserved. Primitive pose sets additionally ignore order and duplicate constraints. '
            'This is an exact semantic-equivalence inventory, not a completed Lean translation.')
        report['declaration_kind_counts'] = dict(kinds)
        report['untranslated_lines_by_declaration_kind'] = dict(untranslated_kinds)
        report['largest_untranslated_declarations'] = [
            {'bytes': size, 'lines': lines, 'module': module, 'name': name, 'kind': kind}
            for size, lines, module, name, kind in sorted(largest_untranslated, reverse=True)]
        report['elapsed_seconds'] = time.monotonic() - started
        report['maximum_rss_platform_units'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        report['scratch_bytes_before_cleanup'] = scratch.stat().st_size if scratch.exists() else 0
        report['pair_pass_requested'] = args.verify_pairs
        report['pair_pass_complete'] = bool(args.verify_pairs and not report['missing'] and
            counts['pair_records_reconstructed'] + counts['pair_unconverted'] == counts['pair_candidate_declarations'] and
            not counts['pair_unconverted'])
        report['size_interpretation'] = {
            'one_line_per_unique_row_and_pose': sequences['row'] + sequences['pose'],
            'one_line_per_unique_tree_syntax_node': sequences['tree_syntax_node'],
            'one_line_per_verified_pair_record': sequences['pair_record'],
            'not_included': ['tree ancestry and pose-output bindings', 'relaxation/chord conversion',
                             'entry and terminal coverage adapters', 'all source outside accepted-seven union',
                             'all currently unsupported declaration schemas'],
            'these_are_component_counts_not_a_whole_proof_upper_bound': True}
        db.close()
        for suffix in ('', '-journal', '-wal', '-shm'):
            Path(str(scratch) + suffix).unlink(missing_ok=True)
        with out.open('w') as stream:
            json.dump(report, stream, indent=2)
            stream.write('\n')
        print(json.dumps({k: report[k] for k in ['status', 'elapsed_seconds', 'counts', 'unique_structures',
                                               'pair_pass_complete', 'global_under_1m_bound_established']}))


if __name__ == '__main__':
    main()
