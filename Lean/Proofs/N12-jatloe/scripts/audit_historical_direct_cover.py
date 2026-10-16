#!/usr/bin/env python3
"""Prepared audit of direct initial covers for six historical whole cases.

Explicit --run is required. No Lean generation/compilation, recovered-program
execution, network, or full archive extraction. At most 256 MiB RSS, 120 seconds,
and 8 MiB output; partial/unsupported scopes never count as covered. Run inside
scripts/bounded.py as well. This is a finite exact audit, not a Lean receipt.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import argparse
import gzip
import hashlib
import itertools
import json
import re
import resource
import signal
import sys
import time
from provenance_source import binary_stream

from audit_c898_direct_cover import (ROOT, point_forms, primitive_normal,
                                     strongest_parallel, evaluate, intersection)

CASES = (701, 713, 717, 973, 978, 979)
DECL = re.compile(rb'^(?:noncomputable )?(?:def|theorem|lemma) (\w+)')
LINE_CAP = 8 * 1024**2
OUT_CAP = 8 * 1024**2


class Unsupported(Exception):
    pass


class Stop(Exception):
    pass


def need(condition, reason):
    if not condition:
        raise Unsupported(reason)


def qtext(text):
    return Q(text.replace('(', '').replace(')', '').strip())


def point_list(expr):
    # Only literal rational pairs. Never eval recovered source.
    expr = expr.strip()
    need(expr.startswith('[') and expr.endswith(']'), 'nonliteral point list')
    tokens = re.findall(r'-?\d+(?:/\d+)?|[(),\[\]]', expr)
    need(''.join(tokens) == re.sub(r'\s', '', expr), 'unsupported point token')
    values = re.findall(r'-?\d+(?:/\d+)?', expr)
    need(len(values) % 2 == 0, 'odd point-coordinate count')
    return [[str(Q(values[i])), str(Q(values[i+1]))] for i in range(0, len(values), 2)]


class JsonStream:
    """Skip large trees in fixed buffers; retain only small owner metadata.

    Balanced JSON values are skipped lexically, not decoded into Python trees.
    Selected values are decoded by the standard parser. The full raw file is
    hashed, including skipped bytes. No archive/JSON text is executed.
    """
    marks = re.compile(rb'["\\{}\[\]]')
    atom_end = re.compile(rb'[\s,\]}]')

    def __init__(self, path, guard):
        self.f = binary_stream(path)
        self.guard = guard
        self.buf, self.pos, self.offset = b'', 0, 0
        self.sha, self.size = hashlib.sha256(), 0

    def more(self):
        self.guard()
        need(self.pos == len(self.buf), 'JSON refill with unconsumed bytes')
        self.offset += len(self.buf)
        self.buf = self.f.read(65536)
        self.pos = 0
        self.sha.update(self.buf)
        self.size += len(self.buf)
        return bool(self.buf)

    def peek(self):
        if self.pos == len(self.buf) and not self.more():
            return None
        return self.buf[self.pos]

    def space(self):
        while self.peek() is not None:
            m = re.match(rb'\s*', self.buf[self.pos:])
            self.pos += m.end()
            if self.pos < len(self.buf):
                return

    def punctuation(self, char):
        self.space()
        need(self.peek() == ord(char), f'expected JSON punctuation {char}')
        self.pos += 1

    def value(self, capture):
        self.space()
        first = self.peek()
        need(first is not None, 'truncated JSON value')
        parts, length = [], 0
        composite = first in (ord('['), ord('{'))
        quoted = first == ord('"')
        depth, in_string, ignore_at = 0, False, -1
        while True:
            if self.pos == len(self.buf):
                need(self.more(), 'truncated JSON composite')
            start, end = self.pos, None
            if composite or quoted:
                for m in self.marks.finditer(self.buf, start):
                    absolute = self.offset + m.start()
                    if absolute == ignore_at:
                        continue
                    ch = m.group()[0]
                    if in_string:
                        if ch == ord('\\'):
                            ignore_at = absolute + 1
                        elif ch == ord('"'):
                            in_string = False
                            if quoted and depth == 0:
                                end = m.end()
                                break
                    elif ch == ord('"'):
                        in_string = True
                    elif ch in (ord('['), ord('{')):
                        depth += 1
                    elif ch in (ord(']'), ord('}')):
                        depth -= 1
                        if depth == 0:
                            end = m.end()
                            break
            else:
                m = self.atom_end.search(self.buf, start)
                if m:
                    end = m.start()
            stop = len(self.buf) if end is None else end
            if capture:
                length += stop-start
                need(length <= 1024**2, 'selected JSON value exceeds 1 MiB')
                parts.append(self.buf[start:stop])
            self.pos = stop
            if end is not None:
                return json.loads(b''.join(parts), parse_float=Q) if capture else None

    def owners(self):
        result = []
        self.punctuation('[')
        while True:
            self.space()
            if self.peek() == ord(']'):
                self.pos += 1
                break
            self.punctuation('{')
            record = {}
            while True:
                key = self.value(True)
                need(isinstance(key, str), 'non-string JSON key')
                self.punctuation(':')
                take = key in ('owner', 'N', 'inside', 'outside')
                value = self.value(take)
                if take:
                    need(key not in record, 'duplicate JSON metadata key')
                    record[key] = value
                self.space()
                ch = self.peek()
                if ch == ord('}'):
                    self.pos += 1
                    break
                self.punctuation(',')
            result.append(record)
            self.space()
            if self.peek() != ord(']'):
                self.punctuation(',')
        self.space()
        need(self.peek() is None, 'trailing JSON content')
        return result

    def close(self):
        self.f.close()


def source_lines(module, expected, provenance, guard):
    rel = module.replace('.', '/') + '.lean'
    zipped = ROOT / 'evidence/historical/source-gzip' / (rel + '.gz')
    path = zipped if zipped.exists() else ROOT / 'vendor' / rel
    need(path.exists(), f'missing authenticated module {module}')
    sha, size = hashlib.sha256(), 0
    opener = gzip.open if path.suffix == '.gz' else open
    with opener(path, 'rb') as f:
        while True:
            guard()
            line = f.readline(LINE_CAP + 1)
            if not line:
                break
            need(len(line) <= LINE_CAP, f'line cap in {module}')
            sha.update(line)
            size += len(line)
            yield line.decode('utf-8')
    need(sha.hexdigest() == expected[module], f'source hash mismatch: {module}')
    provenance.append({'module': module, 'path': str(path.relative_to(ROOT)),
                       'sha256': sha.hexdigest(), 'bytes': size})


def declarations(module, expected, provenance, guard, wanted):
    name, parts, size = None, [], 0
    for line in source_lines(module, expected, provenance, guard):
        match = DECL.match(line.encode())
        if match:
            if name:
                yield name, ''.join(parts)
            candidate = match[1].decode()
            name = candidate if wanted(candidate) else None
            parts, size = [], 0
        if name:
            size += len(line)
            need(size <= LINE_CAP, f'declaration cap: {name}')
            parts.append(line)
    if name:
        yield name, ''.join(parts)


def load_case(case, guard, report):
    receipt_path = ROOT / f'evidence/inherited/evidence/C{case}/case-replay.json'
    raw = receipt_path.read_bytes()
    expected = json.loads(raw)['local_source_sha256']
    record = {'case': case, 'receipt_sha256': hashlib.sha256(raw).hexdigest(),
              'sources': [], 'owners': [], 'status': 'mapping incomplete', 'roots': []}
    report['cases'].append(record)
    source_meta, roots, checks, enclosures, poses, domains, masks = {}, {}, {}, {}, {}, {}, {}
    family = (rf'(?:region{case}(?:Inside|Outside)\d+|region{case}Root\d+_\d+(?:_checked)?|'
              rf'owner{case}_\d+|continuousScout{case}Initial\d+_\d+|'
              rf'continuousScout{case}Domain\d+_0|case{case}_shared_impossible)')
    wanted = re.compile(family).fullmatch
    own = sorted((m for m in expected if re.fullmatch(rf'S12.Push{case}Chunk\d+', m)),
                 key=lambda m: int(m.split('Chunk')[1]))
    need(own, f'no source chunks for case {case}')
    for module in own:
        for name, text in declarations(module, expected, record['sources'], guard, wanted):
            line = text.splitlines()[0]
            points = re.fullmatch(rf'region{case}(Inside|Outside)(\d+)', name)
            root = re.fullmatch(rf'region{case}Root(\d+)_(\d+)', name)
            check = re.fullmatch(rf'region{case}Root(\d+)_(\d+)_checked', name)
            owner = re.fullmatch(rf'owner{case}_(\d+)', name)
            pose = re.fullmatch(rf'continuousScout{case}Initial(\d+)_(\d+)', name)
            domain = re.fullmatch(rf'continuousScout{case}Domain(\d+)_0', name)
            if points:
                key = (int(points[2]), points[1].lower())
                need(key not in source_meta, f'duplicate point list {name}')
                source_meta[key] = point_list(line.split(':=', 1)[1])
            elif root:
                m = re.search(r': PoseRoot := ⟨⟨(angle(\d+)_(\d+)),\1_checked⟩,regionTreeFromText ', line)
                need(m, f'unsupported initial root {name}')
                roots[name] = (int(root[1]), int(m[2]), int(m[3]))
            elif check:
                expected_check = f'{name[:-8]}.Check region{case}Inside{check[1]} region{case}Outside{check[1]}'
                need(expected_check in line, f'root premise mismatch {name}')
                checks[name[:-8]] = True
            elif owner:
                m = re.search(r': OwnerEnclosure := ⟨region'+str(case)+r'Inside(\d+),region'+str(case)+r'Outside(\d+),\[(.*?)\]⟩', line)
                need(m and m[1] == owner[1] == m[2], f'unsupported owner enclosure {name}')
                names = re.findall(rf'⟨(region{case}Root\d+_\d+),\1_checked⟩', m[3])
                need(names and len(names) == m[3].count('⟨'), f'nonliteral owner root list {name}')
                enclosures[int(owner[1])] = names
            elif pose:
                m = re.search(r': PoseLeaf := ⟨⟨(angle(\d+)_(\d+)),\1_checked⟩,regionConstraintsFromText "([^"\n]*)"⟩', line)
                need(m, f'unsupported reduced pose {name}')
                rows = []
                for raw_row in m[4].split(';') if m[4] else []:
                    fields = raw_row.split(',')
                    need(len(fields) == 4 and fields[3] in ('0','1','false','true'), f'unsupported row {name}')
                    row = tuple(map(Q, fields[:3]))
                    strict = fields[3] in ('1','true')
                    need(not strict or (row[0] == row[1] == 0 and row[2] > 0), f'nontrivial strict target {name}')
                    if not strict:
                        rows.append(row)
                poses[name] = {'grid': int(m[2]), 'angle': int(m[3]), 'rows': rows}
            elif domain:
                m = re.search(r': List PoseLeaf := \[([^\]]*)\]', line)
                need(m, f'nonliteral initial target list {name}')
                names = [x.strip() for x in m[1].split(',') if x.strip()]
                need(all(re.fullmatch(rf'continuousScout{case}Initial{domain[1]}_\d+', x) for x in names), f'foreign target in {name}')
                domains[int(domain[1])] = names
            elif name == f'case{case}_shared_impossible':
                need('(p : NormalizedPacking)' in text and 'common_certified_enclosure_sound' in text,
                     'unsupported original packing entrance')
                record['entrance_statement'] = text.split(':=',1)[0].strip()
                for owner_id, mask in re.findall(rf'change OrientedPoseCovered owner{case}_(\d+)\.leaves \(p.square \(ownerIndex p (\d+)\)\)', text):
                    masks[int(owner_id)] = int(mask)
                record['used_final_owner_slots'] = [int(x) for x in re.findall(r'\bhc(\d+)\b', text.split('exact mixedGeometry')[-1])]
    need('entrance_statement' in record, 'missing original whole-case entrance')
    need(set(domains) <= set(enclosures), 'target owner has no recognized initial enclosure')
    record['target_owner_slots'] = sorted(domains)
    record['region_owner_slots'] = sorted(enclosures)
    record['unsupported_owner_slots'] = sorted(set(enclosures)-set(domains))
    record['owner_masks'] = masks

    # Same accepted generic semantics, checked by source hash and exact shape.
    helpers = {}
    reference = json.loads((ROOT/'evidence/inherited/evidence/C898/case-replay.json').read_text())['local_source_sha256']
    for module in ('S12.AngleData', 'S12.PoseRegion', 'S12.OwnerEnclosure', 'S12.CommonCertifiedEnclosure'):
        need(module in expected, f'missing generic source hash {module}')
        need(expected[module] == reference.get(module), f'generic semantics differ from C898: {module}')
        helpers[module] = ''.join(source_lines(module, expected, record['sources'], guard))
    pose_region = re.sub(r'\s', '', helpers['S12.PoseRegion'])
    need('defouterReference(w:AngleEnclosure):ReferenceSquare:=⟨w.c,w.s,(1001/1000)*w.outer⟩' in pose_region,
         'unsupported upper-side semantics')
    need('(hsize:q.side≤1001/1000)' in pose_region and '(ha:1<q.side)' in pose_region,
         'unsupported side interval')
    need('outside.map(pointForms(w.reference1))' in pose_region,
         'unsupported outside semantics')
    need('4-w.wall/2' in pose_region, 'unsupported container side')
    record['side_bounds'] = {'lower_exclusive': '1', 'upper_inclusive': '1001/1000', 'container_side': '4'}
    record['actual_entrance_status'] = 'Historical checked entrance retained; replacement Lean adapter not generated or checked.'
    angles = {}
    for name, fields in re.findall(r'def (angle\d+_\d+) : AngleEnclosure := ⟨([^⟩]+)⟩', helpers['S12.AngleData']):
        values = tuple(qtext(x) for x in fields.split(','))
        need(len(values) == 7, f'unsupported angle {name}')
        angles[name] = values

    manifest = json.loads((ROOT/'audit/SELECTED_PROGRESS_RECOVERY_PLAN.json').read_text())
    items = manifest['needed'] + manifest['existing']
    matching = [x for x in items if x['path'] == f'data/region{case}.json']
    need(len(matching) == 1, 'missing/ambiguous region provenance')
    item = matching[0]
    path = ROOT / item.get('target', item.get('existing_path', ''))
    reader = JsonStream(path, guard)
    try:
        owners = reader.owners()
        need(reader.sha.hexdigest() == item['sha256'], 'region JSON hash mismatch')
        need(reader.size == item['size'], 'region JSON size mismatch')
        record['region_json'] = {'path':str(path.relative_to(ROOT)), 'sha256':reader.sha.hexdigest(), 'bytes':reader.size}
    finally:
        reader.close()
    need(len({o['owner'] for o in owners}) == len(owners), 'duplicate JSON owners')
    need({o['owner'] for o in owners} == set(enclosures), 'JSON/source owner coverage mismatch')
    for owner in owners:
        owner_id, grid = owner['owner'], owner['N']
        need(owner_id in masks, f'missing actual owner mask {owner_id}')
        for kind in ('inside','outside'):
            actual = [[str(Q(x)),str(Q(y))] for x,y in owner[kind]]
            need(actual == source_meta.get((owner_id,kind)), f'JSON/source {kind} mismatch for owner {owner_id}')
            owner[kind] = actual
        root_names = enclosures[owner_id]
        need(all(name in roots and name in checks for name in root_names), f'unresolved root/check owner {owner_id}')
        actual_angles = [roots[name] for name in root_names]
        need(actual_angles == [(owner_id,grid,i) for i in range(grid)], f'nonstandard root angle coverage owner {owner_id}')
        values = [angles.get(f'angle{grid}_{i}') for i in range(grid)]
        need(all(values), f'missing angle constants for grid {grid}')
        need(values[0][0] == 0 and values[-1][1] == 1 and all(values[i][1] == values[i+1][0] for i in range(grid-1)), 'noncontiguous closed grid')
        need(all(v[0] <= v[1] and v[2]**2+v[3]**2 == 1 and v[4] > 0 and v[5] > 0 for v in values), 'bad angle constants')
        owner['mask'] = masks[owner_id]
        owner['root_names'] = root_names
        owner['targets'] = {}
        if owner_id not in domains:
            owner['unsupported'] = 'No recognized literal initial reduced-pose domain; no empty-angle inference.'
        else:
            need(len(set(domains[owner_id])) == len(domains[owner_id]), 'duplicate target name')
            for name in domains[owner_id]:
                need(name in poses, f'unresolved target pose {name}')
                target = poses[name]
                need(target['grid'] == grid, f'target/root grid mismatch {name}')
                key = target['angle']
                need(0 <= key < grid and key not in owner['targets'], f'multiple/invalid targets at owner-angle {owner_id}/{key}')
                owner['targets'][key] = (name, target['rows'])
        record['owners'].append({k:v for k,v in owner.items() if k != 'targets'})
    record['status'] = 'mapping authenticated'
    return record, owners, angles


def check_owner_angle(owner, angle_id, values):
    _, _, c, s, outer, inner, wall = values
    inside = [row for p in owner['inside'] for row in point_forms(c,s,Q(1001,1000)*outer,p)]
    base = strongest_parallel(inside + [(Q(1),Q(0),-wall/2), (Q(-1),Q(0),4-wall/2),
                                       (Q(0),Q(1),-wall/2), (Q(0),Q(-1),4-wall/2)])
    forbidden = [[primitive_normal(row) for row in point_forms(c,s,inner,p)] for p in owner['outside']]
    lines = sorted(set(base + list(itertools.chain.from_iterable(forbidden))))
    target = owner['targets'].get(angle_id)
    rows = [] if target is None else list(set(target[1]))
    vertices, pair_count = set(), 0
    for a,b in itertools.combinations(lines,2):
        p = intersection(a,b)
        if p is None:
            continue
        pair_count += 1
        if all(evaluate(row,p)>=0 for row in base) and all(any(evaluate(row,p)<=0 for row in block) for block in forbidden):
            vertices.add(p)
    failed = sum(evaluate(row,p)<0 for p in vertices for row in rows)
    examples = [[list(map(str,p)),list(map(str,row))] for p in sorted(vertices) for row in rows if evaluate(row,p)<0][:3]
    absent_nonempty = target is None and bool(vertices)
    return {'owner':owner['owner'], 'mask':owner['mask'], 'grid':owner['N'], 'angle':angle_id,
            'historical_root':owner['root_names'][angle_id],
            'target_pose':None if target is None else target[0],
            'target_rows':len(rows), 'boundary_planes':len(lines), 'nonparallel_pairs':pair_count,
            'feasible_vertices':len(vertices), 'target_vertex_checks':len(vertices)*len(rows),
            'target_failures':failed, 'absent_pose_closed_nonempty':absent_nonempty,
            'passed':not failed and not absent_nonempty, 'failure_examples':examples,
            'missing_target_examples':[list(map(str,p)) for p in sorted(vertices)[:3]] if absent_nonempty else []}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', action='store_true')
    ap.add_argument('--case', type=int, action='append', choices=CASES)
    ap.add_argument('--output', default='evidence/historical-direct-cover-audit.json')
    args = ap.parse_args()
    if not args.run:
        ap.error('Prepared only; parent must assign the bounded compute slot before --run.')
    started = time.monotonic()
    report = {'scope':'Exact finite direct-cover audit; no generated/replayed Lean adapter.',
              'status':'incomplete', 'cases':[], 'unsupported':[],
              'limits':{'rss_mib':256,'seconds':120,'output_bytes':OUT_CAP},
              'vertex_soundness':'Compact.Core.PlanarVertex.nonnegative_of_vertices accepted separately; integer checker and every case bridge still require Lean acceptance.',
              'strict_boundary_policy':'Compulsory inputs closed; forbidden rectangles OPEN; boundary touching retained. No strict filtering can prove emptiness.'}

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if rss > 256*1024**2 or time.monotonic()-started > 115:
            raise Stop('internal resource limit')

    def interrupted(*_):
        raise Stop('termination requested')

    signal.signal(signal.SIGALRM,guard)
    signal.signal(signal.SIGTERM,interrupted)
    signal.signal(signal.SIGINT,interrupted)
    signal.setitimer(signal.ITIMER_REAL,.2,.2)
    try:
        for case in args.case or CASES:
            try:
                record, owners, angles = load_case(case,guard,report)
                for owner in owners:
                    if 'unsupported' in owner:
                        report['unsupported'].append({'case':case,'owner':owner['owner'],'reason':owner['unsupported']})
                        continue
                    for angle in range(owner['N']):
                        guard()
                        record['roots'].append(check_owner_angle(owner,angle,angles[f'angle{owner["N"]}_{angle}']))
                record['counts'] = dict(Counter({
                    'roots':len(record['roots']),
                    'failed_roots':sum(not r['passed'] for r in record['roots']),
                    'line_pairs':sum(r['nonparallel_pairs'] for r in record['roots']),
                    'absent_target_angles':sum(r['target_pose'] is None for r in record['roots'])}))
                record['status'] = 'finite audit complete' if not record['unsupported_owner_slots'] else 'partial owner coverage'
                record['all_checked_roots_pass'] = record['counts']['failed_roots'] == 0
                record['all_initial_roots_audited'] = not record['unsupported_owner_slots']
            except Unsupported as error:
                report['unsupported'].append({'case':case,'reason':str(error)})
                report['cases'][-1]['status'] = 'unsupported mapping; no coverage claim'
        report['status'] = 'audit complete with explicit unsupported scope' if report['unsupported'] else 'finite audit complete'
        report['all_selected_initial_covers_pass'] = not report['unsupported'] and all(
            r.get('all_checked_roots_pass', False) and r.get('all_initial_roots_audited', False)
            for r in report['cases'])
    except Stop as error:
        report['status'] = 'stopped safely; partial scope only'
        report['stop_reason'] = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    report['elapsed_seconds'] = time.monotonic()-started
    report['source_script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    output = ROOT/args.output
    need(output.resolve().is_relative_to((ROOT/'evidence').resolve()), 'output must stay under evidence')
    temporary = output.with_suffix('.json.tmp')
    written = 0
    try:
        with temporary.open('wb') as f:
            for part in json.JSONEncoder(separators=(',',':')).iterencode(report):
                raw = part.encode()
                written += len(raw)
                if written > OUT_CAP:
                    raise Stop('8 MiB output cap')
                f.write(raw)
        temporary.replace(output)
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps({'status':report['status'],'cases':len(report['cases']),
                      'unsupported':len(report['unsupported']),'elapsed_seconds':report['elapsed_seconds'],
                      'output':str(output.relative_to(ROOT))}))


if __name__ == '__main__':
    main()
