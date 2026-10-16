#!/usr/bin/env python3
"""Parent-only exact co-occurring strip-recipe count after the boxed bank.

No Lean output, activation, geometry search, or changed obligations. A strip
shares an actual normal between a lower and an upper face which co-occur in
one retained original pose. Strictness and original integer scaling survive.
Only pairs wholly inside one current bounded row leaf may be chosen. Existing
box records are immutable and excluded from matching. Explicit disjoint
matches are a lower bound on available sharing, not an optimality assertion.

Parent serial200MiB/60s; internal190MiB/55s; transactional output8MiB.
"""
from collections import Counter
from math import gcd
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

from prepare_historical_box_bank import decode_line

ROOT = Path(__file__).resolve().parents[1]
BANK = ROOT / 'evidence/historical-box-bank'


def need(test, message):
    if not test:
        raise ValueError(message)


def encode_strip(lower_id, upper_id, rows):
    lower, upper = rows[lower_id], rows[upper_id]
    x, y, c, strict, den = lower
    X, Y, C, Strict, Den = upper
    g, G = gcd(abs(x), abs(y)), gcd(abs(X), abs(Y))
    need(g > 0 and G > 0 and (x//g, y//g) == (-X//G, -Y//G),
         'faces do not have opposite primitive normals')
    mask = int(strict) + 2*int(Strict)
    if (x, y) == (-X, -Y):
        text = f'M:{lower_id},{upper_id};{x},{y};{-c},{C};{den},{Den};{mask}'
        decoded = {lower_id:(x,y,c,strict,den), upper_id:(-x,-y,C,Strict,Den)}
        kind = 'same_integer_normal'
    else:
        # Use their largest exact common normal, avoiding needless unit-scale
        # factors while retaining each original integer coefficient verbatim.
        common = gcd(g, G)
        nx, ny = x//g*common, y//g*common
        k, K = g//common, G//common
        text = f'P:{lower_id},{upper_id};{nx},{ny};{k},{K};{-c},{C};{den},{Den};{mask}'
        decoded = {lower_id:(k*nx,k*ny,c,strict,den),
                   upper_id:(-K*nx,-K*ny,C,Strict,Den)}
        kind = 'positive_scaled_normal'
    need(decoded == {lower_id:lower,upper_id:upper}, 'strip decoder changes an original row')
    return text, kind


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    parser.add_argument('--output', default='evidence/historical-strip-recipes')
    args = parser.parse_args()
    need(args.run, 'parent serial slot and --run required')
    dest = (ROOT/args.output).resolve()
    need(dest.is_relative_to(ROOT/'evidence'), 'output must be under evidence')
    stage = dest.with_name(dest.name+'.staging')
    need(not dest.exists() and not stage.exists(), 'refusing existing output')
    started = time.monotonic()
    sources = {}
    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(rss < 190*1024**2 and time.monotonic()-started < 55, '190MiB/55second working guard')
    def stop(*_):
        raise RuntimeError('termination requested')
    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL,.2,.2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    def read(path, expected=None):
        need(path.stat().st_size <= 16*1024**2, 'oversized metadata/source load')
        raw = path.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        need(expected is None or digest == expected, 'source hash mismatch: '+str(path))
        sources[str(path.relative_to(ROOT))] = digest
        guard()
        return raw.decode()
    def load(path, expected=None):
        return json.loads(read(path, expected))
    stage.mkdir(parents=True)
    try:
        bank = load(BANK/'manifest.json')
        need(bank['grouped_boxes'] == 6298 and bank['original_pose_count'] == 12682,
             'unexpected boxed-bank scope; review before changing count expectations')
        polygon_path = ROOT/'evidence/historical-polygon-redundancy/manifest.json'
        polygon = load(polygon_path, bank['sources'][str(polygon_path.relative_to(ROOT))])
        selection_path = ROOT/'evidence/historical-direct-bank/selection.json'
        selection = load(selection_path, polygon['sources'][str(selection_path.relative_to(ROOT))])
        poses_path = ROOT/'evidence/historical-compact-data/poses.json'
        poses = load(poses_path, bank['sources'][str(poses_path.relative_to(ROOT))])
        need(len(selection['pose_ids']) == bank['original_pose_count'], 'pose coverage differs')
        rows, leaves, raw_lengths = {}, {}, {}
        boxed = set()
        for name, digest in bank['outputs'].items():
            if '/RowsChunks/' not in name:
                continue
            source = read(BANK/'proposal'/name, digest)
            _, sep, rest = source.partition('sparse_rows% "\n')
            need(bool(sep), 'missing sparse row literal: '+name)
            payload, sep, _ = rest.partition('\n"')
            need(bool(sep), 'unterminated sparse row literal')
            for line in payload.splitlines():
                decoded = decode_line(line)
                for rid, row in decoded.items():
                    need(rid not in rows, 'row appears in two leaves')
                    rows[rid], leaves[rid] = row, name
                    if line.startswith('B:'):
                        boxed.add(rid)
                    else:
                        raw_lengths[rid] = len(line.encode())+1
        need(len(boxed) == bank['grouped_row_records'], 'boxed scope differs')
        direction = {}
        for rid, (x,y,_,_,_) in rows.items():
            if rid in boxed or (x == 0 and y == 0):
                continue
            g = gcd(abs(x),abs(y))
            positive = x > 0 or (x == 0 and y > 0)
            direction[rid] = ((x//g,y//g) if positive else (-x//g,-y//g), positive)
        # De-duplicate actual co-occurrence edges. No Cartesian product of
        # whole pose families is materialized: each pose has only its own rows.
        candidates = {}
        crossing = set()
        for pid in selection['pose_ids']:
            pose = poses[pid]
            need(pose['index'] == pid, 'original pose ID mismatch')
            by_normal = {}
            for rid in set(pose['rows']):
                if rid not in direction:
                    continue
                normal, positive = direction[rid]
                by_normal.setdefault(normal, ([],[]))[0 if positive else 1].append(rid)
            for lower, upper in by_normal.values():
                for a in lower:
                    for b in upper:
                        if leaves[a] != leaves[b]:
                            crossing.add((a,b))
                            continue
                        if (a,b) not in candidates:
                            text, kind = encode_strip(a,b,rows)
                            savings = raw_lengths[a]+raw_lengths[b]-len(text.encode())-1
                            if savings > 0:
                                candidates[(a,b)] = (savings,pid,text,kind)
            need(len(candidates) <= 300000 and len(crossing) <= 300000, 'candidate-edge cap')
            guard()
        used = set()
        records = []
        counts = Counter()
        saved_bytes = 0
        # Prefer exact coefficient sharing, then the larger actual byte saving.
        ordered = sorted(candidates.items(), key=lambda item:
            (item[1][3] != 'same_integer_normal', -item[1][0], item[0]))
        for (a,b), (saving,pid,text,kind) in ordered:
            if a in used or b in used:
                continue
            need(a in poses[pid]['rows'] and b in poses[pid]['rows'], 'lost original co-occurrence')
            need(a not in boxed and b not in boxed, 'strip overlaps immutable box')
            used.update((a,b))
            records.append({'pose':pid,'rows':[a,b],'leaf':leaves[a],
                            'recipe':text,'kind':kind,'saved_bytes':saving})
            counts[kind] += 1
            x,y = rows[a][:2]
            counts['axis' if x == 0 or y == 0 else 'non_axis'] += 1
            counts['with_strict_face' if rows[a][3] or rows[b][3] else 'closed'] += 1
            saved_bytes += saving
        need(not used.intersection(boxed), 'final overlap with box records')
        report = {
            'status':'complete exact co-occurring strip count; no Lean source emitted or activated',
            'sources':sources, 'original_poses':len(selection['pose_ids']),
            'immutable_box_groups':bank['grouped_boxes'],
            'eligible_raw_rows':len(direction), 'candidate_same_leaf_pairs':len(candidates),
            'candidate_cross_leaf_pairs':len(crossing), 'selected_disjoint_strips':len(records),
            'selected_rows':len(used), 'selected':dict(counts),
            'potential_source_record_lines_saved':len(records),
            'exact_recipe_bytes_saved_before_generic_source':saved_bytes,
            'boxed_bank_lines':bank['source_lines'],
            'candidate_bank_lines_before_generic_source':bank['source_lines']-len(records),
            'kernel_work':'A literal decoder can preserve the exact same row tree. This changes neither kernel row-node count nor numerical obligations.',
            'mathematical_meaning':'One actual linear form lies between two exact bounds. Positive face scales, strictness, denominator and both original row IDs remain explicit.',
            'limits':'Greedy disjoint matching is a witnessed lower bound; cross-leaf pairs stay raw. No local polygon inequality is deleted.',
            'required_before_any_saving_claim':['Implement the exact strip decoder and ordinary-kernel equality pilot.',
                'Emit the complete proposal, verify every original row and measure its full source closure.',
                'Preserve existing direct-bank activation gates; replay actual dependent case proofs.'],
            'seconds':time.monotonic()-started,
        }
        written = 0
        for name, value in [('manifest.json',report),('strips.json',records)]:
            blob = (json.dumps(value,separators=(',',':'))+'\n').encode()
            written += len(blob)
            need(written <= 8*1024**2, '8MiB output cap')
            (stage/name).write_bytes(blob)
        guard()
        stage.rename(dest)
        print(json.dumps({key:report[key] for key in ('status','candidate_same_leaf_pairs',
            'candidate_cross_leaf_pairs','selected_disjoint_strips','selected',
            'potential_source_record_lines_saved','exact_recipe_bytes_saved_before_generic_source',
            'candidate_bank_lines_before_generic_source','seconds')},indent=2))
    except BaseException:
        shutil.rmtree(stage,ignore_errors=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)


if __name__ == '__main__':
    main()
