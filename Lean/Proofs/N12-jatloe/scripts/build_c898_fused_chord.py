#!/usr/bin/env python3
"""Prepare53 direct original-angle exits for the two fused C898 chord cuts.

Run only under the parent's serial process/RSS guard.  The bounded exact
search uses at most two rows per target, produces at most256KiB, and never
edits the accepted old chain.  Every emitted certificate requires Lean replay.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import argparse
import hashlib
import json
import re
import signal
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def supports(a, b, target):
    det = a[0]*b[1]-a[1]*b[0]
    if not det:
        return False
    u = (target[0]*b[1]-target[1]*b[0])/det
    v = (a[0]*target[1]-a[1]*target[0])/det
    slack = target[2]-u*a[2]-v*b[2]
    return (u >= 0 and v >= 0 and slack >= 0 and
            (not target[3] or slack > 0 or u > 0 and a[3] or v > 0 and b[3]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true', required=True)
    args = parser.parse_args()
    del args
    start = time.monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('60s cap')))
    signal.alarm(60)
    paths = [ROOT/'evidence/c898-shared-pose-map.json',
             ROOT/'Compact/Cases/C898/SharedDomains.lean',
             ROOT/'Compact/Cases/C898/ChordRadii.lean']
    raw = json.loads(paths[0].read_text())
    poses = {p['index']: p for p in raw['poses']}
    rows = [tuple(F(x, r['denominator']) for x in r['integers'])+(r['strict'],)
            for r in raw['rows']]
    domains = paths[1].read_text()

    def domain(suffix):
        match = re.search(r'def continuousScout898Domain5_'+suffix+
                          r'Ids\b[^\n]*:= \[([^\]]*)\]', domains)
        assert match, suffix
        return [int(x) for x in match[1].split(',')]

    sources, targets = domain('0'), domain('11')
    assert len(sources) == 53 and len(targets) == 49
    by_angle = {poses[t]['angle']: t for t in targets}
    assert len(by_angle) == 49
    radii = {int(m[1]): F(m[2]) for m in re.finditer(
        r'^def radius(\d+) : Radius := ⟨\([^\n]*?\), \(([^()]*)\)⟩$',
        paths[2].read_text(), re.M)}
    assert len(radii) == 64
    lower, upper = F(79616259,50000000), F(252785619,100000000)
    plans, caches, missing, support_count = [], [], [], 0

    def row_literal(row):
        x, y, c, strict = row
        return f'⟨{x},{y},{c},{str(strict).lower()}⟩'

    def original_row(rowid):
        record = raw['rows'][rowid]
        return (*record['integers'], record['strict'])

    for source in sources:
        sp = poses[source]
        radius = radii[sp['angle']]
        low, high = lower+radius, upper-radius
        sr = [(F(1),F(0),-low,True),(F(-1),F(0),high,True)] + [rows[r] for r in sp['rows']]

        def pair(target):
            result = next((ij for ij in combinations(range(len(sr)),2)
                           if supports(sr[ij[0]],sr[ij[1]],target)), None)
            assert result is not None, (source, sp['angle'], str(target))
            return result

        target = by_angle.get(sp['angle'])
        inputs = [(low.denominator, 0, -low.numerator, True),
                  (-high.denominator, 0, high.numerator, True)]
        inputs += [original_row(rowid) for rowid in sp['rows']]
        cached_supports = []
        if target is None:
            left, right = pair((F(-1),F(0),low,False))
            plans.append(f'  ⟨{source}, none, [], {left}, {right}⟩')
            missing.append(sp['angle'])
            support_count += 1
        else:
            certificates = []
            for rowid in dict.fromkeys(poses[target]['rows']):
                if rowid in sp['rows']:
                    continue
                left, right = pair(rows[rowid])
                support = f'⟨{rowid}, {left}, {right}⟩'
                certificates.append(support)
                cached_supports.append(f'({support},{row_literal(original_row(rowid))})')
                support_count += 1
            plans.append(f'  ⟨{source}, some {target}, ['+', '.join(certificates)+'], 0, 0⟩')
        closing = (-low.denominator, 0, low.numerator, False)
        caches.append((source,sp['angle'],
            '⟨['+', '.join(map(row_literal,inputs))+'], ['+
            ', '.join(cached_supports)+'], '+row_literal(closing)+'⟩'))
    assert sorted(missing) == [0,1,56,63]
    head = ['import Compact.Cases.C898.ChordFusedCache',
            'import Compact.Cases.C898.SharedDomains', '',
            'namespace N12Compact.C898Chord.Fused',
            'open C898Shared CoordinateBound', 'set_option Elab.async false',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    names = []
    for index,(plan,(source,angle,cache)) in enumerate(zip(plans,caches)):
        name = f'plan{index:02}'
        names.append(name)
        head += [f'def {name} : DirectPlan := {plan.strip()}',
                 f'private def cache{index:02} : PlanCache := {cache}',
                 f'private theorem angle{index:02}_exact : poseAngle {source} = {angle} := by',
                 '  decide +kernel',
                 f'private theorem radius{index:02}_exact : poseRadius {source} = radius{angle} := by',
                 f'  unfold poseRadius; rw [angle{index:02}_exact]; rfl',
                 f'private theorem cache{index:02}_exact : cache{index:02}.Exact {name} := by',
                 '  unfold PlanCache.Exact',
                 '  refine ⟨?_, ?_, ?_, ?_⟩',
                 f'  · change cache{index:02}.inputs = cutRows {source}',
                 f'    simp only [cutRows,lowerCut,upperCut,radius{index:02}_exact]',
                 '    decide +kernel',
                 '  · decide +kernel',
                 f'  · exact @of_decide_eq_true',
                 f'      (∀ entry ∈ cache{index:02}.supports, rows entry.1.target = entry.2)',
                 f'      (List.decidableBAll _ cache{index:02}.supports) (by decide +kernel)',
                 f'  · change cache{index:02}.closing = upper (leftHi + (poseRadius {source}).radius) false',
                 f'    rw [radius{index:02}_exact]',
                 '    decide +kernel',
                 f'private theorem shape{index:02} : {name}.Shape := by decide +kernel',
                 f'private theorem numeric{index:02} : cache{index:02}.Numeric {name} := by',
                 '  decide +kernel',
                 f'private theorem {name}_checked : {name}.Check :=',
                 f'  cache{index:02}.toCheck {name} cache{index:02}_exact shape{index:02} numeric{index:02}', '']
    tail = ['def plans : List DirectPlan := ['+', '.join(names)+']', '',
            'theorem plans_checked : ∀ plan ∈ plans, plan.Check := by',
            '  intro plan member',
            '  simp only [plans,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member',
            '  rcases member with '+' | '.join('rfl' for _ in names)]
    tail += [f'  · exact {name}_checked' for name in names]
    tail += [
            'theorem plans_covered : DirectCoverCheck continuousScout898Domain5_0Ids',
            '    continuousScout898Domain5_11Ids plans := by decide +kernel', '',
            '#print axioms plans_checked', 'end N12Compact.C898Chord.Fused', '']
    data_source = '\n'.join(head+tail)
    neighbors = ['import Compact.Cases.C898.ChordFusedGeometry',
                 'import Compact.Cases.C898.SharedDomains', '',
                 'namespace N12Compact.C898Chord.Fused',
                 'open S12 S12Pilot C898Shared AngleSection',
                 'set_option Elab.async false', 'set_option maxRecDepth 100000',
                 'set_option maxHeartbeats 0', '']
    for step, name, lo, hi in ((9,'LeftNeighbors','leftLo','leftHi'),
                               (10,'RightNeighbors','rightLo','rightHi')):
        path = ROOT/f'Compact/Cases/C898/ChordStep{step}.lean'
        paths.append(path)
        text = path.read_text()
        block = text[text.index('def neighbors0'):text.index('def plans')]
        neighbors += [f'namespace {name}', f'def lo : ℚ := {lo}', f'def hi : ℚ := {hi}',
                      block, f'end {name}', '']
    neighbors += ['end N12Compact.C898Chord.Fused', '']
    neighbor_source = '\n'.join(neighbors)
    output = {
        ROOT/'Compact/Cases/C898/ChordFusedData.lean': data_source,
        ROOT/'Compact/Cases/C898/ChordFusedNeighbors.lean': neighbor_source,
    }
    assert sum(len(s.encode()) for s in output.values()) <= 256*1024
    report = {'scope':'Exact direct-support preparation; not Lean acceptance.',
              'source_roots':len(sources),'target_poses':len(targets),
              'empty_angles':sorted(missing),'two_row_supports':support_count,
              'old_chord_branch_plans_replaced':105,'old_chord_links_replaced':101,
              'old_intermediate_relaxed_poses_bypassed':52,
              'lean_lines':sum(s.count('\n') for s in output.values()),
              'lean_bytes':sum(len(s.encode()) for s in output.values()),
              'inputs':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in paths}, 'elapsed_seconds':time.monotonic()-start}
    # All arithmetic/source checks finish before any generated output is written.
    for path, text in output.items():
        path.write_text(text)
    (ROOT/'evidence/c898-fused-chord.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
