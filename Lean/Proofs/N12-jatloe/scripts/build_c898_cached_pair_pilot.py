#!/usr/bin/env python3
"""Emit exact C898 Step14 cached-vertex pair proofs; never invoke Lean.

The authenticated pilot is exactly eight sources times 53 neighbors. Each
two-row basis gets one cached intersection and one opaque membership/identity
proof. Pair decisions use only local cached values, not the global row table.
Explicit --run; intended parent guard:192MiB,120sec,8MiB output. No archives.
"""
from pathlib import Path
from functools import reduce
from math import gcd
import argparse
import hashlib
import json
import re
import resource
import signal
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'Compact/Cases/C898'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def row_text(row):
    return '⟨' + ', '.join(map(str, row['integers'])) + ', ' + str(row['strict']).lower() + '⟩'


def vertex(a, b):
    ax, ay, ac = a['integers']
    bx, by, bc = b['integers']
    x, y, d = ay * bc - ac * by, ac * bx - ax * bc, ax * by - ay * bx
    assert d != 0
    if d < 0:
        x, y, d = -x, -y, -d
    common = reduce(gcd, (abs(x), abs(y), d))
    x, y, d = x // common, y // common, d // common
    assert ax*x + ay*y + ac*d == 0 and bx*x + by*y + bc*d == 0 and d > 0
    return x, y, d


def strict_support(a, b, x, y):
    ax, ay, _ = a['integers']
    bx, by, _ = b['integers']
    det = ax*by-ay*bx
    sign = 1 if det > 0 else -1
    left, right = sign*(x*by-y*bx), sign*(ax*y-ay*x)
    assert left >= 0 and right >= 0 and sign*det > 0
    return (left > 0 and a['strict']) or (right > 0 and b['strict'])


def ref_text(ref):
    return '⟨' + ', '.join(map(str, ref)) + '⟩'


def header(imports):
    return [*[f'import {name}' for name in imports], '',
            'set_option Elab.async false', 'set_option maxRecDepth 10000',
            'set_option linter.unnecessarySeqFocus false', '',
            'namespace N12Compact.C898Cached',
            'open C898Shared CachedSupportFan', 'noncomputable section', '']


def footer():
    return ['', 'end', 'end N12Compact.C898Cached', '']


def chunk_check_lines(prefix, predicate, sources, neighbors):
    """Opaque batches bound reduction caches, with one shared coverage theorem."""
    count = (neighbors+7)//8
    lines = []
    for source in range(sources):
        for block in range(count):
            lines += [f'theorem {prefix}_source{source}_block{block} :',
                      f'    FiniteCheckChunks.Check ({predicate} {source}) {block} := by',
                      '  decide +kernel', '']
        lines += [f'theorem {prefix}_source{source}_checked (j : Fin {neighbors}) :',
                  f'    {predicate} {source} j := by',
                  f'  refine FiniteCheckChunks.sound ({predicate} {source}) (count := {count})',
                  '    (by decide) ?_ j', '  intro block', '  fin_cases block']
        lines += [f'  · exact {prefix}_source{source}_block{block}' for block in range(count)]
        lines += ['']
    return lines


def coverage_lines(sources,neighbors):
    source_ids=', '.join(str(s['pose']) for s in sources)
    neighbor_ids=', '.join(str(n['pose']) for n in neighbors)
    return [f'def cachedStep14SourcePoseId : Fin 8 → Fin poseCount := ![{source_ids}]',
            f'def cachedStep14NeighborPoseId : Fin 53 → Fin poseCount := ![{neighbor_ids}]','',
            'theorem cachedStep14_source_pose_exact (i : Fin 8) :',
            '    (cachedStep14Source i).pose = cachedStep14SourcePoseId i := by',
            '  fin_cases i <;> rfl','',
            'theorem cachedStep14_neighbor_pose_exact (j : Fin 53) :',
            '    (cachedStep14Neighbor j).pose = cachedStep14NeighborPoseId j := by',
            '  fin_cases j <;> rfl','',
            'theorem cachedStep14_source_empty (i : Fin 8) :',
            '    (cachedStep14Source i).block = [] := by fin_cases i <;> rfl','',
            'private theorem source_ids_complete :',
            '    ∀ source ∈ continuousScout898Domain5_14Ids,',
            '      ∃ i : Fin 8, cachedStep14SourcePoseId i = source := by',
            '  have exact_ids : (List.finRange 8).map cachedStep14SourcePoseId =',
            '      continuousScout898Domain5_14Ids := by rfl',
            '  intro source member', '  rw [← exact_ids] at member',
            '  obtain ⟨i, _, hi⟩ := List.mem_map.mp member', '  exact ⟨i, hi⟩','',
            'private theorem neighbor_ids_complete :',
            '    ∀ neighbor ∈ continuousScout898Domain9_8Ids,',
            '      ∃ j : Fin 53, cachedStep14NeighborPoseId j = neighbor := by',
            '  have exact_ids : (List.finRange 53).map cachedStep14NeighborPoseId =',
            '      continuousScout898Domain9_8Ids := by rfl',
            '  intro neighbor member', '  rw [← exact_ids] at member',
            '  obtain ⟨j, _, hj⟩ := List.mem_map.mp member', '  exact ⟨j, hj⟩','',
            'theorem cachedStep14_sources_complete :',
            '    ∀ source ∈ continuousScout898Domain5_14Ids, ∃ i : Fin 8,',
            '      (cachedStep14Source i).pose = source ∧ (cachedStep14Source i).block = [] := by',
            '  intro source member',
            '  obtain ⟨i,hi⟩ := source_ids_complete source member',
            '  exact ⟨i,(cachedStep14_source_pose_exact i).trans hi,cachedStep14_source_empty i⟩','',
            'theorem cachedStep14_neighbors_complete :',
            '    ∀ neighbor ∈ continuousScout898Domain9_8Ids, ∃ j : Fin 53,',
            '      (cachedStep14Neighbor j).pose = neighbor := by',
            '  intro neighbor member',
            '  obtain ⟨j,hj⟩ := neighbor_ids_complete neighbor member',
            '  exact ⟨j,(cachedStep14_neighbor_pose_exact j).trans hj⟩','']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('source-only preparation requires explicit --run from the coordinating worker')
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('120-second deadline')))
    signal.alarm(120)
    start = time.monotonic()
    inputs = [ROOT/'evidence/c898-step14-support-fan-pilot.json',
              ROOT/'evidence/c898-shared-pose-map.json', OUT/'References.lean']
    pilot, shared = [json.loads(path.read_text()) for path in inputs[:2]]
    refs = [tuple(map(int, match)) for match in re.findall(
        r'⟨(-?\d+), (-?\d+), (\d+), (-?\d+), (\d+)⟩', inputs[2].read_text())[:64]]
    assert len(refs) == 64
    records = pilot['record_map']
    sources = list(dict.fromkeys((r['source_context'], r['source'], r['block'], r['angles'][0]) for r in records))
    neighbors = list(dict.fromkeys((r['neighbor_context'], r['neighbor'], r['angles'][1]) for r in records))
    assert len(records) == 424 and len(sources) == 8 and len(neighbors) == 53
    assert all((r['source_context'],r['neighbor_context']) ==
               (sources[i//53][0],neighbors[i%53][0]) for i,r in enumerate(records))
    contexts = pilot['contexts']
    assert len(contexts) == 61
    mapping = {c['original_context']: c['local_fan'] for c in contexts}
    assert len(mapping) == 61
    roles = {c: ('source',p,b,a) for c,p,b,a in sources}
    roles.update({c: ('neighbor',p,None,a) for c,p,a in neighbors})
    assert len(roles) == 61
    rows, poses, blocks = shared['rows'], shared['poses'], shared['blocks']
    data = header(['Compact.Cases.C898.CachedPairFan'])
    cert = header(['Compact.Cases.C898.PairStep14CachedData'])
    diagnostic_context = header(['Compact.Cases.C898.PairStep14CachedData'])
    cache = {}
    for context in contexts:
        ident, local = context['original_context'], context['local_fan']
        role, pose, block, angle = roles[ident]
        assert poses[pose]['angle'] == angle
        indices = ([] if block is None else blocks[block]['rows']) + poses[pose]['rows']
        input_expr = f'poseRows {pose}' if block is None else f'blockRows {block} ++ poseRows {pose}'
        entries = context['entries']
        assert 0 < len(entries) <= 7
        values = []
        data += [f'def cachedInputs{local} : List (Fin rowCount) := {input_expr}', '',
                 f'def cachedEntries{local} : Array (Entry rowCount) := #[']
        for key, first, second in entries:
            assert first in indices and second in indices
            a, b = rows[first], rows[second]
            x, y, d = vertex(a, b)
            values.append((key, a, b, x, y, d))
            data.append(f'  ⟨{key}, {first}, {second}, ⟨{row_text(a)}, {row_text(b)}, {x}, {y}, {d}⟩⟩,')
        cache[ident] = values
        data += [']', '', f'def cachedEntry{local} (i : Fin {len(entries)}) : Entry rowCount :=',
                 f'  cachedEntries{local}[i.val]ʼ(by change i.val < {len(entries)}; exact i.isLt)'.replace('ʼ', "'"), '',
                 f'def cachedReference{local} : ReferenceAxis.Reference := {ref_text(refs[angle])}', '']
        proof = [f'theorem cachedEntries{local}_checked (i : Fin {len(entries)}) :',
                 f'    (cachedEntry{local} i).Check rows cachedInputs{local} := by',
                 '  revert i', '  decide +kernel', '']
        cert += proof
        if local == 0:
            diagnostic_context += proof + ['#print axioms cachedEntries0_checked']
        cert += [f'def cachedContext{local} : Context rows :=',
                 f'  ⟨cachedInputs{local}, cachedReference{local},',
                 f'    ⟨cachedEntry{local} 0, cachedEntries{local}_checked 0⟩,',
                 f'    Array.ofFn (fun i : Fin {len(entries)} =>',
                 f'      ⟨cachedEntry{local} i, cachedEntries{local}_checked i⟩)⟩', '',
                 f'theorem cachedReference{local}_exact :',
                 f'    cachedReference{local} = references (poseAngle {pose}) := by',
                 '  decide +kernel', '', f'def cachedPose{local} : PoseContext where',
                 f'  pose := {pose}',
                 f'  block := ' + ('[]' if block is None else f'blockRows {block}'),
                 f'  keyAngle := {angle}', f'  context := cachedContext{local}',
                 '  inputs_exact := by rfl' if block is not None else
                 f'  inputs_exact := by change poseRows {pose} = [] ++ poseRows {pose}; rfl',
                 f'  reference_exact := cachedReference{local}_exact', '']
    # Independently recheck every chosen cached support against every original
    # axis. This audit only validates emitted candidate data; Lean decides it.
    def select(ident, key):
        selected = cache[ident][0]
        for item in cache[ident]:
            if item[0] <= key:
                selected = item
        return selected
    for record in records:
        ac, bc = record['source_context'], record['neighbor_context']
        aa, ba = record['angles']
        a, b = refs[aa], refs[ba]
        for axis in range(8):
            angle = aa if axis < 4 else ba
            quadrant = [0,2,1,3][axis%4]
            key = 64*quadrant+angle
            c, s = refs[angle][:2]
            x, y = [(c,s),(-s,c),(-c,-s),(s,-c)][quadrant]
            A, B = select(ac,key), select(bc,(key+128)%256)
            astrict = strict_support(A[1],A[2],x,y)
            bstrict = strict_support(B[1],B[2],-x,-y)
            ax, ay, ad = A[3:]
            bx, by, bd = B[3:]
            scale = 2*a[2]*a[4]*b[2]*b[4]
            radius = a[3]*(abs(x*a[0]+y*a[1])+abs(-x*a[1]+y*a[0]))*b[2]*b[4] + \
                     b[3]*(abs(x*b[0]+y*b[1])+abs(-x*b[1]+y*b[0]))*a[2]*a[4]
            lhs = scale*(bd*(-x*ax-y*ay)+ad*(x*bx+y*by))
            rhs = ad*bd*radius
            assert lhs <= rhs and (lhs < rhs or astrict or bstrict)
    for label, records0 in [('Source',sources),('Neighbor',neighbors)]:
        cert += [f'def cachedStep14{label}Data : Array PoseContext := #[',
                 '  ' + ', '.join(f'cachedPose{mapping[item[0]]}' for item in records0), ']', '',
                 f'def cachedStep14{label} (i : Fin {len(records0)}) : PoseContext :=',
                 f'  cachedStep14{label}Data[i.val]ʼ(by change i.val < {len(records0)}; exact i.isLt)'.replace('ʼ', "'"), '']
    cert += ['def CachedStep14Pair (i : Fin 8) (j : Fin 53) : Prop :=',
             '  (cachedStep14Source i).PairCheck (cachedStep14Neighbor j)', '',
             'instance (i : Fin 8) (j : Fin 53) : Decidable (CachedStep14Pair i j) :=',
             '  inferInstanceAs (Decidable ((cachedStep14Source i).PairCheck _))', '']
    proofs = header(['Compact.Cases.C898.PairStep14CachedContexts',
                     'Compact.Core.FiniteCheckChunks'])
    proofs += chunk_check_lines('cachedStep14','CachedStep14Pair',8,53)
    proofs += ['theorem cachedStep14_checked (i : Fin 8) (j : Fin 53) :',
               '    CachedStep14Pair i j := by', '  fin_cases i']
    proofs += [f'  · exact cachedStep14_source{i}_checked j' for i in range(8)]
    proofs += ['', 'theorem cachedStep14_overlap (i : Fin 8) (j : Fin 53)',
               '    (q t : S12Pilot.OpenSquare)',
               '    (hq : (poses (cachedStep14Source i).pose).Realizes q)',
               '    (ht : (poses (cachedStep14Neighbor j).pose).Realizes t)',
               '    (block : ∀ k ∈ (cachedStep14Source i).block,',
               '      (rows k).Holds ![S12.centerX q, S12.centerY q]) :',
               '    ∃ x y, q.Inside x y ∧ t.Inside x y := by',
               '  apply PoseContext.pair_sound _ _ (cachedStep14_checked i j) q t hq ht block',
               '  have empty : ∀ k : Fin 53, (cachedStep14Neighbor k).block = [] := by',
               '    decide +kernel',
               '  simp only [empty j, List.not_mem_nil, false_implies, forall_const]', '',
               '#print axioms cachedStep14_overlap']
    first = header(['Compact.Cases.C898.PairStep14CachedContexts'])
    first += ['theorem cachedStep14_first4 :',
              '    ∀ j : Fin 4, CachedStep14Pair 0 ⟨j.val, by omega⟩ := by',
              '  decide +kernel', '', '#print axioms cachedStep14_first4']
    first8 = header(['Compact.Cases.C898.PairStep14CachedContexts',
                     'Compact.Core.FiniteCheckChunks'])
    first8 += ['theorem cachedStep14_first8 :',
               '    FiniteCheckChunks.Check (CachedStep14Pair 0) 0 := by',
               '  decide +kernel', '', '#print axioms cachedStep14_first8']
    whole = header(['Compact.Cases.C898.PairStep14CachedPilot',
                    'Compact.Cases.C898.SharedDomains', 'S12.OrientedCoverage'])
    whole += coverage_lines([{'pose':s[1]} for s in sources],[{'pose':n[1]} for n in neighbors])
    whole += ['/-- The complete original terminal transition, with every source and',
              'neighbor covered. No pair records, complement plans or relaxation links',
              'are needed because all eight original pruning blocks are empty. -/',
              'theorem pairStep14_sound (q t : S12Pilot.OpenSquare)',
              '    (hq : S12.OrientedPoseCovered continuousScout898Domain5_14 q)',
              '    (ht : S12.OrientedPoseCovered continuousScout898Domain9_8 t)',
              '    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :',
              '    S12.OrientedPoseCovered continuousScout898Domain5_15 q := by',
              '  obtain ⟨source, member, realizes⟩ := hq',
              '  obtain ⟨source, in_sources, rfl⟩ := List.mem_map.mp member',
              '  obtain ⟨i, hi, empty⟩ := cachedStep14_sources_complete source in_sources',
              '  obtain ⟨neighbor, member, neighbor_realizes⟩ := ht',
              '  obtain ⟨neighbor, in_neighbors, rfl⟩ := List.mem_map.mp member',
              '  obtain ⟨j, hj⟩ := cachedStep14_neighbors_complete neighbor in_neighbors',
              '  obtain ⟨x, y, overlap⟩ := cachedStep14_overlap i j q t',
              '    (by simpa only [hi] using realizes.1)',
              '    (by simpa only [hj] using neighbor_realizes.1)',
              '    (by simp only [empty, List.not_mem_nil, false_implies, forall_const])',
              '  exact (disjoint x y overlap).elim', '',
              '#print axioms pairStep14_sound']
    outputs = {
        'PairStep14CachedData.lean': data,
        'PairStep14CachedContexts.lean': cert,
        'PairStep14CachedFirstContext.lean': diagnostic_context,
        'PairStep14CachedFirst4.lean': first,
        'PairStep14CachedFirst8.lean': first8,
        'PairStep14CachedPilot.lean': proofs,
        'PairStep14Cached.lean': whole,
    }
    rendered = {name:'\n'.join(lines+footer()) for name,lines in outputs.items()}
    assert sum(len(text.encode()) for text in rendered.values()) < 8*1024*1024
    for name,text in rendered.items():
        path = OUT/name
        temporary = path.with_suffix('.lean.tmp')
        temporary.write_text(text)
        temporary.replace(path)
    report = {
        'scope':'exact whole424-pair Step14 candidate source; no Lean acceptance claimed',
        'pairs':424,'axes':3392,'sources':8,'neighbors':53,'contexts':61,
        'cached_basis_entries':sum(len(c['entries']) for c in contexts),
        'pair_check_batch_size':8,'opaque_batch_lemmas':56,
        'cartesian_record_order_verified':True,'all_axis_arithmetic_verified':True,
        'input_sha256':{str(p.relative_to(ROOT)):sha(p) for p in inputs},
        'output':{str((OUT/n).relative_to(ROOT)):{'sha256':sha(OUT/n),
                  'bytes':len(t.encode()),'lines':t.count('\n')} for n,t in rendered.items()},
        'source_index_map':[dict(zip(['original_context','pose','block','angle'],s)) for s in sources],
        'neighbor_index_map':[dict(zip(['original_context','pose','angle'],n)) for n in neighbors],
        'elapsed_seconds':time.monotonic()-start,
        'peak_ru_maxrss_platform_units':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'trust_boundary':'candidate offline arithmetic does not prove exclusions; generic soundness, copied-row identities, membership, all424pair checks and original whole-step domain coverage require Lean acceptance',
    }
    (ROOT/'evidence/c898-step14-cached-pair-pilot.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['pairs','axes','contexts','cached_basis_entries','elapsed_seconds']}))


if __name__ == '__main__':
    main()
