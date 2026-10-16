#!/usr/bin/env python3
"""Complete the five small alternative-owner branches by segment crossings.

Running this also runs the eight direct case writer, then assembles all 13.
Every finite assignment survives the original certified domains. Every bad
assignment carries a rational crossing certificate checked separately in Lean.
No numerical optimizer, Lean process, or sampled hull is used.
"""
import hashlib
import itertools
import json
from provenance_source import read_bytes
from fractions import Fraction as F
import build_four_square_high_right as base

ROOT = base.ROOT
POINT = lambda xs: tuple(map(F, xs))
MARKERS = list(map(POINT, [
    (1, '457/500'), ('457/500', 1), (3, '457/500'), ('1543/500', 1),
    (3, '1543/500'), ('1543/500', 3), (1, '1543/500'), ('457/500', 3),
    ('33/20', '33/20'), ('47/20', '33/20'), ('47/20', '47/20'), ('33/20', '47/20'),
    ('457/500', 2), (2, '457/500'), ('1543/500', 2), (2, '1543/500')]))
AUX = list(map(POINT, [
    (1, '87/50'), (1, '113/50'), ('8/5', 1), ('8/5', 3), (2, '87/50'),
    (2, '113/50'), ('12/5', 1), ('12/5', 3), (3, '87/50'), (3, '113/50'),
    (1, '8/5'), (1, '12/5'), ('87/50', 1), ('87/50', 2), ('87/50', 3),
    ('113/50', 1), ('113/50', 2), ('113/50', 3), (3, '8/5'), (3, '12/5')]))


def inside(mask, owned):
    # Only primitive original markers and auxiliary points are needed.
    return ([MARKERS[i] for i in range(16) if mask >> i & 1] +
            [AUX[i] for i in range(20) if owned >> i & 1])


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def crossing(pa, pb):
    for p, q in itertools.combinations(pa, 2):
        for r, s in itertools.combinations(pb, 2):
            v, w = sub(q, p), sub(s, r)
            det = cross(v, w)
            if not det:
                continue
            t, u = cross(sub(r, p), w) / det, cross(sub(r, p), v) / det
            if 0 <= t <= 1 and 0 <= u <= 1:
                assert tuple((1-t)*p[k]+t*q[k] for k in range(2)) == tuple(
                    (1-u)*r[k]+u*s[k] for k in range(2))
                return p, q, r, s, t, u


def finite_assignments(domains, order):
    result = []

    def visit(k, used, chosen):
        if k == len(order):
            result.append(chosen)
            return
        for value in domains[order[k]]:
            if not value & used:
                visit(k+1, used | value, chosen+[value])

    visit(0, 0, [])
    assert len(result) <= 4
    return result


def point(p):
    return '(' + ','.join(map(str, p)) + ')'


certificates = []
report = {'validation': 'Exact finite assembly only; full Lean replay pending.', 'cases': []}
for case in [678, 680, 691, 694, 711]:
    path = ROOT / f'evidence/historical/data/case{case}-input.json'
    raw = read_bytes(path)
    data = json.loads(raw)
    masks = [sum(1 << i for i in g) for g in data['row']['groups']]
    domains, declarations = base.derive_domains(case, masks)
    order = sorted(domains, key=lambda m: len(domains[m]))
    assignments = finite_assignments(domains, order)
    role_masks = [masks[i] for i in base.ROLES[case]]
    role_values = [data['domains'][i][0] for i in base.ROLES[case]]
    swapped = case not in [680, 711]
    left_barrier = 1 if swapped else 2
    decisions = []
    for assignment in assignments:
        actual = dict(zip(order, assignment))
        if all(actual[m] == v for m, v in zip(role_masks, role_values)):
            decisions.append({'kind': 'template'})
            continue
        found = None
        for ma, mb in itertools.combinations(order, 2):
            witness = crossing(inside(ma, actual[ma]), inside(mb, actual[mb]))
            if witness:
                certificate = (ma, mb, actual[ma], actual[mb], *witness)
                if certificate not in certificates:
                    certificates.append(certificate)
                found = {'kind': 'crossing', 'certificate': certificates.index(certificate),
                         'first_mask': ma, 'second_mask': mb}
                break
        assert found is not None, (case, assignment)
        decisions.append(found)
    entry = {'id': case, 'source': str(path.relative_to(ROOT)),
             'sha256': hashlib.sha256(raw).hexdigest(), 'domain_order': order,
             'assignments': assignments, 'branches': decisions,
             'role_masks': role_masks, 'role_values': role_values,
             'transform': [swapped, False, False], 'left_barrier_mask': left_barrier}
    report['cases'].append(entry)
    fs = base.finset
    source = ['import Compact.Bridge.FourSquareCaseHighRight',
              'import Compact.Bridge.OwnerBudget',
              'import Compact.Cases.FourSquareHighRight.Crossings',
              'import S12.DomainEnumeration', 'import S12.DomainSpecData', '',
              f'/-! Original case {case}: exhaustive ownership alternatives, then',
              'the shared geometry or a strict segment crossing. -/',
              'namespace N12Compact.FourSquareHighRightCases',
              'open S12 OwnerBudget FourSquareCaseHighRight',
              'set_option maxRecDepth 10000', 'set_option maxHeartbeats 0', '',
              f'def family{case} : Finset Nat := {fs(sorted(masks))}', '']
    source += declarations
    source += [f'def domains{case} : List (CertifiedDomain family{case}) :=',
               '  [' + ','.join(f'domain{case}_{m}' for m in order) + ']', '',
               f'theorem domains{case}_members : ∀ d ∈ domains{case}, d.mask ∈ family{case} := by decide +kernel',
               f'theorem domains{case}_distinct : domains{case}.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel', '',
               f'def data{case} : FourSquareCaseHighRight.Data :=',
               f'  ⟨⟨{str(swapped).lower()},false,false⟩, ![' + ','.join(map(str, role_masks)) + '],',
               '    ![' + ','.join(fs(base.members(v)) for v in role_values) + f'], {left_barrier}⟩', '',
               f'theorem data{case}_checked : data{case}.Check family{case} := by decide +kernel', '',
               f'def assignments{case} : List (List (Finset Nat)) :=',
               '  [' + ',\n   '.join('[' + ','.join(fs(base.members(v)) for v in a) + ']'
                                      for a in assignments) + ']', '',
               f'theorem assignments{case}_checked : DomainCasesCheck domains{case} assignments{case} := by decide +kernel', '',
               f'theorem case{case}_impossible (p : NormalizedPacking)',
               f'    (hf : codedMarkerFamily p = family{case}) : False := by',
               f'  have h := domain_cases_sound domains{case} domains{case}_members domains{case}_distinct',
               f'    assignments{case} assignments{case}_checked p hf',
               f'  simp only [assignments{case}, List.mem_cons, List.not_mem_nil, or_false] at h',
               '  rcases h with ' + ' | '.join(f'h{i}' for i in range(len(assignments)))]
    for branch, (assignment, decision) in enumerate(zip(assignments, decisions)):
        actual = dict(zip(order, assignment))
        if decision['kind'] == 'template':
            source += [f'  · apply FourSquareCaseHighRight.impossible_of_owned data{case} family{case}',
                       f'      data{case}_checked p hf', '    intro i', '    fin_cases i']
            for m, v in zip(role_masks, role_values):
                source += [f'    · have hh := congrArg (fun xs : List (Finset Nat) => xs[{order.index(m)}]!) h{branch}',
                           f'      change natCombinedOwners p (ownerIndex p {m}) = {fs(base.members(v))} at hh',
                           '      exact hh']
        else:
            idx, ma, mb = decision['certificate'], decision['first_mask'], decision['second_mask']
            source += [f'  · apply OwnerSegmentCrossing.impossible crossing{idx} crossing{idx}_inputs crossing{idx}_checked',
                       f'      family{case} (by decide +kernel) (by decide +kernel) p hf']
            for m in [ma, mb]:
                source += [f'    · have hh := congrArg (fun xs : List (Finset Nat) => xs[{order.index(m)}]!) h{branch}',
                           f'      change natCombinedOwners p (ownerIndex p {m}) = {fs(base.members(actual[m]))} at hh',
                           '      exact hh']
    source += ['', f'#print axioms case{case}_impossible',
               'end N12Compact.FourSquareHighRightCases', '']
    (ROOT / f'Compact/Cases/FourSquareHighRight/Case{case}.lean').write_text('\n'.join(source))

source = ['import Compact.Bridge.OwnerSegmentCrossing', '',
          '/-! Literal strict segment intersections, shared across the five cases. -/',
          'namespace N12Compact.FourSquareHighRightCases',
          'open S12 OwnerSegmentCrossing', '']
report['crossings'] = []
for idx, (ma, mb, oa, ob, p, q, r, s, t, u) in enumerate(certificates):
    source += [f'def crossing{idx} : OwnerSegmentCrossing.Data :=',
               '  ⟨' + f'{ma},{mb},{base.finset(base.members(oa))},{base.finset(base.members(ob))},',
               '    ' + ','.join(point(pt) for pt in [p, q, r, s]) + f', {t}, {u}⟩', '',
               f'theorem crossing{idx}_inputs : crossing{idx}.InputCheck := by decide +kernel',
               f'theorem crossing{idx}_checked : crossing{idx}.CrossCheck := by',
               f'  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing{idx}]', '']
    report['crossings'].append({'id': idx, 'masks': [ma, mb], 'owned': [oa, ob],
                                'points': [[str(x), str(y)] for x, y in [p, q, r, s]],
                                'weights': [str(t), str(u)]})
source += ['end N12Compact.FourSquareHighRightCases', '']
(ROOT / 'Compact/Cases/FourSquareHighRight/Crossings.lean').write_text('\n'.join(source))

all_cases = sorted(base.accepted + [entry['id'] for entry in report['cases']])
(ROOT / 'Compact/Cases/FourSquareHighRight.lean').write_text(''.join(
    f'import Compact.Cases.FourSquareHighRight.Case{case}\n' for case in all_cases))
assembly = ['import Compact.Cases.FourSquareHighRight', 'import Completion.Contracts', '',
            '/-! All thirteen original obligations of the higher-right family. -/',
            'namespace N12Compact.FourSquareHighRightCases', 'open S12 S12Completion',
            'set_option maxRecDepth 10000', 'set_option maxHeartbeats 0', '',
            f'def coveredIds : Finset Nat := {base.finset(all_cases)}', '',
            'def coveredFamilies : List (Nat × Finset Nat) :=',
            '  [' + ','.join(f'({c},family{c})' for c in all_cases) + ']', '',
            'theorem covered_families_excluded : ∀ entry ∈ coveredFamilies, ExcludesFamily entry.2 := by',
            '  intro entry h',
            '  simp only [coveredFamilies, List.mem_cons, List.not_mem_nil, or_false] at h',
            '  rcases h with ' + ' | '.join('rfl' for _ in all_cases)]
assembly += [f'  · exact case{case}_impossible' for case in all_cases]
assembly += ['', 'theorem covered_rows_checked : ∀ r ∈ retainedRows, r.originalId ∈ coveredIds →',
             '    (r.originalId, r.groups) ∈ coveredFamilies := by decide +kernel', '',
             'theorem covered_cases_excluded (id : Nat) (hid : id ∈ coveredIds) : ExcludesCase id := by',
             '  intro r hr he',
             '  exact covered_families_excluded (r.originalId, r.groups)',
             '    (covered_rows_checked r hr (by simpa only [he] using hid))', '',
             '#print axioms covered_cases_excluded', 'end N12Compact.FourSquareHighRightCases', '']
(ROOT / 'Compact/Assembly/FourSquareHighRightCases.lean').write_text('\n'.join(assembly))
report['elapsed_seconds_including_direct_cases'] = base.time.monotonic() - base.START
report['peak_rss_bytes_macos'] = base.resource.getrusage(base.resource.RUSAGE_SELF).ru_maxrss
assert report['peak_rss_bytes_macos'] < 30 * 1024 * 1024
(ROOT / 'evidence/four-square-high-right-alternatives.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'assembled': all_cases, 'crossings': len(certificates),
                  'finite_branches': sum(len(c['assignments']) for c in report['cases']),
                  'rss_bytes': report['peak_rss_bytes_macos']}))
