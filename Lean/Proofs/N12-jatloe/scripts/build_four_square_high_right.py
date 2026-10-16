#!/usr/bin/env python3
"""Bind the checked high-right geometry to exact original case data.

This small writer audits literal domains and emits ordinary Lean obligations;
it is not a proof oracle. It never invokes Lean, Lake or a numerical solver.
The finite audit has a 10-second and 30-MiB guard. An archived singleton is
accepted only when the independently proved input domains force that value.
"""
from pathlib import Path
from provenance_source import read_bytes, read_text
import hashlib
import json
import re
import resource
import signal
import sys
import time

signal.alarm(10)
START = time.monotonic()
ROOT = Path(__file__).resolve().parents[1]
TEXT = (ROOT / 'source/S12/DomainSpecData.lean').read_text()
ROLES = {
    678: [11, 7, 10, 3], 680: [11, 8, 9, 4],
    691: [10, 7, 9, 3], 694: [10, 7, 9, 3],
    711: [11, 7, 8, 4],
    846: [7, 6, 9, 3], 847: [7, 6, 9, 3],
    852: [7, 6, 9, 3], 853: [7, 6, 9, 3],
    886: [6, 5, 9, 3], 887: [6, 5, 9, 3],
    1073: [6, 5, 9, 2], 1074: [6, 5, 9, 2],
}
EXTRA_ROLES = {
    669: [8, 9, 10, 4], 670: [8, 9, 10, 4],
    673: [8, 7, 10, 3], 674: [8, 7, 10, 3],
    675: [6, 7, 10, 1], 690: [10, 7, 9, 3],
    848: [7, 6, 9, 3], 850: [7, 6, 9, 3],
}
EXTRA_MODE = '--extra' in sys.argv
FAMILY_NAME = 'FourSquareHighRightExtra' if EXTRA_MODE else 'FourSquareHighRight'
NAMESPACE = FAMILY_NAME + 'Cases'


def sets(text):
    return [sum(1 << int(i) for i in re.findall(r'\d+', s))
            for s in re.findall(r'\{([^}]*)\}', text)]


def members(mask):
    return [i for i in range(20) if mask >> i & 1]


def finset(values):
    return '{' + ','.join(map(str, values)) + '}' if values else '∅'


single = {}
for i, m, k, lo, hi, allowed in re.findall(
        r'def singleSpec(\d+) : SingleSpec := ⟨(\d+),(\d+),(\d+),(\d+),\[([^\]]*)\]', TEXT):
    if lo == hi == '1':
        single[int(m), int(k)] = (int(i), sets(allowed))
single_ids = {entry[0] for entry in single.values()}
combined = {}
for i, m, f, g, allowed in re.findall(
        r'def combinedSpec(\d+) : CombinedSpec := ⟨(\d+),⟨singleSpec(\d+),singleSpec\d+_checked⟩,⟨singleSpec(\d+),singleSpec\d+_checked⟩,\[([^\]]*)\]', TEXT):
    if int(f) in single_ids and int(g) in single_ids:
        combined[int(m)] = (int(i), sets(allowed))
exempt = [set(map(int, re.findall(r'\d+', line.split(':=')[1])))
          for line in (ROOT / 'source/S12/RawData.lean').read_text().splitlines()
          if line.startswith('def exempt')]


def derive_domains(case, masks):
    domains, definitions = {}, []
    for m in masks:
        if all(m in e for e in exempt):
            continue
        name = f'domain{case}_{m}'
        if m in combined:
            i, allowed = combined[m]
            expr = (f'CertifiedDomain.ofCombined family{case} combinedSpec{i} '
                    f'combinedSpec{i}_checked (by decide +kernel)')
        else:
            halves, values = [], []
            for k in range(2):
                if m in exempt[k]:
                    halves.append(f'(HalfDomain.empty family{case} {m} {k} '
                                  '(by decide +kernel) (by decide +kernel))')
                    values.append([0])
                elif (m, k) in single:
                    i, v = single[m, k]
                    halves.append(f'(HalfDomain.ofSpec family{case} singleSpec{i} {k} '
                                  f'singleSpec{i}_checked (by decide +kernel))')
                    values.append(v)
                else:
                    halves.append(f'(HalfDomain.singleton family{case} {m} {k} '
                                  '(by decide +kernel) (by decide +kernel))')
                    values.append([1 << i for i in range(10)])
            expr = f'OwnerBudget.product family{case} {m}\n    ' + '\n    '.join(halves)
            allowed = [a | (b << 10) for a in values[0] for b in values[1]]
        domains[m] = allowed
        definitions.append(f'def {name} : CertifiedDomain family{case} :=\n  {expr}\n')
    return domains, definitions


def exact_assignments(domains):
    order = sorted(domains, key=lambda m: len(domains[m]))
    values, nodes, count = {m: set() for m in order}, 0, 0

    def visit(k, used, chosen):
        nonlocal nodes, count
        nodes += 1
        assert nodes < 100000, 'bounded finite domain audit exceeded'
        if k == len(order):
            count += 1
            for m, value in zip(order, chosen):
                values[m].add(value)
            return
        for value in domains[order[k]]:
            if not value & used:
                visit(k + 1, used | value, chosen + [value])

    visit(0, 0, [])
    return order, values, count, nodes


report = {'validation': 'Source assembly and exact finite audit only; Lean replay pending.',
          'strictness': 'Both R endpoints are actual original query-inside points. '
                       'S12.inside_segment supplies strict interior at t=7/31 and t=12/31.',
          'cases': [], 'unresolved': []}
accepted = []
outdir = ROOT / f'Compact/Cases/{FAMILY_NAME}'
outdir.mkdir(exist_ok=True)
for case, roles in (EXTRA_ROLES if EXTRA_MODE else ROLES).items():
    path = ROOT / f'evidence/historical/data/case{case}-input.json'
    raw = read_bytes(path)
    data = json.loads(raw)
    masks = [sum(1 << i for i in g) for g in data['row']['groups']]
    assert all(len(set(masks) & e) == 2 for e in exempt)
    domains, declarations = derive_domains(case, masks)
    order, values, count, nodes = exact_assignments(domains)
    selected = [(masks[i], data['domains'][i][0]) for i in roles]
    assert all(len(data['domains'][i]) == 1 for i in roles)
    entry = {'id': case, 'source': str(path.relative_to(ROOT)),
             'sha256': hashlib.sha256(raw).hexdigest(),
             'archive_role_indices': roles, 'role_masks': [m for m, _ in selected],
             'finite_assignments': count, 'finite_nodes': nodes,
             'possible_role_values': {str(m): sorted(values[m]) for m, _ in selected}}
    if any(values[m] != {v} for m, v in selected):
        report['unresolved'].append(entry)
        continue
    # The currently certified subfamily has the same coordinate swap and left
    # singleton barrier. Retain explicit assertions before writing adapters.
    transform = ([False, True, True] if case == 675 else
                 [False, False, False] if case in [669, 670] else [True, False, False])
    barrier = 32 if case == 675 else 2 if case in [669, 670] else 1
    assert barrier in masks
    if not EXTRA_MODE:
        assert case not in [680, 711]
        assert selected == [(1024, 65568), (512, 262400), (8192, 32832), (16, 131200)]
    entry['transform'] = transform
    entry['left_barrier_mask'] = barrier
    if transform == [True, False, False]:
        endpoint0, endpoint1, aux_index, seed_transform = (
            ['113/50', '3'], ['72/25', '3'], 17, [False, True, True])
    elif transform == [False, False, False]:
        endpoint0, endpoint1, aux_index, seed_transform = (
            ['3', '113/50'], ['3', '72/25'], 9, [True, True, True])
    else:
        assert transform == [False, True, True]
        endpoint0, endpoint1, aux_index, seed_transform = (
            ['1', '87/50'], ['1', '28/25'], 0, [True, False, False])
    entry['right_endpoint_provenance'] = [
        {'canonical': ['3', '113/50'], 'original': endpoint0,
         'kind': 'combined auxiliary', 'index': aux_index, 'owner_mask': selected[3][0]},
        {'canonical': ['3', '72/25'], 'original': endpoint1,
         'kind': 'singleton seed', 'base_index': 0,
         'seed_transform': seed_transform, 'owner_mask': selected[3][0]},
    ]
    source = ['import Compact.Bridge.FourSquareCaseHighRight',
              'import Compact.Bridge.OwnerBudget', 'import S12.DomainSpecData', '',
              f'/-! Original marker case {case}. Every domain and query-point premise',
              'is derived from the original packing; archived hulls are not assumptions. -/',
              f'namespace N12Compact.{NAMESPACE}',
              'open S12 OwnerBudget FourSquareCaseHighRight',
              'set_option maxRecDepth 10000', 'set_option maxHeartbeats 0', '',
              f'def family{case} : Finset Nat := {finset(sorted(masks))}', '']
    source += declarations
    source += [f'def domains{case} : List (CertifiedDomain family{case}) :=',
               '  [' + ','.join(f'domain{case}_{m}' for m in order) + ']', '',
               f'theorem domains{case}_members : ∀ d ∈ domains{case}, d.mask ∈ family{case} := by decide +kernel',
               f'theorem domains{case}_distinct : domains{case}.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel', '',
               f'def data{case} : FourSquareCaseHighRight.Data :=',
               '  ⟨⟨' + ','.join(str(t).lower() for t in transform) + '⟩, ![' +
               ','.join(str(m) for m, _ in selected) + '],',
               '    ![' + ','.join(finset(members(v)) for _, v in selected) + f'], {barrier}⟩', '',
               f'theorem data{case}_checked : data{case}.Check family{case} := by decide +kernel', '',
               f'theorem forced{case} (p : NormalizedPacking) (hf : codedMarkerFamily p = family{case}) :',
               f'    ∀ i, natCombinedOwners p (ownerIndex p (data{case}.masks i)) = data{case}.owned i := by',
               '  intro i', '  fin_cases i']
    for mask, value in selected:
        source += [f'  · exact certified_domain_forced domains{case} domains{case}_members domains{case}_distinct',
                   f'      {mask} {finset(members(value))} (by decide +kernel) p hf']
    source += ['', f'theorem case{case}_impossible (p : NormalizedPacking)',
               f'    (hf : codedMarkerFamily p = family{case}) : False :=',
               f'  FourSquareCaseHighRight.impossible data{case} family{case} data{case}_checked forced{case} p hf', '',
               f'#print axioms case{case}_impossible', f'end N12Compact.{NAMESPACE}', '']
    target = outdir / f'Case{case}.lean'
    target.write_text('\n'.join(source))
    entry['lean_path'] = str(target.relative_to(ROOT))
    entry['lean_lines'] = len(target.read_text().splitlines())
    report['cases'].append(entry)
    accepted.append(case)

if EXTRA_MODE:
    # The two vectors are exactly the already checked source format of 678,
    # replacing its mask2048 domain with the narrower mask32768 domain. Prove
    # exhaustive equality of vectors independently before reusing that text.
    old = json.loads((ROOT / 'evidence/four-square-high-right-alternatives.json').read_text())
    record = next(c for c in old['cases'] if c['id'] == 678)
    order = [32768 if m == 2048 else m for m in record['domain_order']]
    case690 = json.loads(read_text(ROOT / 'evidence/historical/data/case690-input.json'))
    masks690 = [sum(1 << i for i in g) for g in case690['row']['groups']]
    domains690, _ = derive_domains(690, masks690)
    actual_vectors = []
    def collect(k, used, chosen):
        if k == len(order):
            actual_vectors.append(chosen)
            return
        for value in domains690[order[k]]:
            if not value & used:
                collect(k+1, used | value, chosen+[value])
    collect(0, 0, [])
    assert sorted(actual_vectors) == sorted(record['assignments'])
    text = (ROOT / 'Compact/Cases/FourSquareHighRight/Case678.lean').read_text()
    text = text.replace('678', '690').replace('2048', '32768')
    text = text.replace('combinedSpec12', 'combinedSpec22')
    text = text.replace('namespace N12Compact.FourSquareHighRightCases',
                        f'namespace N12Compact.{NAMESPACE}\nopen N12Compact.FourSquareHighRightCases')
    text = text.replace('end N12Compact.FourSquareHighRightCases', f'end N12Compact.{NAMESPACE}')
    (outdir / 'Case690.lean').write_text(text)
    accepted.append(690)
    accepted.sort()
    record = dict(record, id=690, domain_order=order,
                  source='evidence/historical/data/case690-input.json',
                  sha256=hashlib.sha256(read_bytes(ROOT/'evidence/historical/data/case690-input.json')).hexdigest(),
                  validation='Two exhaustive vectors; the same crossing0 eliminates the other branch.')
    report['crossing_completed'] = record
    report['unresolved'] = []

(ROOT / f'Compact/Cases/{FAMILY_NAME}.lean').write_text(''.join(
    f'import Compact.Cases.{FAMILY_NAME}.Case{case}\n' for case in accepted))
assembly = [f'import Compact.Cases.{FAMILY_NAME}', 'import Completion.Contracts', '',
            '/-! Original case obligations discharged by the shared higher-right geometry. -/',
            f'namespace N12Compact.{NAMESPACE}', 'open S12 S12Completion',
            'set_option maxRecDepth 10000', 'set_option maxHeartbeats 0', '',
            f'def coveredIds : Finset Nat := {finset(accepted)}', '',
            'def coveredFamilies : List (Nat × Finset Nat) :=',
            '  [' + ','.join(f'({c},family{c})' for c in accepted) + ']', '',
            'theorem covered_families_excluded : ∀ entry ∈ coveredFamilies, ExcludesFamily entry.2 := by',
            '  intro entry h',
            '  simp only [coveredFamilies, List.mem_cons, List.not_mem_nil, or_false] at h',
            '  rcases h with ' + ' | '.join('rfl' for _ in accepted)]
assembly += [f'  · exact case{c}_impossible' for c in accepted]
assembly += ['', 'theorem covered_rows_checked : ∀ r ∈ retainedRows, r.originalId ∈ coveredIds →',
             '    (r.originalId, r.groups) ∈ coveredFamilies := by decide +kernel', '',
             'theorem covered_cases_excluded (id : Nat) (hid : id ∈ coveredIds) : ExcludesCase id := by',
             '  intro r hr he',
             '  exact covered_families_excluded (r.originalId, r.groups)',
             '    (covered_rows_checked r hr (by simpa only [he] using hid))', '',
             '#print axioms covered_cases_excluded', f'end N12Compact.{NAMESPACE}', '']
(ROOT / f'Compact/Assembly/{NAMESPACE}.lean').write_text('\n'.join(assembly))
report['elapsed_seconds'] = time.monotonic() - START
report['peak_rss_bytes_macos'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
assert report['peak_rss_bytes_macos'] < 30 * 1024 * 1024
evidence = 'four-square-high-right-extra.json' if EXTRA_MODE else 'four-square-high-right-family.json'
(ROOT / f'evidence/{evidence}').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'assembled': accepted, 'unresolved': [c['id'] for c in report['unresolved']],
                  'seconds': report['elapsed_seconds'], 'rss_bytes': report['peak_rss_bytes_macos']}))
