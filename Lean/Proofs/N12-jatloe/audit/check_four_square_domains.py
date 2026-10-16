"""Small, bounded adapter audit; does not generate or validate Lean proofs.

Run under the project's aggregate RSS guard. Every search is capped at 100000
nodes, and the entire process has a 15 second wall alarm.
"""
import json
import re
import signal
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from provenance_source import read_text

signal.alarm(15)
ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / 'source/S12/DomainSpecData.lean').read_text()
singles = {}
for no, mask, kind, lower, upper, allowed in re.findall(
        r'def singleSpec(\d+) : SingleSpec := ⟨(\d+),(\d+),(\d+),(\d+),\[([^\]]*)\]', source):
    if lower == upper == '1':
        singles[int(mask), int(kind)] = (int(no), [
            sum(1 << int(v) for v in item.split(',') if v)
            for item in re.findall(r'\{([^}]*)\}', allowed)])
combined = {}
for no, mask, first, second, allowed in re.findall(
        r'def combinedSpec(\d+) : CombinedSpec := ⟨(\d+),⟨singleSpec(\d+),[^⟩]+⟩,⟨singleSpec(\d+),[^⟩]+⟩,\[([^\]]*)\]', source):
    if all(any(v[0] == int(i) for v in singles.values()) for i in [first, second]):
        combined[int(mask)] = (int(no), [
            sum(1 << int(v) for v in item.split(',') if v)
            for item in re.findall(r'\{([^}]*)\}', allowed)])

failed = []
for case in [28, 78, 537, 556, 565, 567, 569, 570, 575, 576, 577, 585, 1085, 1086, 1087]:
    record = json.loads(read_text(ROOT / f'evidence/historical/data/case{case}-input.json'))
    masks = [sum(1 << v for v in group) for group in record['row']['groups']]
    domains, specs = [], []
    for mask in masks:
        if mask in [12, 48, 192]:
            domains.append([0]); specs.append('budget0')
        elif mask in combined:
            domains.append(combined[mask][1]); specs.append(f'combinedSpec{combined[mask][0]}')
        else:
            first = singles.get((mask, 0), ('budget1', [1 << n for n in range(10)]))
            second = singles.get((mask, 1), ('budget1', [1 << n for n in range(10)]))
            # Independently proved seed/segment ownership, followed by card=1.
            if mask in [8196, 8708]:
                second = ('wallSeedHull', [1 << 5])
            if mask == 4098:
                second = ('wallSeedHull', [1 << 0])
            if mask == 64:
                second = ('singletonSeed', [1 << 4])
            domains.append([a | (b << 10) for a in first[1] for b in second[1]])
            specs.append([first[0], second[0]])
    order = sorted(range(len(domains)), key=lambda i: len(domains[i]))
    seen = [set() for _ in domains]
    assignment = [0] * len(domains)
    nodes, solutions = [0], [0]

    def visit(depth, used):
        nodes[0] += 1
        if nodes[0] > 100000:
            raise RuntimeError('node budget exceeded')
        if depth == len(domains):
            solutions[0] += 1
            for index, value in enumerate(assignment):
                seen[index].add(value)
            return
        index = order[depth]
        for value in domains[index]:
            if not value & used:
                assignment[index] = value
                visit(depth + 1, used | value)

    visit(0, 0)
    selected = ([7, 8, 9, 10] if case in [28, 537, 556] else
                [7, 6, 10, 8] if case in [575, 576] else
                [6, 5, 9, 11] if case in [1085, 1086, 1087] else [6, 7, 8, 10])
    if any(sorted(seen[i]) != sorted(record['domains'][i]) for i in selected):
        failed.append(case)
    print(json.dumps(dict(case=case, solutions=solutions[0], nodes=nodes[0],
                          needed=[dict(mask=masks[i], possible=sorted(seen[i]),
                                       target=record['domains'][i]) for i in selected],
                          specs=dict(zip(masks, specs)))))
if failed:
    raise SystemExit(f'Required owner sets are not uniquely proved for cases {failed}')
