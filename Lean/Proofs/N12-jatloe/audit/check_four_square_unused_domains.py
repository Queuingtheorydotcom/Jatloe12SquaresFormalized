"""Small, bounded adapter audit; does not generate or validate Lean proofs.

The three-exempt cases use PromotedOwnerBudget: wall seed membership first
proves the special owner nonempty, then the exact budget becomes one for
all other nonexempt owners. This script assumes those proved source rules;
it does not itself validate their geometric proofs.

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
for case in [841,842]:
    record = json.loads(read_text(ROOT / f'evidence/historical/data/case{case}-input.json'))
    masks = [sum(1 << v for v in group) for group in record['row']['groups']]
    domains, specs = [], []
    for mask in masks:
        if mask in [12, 48, 192]:
            domains.append([0]); specs.append('budget0')
        elif mask == 520:
            # Reflected SingleSpec24 forces F8 or F6; exact seed/auxiliary
            # triangle forces G8 whenever F8 is owned.
            domains.append([(1 << 8) | (1 << 18)] +
                           [(1 << 6) | (1 << (10 + j)) for j in range(10)])
            specs.append('reflectedSpec24+exactHull')
        elif mask == 2112:
            # Transposed/reflected copy of the same exact triangle.
            domains.append([(1 << 3) | (1 << 14)] +
                           [(1 << j) | (1 << 11) for j in range(10)])
            specs.append('transformedSpec24+exactHull')
        elif mask == 33792:
            domains.append([(1 << f) | (1 << (g + 10))
                            for f in [7,5] for g in [6,7,9]])
            specs.append('halfTurnSpec72+exactHull')
        elif mask == 4288:
            domains.append([(1 << 1) | (1 << 11)])
            specs.append('promotedWallSeedHull')
        elif mask == 32816:
            domains.append([(1 << 7) | (1 << 17)])
            specs.append('promotedWallSeedHull')
        elif mask in combined:
            domains.append(combined[mask][1]); specs.append(f'combinedSpec{combined[mask][0]}')
        else:
            first = singles.get((mask, 0), ('budget1', [1 << n for n in range(10)]))
            second = singles.get((mask, 1), ('budget1', [1 << n for n in range(10)]))
            # Explicit original wall-seed convex combinations, then card=1.
            if mask == 4224:
                first = ('wallSeedHull', [1 << 1])
            if mask == 32784:
                first = ('wallSeedHull', [1 << 7])
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
    selected = ([7,8,9,11,6] if case in [841,842] else
                [6,5,9,11,7] if case == 995 else [6,7,8,10,5])
    if any(sorted(seen[i]) != sorted(record['domains'][i]) for i in selected):
        failed.append(case)
    print(json.dumps(dict(case=case, solutions=solutions[0], nodes=nodes[0],
                          needed=[dict(mask=masks[i], possible=sorted(seen[i]),
                                       target=record['domains'][i]) for i in selected],
                          specs=dict(zip(masks, specs)))))
if failed:
    raise SystemExit(f'Required owner sets are not uniquely proved for cases {failed}')
