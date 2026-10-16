#!/usr/bin/env python3
"""Prepare, but do not activate, an exact used-key complement dictionary.

This is a source audit and encoder, not proof acceptance. The existing Lean
PairPlan.Check still verifies every complement's actual integer coefficients.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
case = root / 'Compact/Cases/C898'
manifest = json.loads((root / 'evidence/c898-shared-pose-map.json').read_text())
dense_path = case / 'PairComplements.lean'
dense_bytes = dense_path.read_bytes()
dense = list(map(int, re.findall(r'\d+', dense_bytes.decode().split(':= #[', 1)[1].split(']', 1)[0])))
assert len(dense) == manifest['row_count'] == 26026

block_text = (case / 'PairRecords.lean').read_text().split(':= #[', 1)[1].split('\n]', 1)[0]
blocks = []
for line in block_text.splitlines():
    if line.strip():
        assert re.fullmatch(r'\s*\[[\d, ]*\],', line), line
        blocks.append(list(map(int, re.findall(r'\d+', line))))
assert blocks == [b['rows'] for b in manifest['blocks']]

steps = []
all_blocks = []
source_paths = []
for path in sorted(case.glob('PairStep[0-9][0-9].lean')):
    source = path.read_text()
    plan_lines = source.split('Plans : List PairPlan := [\n', 1)[1].split('\n]', 1)[0].splitlines()
    plan_blocks = []
    for line in plan_lines:
        match = re.match(r'\s*⟨\d+, \w+, (\(some (\d+)\)|none),', line)
        assert match, line
        if match[2] is not None:
            plan_blocks.append(int(match[2]))
    assert len(re.findall(r'\bcomplement\b', source)) == 2
    used_rows = sorted({i for block in plan_blocks for i in blocks[block]})
    steps.append({'source': str(path.relative_to(root)), 'plans': len(plan_lines),
                  'blocks': plan_blocks, 'used_rows': used_rows})
    source_paths.append(path)
    all_blocks.extend(plan_blocks)
assert len(steps) == 13
assert sorted(all_blocks) == list(range(len(blocks))) == list(range(500))
used = sorted({i for block in blocks for i in block})
used_set = set(used)
assert len(used) == 725
pairs = [(i, dense[i]) for i in used]
for i, j in pairs:
    a, b = manifest['rows'][i], manifest['rows'][j]
    assert b['integers'] == [-v for v in a['integers']]
    assert b['strict'] is not a['strict']
    assert b['denominator'] == a['denominator']

def lookup(key):
    lo, hi, depth = 0, len(pairs), 0
    for _ in range(len(pairs)):
        if lo >= hi:
            return 0, depth
        depth += 1
        mid = (lo + hi) // 2
        k, value = pairs[mid]
        if key == k:
            return value, depth
        if key < k:
            hi = mid
        else:
            lo = mid + 1
    return 0, depth

assert all(lookup(i)[0] == dense[i] for i in used)
assert all(lookup(i)[0] == (dense[i] if i in used_set else 0) for i in range(len(dense)))

lines = [
    'import Compact.Cases.C898.SharedRows', '',
    'set_option Elab.async false', 'set_option linter.unnecessarySeqFocus false', '',
    'namespace N12Compact.C898Shared', '',
    '/-- Exactly the keys used by all thirteen pairwise plans. The plan checker',
    'still verifies every returned row is the exact strict complement. -/',
    'noncomputable def complementData : Array (Nat × Fin rowCount) := #[',
]
lines += [f'  ({i}, {j}),' for i, j in pairs]
lines += [
    ']', '',
    '/-- Total bounded search. A missing key returns row zero; that value must',
    'still pass the ordinary complement check before any theorem can use it. -/',
    'private def findComplement (entries : Array (Nat × Fin rowCount)) (key : Nat) :',
    '    Nat → Nat → Nat → Fin rowCount',
    '  | 0, _, _ => 0',
    '  | fuel + 1, lo, hi =>',
    '      if lo < hi then',
    '        let mid := (lo + hi) / 2',
    '        match entries[mid]? with',
    '        | none => 0',
    '        | some (found, value) =>',
    '            if key = found then value',
    '            else if key < found then findComplement entries key fuel lo mid',
    '            else findComplement entries key fuel (mid + 1) hi',
    '      else 0', '',
    'noncomputable def complement (i : Fin rowCount) : Fin rowCount :=',
    '  findComplement complementData i.val complementData.size 0 complementData.size', '',
    'end N12Compact.C898Shared', '',
]
proposal = root / 'evidence/proposals/PairComplements.lean'
proposal.parent.mkdir(parents=True, exist_ok=True)
proposal.write_text('\n'.join(lines))
evidence = {
    'status': 'Prepared proposal only; active pilot source unchanged; Lean validation pending.',
    'dense_source': str(dense_path.relative_to(root)),
    'dense_source_sha256': hashlib.sha256(dense_bytes).hexdigest(),
    'dense_count': len(dense), 'dense_nonzero': sum(v != 0 for v in dense),
    'plan_count': sum(s['plans'] for s in steps), 'block_count': len(blocks),
    'used_key_count': len(used), 'maximum_search_steps': max(lookup(i)[1] for i in range(len(dense))),
    'every_used_value_preserved': True, 'every_used_integer_opposite_verified': True,
    'all_500_blocks_reached_exactly_once': True,
    'unused_nonzero_values_changed_to_zero': sum(dense[i] != 0 for i in range(len(dense)) if i not in used_set),
    'pairs': pairs, 'steps': steps,
    'proposal': str(proposal.relative_to(root)),
    'proposal_sha256': hashlib.sha256(proposal.read_bytes()).hexdigest(),
    'source_hashes': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in source_paths + [case / 'PairPlans.lean', case / 'PairRecords.lean',
                          root / 'Compact/Core/PairPruning.lean']},
}
(root / 'evidence/c898-sparse-complement-proposal.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({k: evidence[k] for k in ['plan_count', 'block_count', 'used_key_count',
    'maximum_search_steps', 'every_used_value_preserved', 'unused_nonzero_values_changed_to_zero']}))
