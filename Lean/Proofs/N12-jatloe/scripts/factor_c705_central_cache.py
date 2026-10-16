#!/usr/bin/env python3
"""Reproduce the complete central-owner cache checks without changing its labels."""
import argparse
import hashlib
import json
from pathlib import Path
import re
from factor_c979_upper_three import git

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Compact/Completion/OtherCases/C705716/InitialDomains.lean'
MANIFEST = ROOT / 'audit/c705-central-cache-factor.json'
RELATIVE = 'projects/n12-refactored/Compact/Completion/OtherCases/C705716/InitialDomains.lean'
IMPORT = 'import Compact.Core.FiniteKernelDecision\n'


def sha(source):
    return hashlib.sha256(source.encode()).hexdigest()


def boolean_proofs(source, close=True):
    old = r'trim \(product(\d+) b\) combinedQueries\1 \(by decide \+kernel\)'
    new = r'trim (product\1 b) combinedQueries\1 (by cases b <;> decide +kernel)'
    if not close:
        old = r'trim \(product(\d+) b\) combinedQueries\1 \(by cases b <;> decide \+kernel\)'
        new = r'trim (product\1 b) combinedQueries\1 (by decide +kernel)'
    result, count = re.subn(old, new, source)
    if count != 8:
        raise ValueError('Expected all eight original Boolean trim obligations')
    return result


def factor(complete_original):
    source = boolean_proofs(complete_original)
    start = source.index('def initial6 (b : Bool)')
    end = source.index('def initial7 (b : Bool)', start)
    original = source[start:end]
    match = re.search(r'\(if b then (\[.*?\]) else (\[.*?\])\)\n', original)
    if not match:
        raise ValueError('Original central cache table differs')
    yes, no = match.groups()
    generated = f'''private def initial6Allowed (b : Bool) : List (Finset Nat) :=
  if b then {yes} else {no}

'''
    for flag, product in [('false', '256'), ('true', '512')]:
        prefix = 'initial6_' + flag
        generated += f'''private def {prefix}_input : List (Finset Nat) := (product{product} {flag}).allowed

private def {prefix}_keep (owned : Finset Nat) : Bool :=
  decide (∀ query ∈ combinedQueries{product}, owned ≠ query.val.owned)

private def {prefix}_claim (index : Fin 121) : Prop :=
  let owned := {prefix}_input.getD index.val ∅
  {prefix}_keep owned = true → owned ∈ initial6Allowed {flag}

private instance : DecidablePred {prefix}_claim := fun index => by
  unfold {prefix}_claim
  infer_instance

private theorem {prefix}_length : {prefix}_input.length = 121 := by decide +kernel

'''
        for block in range(16):
            generated += f'''private theorem {prefix}_block{block} :
    N12Compact.FiniteCheckChunks.Check {prefix}_claim {block} := by
  intro offset valid
  dsimp only [{prefix}_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

'''
        generated += f'''private theorem {prefix}_checked : ∀ index : Fin 121, {prefix}_claim index :=
  N12Compact.FiniteCheckChunks.sound {prefix}_claim (count := 16) (by decide) (by
    intro block
    fin_cases block
'''
        for block in range(16):
            generated += f'    · exact {prefix}_block{block}\n'
        generated += f'''  )

private theorem {prefix}_included :
    ∀ owned ∈ (domain{product} {flag}).allowed, owned ∈ initial6Allowed {flag} := by
  change ∀ owned ∈ {prefix}_input.filter {prefix}_keep, owned ∈ initial6Allowed {flag}
  exact filter_subset_of_indexed {prefix}_input (initial6Allowed {flag}) {prefix}_keep ∅
    {prefix}_length {prefix}_checked

'''
    # Replace precisely the original parenthesized table, then the inclusion proof.
    table = '(if b then ' + yes + ' else ' + no + ')'
    replacement = original.replace(table, '(initial6Allowed b)', 1)
    needle = '(by cases b <;> decide +kernel) (by cases b <;> decide +kernel),'
    updated = '''(by cases b <;> decide +kernel) (by
      cases b
      · exact initial6_false_included
      · exact initial6_true_included),'''
    if replacement.count(needle) != 1:
        raise ValueError('Original central inclusion proof differs')
    replacement = replacement.replace(needle, updated, 1)
    proposed = 'import Compact.Core.FiniteKernelDecision\n' + source[:start] + generated + replacement + source[end:]
    inverse = proposed.removeprefix('import Compact.Core.FiniteKernelDecision\n')
    inverse = inverse.replace(generated + replacement, original, 1)
    if inverse != source:
        raise ValueError('Original source inverse failed')

    report = {'original_sha256': sha(complete_original), 'source_sha256': sha(proposed),
              'original_initial6': original, 'generated': generated + replacement,
              'candidates_per_case': 121, 'kernel_blocks': 32, 'closed_boolean_proofs': 8,
              'new_modules': 0, 'new_native_sites': 0, 'lean_accepted': False}
    return proposed, report


def check():
    report = json.loads(MANIFEST.read_text())
    source = SOURCE.read_text()
    if not source.startswith(IMPORT) or source.count(report['generated']) != 1:
        raise ValueError('Generated central cache checks differ')
    fixed = source[len(IMPORT):].replace(report['generated'], report['original_initial6'], 1)
    original = boolean_proofs(fixed, close=False)
    baseline = git('show', report['baseline_commit'] + ':' + RELATIVE)
    if original != baseline:
        raise ValueError('Original source differs from recorded Git baseline')
    expected, fields = factor(original)
    if source != expected or fields != {k:v for k,v in report.items() if k != 'baseline_commit'}:
        raise ValueError('Exact source inverse or deterministic producer differs')
    print(json.dumps({'source_inverse':'pass', 'candidates_per_case':121, 'kernel_blocks':32,
                      'closed_boolean_proofs':8, 'new_modules':0, 'new_native_sites':0,
                      'lean_accepted':False}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        check()
        return
    baseline_commit = (json.loads(MANIFEST.read_text())['baseline_commit']
                       if MANIFEST.exists() else git('rev-parse', 'HEAD').strip())
    original = git('show', baseline_commit + ':' + RELATIVE)
    proposed, report = factor(original)
    current = SOURCE.read_text()
    if current not in (original, boolean_proofs(original), proposed):
        raise ValueError('Unexpected local initial-domain edit')
    if current != proposed:
        SOURCE.write_text(proposed)
    MANIFEST.write_text(json.dumps({'baseline_commit':baseline_commit, **report}, indent=2)+'\n')
    check()


if __name__ == '__main__':
    main()
