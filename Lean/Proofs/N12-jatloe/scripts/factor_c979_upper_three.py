#!/usr/bin/env python3
"""Split existing upper-three ownership metadata into ordinary kernel batches."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'Compact/Cases/C979/EntryQueryChunks'
MANIFEST = ROOT / 'audit/c979-upper-three-factor.json'
IMPORT = 'import Compact.Core.FiniteKernelDecision\n'


def sha(source):
    return hashlib.sha256(source.encode()).hexdigest()


def git(*args):
    return subprocess.check_output(
        ['git', '-c', 'safe.directory=' + str(ROOT.parents[1]), *args], cwd=ROOT, text=True)


def indexed_proofs(name, mask, low, high, allowed, kind, old_metadata):
    signature = name + 'Signatures'
    claim = name + '_owned_claim'
    helpers = f'''private def {claim} (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  {low} ≤ owned.card → owned.card ≤ {high} →
    owned ∈ ({allowed} : List (Finset Nat)) ∨ ({mask},{kind},owned) ∈ {signature}

private instance : DecidablePred {claim} := fun index => by
  unfold {claim}
  infer_instance

private theorem {name}_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

'''
    for block in range(22):
        helpers += f'''private theorem {name}_owned_block{block} :
    N12Compact.FiniteCheckChunks.Check {claim} {block} := by
  intro offset valid
  dsimp only [{claim}]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

'''
    metadata = old_metadata[:-len('  decide +kernel\n')]
    metadata += f'''  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [{name}_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound {claim}
    (count := 22) (by decide) (by
      intro block
      fin_cases block
'''
    for block in range(22):
        metadata += f'      · exact {name}_owned_block{block}\n'
    metadata += f'''    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [{claim}] at indexed
  rw [value] at indexed
  exact indexed low high
'''
    return helpers, metadata


def factor(original):
    match = re.search(r'^def (single979_\d+_[01]) : DirectSingleDomain := ⟨(\d+),(\d+),(\d+),(\[.*?\]),\[', original, re.M)
    if not match or int(match[4]) != 3:
        raise ValueError('Expected an original upper-three domain')
    name, mask, low, high, allowed = match.groups()
    kind = name.rsplit('_', 1)[1]
    signature = name + 'Signatures'
    claim = name + '_owned_claim'
    start = original.index('private theorem ' + name + '_metadata')
    end = original.index('#check ' + name + '_metadata', start)
    old_metadata = original[start:end]
    if not old_metadata.endswith('  decide +kernel\n'):
        raise ValueError('Unexpected original metadata decision')
    helpers, metadata = indexed_proofs(name, mask, low, high, allowed, kind, old_metadata)
    source = IMPORT + original[:start] + helpers + metadata + original[end:]
    if source.count('native_decide') != original.count('native_decide'):
        raise ValueError('Native inventory changed')
    report = {'name': name, 'original_sha256': sha(original), 'source_sha256': sha(source),
              'original_metadata': old_metadata, 'helpers': helpers,
              'metadata': metadata, 'subsets': 176, 'blocks': 22, 'block_size': 8}
    return source, report


def reconstruct(source, record):
    insertion = record['helpers'] + record['metadata']
    if not source.startswith(IMPORT) or source.count(insertion) != 1:
        raise ValueError('Generated kernel metadata differs')
    return source[len(IMPORT):].replace(insertion, record['original_metadata'], 1)


def check():
    report = json.loads(MANIFEST.read_text())
    for record in report['records']:
        source = (ROOT / record['path']).read_text()
        original = reconstruct(source, record)
        if sha(source) != record['source_sha256'] or sha(original) != record['original_sha256']:
            raise ValueError('Source inverse differs: ' + record['path'])
        baseline = git('show', report['baseline_commit'] + ':' + 'projects/n12-refactored/' + record['path'])
        if original != baseline:
            raise ValueError('Original differs from recorded Git baseline')
        expected, fields = factor(original)
        if source != expected or fields != {k: v for k, v in record.items() if k != 'path'}:
            raise ValueError('Deterministic producer differs')
    if len(report['records']) != 8:
        raise ValueError('Expected all eight original upper-three domains')
    print(json.dumps({'source_inverse': 'pass', 'domains': 8, 'subsets_per_domain': 176,
                      'ordinary_kernel_blocks': 176, 'new_modules': 0,
                      'new_native_sites': 0, 'lean_accepted': False}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        check()
        return
    baseline_commit = (json.loads(MANIFEST.read_text())['baseline_commit']
                       if MANIFEST.exists() else git('rev-parse', 'HEAD').strip())
    records = []
    for path in sorted(OUT.glob('Chunk*.lean')):
        relative = path.relative_to(ROOT).as_posix()
        original = git('show', baseline_commit + ':projects/n12-refactored/' + relative)
        match = re.search(r'^def single979_\d+_[01] : DirectSingleDomain := ⟨\d+,\d+,(\d+),', original, re.M)
        if not match or int(match[1]) != 3:
            continue
        proposed, fields = factor(original)
        if path.read_text() not in (original, proposed):
            raise ValueError('Unexpected local edit: ' + relative)
        records.append({'path': relative, **fields})
    if len(records) != 8:
        raise ValueError('Original upper-three domain inventory differs')
    for record in records:
        path = ROOT / record['path']
        original = git('show', baseline_commit + ':projects/n12-refactored/' + record['path'])
        path.write_text(factor(original)[0])
    MANIFEST.write_text(json.dumps({'baseline_commit': baseline_commit, 'records': records,
                                  'new_modules': 0, 'new_native_sites': 0,
                                  'lean_accepted': False}, indent=2) + '\n')
    check()


if __name__ == '__main__':
    main()
