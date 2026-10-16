#!/usr/bin/env python3
"""Keep all C717 ownership subsets while bounding each kernel decision."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from factor_c979_upper_three import git, indexed_proofs

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Compact/Cases/C717/EntryQueries.lean'
MANIFEST = ROOT / 'audit/c717-upper-three-factor.json'
OUT = ROOT / 'Compact/Cases/C717/EntryQueryChunks'
IMPORT = 'import Compact.Core.FiniteKernelDecision\n'
FOOTER = 'end\nend S12\n'
AGGREGATE = ('import Compact.Cases.C717.EntryQueryChunks.Chunk00\n'
             'import Compact.Cases.C717.EntryQueryChunks.Chunk01\n')
RELATIVE = 'projects/n12-refactored/Compact/Cases/C717/EntryQueries.lean'


def sha(source):
    return hashlib.sha256(source.encode()).hexdigest()


def factor(original):
    source, records = original, []
    for match in re.finditer(r'^def (single717_\d+_[01]) : DirectSingleDomain := ⟨(\d+),(\d+),(\d+),(\[.*?\]),\[', original, re.M):
        name, mask, low, high, allowed = match.groups()
        if int(high) != 3:
            continue
        kind = name.rsplit('_', 1)[1]
        signature = name + 'Signatures'
        old_public = f'''theorem {name}_checked : {name}.Check case717Family {kind} :=
  N12Compact.SmallOwnerDomainThree.checked {name} case717Family {kind}
    {signature} (by rfl) (by decide) (by decide +kernel)
'''
        if source.count(old_public) != 1:
            raise ValueError('Original public ownership proof differs: ' + name)
        exact = f'''private theorem {name}_queries_exact :
    {signature} = {name}.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

'''
        old_metadata = f'''private theorem {name}_metadata :
    N12Compact.SmallOwnerDomainThree.Check {name} case717Family {kind} {signature} := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨{mask},{low},{high},{allowed},[]⟩ : DirectSingleDomain)
    case717Family {kind} {signature}
  decide +kernel
'''
        helpers, metadata = indexed_proofs(name, mask, low, high, allowed, kind, old_metadata)
        new_public = old_public.replace('(by rfl) (by decide) (by decide +kernel)',
                                        f'{name}_queries_exact (by decide) {name}_metadata')
        generated = exact + helpers + metadata + '\n' + new_public
        source = source.replace(old_public, generated, 1)
        records.append({'name': name, 'original_public': old_public, 'generated': generated,
                        'blocks': 22, 'subsets': 176})
    if len(records) != 8:
        raise ValueError('Expected eight original upper-three domains')
    source = IMPORT + source
    if source.count('native_decide') != original.count('native_decide'):
        raise ValueError('Native inventory changed')
    return source, {'original_sha256': sha(original), 'source_sha256': sha(source),
                    'records': records, 'new_modules': 0, 'new_native_sites': 0,
                    'lean_accepted': False}


def partition(source):
    first = source.index('def single717_0_0 :')
    middle = source.index('def single717_6_0 :')
    if not source.endswith(FOOTER):
        raise ValueError('Original namespace footer differs')
    header = source[:first]
    return {'Chunk00.lean': header + source[first:middle] + FOOTER,
            'Chunk01.lean': header + source[middle:]}


def delivery(original):
    source, fields = factor(original)
    parts = partition(source)
    fields.update({'new_modules': 2, 'aggregate_sha256': sha(AGGREGATE),
                   'partitions': {name: sha(body) for name, body in parts.items()}})
    return source, parts, fields


def check():
    report = json.loads(MANIFEST.read_text())
    first = (OUT / 'Chunk00.lean').read_text()
    second = (OUT / 'Chunk01.lean').read_text()
    header = first[:first.index('def single717_0_0 :')]
    if not second.startswith(header) or not first.endswith(FOOTER):
        raise ValueError('Partition headers or footer differ')
    source = first[:-len(FOOTER)] + second[len(header):]
    if not source.startswith(IMPORT):
        raise ValueError('Kernel helper import differs')
    original = source[len(IMPORT):]
    for record in report['records']:
        if original.count(record['generated']) != 1:
            raise ValueError('Generated ownership block differs')
        original = original.replace(record['generated'], record['original_public'], 1)
    baseline = git('show', report['baseline_commit'] + ':' + RELATIVE)
    if original != baseline:
        raise ValueError('Original source differs from recorded Git baseline')
    expected, parts, fields = delivery(original)
    if (expected != source or SOURCE.read_text() != AGGREGATE or
            fields != {k: v for k, v in report.items() if k != 'baseline_commit'}):
        raise ValueError('Deterministic source inverse differs')
    for name, body in parts.items():
        if (OUT / name).read_text() != body:
            raise ValueError('Partition differs: ' + name)
    print(json.dumps({'source_inverse': 'pass', 'domains': 8, 'ordinary_kernel_blocks': 176,
                      'new_native_sites': 0, 'new_modules': 2, 'lean_accepted': False}))


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
    proposed, parts, report = delivery(original)
    if SOURCE.read_text() not in (original, proposed, AGGREGATE):
        raise ValueError('Unexpected local C717 edit')
    OUT.mkdir(exist_ok=True)
    for name, body in parts.items():
        path = OUT / name
        if path.exists() and path.read_text() != body:
            raise ValueError('Unexpected local partition edit: ' + name)
        path.write_text(body)
    SOURCE.write_text(AGGREGATE)
    MANIFEST.write_text(json.dumps({'baseline_commit': baseline_commit, **report}, indent=2) + '\n')
    check()


if __name__ == '__main__':
    main()
