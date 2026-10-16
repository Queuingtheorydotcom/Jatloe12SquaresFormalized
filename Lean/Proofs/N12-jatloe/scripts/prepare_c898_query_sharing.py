#!/usr/bin/env python3
"""Parent-run source proposal: reuse canonical certified C898 queries.

No Lean, search, arithmetic discovery, active source mutation or network.
All genuinely new queries and every original domain/filter remain unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
RELATIVE = Path('Compact/Cases/C898/EntryDomains.lean')
DEST = ROOT/'evidence/proposals/C898SharedQueries'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('parent must schedule --run')
    assert not DEST.exists(), 'preserve the previous proposal'
    raw = (ROOT/RELATIVE).read_bytes()
    text = raw.decode()
    aliases = {}
    pattern = re.compile(r'def (query898_\d+) : LocalQuery := localQuery(\d+)\n'
                         r'theorem \1_checked : \1.Check := by\n'
                         r'  exact of_decide_eq_true \(List.all_eq_true.mp '
                         r'queryChunk(\d+)_checked \1 \(by decide \+kernel\)\)\n')

    def remove(match):
        name, number, chunk = match.groups()
        assert int(number)//50 == int(chunk), 'canonical chunk mismatch'
        assert name not in aliases
        aliases[name] = int(number)
        return ''

    result = pattern.sub(remove, text)
    assert len(aliases) == 484, ('inherited query count changed', len(aliases))
    reused, removed = 0, 0
    for name, number in aliases.items():
        pair = f'⟨{name},{name}_checked⟩'
        occurrences = result.count(pair)
        result = result.replace(pair, f'(certified_query% {number})')
        reused += occurrences
        pattern_remove = re.compile(r'\.remove _ (\w+) ' + name + r' ' + name + r'_checked ')
        result, count = pattern_remove.subn(
            lambda m: f'N12Compact.SharedLocalQueries.remove _ {m.group(1)} '
                      f'(certified_query% {number}) ', result)
        removed += count
        assert not re.search(r'\b' + name + r'(?:_checked)?\b', result), ('unhandled use', name)
    assert reused + removed == len(aliases), 'each original query should have one certified use'
    result = result.replace('import S12.LocalQueryData\n',
                            'import Compact.Bridge.SharedLocalQueries\n')
    result = result.replace('/- Original domain witnesses; identical foundation queries reuse their existing proofs. -/',
        '/- Original domain witnesses. Canonical certified queries are selected directly;\n'
        'all new query certificates and original filtering stages are retained. -/')
    # Remove only the known query declarations from the declaration census.
    old_names = set(re.findall(r'^(?:def|theorem) (\w+)', text, re.M))
    new_names = set(re.findall(r'^(?:def|theorem) (\w+)', result, re.M))
    expected_removed = set(aliases) | {name+'_checked' for name in aliases}
    assert old_names-new_names == expected_removed and not new_names-old_names
    output = result.encode()
    report = {'scope': 'Exact source sharing of inherited certified queries; Lean replay pending.',
        'lean_checked': False, 'canonical_queries_reused': len(aliases),
        'single_domain_subtype_uses': reused, 'combined_domain_filters': removed,
        'new_query_certificates_preserved': 121,
        'inputs': {str(RELATIVE): sha(raw),
            'Compact/Bridge/SharedLocalQueries.lean': sha((ROOT/'Compact/Bridge/SharedLocalQueries.lean').read_bytes())},
        'before': {'lines': raw.count(b'\n'), 'bytes': len(raw)},
        'output_files': {str(RELATIVE): {'sha256': sha(output), 'lines': output.count(b'\n'),
                                      'bytes': len(output)}},
        'query_indices': aliases}
    target = DEST/RELATIVE
    target.parent.mkdir(parents=True)
    target.write_bytes(output)
    (DEST/'manifest.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'query_indices','inputs'}}))


if __name__ == '__main__':
    main()
