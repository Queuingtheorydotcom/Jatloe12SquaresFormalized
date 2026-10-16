#!/usr/bin/env python3
"""Change only transparent row syntax; dry-run unless --apply is supplied.

All five literal fields and their order must compare identically after rewriting.
This does not establish a Lean theorem or evaluate a numerical certificate.
"""
from pathlib import Path
import argparse, hashlib, json, re

ROOT = Path(__file__).resolve().parents[1]
TABLE = re.compile(r'(def (?:rowData|extraRows) : Array \(Row × Nat\) := )#\[\n(.*?)\n\]', re.S)
ENTRY = re.compile(r'  ⟨⟨(-?\d+), (-?\d+), (-?\d+), (true|false)⟩, (\d+)⟩,?')
NEW_ENTRY = re.compile(r'  \((-?\d+), (-?\d+), (-?\d+), (true|false), (\d+)\),')

def convert(path):
    source = path.read_text()
    matches = list(TABLE.finditer(source))
    assert len(matches) == 1, (str(path), 'expected exactly one old literal row table')
    match = matches[0]
    old_lines = match[2].splitlines()
    fields = []
    for line in old_lines:
        entry = ENTRY.fullmatch(line)
        assert entry, (str(path), 'unrecognized row literal')
        fields.append(entry.groups())
    new_lines = ['  (' + ', '.join(entry) + '),' for entry in fields]
    assert fields == [NEW_ENTRY.fullmatch(line).groups() for line in new_lines]
    replaced = match[1].replace('Array (Row × Nat)', 'Array (Array (Row × Nat))') + 'row_chunks%[\n' + '\n'.join(new_lines) + '\n]'
    output = source[:match.start()] + replaced + source[match.end():]
    output = output.replace('((rowData[i.val]?).getD (⟨0, 0, 0, false⟩, 0))', '(RowSyntax.lookup rowData i.val)')
    output = output.replace('((extraRows[i.val]?).getD (⟨0,0,0,false⟩,0))', '(RowSyntax.lookup extraRows i.val)')
    output = output.replace('((extraRows[i.val - 26026]?).getD (⟨0,0,0,false⟩,0))', '(RowSyntax.lookup extraRows (i.val - 26026))')
    if 'import Compact.Core.RowSyntax\n' not in output:
        output = 'import Compact.Core.RowSyntax\n' + output
    return output, {'path': str(path.relative_to(ROOT)), 'rows': len(fields),
                    'before_sha256': hashlib.sha256(source.encode()).hexdigest(),
                    'after_sha256': hashlib.sha256(output.encode()).hexdigest(),
                    'bytes_before': len(source.encode()), 'bytes_after': len(output.encode()),
                    'all_literal_fields_and_order_identical': True}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('paths', nargs='*', default=[
        'Compact/Cases/C898/SharedRows.lean', 'Compact/Cases/C898/Initial/Rows.lean'])
    args = parser.parse_args()
    results = [((ROOT / name).resolve(), *convert((ROOT / name).resolve())) for name in args.paths]
    # Validate the entire selection before mutating any file.
    if args.apply:
        for path, output, _ in results:
            path.write_text(output)
    report = {'applied': args.apply, 'kernel_check_status': 'pending',
              'transformation': 'fully typed transparent constructor terms in bounded 256-row chunks via RowSyntax',
              'tables': [record for _, _, record in results]}
    if args.apply:
        (ROOT / 'evidence/c898-typed-row-literals.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
