#!/usr/bin/env python3
"""Read one ZIP member at a time; resolve RawSupport bases to actual source rows.

This is a serialization/provenance audit, not certificate or Lean validation.
No archive extraction, numerical optimization, or subprocess is performed.
"""
import collections
import hashlib
import json
import math
from pathlib import Path
import re
import zipfile

ZIP = Path(__import__('os').environ.get('N12_C981_ZIP', str(Path(__file__).resolve().parents[1] / 'inputs/C981-progress-2026-10-10.zip')))
OUT = Path(__file__).with_name('c981-support-inventory.json')


def numbers(s):
    return tuple(int(x) for x in s.split(',') if x.strip())


def primitive(values):
    divisor = math.gcd(*values)
    return tuple(v // divisor for v in values) if divisor else tuple(values)


def exact_row(row):
    x, y, c, d, strict = row
    g = math.gcd(x, y, c, d)
    return x // g, y // g, c // g, d // g, strict


def semantic_row(row):
    return primitive(row[:3]) + (row[4],)


def table(text, name, typ):
    pattern = r'def ' + name + r' : Array ' + re.escape(typ) + r' := #\[(.*?)\n\]'
    match = re.search(pattern, text, re.S)
    if match is None:
        raise ValueError('missing table ' + name)
    return match.group(1)


def audit():
    counts = collections.Counter()
    unique_rows, unique_semantic_rows = set(), set()
    unique_supports, unique_semantic_supports = set(), set()
    sections, skipped = [], []
    largest_member = 0
    with zipfile.ZipFile(ZIP) as archive:
        files = [n for n in archive.namelist()
                 if '/Completion/Cases/C981/' in n and n.endswith('.lean')]
        for path in files:
            data = archive.read(path)
            largest_member = max(largest_member, len(data))
            text = data.decode()
            counts['lean_files'] += 1
            counts['lean_bytes'] += len(data)
            counts['lean_lines'] += data.count(b'\n')
            counts['basis_recipe_occurrences'] += len(re.findall(r'\.basis\s*⟨', text))
            for section in re.split(r'(?m)^namespace ', text)[1:]:
                name = section.splitlines()[0]
                if 'def supports : Array RawSupport' not in section:
                    continue
                try:
                    row_text = table(section, 'rawRows', 'RawRow')
                    rows = [tuple(map(int, m[:4])) + (m[4] == 'true',)
                            for m in re.findall(r'⟨(-?\d+),(-?\d+),(-?\d+),(\d+),(true|false)⟩', row_text)]
                    assert len(rows) == row_text.count('⟨')
                    assert all(r[3] > 0 for r in rows)
                    pose_text = table(section, 'rawPoses', 'RawPose')
                    poses = [(int(a), numbers(b)) for a, b in
                             re.findall(r'⟨(\d+),\[([\d,]*)\]⟩', pose_text)]
                    assert len(poses) == pose_text.count('⟨')
                    neighbors = numbers(re.search(
                        r'def neighbors : List PoseLeaf := \(select poses \[([\d,]*)\]', section).group(1))
                    direction_text = table(section, 'directions', '(Int × Int)')
                    directions = [tuple(map(int, m)) for m in
                                  re.findall(r'\((-?\d+),(-?\d+)\)', direction_text)]
                    support_text = table(section, 'supports', 'RawSupport')
                    supports = [(int(a), int(b), numbers(c)) for a, b, c in
                                re.findall(r'⟨(\d+),(\d+),\[([\d,]*)\]⟩', support_text)]
                    assert len(supports) == support_text.count('⟨')
                    for row in rows:
                        unique_rows.add(exact_row(row))
                        unique_semantic_rows.add(semantic_row(row))
                    local_supports = set()
                    for neighbor, direction, basis in supports:
                        ids = poses[neighbors[neighbor]][1]
                        selected = tuple(rows[ids[i]] for i in basis)
                        assert len(basis) in (1, 2)
                        key = (directions[direction], tuple(sorted(exact_row(r) for r in selected)))
                        semantic = (primitive(directions[direction]),
                                    tuple(sorted(semantic_row(r) for r in selected)))
                        local_supports.add(key)
                        unique_supports.add(key)
                        unique_semantic_supports.add(semantic)
                        counts['support_basis_arity_' + str(len(basis))] += 1
                    counts['support_sections'] += 1
                    counts['raw_row_occurrences'] += len(rows)
                    counts['raw_support_occurrences'] += len(supports)
                    sections.append({'namespace': name, 'file': path,
                                     'file_sha256': hashlib.sha256(data).hexdigest(),
                                     'rows': len(rows), 'supports': len(supports),
                                     'distinct_resolved_supports_within_section': len(local_supports)})
                except (AttributeError, AssertionError, IndexError, ValueError) as exc:
                    skipped.append({'namespace': name, 'reason': str(exc) or type(exc).__name__})
    result = {'scope': 'C981 RawSupport tables only; linear RegionTree implications are separately counted but not semantically decoded',
              'validation': 'parser index and positive denominator checks only, not Lean checking or certificate soundness',
              'counts': dict(counts), 'unique_exact_rows': len(unique_rows),
              'unique_positive_scale_rows': len(unique_semantic_rows),
              'unique_resolved_exact_supports': len(unique_supports),
              'unique_positive_scale_supports': len(unique_semantic_supports),
              'largest_member_read_bytes': largest_member,
              'sections': sections, 'unparsed_support_sections': skipped}
    OUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'sections'}, indent=2))


if __name__ == '__main__':
    audit()
