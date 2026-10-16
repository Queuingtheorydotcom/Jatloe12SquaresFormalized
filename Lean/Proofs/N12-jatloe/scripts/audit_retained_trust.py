#!/usr/bin/env python3
"""Source-only import and trust-site inventory; no Lean or proof acceptance.

Reads each selected local source once, strips nested comments and quoted strings,
and records explicit trust-related syntax. The root manifest remains immutable.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LOCAL = {'Compact', 'Completion', 'S12'}
TRUST = re.compile(r'\b(?:sorry|admit|axiom|native_decide|ofReduceBool|ofReduceNat|unsafe|implemented_by|extern|mkSorry|axiomDecl|evalExpr|trustLevel)\b')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def lex_source(text):
    """Blank nested Lean comments and strings, preserving positions and lines."""
    chars = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        else:
            raw = re.match(r'r(#+)"', text[i:i+24]) if text[i] == 'r' else None
            if raw:
                close = '"' + raw.group(1)
                end = text.find(close, i + len(raw.group(0)))
                i = len(text) if end < 0 else end + len(close)
            elif text[i] == '"':
                i += 1
                while i < len(text):
                    if text[i] == '\\':
                        i += 2
                    elif text[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
            else:
                i += 1
                continue
        for j in range(start, min(i, len(text))):
            if chars[j] != '\n':
                chars[j] = ' '
    return ''.join(chars)


def source_path(module):
    relative = Path(*module.split('.')).with_suffix('.lean')
    return ROOT / 'source' / relative if module.startswith('S12.') else ROOT / relative


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--extra-root', action='append', default=[])
    parser.add_argument('--report', type=Path, default=ROOT/'audit/retained-trust-source.json')
    args = parser.parse_args()
    manifest_path = ROOT/'evidence/preferred-delivery-roots.json'
    manifest_raw = manifest_path.read_bytes()
    manifest = json.loads(manifest_raw)
    roots = list(dict.fromkeys(manifest['roots'] + args.extra_root))
    records, seen, active, missing, cycles = {}, set(), set(), {}, []
    external, sites = set(), []

    def visit(module, parent):
        if module.split('.')[0] not in LOCAL:
            external.add(module)
            return
        if module in active:
            cycles.append({'module': module, 'importer': parent})
            return
        if module in seen:
            return
        seen.add(module)
        file = source_path(module)
        if not file.is_file():
            missing.setdefault(module, []).append(parent)
            return
        raw = file.read_bytes()
        original = raw.decode()
        lexed = lex_source(original)
        deps = [name for line in re.findall(r'^[ \t]*import[ \t]+([^\n]+)', lexed, re.M)
                for name in line.split()]
        relative = str(file.relative_to(ROOT))
        records[module] = {'path': relative, 'sha256': digest(raw), 'bytes': len(raw),
                           'lines': len(raw.splitlines()), 'imports': deps}
        for match in TRUST.finditer(lexed):
            line = lexed.count('\n', 0, match.start()) + 1
            sites.append({'module': module, 'path': relative, 'line': line,
                          'token': match.group(), 'source': original.splitlines()[line-1].strip()})
        active.add(module)
        for dep in deps:
            visit(dep, module)
        active.remove(module)

    for root in roots:
        visit(root, '<root>')
    changed = [module for module, record in records.items()
               if digest((ROOT/record['path']).read_bytes()) != record['sha256']]
    result = {'checked_at': datetime.now(timezone.utc).isoformat(),
        'scope': 'Explicit preferred local source import closure plus named chord pilots; lexical audit only.',
        'root_manifest_sha256': digest(manifest_raw), 'roots': roots,
        'local_modules': len(records), 'local_source_bytes': sum(x['bytes'] for x in records.values()),
        'local_source_lines': sum(x['lines'] for x in records.values()),
        'missing_local_imports': missing, 'import_cycles': cycles,
        'external_imports_not_audited': sorted(external),
        'trust_syntax_sites': sites, 'source_changed_during_scan': changed,
        'root_manifest_changed_during_scan': digest(manifest_path.read_bytes()) != digest(manifest_raw),
        'files': records,
        'kernel_acceptance_claimed': False,
        'limitation': 'Absence of suspicious source syntax is not a theorem axiom audit. Ordinary proof acceptance, macro output and transitive external axioms require Lean replay and #print axioms.'}
    args.report.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()
                     if k not in {'files','external_imports_not_audited','trust_syntax_sites','roots'}}))
    print(json.dumps({'trust_token_counts': dict(Counter(x['token'] for x in sites)),
                      'trust_modules': len({x['module'] for x in sites}),
                      'full_site_list': str(args.report.relative_to(ROOT))}))


if __name__ == '__main__':
    main()
