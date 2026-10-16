#!/usr/bin/env python3
"""Count a complete candidate source union without activating proposal files.

Parent-only, read-only source census apart from its JSON report. No Lean,
subprocesses, archive reads, generation or proof acceptance is performed.
Overlay priority is explicit and every overlay output is authenticated.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
from verify import ROOT, imports

PROJECT = {'Compact', 'Completion', 'S12'}
MAX_SOURCE_BYTES = 64 * 1024 * 1024
MAX_SINGLE_BYTES = 8 * 1024 * 1024


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def local_path(name):
    path = (ROOT / name).resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError('Path outside working project: ' + str(name))
    return path


def read_small(path):
    if path.stat().st_size > MAX_SINGLE_BYTES:
        raise ValueError('Single-source size guard: ' + str(path))
    return path.read_bytes()


def module_of(relative):
    path = Path(relative)
    if path.suffix != '.lean' or '..' in path.parts or path.is_absolute():
        raise ValueError('Invalid Lean output path: ' + relative)
    if path.parts[0] == 'source':
        path = Path(*path.parts[1:])
    module = '.'.join(path.with_suffix('').parts)
    if module.split('.')[0] not in PROJECT:
        raise ValueError('Unrecognized project module: ' + module)
    return module


def module_path(module):
    relative = Path(*module.split('.')).with_suffix('.lean')
    return ROOT / 'source' / relative if module.startswith('S12.') else ROOT / relative


def output_records(manifest, key):
    value = manifest
    for part in key.split('.'):
        value = value[part]
    if isinstance(value, dict):
        return [(p, h if isinstance(h, str) else h['sha256']) for p, h in value.items()]
    return [(r['path'], r['sha256']) for r in value]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--report', type=Path,
                        default=Path('evidence/virtual-preferred-source-budget.json'))
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('Parent serial slot and --run required; no source is activated')
    started = time.monotonic()
    config_path = local_path(args.config)
    config_bytes = read_small(config_path)
    config = json.loads(config_bytes)
    preferred_path = local_path(config.get('preferred_manifest',
                                          'evidence/preferred-delivery-roots.json'))
    preferred_bytes = read_small(preferred_path)
    preferred = json.loads(preferred_bytes)
    roots = list(preferred['roots'])
    replacements = config.get('root_replacements', [])
    for replacement in replacements:
        old, new = replacement['old'], replacement['new']
        if old not in roots or not new or not replacement.get('contract_reason'):
            raise ValueError('Every retired root needs an explicit replacement and reason')
        roots.remove(old)
        roots.extend(new)
    roots.extend(config.get('additional_roots', []))
    roots = list(dict.fromkeys(roots))

    selected, overlay_info, overlay_modules = {}, [], set()
    explicitly_retained = set()
    authenticated_bytes = 0
    for overlay in config.get('overlays', []):
        base = local_path(overlay['base'])
        manifest_path = local_path(overlay['manifest'])
        manifest_bytes = read_small(manifest_path)
        if overlay.get('manifest_sha256') and digest(manifest_bytes) != overlay['manifest_sha256']:
            raise ValueError('Pinned overlay manifest changed: ' + overlay['name'])
        manifest = json.loads(manifest_bytes)
        records = output_records(manifest, overlay.get('outputs_key', 'outputs'))
        exclude = set(overlay.get('diagnostic_outputs', []))
        names = set()
        for relative, expected in records:
            if not relative.endswith('.lean'):
                continue
            module = module_of(relative)
            path = (base / relative).resolve()
            if not path.is_relative_to(base):
                raise ValueError('Overlay path traversal: ' + relative)
            raw = read_small(path)
            authenticated_bytes += len(raw)
            if authenticated_bytes > MAX_SOURCE_BYTES:
                raise ValueError('Overlay source-byte guard exceeded')
            if digest(raw) != expected:
                raise ValueError('Overlay source hash mismatch: ' + str(path))
            selected[module] = (path, overlay['name'], expected)
            overlay_modules.add(module)
            names.add(module)
            if overlay.get('retain_all_outputs', False) and relative not in exclude:
                explicitly_retained.add(module)
        if not exclude.issubset({p for p, _ in records}):
            raise ValueError('Unknown diagnostic exclusion in ' + overlay['name'])
        overlay_info.append({'name': overlay['name'], 'base': overlay['base'],
            'manifest': overlay['manifest'], 'manifest_sha256': digest(manifest_bytes),
            'authenticated_modules': len(names), 'diagnostic_outputs': sorted(exclude),
            'retain_all_outputs': overlay.get('retain_all_outputs', False)})

    seen, visiting, records, external, missing = set(), set(), {}, set(), []
    total_bytes = 0
    forbidden = config.get('forbidden_module_prefixes', [])

    def record(path, logical, origin, expected=None):
        nonlocal total_bytes
        raw = read_small(path)
        total_bytes += len(raw)
        if total_bytes > MAX_SOURCE_BYTES:
            raise ValueError('Selected-source byte guard exceeded')
        sha = digest(raw)
        if expected is not None and sha != expected:
            raise ValueError('Source changed during census: ' + str(path))
        lines = raw.splitlines()
        records[logical] = {'module_or_draft': logical,
            'path': str(path.relative_to(ROOT)), 'origin': origin, 'sha256': sha,
            'bytes': len(raw), 'lines': len(lines),
            'lexical_items': len(re.findall(rb'\w+|[^\w\s]', raw)),
            'largest_line_bytes': max(map(len, lines), default=0)}
        return imports(raw.decode())

    def visit(module, ancestry, draft=False):
        if module.split('.')[0] not in PROJECT:
            external.add(module)
            return
        if any(module.startswith(prefix) for prefix in forbidden):
            raise ValueError('Retired route remains imported: ' + ' -> '.join(ancestry + [module]))
        if module in seen:
            return
        if module in visiting:
            raise ValueError('Import cycle: ' + ' -> '.join(ancestry + [module]))
        if time.monotonic() - started > 60:
            raise ValueError('60-second metadata census guard exceeded')
        path, origin, expected = selected.get(module, (module_path(module), 'working', None))
        if not path.exists():
            missing.append({'module': module, 'ancestry': ancestry, 'retained_draft': draft})
            return
        visiting.add(module)
        dependencies = record(path, module, origin, expected)
        for dependency in dependencies:
            visit(dependency, ancestry + [module], draft)
        visiting.remove(module)
        seen.add(module)

    for root in roots:
        visit(root, [])
    root_closure = set(seen)
    for module in sorted(explicitly_retained):
        visit(module, ['explicitly retained proposal output'])
    draft_sources = preferred.get('unresolved_retained_draft_files', [])
    for draft in draft_sources:
        path = local_path(draft['path'])
        for dependency in record(path, draft['path'], 'retained unresolved draft'):
            visit(dependency, [draft['path']], True)

    allowed_missing = {m for d in draft_sources for m in
                       ([d['missing_import']] if 'missing_import' in d else d.get('missing_imports', []))}
    unexpected_missing = [m for m in missing if not m['retained_draft'] or m['module'] not in allowed_missing]
    ordered = [records[k] for k in sorted(records)]
    for source in ordered:
        if digest(read_small(local_path(source['path']))) != source['sha256']:
            raise ValueError('Source changed during census: ' + source['path'])
    if read_small(config_path) != config_bytes or read_small(preferred_path) != preferred_bytes:
        raise ValueError('Root configuration changed during census')
    summary = {'project_modules': len(seen), 'retained_draft_files': len(draft_sources),
        'all_retained_lean_files': len(ordered),
        'lines': sum(r['lines'] for r in ordered),
        'bytes': sum(r['bytes'] for r in ordered),
        'lexical_items': sum(r['lexical_items'] for r in ordered)}
    result = {'scope': 'virtual full preferred closure plus explicit retained proposal outputs and drafts',
        'config': str(config_path.relative_to(ROOT)), 'config_sha256': digest(config_bytes),
        'preferred_manifest_sha256': digest(preferred_bytes), 'roots': roots,
        'root_replacements': replacements, 'overlays_in_priority_order': overlay_info,
        'summary': summary, 'files': ordered,
        'explicitly_retained_outside_root_closure': sorted(explicitly_retained - root_closure),
        'unselected_overlay_modules': sorted(overlay_modules - seen),
        'missing_imports': missing, 'unexpected_missing_imports': unexpected_missing,
        'external_direct_imports': sorted(external),
        'external_transitive_module_count': None,
        'source_complete_except_named_retained_drafts': not unexpected_missing,
        'within_300000_source_lines': not unexpected_missing and summary['lines'] <= 300000,
        'proofs_accepted_by_this_census': False, 'all_remaining_geometry_bounded': False,
        'eventual_submillion_bound_established': False,
        'seconds': round(time.monotonic() - started, 3)}
    report = local_path(args.report)
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'report': str(report.relative_to(ROOT)), 'summary': summary,
        'unexpected_missing': unexpected_missing,
        'within_300000_source_lines': result['within_300000_source_lines']}))
    if unexpected_missing:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
