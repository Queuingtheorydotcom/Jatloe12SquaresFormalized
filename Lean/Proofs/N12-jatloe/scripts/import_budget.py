#!/usr/bin/env python3
"""Read-only source-header dependency census; never starts Lean/Lake or fetches data.

Includes implicit Init, pinned toolchain source, Mathlib and its manifest packages.
Optional virtual reports resolve project modules to authenticated proposal
overlays without activation. --report writes full JSON and prints a summary.
Artifact presence is not a validity or freshness check.
The current assembled roots do not bound the missing final proof's future cost.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ROOTS = [
    'Compact.Assembly.SymbolicRegistry', 'Compact.Cases.C898.Complete',
    'Compact.Bridge.C977WallCenters', 'Compact.Bridge.C981WallCenters',
    'Compact.Cases.C981V116',
]
IDENT = re.compile(r"(?:[A-Za-z_][A-Za-z0-9_']*|«[^»]+»)(?:\.(?:[A-Za-z_][A-Za-z0-9_']*|«[^»]+»))*")
PROJECT = {'Compact', 'Completion', 'S12'}


def project_path(module):
    relative = Path(*module.split('.')).with_suffix('.lean')
    return ROOT / ('source' if module.split('.')[0] == 'S12' else '') / relative


def local_path(path):
    value = (ROOT / path).resolve()
    if not value.is_relative_to(ROOT):
        raise ValueError('Path escapes project: ' + str(path))
    return value


def sha256(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            h.update(block)
    return h.hexdigest()


class VirtualSources:
    """Validate the complete selected union, not just a convenient root subset."""
    def __init__(self, path):
        self.report_path = local_path(path)
        self.pinned_files = {}
        self.authenticated_source_bytes = 0
        def load(path, expected=None):
            if path.stat().st_size > 8 * 1024 * 1024:
                raise ValueError('Oversized virtual manifest: ' + str(path))
            raw = path.read_bytes()
            digest = hashlib.sha256(raw).hexdigest()
            if expected is not None and expected != digest:
                raise ValueError('Stale virtual report/config/manifest: ' + str(path))
            self.pinned_files[path] = digest
            return json.loads(raw)
        report = load(self.report_path)
        self.report = report
        if not report.get('source_complete_except_named_retained_drafts') or report.get('unexpected_missing_imports'):
            raise ValueError('Virtual report has unexpected missing sources')
        config_path = local_path(report['config'])
        config = load(config_path, report['config_sha256'])
        preferred_path = local_path(config.get('preferred_manifest', 'evidence/preferred-delivery-roots.json'))
        preferred = load(preferred_path, report['preferred_manifest_sha256'])
        roots = list(preferred['roots'])
        for replacement in config.get('root_replacements', []):
            if replacement['old'] not in roots or not replacement['new'] or not replacement.get('contract_reason'):
                raise ValueError('Invalid declared root replacement')
            roots.remove(replacement['old'])
            roots.extend(replacement['new'])
        roots.extend(config.get('additional_roots', []))
        self.roots = list(dict.fromkeys(roots))
        if self.roots != report['roots'] or config.get('root_replacements', []) != report['root_replacements']:
            raise ValueError('Virtual report roots do not match its configuration')
        self.forbidden = config.get('forbidden_module_prefixes', [])
        overlay_records = {}
        retained = set()
        overlays = config.get('overlays', [])
        infos = report['overlays_in_priority_order']
        if len(overlays) != len(infos):
            raise ValueError('Virtual report overlay list changed')
        for overlay, info in zip(overlays, infos):
            for key in ('name', 'base', 'manifest'):
                if overlay[key] != info[key]:
                    raise ValueError('Virtual overlay identity/order changed')
            if overlay.get('manifest_sha256', info['manifest_sha256']) != info['manifest_sha256']:
                raise ValueError('Virtual overlay pin changed')
            if bool(overlay.get('retain_all_outputs', False)) != info['retain_all_outputs'] or \
                    sorted(overlay.get('diagnostic_outputs', [])) != info['diagnostic_outputs']:
                raise ValueError('Virtual overlay retention policy changed')
            manifest = load(local_path(overlay['manifest']), info['manifest_sha256'])
            records = manifest
            for part in overlay.get('outputs_key', 'outputs').split('.'):
                records = records[part]
            records = [(p, h if isinstance(h, str) else h['sha256']) for p, h in records.items()] \
                if isinstance(records, dict) else [(r['path'], r['sha256']) for r in records]
            base = local_path(overlay['base'])
            excluded = set(overlay.get('diagnostic_outputs', []))
            if not excluded <= {p for p, _ in records}:
                raise ValueError('Unknown diagnostic exclusion')
            names = set()
            for relative, digest in records:
                path = Path(relative)
                if path.suffix != '.lean':
                    continue
                if path.is_absolute() or '..' in path.parts:
                    raise ValueError('Invalid overlay source path')
                parts = path.with_suffix('').parts
                if parts[0] == 'source':
                    parts = parts[1:]
                if not parts or parts[0] not in PROJECT:
                    raise ValueError('Unrecognized overlay module')
                module = '.'.join(parts)
                source = (base/path).resolve()
                if not source.is_relative_to(base):
                    raise ValueError('Overlay source escapes its base')
                overlay_records[module] = (source, overlay['name'], digest)
                names.add(module)
                if overlay.get('retain_all_outputs') and relative not in excluded:
                    retained.add(module)
            if len(names) != info['authenticated_modules']:
                raise ValueError('Overlay module count changed')
        self.explicitly_retained = retained
        self.extra_roots = report['explicitly_retained_outside_root_closure']
        self.draft_specs = preferred.get('unresolved_retained_draft_files', [])
        draft_paths = {d['path'] for d in self.draft_specs}
        self.allowed_missing = {m for d in self.draft_specs for m in
            ([d['missing_import']] if 'missing_import' in d else d.get('missing_imports', []))}
        self.expected_missing = {m['module'] for m in report['missing_imports']}
        if any(not m['retained_draft'] or m['module'] not in self.allowed_missing
               for m in report['missing_imports']):
            raise ValueError('Virtual report disguises unexpected missing source as a draft')
        self.modules, self.drafts = {}, {}
        for entry in report['files']:
            logical = entry['module_or_draft']
            source = local_path(entry['path'])
            if logical in draft_paths:
                if source != local_path(logical) or entry['origin'] != 'retained unresolved draft':
                    raise ValueError('Retained draft path/origin differs')
                target = self.drafts
            else:
                if logical.split('.')[0] not in PROJECT or not IDENT.fullmatch(logical):
                    raise ValueError('Invalid selected project module: ' + logical)
                expected_path, origin, expected = overlay_records.get(logical,
                    (project_path(logical).resolve(), 'working', entry['sha256']))
                if source != expected_path or entry['origin'] != origin or entry['sha256'] != expected:
                    raise ValueError('Selected source differs from overlay priority: ' + logical)
                if any(logical.startswith(prefix) for prefix in self.forbidden):
                    raise ValueError('Retired route remains selected: ' + logical)
                target = self.modules
            if logical in target:
                raise ValueError('Duplicate selected source: ' + logical)
            size = source.stat().st_size
            self.authenticated_source_bytes += size
            if size > 8*1024*1024 or self.authenticated_source_bytes > 64*1024*1024:
                raise ValueError('Virtual selected-source byte guard exceeded')
            if size != entry['bytes'] or sha256(source) != entry['sha256']:
                raise ValueError('Stale selected source: ' + str(source))
            self.pinned_files[source] = entry['sha256']
            target[logical] = entry
        if set(self.drafts) != draft_paths or not retained <= self.modules.keys():
            raise ValueError('Virtual report omitted retained source')
        summary = report['summary']
        if len(self.modules) != summary['project_modules'] or len(self.drafts) != summary['retained_draft_files'] or \
                len(report['files']) != summary['all_retained_lean_files'] or \
                sum(r['bytes'] for r in report['files']) != summary['bytes'] or \
                sum(r['lines'] for r in report['files']) != summary['lines']:
            raise ValueError('Virtual report summary is inconsistent')

    def check_stable(self):
        for path, expected in self.pinned_files.items():
            if sha256(path) != expected:
                raise ValueError('Source/config/report changed during census: ' + str(path))


class MoreHeader(Exception):
    pass


def parse_header(text, eof):
    """Lean 4.19 header: optional prelude, then import [runtime] identifier.

    Nested comments and consecutive imports on one line are supported. Stop at
    the first ordinary command; imports appearing in body comments do not count.
    """
    def token(pos):
        while True:
            while pos < len(text) and text[pos].isspace():
                pos += 1
            if pos == len(text):
                if not eof:
                    raise MoreHeader
                return None, pos
            if text.startswith('--', pos):
                end = text.find('\n', pos + 2)
                if end < 0:
                    if not eof:
                        raise MoreHeader
                    return None, len(text)
                pos = end + 1
            elif text.startswith('/-', pos):
                depth, pos = 1, pos + 2
                while depth:
                    if pos + 1 >= len(text):
                        if eof:
                            raise ValueError('Unclosed comment in module header')
                        raise MoreHeader
                    if text.startswith('/-', pos):
                        depth, pos = depth + 1, pos + 2
                    elif text.startswith('-/', pos):
                        depth, pos = depth - 1, pos + 2
                    else:
                        pos += 1
            else:
                break
        match = IDENT.match(text, pos)
        if match is None:
            if not eof and pos + 1 == len(text):
                raise MoreHeader
            return text[pos], pos + 1
        if match.end() == len(text) and not eof:
            raise MoreHeader
        return match.group(), match.end()

    word, pos = token(0)
    prelude = word == 'prelude'
    if prelude:
        word, pos = token(pos)
    dependencies = [] if prelude else ['Init']
    while word == 'import':
        name, pos = token(pos)
        if name == 'runtime':
            name, pos = token(pos)
        if name is None or not IDENT.fullmatch(name):
            raise ValueError('Invalid import header')
        dependencies.append(name.replace('«', '').replace('»', ''))
        word, pos = token(pos)
    return list(dict.fromkeys(dependencies)), prelude


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('roots', nargs='*')
    parser.add_argument('--max-modules', type=int, default=12000)
    parser.add_argument('--max-header-bytes', type=int, default=64 * 1024 * 1024)
    parser.add_argument('--virtual-report', type=Path,
                        help='Authenticate and count the full selected source overlay, without activation')
    parser.add_argument('--report', type=Path,
                        help='Write complete JSON here and print only a compact summary')
    args = parser.parse_args()
    if args.virtual_report and args.roots:
        parser.error('Virtual mode counts its entire authenticated union; do not supply a partial root list')
    virtual = VirtualSources(args.virtual_report) if args.virtual_report else None
    roots = virtual.roots if virtual else args.roots or DEFAULT_ROOTS
    pin = (ROOT / 'lean-toolchain').read_text().strip()
    if pin != 'leanprover/lean4:v4.19.0':
        raise SystemExit('Unexpected toolchain pin: ' + pin)
    toolchain = Path.home() / '.elan/toolchains/leanprover--lean4---v4.19.0'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = [(p['name'], ROOT / p['dir']) for p in manifest['packages']]
    records, errors, active, expected_missing = {}, [], set(), []
    bytes_read = 0

    def resolve(module):
        rel = Path(*module.split('.')).with_suffix('.lean')
        prefix = module.split('.')[0]
        if prefix in PROJECT:
            if virtual:
                if module not in virtual.modules:
                    raise ValueError('Project import absent from authenticated virtual selection: ' + module)
                source = local_path(virtual.modules[module]['path'])
            else:
                source = project_path(module)
            candidates = [('project', source, ROOT / '.lake/build/lib/lean')]
        else:
            candidates = [('Mathlib' if name == 'mathlib' else 'package:' + name,
                           directory / rel, directory / '.lake/build/lib/lean')
                          for name, directory in packages]
            candidates += [('toolchain:' + prefix, directory / rel, toolchain / 'lib/lean')
                           for directory in [toolchain / 'src/lean', toolchain / 'src/lean/lake']]
        found = [(group, source, objects) for group, source, objects in candidates if source.is_file()]
        if len(found) != 1:
            raise ValueError('Missing or ambiguous source: ' + module + ' ' + str([str(x[1]) for x in found]))
        return (*found[0], rel)

    def header(source):
        nonlocal bytes_read
        text, raw_count = '', 0
        with source.open(encoding='utf-8-sig') as stream:
            while True:
                chunk = stream.read(4096)
                raw_count += len(chunk.encode())
                bytes_read += len(chunk.encode())
                if bytes_read > args.max_header_bytes or raw_count > 1024 * 1024:
                    raise ValueError('Header read budget reached; closure incomplete')
                text += chunk
                try:
                    return parse_header(text, not chunk)
                except MoreHeader:
                    continue

    def visit(module, draft=False):
        if virtual and draft and module in virtual.allowed_missing and module not in virtual.modules:
            if project_path(module).is_file():
                raise ValueError('Previously absent draft dependency is now present; refresh virtual report: ' + module)
            expected_missing.append({'module':module, 'retained_draft':True})
            return
        if module in active:
            raise ValueError('Import cycle at ' + module)
        if module in records:
            return
        if len(records) >= args.max_modules:
            raise ValueError('Module census limit reached; closure incomplete')
        active.add(module)
        try:
            group, source, objects, rel = resolve(module)
            dependencies, prelude = header(source)
            artifact_sizes = {}
            for suffix in ['.olean', '.ilean']:
                artifact = objects / rel.with_suffix(suffix)
                artifact_sizes[suffix[1:]] = artifact.stat().st_size if artifact.is_file() else None
            records[module] = dict(module=module, group=group, source=str(source),
                source_bytes=source.stat().st_size, imports=dependencies,
                prelude=prelude, artifacts=artifact_sizes)
            if virtual and group == 'project':
                records[module]['source_sha256'] = virtual.modules[module]['sha256']
                records[module]['source_origin'] = virtual.modules[module]['origin']
            for dependency in dependencies:
                visit(dependency, draft)
        except (OSError, ValueError) as error:
            errors.append(dict(module=module, error=str(error)))
        finally:
            active.remove(module)

    for root in roots:
        visit(root)
    root_closure = set(records)
    if virtual:
        actual_outside = virtual.explicitly_retained - root_closure
        if actual_outside != set(virtual.extra_roots):
            errors.append({'module':'virtual report','error':'Explicit retained roots differ from actual root closure'})
        for root in virtual.extra_roots:
            visit(root)
    build_closure = set(records)
    draft_records = []
    if virtual:
        for path, entry in sorted(virtual.drafts.items()):
            try:
                dependencies, prelude = header(local_path(entry['path']))
                draft_records.append(dict(path=path, sha256=entry['sha256'],
                    source_bytes=entry['bytes'], imports=dependencies, prelude=prelude,
                    is_build_root=False))
                for dependency in dependencies:
                    visit(dependency, draft=True)
            except (OSError, ValueError) as error:
                errors.append({'module':path,'error':str(error)})
        actual_project = {n for n,r in records.items() if r['group'] == 'project'}
        if actual_project != virtual.modules.keys():
            errors.append({'module':'virtual report','error':'Authenticated project source selection differs from traversed union',
                'not_traversed':sorted(virtual.modules.keys()-actual_project),
                'not_authenticated':sorted(actual_project-virtual.modules.keys())})
        if {m['module'] for m in expected_missing} != virtual.expected_missing:
            errors.append({'module':'virtual report','error':'Named unresolved draft imports changed'})
        try:
            virtual.check_stable()
        except (OSError, ValueError) as error:
            errors.append({'module':'virtual report','error':str(error)})

    def summary(names):
        items = [records[n] for n in names if n in records]
        return dict(modules=len(items), source_bytes=sum(x['source_bytes'] for x in items),
            groups=dict(Counter(x['group'] for x in items)),
            objects_present=sum(x['artifacts']['olean'] is not None for x in items),
            objects_missing=sum(x['artifacts']['olean'] is None for x in items),
            present_olean_bytes=sum(x['artifacts']['olean'] or 0 for x in items),
            present_ilean_bytes=sum(x['artifacts']['ilean'] or 0 for x in items))

    def reachable(root):
        seen, todo = set(), [root]
        while todo:
            module = todo.pop()
            if module in seen:
                continue
            seen.add(module)
            if module in records:
                todo.extend(records[module]['imports'])
        return seen

    cache_plan = json.loads((ROOT / 'evidence/mathlib-cache-plan.json').read_text())
    plan_names = {x['module'] for x in cache_plan}
    external_names = {n for n, r in records.items() if r['group'] != 'project'}
    library_names = {n for n, r in records.items() if r['group'] == 'Mathlib' or r['group'].startswith('package:')}
    cache_entries = [x for x in cache_plan if x['module'] in library_names]
    compressed_present = [ROOT / '.lake/cache' / x['file'] for x in cache_entries]
    result = dict(toolchain=pin, roots=roots, complete_source_import_census=not errors,
        scope=('Authenticated complete virtual project union plus present draft dependencies; '
               'named unresolved drafts are not build roots. Missing final proof remains unbounded.'
               if virtual else 'Current explicit root union only; missing final proof is not bounded.'),
        implicit_Init_included=True, runtime_imports_included=True,
        per_root={r: summary(reachable(r)) for r in roots}, union=summary(records),
        project=summary(set(records) - external_names), external=summary(external_names),
        below_9000_for_current_roots=(len(records) < 9000) if not errors else None,
        final_proof_below_9000_established=False, header_bytes_read=bytes_read,
        errors=errors, cache_plan_comparison=dict(last_plan_entries=len(cache_plan),
            imported_libraries_in_last_plan=len(library_names & plan_names),
            imported_libraries_outside_last_plan=sorted(library_names - plan_names),
            mapped_compressed_artifacts_present=sum(p.is_file() for p in compressed_present),
            mapped_compressed_bytes=sum(p.stat().st_size for p in compressed_present if p.is_file()),
            compressed_mapping_complete=library_names <= plan_names),
        limits=['Source/header census is not Lean replay or a proof of mathematical completeness.',
            'Object presence does not certify source freshness, validity, or prior acceptance.',
            'Cached external modules may avoid compilation; source module count alone is not a time estimate.',
            'No compiler executable, package build, JS assets or unrelated cache files are counted as Lean modules.',
            'Unconstructed certificates and future imports have unknown cost.'],
        modules=[records[n] for n in sorted(records)])
    if virtual:
        result['virtual_selection'] = dict(report=str(virtual.report_path.relative_to(ROOT)),
            report_sha256=virtual.pinned_files[virtual.report_path],
            config=virtual.report['config'], config_sha256=virtual.report['config_sha256'],
            all_listed_source_hashes_authenticated=True,
            authenticated_project_source_bytes=virtual.authenticated_source_bytes,
            explicitly_retained_build_roots=virtual.extra_roots,
            source_proposal_summary=virtual.report['summary'], activation_performed=False)
        result['buildable_source_root_union'] = summary(build_closure)
        result['root_union_before_explicit_retained_outputs'] = summary(root_closure)
        result['present_draft_dependency_additions'] = summary(set(records)-build_closure)
        result['retained_unresolved_drafts'] = dict(files=draft_records,
            known_missing_imports=sorted(virtual.expected_missing),
            source_files_counted_as_build_modules=False,
            actual_drafts_import_closed=False if virtual.expected_missing else True)
        result['below_9000_for_buildable_source_roots'] = len(build_closure) < 9000 if not errors else None
        result['below_9000_including_present_draft_dependencies'] = len(records) < 9000 if not errors else None
    if args.report:
        report_path = local_path(args.report)
        if virtual and report_path in virtual.pinned_files:
            raise ValueError('Output must not overwrite authenticated source/config/report')
        report_path.parent.mkdir(parents=True,exist_ok=True)
        report_path.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(dict(report=str(report_path.relative_to(ROOT)),
            complete=not errors, union=result['union'], project=result['project'],
            external=result['external'],
            below_9000=result['below_9000_for_current_roots'],
            retained_draft_files=len(draft_records), expected_missing_draft_imports=sorted(
                virtual.expected_missing) if virtual else [],
            error_count=len(errors), errors=errors[:8])))
    else:
        print(json.dumps(result, indent=2))
    if errors:
        sys.exit(2)


if __name__ == '__main__':
    main()
