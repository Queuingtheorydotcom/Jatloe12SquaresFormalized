#!/usr/bin/env python3
"""Inventory the current conditional assembly and every new proof module.

Package source headers, including Lean's implicit Init import, determine the
external closure. This inventories current source; it cannot bound unwritten
future proof obligations or certify a theorem's acceptance.

The selected proof closure is enforced by default. Retained alternatives are
also inventoried; --all-retained enforces their completeness and budget too.
"""
import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = Path.home()/'.elan/toolchains/leanprover--lean4---v4.19.0/src/lean'
SPEC = importlib.util.spec_from_file_location('local_verify', ROOT/'scripts/verify.py')
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)

def header_imports(path):
    # Read only the import header. Some retained certificate files have enormous
    # bodies; processing those bodies cannot discover another header import.
    imports, prelude, depth = [], False, 0
    with path.open() as source:
        for raw in source:
            output, i = [], 0
            while i < len(raw):
                if raw[i:i+2] == '/-':
                    depth += 1; i += 2
                elif depth and raw[i:i+2] == '-/':
                    depth -= 1; i += 2
                elif depth:
                    i += 1
                elif raw[i:i+2] == '--':
                    break
                else:
                    output.append(raw[i]); i += 1
            line = ''.join(output).strip()
            if not line: continue
            if line == 'prelude': prelude = True; continue
            if line.startswith('import '):
                imports.extend(line.removeprefix('import ').split())
            else: break
    if not prelude and path.name != 'Init.lean': imports.append('Init')
    return imports

def external_closure(sources, packages):
    """Return the discovered closure and missing sources, never assume completeness."""
    externals = set()
    for source in sources:
        externals.update(d for d in header_imports(source)
            if d.split('.')[0] not in {'Compact','Completion','S12'})
    pending = list(externals | {'Init'})
    seen, missing = set(), set()
    while pending:
        module = pending.pop()
        if module in seen: continue
        seen.add(module)
        relative = Path(*module.split('.')).with_suffix('.lean')
        # Lake ships its sources under src/lean/lake rather than src/lean.
        path = next((p/relative for p in [LEAN,LEAN/'lake']+packages
                     if (p/relative).is_file()), None)
        if path is None:
            missing.add(module); continue
        pending.extend(header_imports(path))
    return seen, missing

def within_limit(count, limit, complete):
    # An incomplete closure is a lower bound, not evidence of budget compliance.
    return count <= limit if complete else None

def main(roots=None, all_retained=False):
    if roots is None:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--all-retained', action='store_true',
            help='also require complete, within-budget retained alternatives')
        parser.add_argument('modules', nargs='*', help='additional selected roots')
        args = parser.parse_args()
        all_retained = args.all_retained
        roots = ['Compact.Assembly.SourceAssembly', 'Compact.Assembly.C981Progress']
        roots += ['.'.join(p.relative_to(ROOT).with_suffix('').parts)
            for p in sorted((ROOT/'Compact/Completion').rglob('*.lean'))]
        roots += args.modules
    project = VERIFY.closure(roots)
    package_dir = ROOT/'.lake/packages'
    packages = [p for p in package_dir.iterdir() if p.is_dir()] if package_dir.is_dir() else []
    seen, missing = external_closure([VERIFY.path(m) for m in project], packages)
    selected_complete = not missing

    all_source_files = list(ROOT.glob('*.lean'))
    for directory in ('source','Compact','Completion'):
        all_source_files.extend((ROOT/directory).rglob('*.lean'))
    retained_seen, retained_missing = external_closure(all_source_files, packages)
    # An absent local import in an unselected alternative also hides an unknown
    # external dependency closure. Do not certify that inventory as complete.
    retained_missing_project = {dep for source in all_source_files
        for dep in header_imports(source)
        if dep.split('.')[0] in {'Compact','Completion','S12'}
        and not VERIFY.path(dep).is_file()}
    retained_complete = not retained_missing and not retained_missing_project
    selected_total = len(project)+len(seen)
    retained_total = len(all_source_files)+len(retained_seen)
    report = {'roots':roots,'project_modules':len(project),
        'project_source_lines':sum(len(VERIFY.path(m).read_text().splitlines()) for m in project),
        'external_modules':len(seen),'combined_modules':selected_total,
        'missing_external_sources':sorted(missing),
        'selected_source_closure_complete':selected_complete,
        'preferred_module_limit':8000, 'hard_module_limit':10000,
        'current_source_under_8000':within_limit(selected_total,8000,selected_complete),
        'current_source_under_hard_limit':within_limit(selected_total,10000,selected_complete),
        'global_optimality_proved':False,'future_unwritten_obligations_included':False}
    report['all_project_lean_files'] = len(all_source_files)
    # Keep the historical comparison explicitly separate from the audited
    # retained inventory: alternatives can import additional library modules.
    report['all_project_files_plus_current_external_closure'] = len(all_source_files)+len(seen)
    report.update({
        'retained_external_modules':len(retained_seen),
        'retained_combined_modules':retained_total,
        'missing_retained_external_sources':sorted(retained_missing),
        'missing_retained_project_sources':sorted(retained_missing_project),
        'retained_source_closure_complete':retained_complete,
        'retained_source_under_8000':within_limit(retained_total,8000,retained_complete),
        'retained_source_under_hard_limit':within_limit(retained_total,10000,retained_complete),
        'source_census_complete':selected_complete and retained_complete,
        'enforced_scope':'all_retained' if all_retained else 'selected',
        'enforced_source_closure_complete':selected_complete and
            (retained_complete if all_retained else True)})
    verification = ROOT/'.verification'
    verification.mkdir(parents=True,exist_ok=True)
    (verification/'current-source-census.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='roots'}))
    if not report['enforced_source_closure_complete']:
        raise SystemExit('Source census incomplete: missing sources; module-budget compliance is unknown')
    if not report['current_source_under_hard_limit'] or (
            all_retained and not report['retained_source_under_hard_limit']):
        raise SystemExit('Whole current proof closure exceeds the hard 10000-module limit')

if __name__=='__main__':
    main()
