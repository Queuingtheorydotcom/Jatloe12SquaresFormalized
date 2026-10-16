#!/usr/bin/env python3
"""Authenticate inherited numerical sites before auditing their Lean axiom owners.

This does not compile a proof or validate cached objects. The caller must replay
the closure with authenticated receipts. Missing original bytes fail closed.
Run --prepare to emit a bounded Lean query; run --log on its successful output.
The query must be run outside any namespace, with fully qualified pretty names.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from audit_retained_trust import lex_source

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*'
PROVENANCE_COMMIT = '62f00515138e342483cbc21614f03a012aa03149'
SNAPSHOT_COMMIT = '793917a030fa3ec26772d28d77fa03d3c51485c7'


def pinned_json(relative, revision):
    """Read reviewed historical manifests, never approve current self hashes."""
    prefix = 'projects/n12-refactored/'
    return json.loads(subprocess.check_output(
        ['git', 'show', revision + ':' + prefix + relative], cwd=ROOT))


def audit_factoring(provenance):
    """Reuse the existing byte-for-byte inverse auditors without write flags."""
    vendor_hashes = {item['vendor_sha256'] for item in provenance['records']}
    for stem in ('domain_spec', 'core', 'local_query'):
        manifest_name = stem.replace('_', '-') + '-data-factoring.json'
        relative = 'evidence/' + manifest_name
        pinned = pinned_json(relative, SNAPSHOT_COMMIT)
        require(json.loads((ROOT/relative).read_text()) == pinned, 'Factoring manifest changed: ' + relative)
        require(pinned['original_sha256'] in vendor_hashes, 'Factoring original is not approved: ' + relative)
        # Existing auditors reconstruct original numerical declarations from the
        # actual helper bytes, check helper sets/hashes, and reject extra sites.
        environment = dict(os.environ)
        environment.pop('PYTHONOPTIMIZE', None)
        result = subprocess.run([sys.executable, str(ROOT/'scripts'/('factor_' + stem + '_data.py'))],
                                cwd=ROOT, env=environment, capture_output=True, text=True)
        require(result.returncode == 0, 'Factoring inverse audit failed: ' + stem + '\n' + result.stderr)


class AuditError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def native_sites(raw, definitions=False):
    """Accept existing named S12 numerical theorems and certificate definitions.

    Unsupported syntax is an audit failure, never an inferred approval. Whole
    current source hashes authenticate definitions and namespace context too.
    """
    text = lex_source(raw.decode())
    namespace = []
    sites = {}
    commands = list(re.finditer(r'^(?:theorem|def|lemma|namespace|end|import|open|set_option|#print)\b', text, re.M))
    consumed = 0
    for index, command in enumerate(commands):
        block = text[command.start():commands[index+1].start() if index+1 < len(commands) else len(text)]
        stripped = block.strip()
        match = re.fullmatch(r'namespace (' + NAME + ')', stripped)
        if match:
            namespace.append(match[1])
        elif re.fullmatch(r'end(?: ' + NAME + ')?', stripped):
            require(bool(namespace), 'Unsupported section/end in native source')
            namespace.pop()
        native_count = len(re.findall(r'\bnative_decide\b', block))
        if native_count or (definitions and stripped.startswith('def ')):
            match = re.fullmatch(r'(?:theorem|def) (' + NAME + r')\s+(.+):=(.+)', stripped, re.S)
            require(match is not None, 'Unsupported native site: ' + stripped[:160])
            consumed += native_count
            name = '.'.join(namespace + [match[1]])
            require(name not in sites, 'Duplicate native declaration: ' + name)
            sites[name] = stripped
    require(consumed == len(re.findall(r'\bnative_decide\b', text)), 'Native site outside supported theorem')
    return sites


def closure(root_module, project=ROOT):
    files = {}

    def visit(module):
        if module in files or module.split('.')[0] not in {'S12', 'Compact', 'Completion'}:
            return
        path = project / ('source' if module.startswith('S12.') else '') / Path(*module.split('.')).with_suffix('.lean')
        require(path.is_file(), 'Missing local module: ' + module)
        raw = path.read_bytes()
        files[module] = (path, raw)
        for imports in re.findall(r'^\s*import\s+([^\n]+)', lex_source(raw.decode()), re.M):
            for dependency in imports.split():
                visit(dependency)

    visit(root_module)
    return files


def authenticated_sites(files, provenance, snapshot, originals, project=ROOT):
    """Both pinned whole current files and hash-verified vendor sites are required.

    The snapshot authenticates relocated definitions as well as proof lines.
    Vendor matching authenticates the original approval of each named native
    theorem. Neither a same-looking suffix nor a manifest boolean is authority.
    """
    hashes = {item['path']: item['sha256'] for item in snapshot['files']}
    approved = {}
    approved_definitions = {}
    for record in provenance['records']:
        path = originals / record['vendor']
        require(path.is_file(), 'Missing original provenance source: ' + str(path))
        raw = path.read_bytes()
        require(sha(raw) == record['vendor_sha256'], 'Original hash mismatch: ' + str(path))
        sites = native_sites(raw)
        for name, body in native_sites(raw, definitions=True).items():
            require(name not in approved_definitions or approved_definitions[name] == body,
                    'Conflicting original definition: ' + name)
            approved_definitions[name] = body
        # AngleData64 and AngleData128 share one vendor file containing all grids.
        count = sum(len(re.findall(r'\bnative_decide\b', body)) for body in sites.values())
        expected = record['site_occurrences']
        require(count >= expected if 'AngleData' in record.get('module', '') else count == expected,
                'Original site inventory mismatch: ' + record['vendor'])
        for name, body in sites.items():
            require(name not in approved or approved[name] == body, 'Conflicting original site: ' + name)
            approved[name] = body
    current = {}
    for module, (path, raw) in files.items():
        text = lex_source(raw.decode())
        require(not re.search(r'\b(?:axiom|sorry|admit|unsafe|ofReduceBool|ofReduceNat)\b', text),
                'Unapproved trust syntax: ' + module)
        if not re.search(r'\bnative_decide\b', text):
            continue
        relative = path.relative_to(project).as_posix()
        require(relative in hashes and sha(raw) == hashes[relative], 'Native source hash mismatch: ' + relative)
        for name, body in native_sites(raw, definitions=True).items():
            require(name in approved_definitions and approved_definitions[name] == body,
                    'Numerical definition differs from original: ' + name)
        for name, body in native_sites(raw).items():
            require(name in approved and approved[name] == body, 'Uninventoried native declaration: ' + name)
            require(name not in current, 'Duplicate current native declaration: ' + name)
            current[name] = {'module': module, 'path': relative, 'sha256': sha(raw),
                             'native_site_count': len(re.findall(r'\bnative_decide\b', body))}
    return current


def query(root_module, theorem, sites):
    require(re.fullmatch(NAME, root_module) and re.fullmatch(NAME, theorem), 'Invalid Lean name')
    return ('import ' + root_module + '\nset_option pp.fullNames true\n' +
            '#print axioms ' + theorem + '\n' +
            ''.join('#print axioms ' + name + '\n' for name in sorted(sites)))


def validate_log(log, theorem, sites):
    require(not re.search(r'\berror(?:\(|:)|\bsorryAx\b', log), 'Lean query failed or contains admissions')
    results = {}
    pattern = r"'?(" + NAME + r")'? (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, log, re.S):
        require(match[1] not in results, 'Duplicate axiom output: ' + match[1])
        results[match[1]] = {x.strip() for x in (match[2] or '').split(',') if x.strip()}
    require(set(results) == set(sites) | {theorem}, 'Missing or unexpected Lean axiom query output')
    owners = {}
    for name in sites:
        for axiom in results[name] - STANDARD:
            # An approved declaration can depend on OTHER approved numerical
            # results, but each generated axiom must also occur in its own
            # authenticated owner query. No unrelated suffix is ever accepted.
            if re.fullmatch(re.escape(name) + r'\._native\.native_decide\.ax_[1-9][0-9]*(?:_[0-9]+)*', axiom):
                owners[axiom] = name
    for name, axioms in results.items():
        require(not (axioms - STANDARD - owners.keys()),
                'Unmapped axiom in ' + name + ': ' + ', '.join(sorted(axioms - STANDARD - owners.keys())))
    return {'final_axioms': sorted(results[theorem]), 'native_axiom_owners': owners,
            'inherited_native_compiler_trust': bool(results[theorem] - STANDARD),
            'authenticated_native_declarations': sites}


def validate_runtime(files, manifest, final_axioms, project=ROOT):
    """Check against a reviewed, committed output of the original-byte audit.

    This path is for CI without vendor archives. The manifest is a trust-policy
    input, just like this script, and must never be regenerated from unchecked
    current sources. It freezes exact source hashes AND actual axiom names.
    """
    sites = manifest['authenticated_native_declarations']
    owners = manifest['native_axiom_owners']
    found = {}
    for module, (path, raw) in files.items():
        text = lex_source(raw.decode())
        require(not re.search(r'\b(?:axiom|sorry|admit|unsafe|ofReduceBool|ofReduceNat)\b', text),
                'Unapproved trust syntax: ' + module)
        if not re.search(r'\bnative_decide\b', text):
            continue
        for name, body in native_sites(raw).items():
            require(name in sites, 'Uninventoried native declaration: ' + name)
            item = sites[name]
            require(item['module'] == module and item['path'] == path.relative_to(project).as_posix()
                    and item['sha256'] == sha(raw), 'Native source hash/owner mismatch: ' + name)
            require(item['native_site_count'] == len(re.findall(r'\bnative_decide\b', body)),
                    'Native site count mismatch: ' + name)
            require(name not in found, 'Duplicate current native declaration: ' + name)
            found[name] = item
    require(found == sites, 'Runtime native closure differs from authenticated manifest')
    require(set(owners.values()) <= sites.keys(), 'Unauthenticated axiom owner in manifest')
    final_axioms = set(final_axioms)
    require(not (final_axioms - STANDARD - owners.keys()),
            'Unmapped final axiom: ' + ', '.join(sorted(final_axioms - STANDARD - owners.keys())))
    return {'final_axioms': sorted(final_axioms),
            'inherited_native_compiler_trust': bool(final_axioms - STANDARD)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root-module', default='Compact.Assembly.Final')
    parser.add_argument('--theorem', default='N12Compact.Final.optimality')
    parser.add_argument('--provenance-root', type=Path, required=True,
                        help='Directory containing vendor/S12 originals (hash checked)')
    parser.add_argument('--prepare', type=Path, help='Write the Lean axiom query, without running Lean')
    parser.add_argument('--log', type=Path, help='Output of successful execution of the prepared query')
    args = parser.parse_args()
    provenance = pinned_json('audit/retained-native-provenance.json', PROVENANCE_COMMIT)
    snapshot = pinned_json('evidence/final-source-manifest-2026-10-15.json', SNAPSHOT_COMMIT)
    audit_factoring(provenance)
    sites = authenticated_sites(closure(args.root_module), provenance, snapshot, args.provenance_root)
    require(args.prepare is not None or args.log is not None, 'Specify --prepare or --log')
    if args.prepare:
        args.prepare.write_text(query(args.root_module, args.theorem, sites))
        print(json.dumps({'authenticated_declarations': len(sites),
                          'native_site_count': sum(item['native_site_count'] for item in sites.values()),
                          'provenance_commit': PROVENANCE_COMMIT, 'snapshot_commit': SNAPSHOT_COMMIT,
                          'query': str(args.prepare), 'lean_query_run': False}))
    if args.log:
        report = validate_log(args.log.read_text(), args.theorem, sites)
        report['authentication'] = {
            'provenance_commit': PROVENANCE_COMMIT, 'snapshot_commit': SNAPSHOT_COMMIT,
            'provenance_sha256': sha(json.dumps(provenance, sort_keys=True).encode()),
            'snapshot_sha256': sha(json.dumps(snapshot, sort_keys=True).encode()),
            'root_module': args.root_module, 'theorem': args.theorem,
            'query_sha256': sha(query(args.root_module, args.theorem, sites).encode()),
            'query_log_sha256': sha(args.log.read_bytes()),
            'original_source_sha256': {item['vendor']: item['vendor_sha256'] for item in provenance['records']}}
        print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
