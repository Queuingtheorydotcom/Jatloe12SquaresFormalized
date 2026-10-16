#!/usr/bin/env python3
"""Factor the exact C976 certificates consumed by the original C981 entrance.

Data expressions are copied verbatim from the inherited source. New query
checks use ordinary kernel reduction; each direct-domain coverage proof uses
SmallOwnerDomain's proved cardinality reduction. No geometric domain,
budget, label, or original C981 representative is altered.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'source/S12/Case976Domains.lean'
DEST = ROOT/'Compact/Bridge/C981DomainReuse'

def main():
    original = SOURCE.read_text()
    definitions = dict(re.findall(r'^def (\w+)\s*:\s*([^\n]+)$', original, re.M))
    wanted = ['case976Family'] + [f'single976_{i}_{k}'
        for i in [2,3,4,7] for k in [0,1]]
    selected_queries = set(range(649,706)) | set(range(230,233)) | \
        set(range(249,252)) | set(range(268,271))
    for name in wanted[1:]:
        selected_queries.update(int(n) for n in re.findall(r'query976_(\d+)', definitions[name]))
    DEST.mkdir(parents=True, exist_ok=True)
    chunk_modules = []
    chunks = []
    for start in range(0,len(selected_queries),25):
        indices = sorted(selected_queries)[start:start+25]
        number = start//25
        filename = DEST/f'Queries{number:02}.lean'
        module = f'Compact.Bridge.C981DomainReuse.Queries{number:02}'
        chunk_modules.append(module)
        lines = ['import Compact.Bridge.SharedLocalQueries',
            '', '/-! Exact inherited query data, with ordinary kernel checks. -/',
            'namespace N12Compact.C981DomainSubset', 'open S12 S12Pilot',
            'set_option Elab.async false', 'set_option maxHeartbeats 2000000',
            'set_option maxRecDepth 100000', 'noncomputable section', '']
        for index in indices:
            name = f'query976_{index}'
            body = definitions[name]
            assert body.startswith('LocalQuery := ')
            lines.append(f'checked_local_query {name} := {body.removeprefix("LocalQuery := ")}')
        lines += ['', 'end', 'end N12Compact.C981DomainSubset', '']
        filename.write_text('\n'.join(lines))
        chunks.append({'module':module,'queries':indices})
    lines = [f'import {m}' for m in chunk_modules] + [
        'import Compact.Bridge.SmallOwnerDomain', '',
        '/-! The unchanged direct domains selected by C981. Exact signatures',
        'are checked over all cardinality-at-most-two labels; the symbolic',
        'SmallOwnerDomain theorem recovers the original full statement. -/',
        'namespace N12Compact.C981DomainSubset', 'open S12 S12Pilot',
        'set_option Elab.async false', 'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 2000000', 'noncomputable section', '']
    lines.append(f'def case976Family : {definitions["case976Family"]}')
    for name in wanted[1:]:
        lines.append(f'def {name} : {definitions[name]}')
        query_ids = sorted(set(int(n) for n in re.findall(r'query976_(\d+)',definitions[name])))
        signatures = []
        for index in query_ids:
            sig = re.match(r'LocalQuery := ⟨(\d+),(\d+),(∅|\{[^}]*\}),',
                definitions[f'query976_{index}'])
            assert sig is not None
            signatures.append('('+','.join(sig.groups())+')')
        signature_name = name+'_signatures'
        lines.append(f'def {signature_name} : List N12Compact.SmallOwnerDomain.Signature :=')
        lines.append('  ['+','.join(signatures)+']')
        kind = name.rsplit('_',1)[1]
        lines += [f'theorem {name}_checked : {name}.Check case976Family {kind} := by',
            f'  apply N12Compact.SmallOwnerDomain.checked {name} case976Family {kind}',
            f'    {signature_name}', '  · rfl', '  · decide +kernel',
            '  · decide +kernel', '']
    lines += ['#print axioms single976_7_0_checked',
        '#print axioms single976_7_1_checked', 'end',
        'end N12Compact.C981DomainSubset', '']
    (DEST/'Subset.lean').write_text('\n'.join(lines))
    receipt = {'source':'source/S12/Case976Domains.lean',
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'copied_definitions':wanted,
        'query_count':len(selected_queries),'chunks':chunks,
        'data_expressions_copied_verbatim':True,
        'new_native_decide_sites':0,
        'kernel_verification_required':True}
    (ROOT/'.verification/c981-domain-factorization.json').write_text(
        json.dumps(receipt,indent=2)+'\n')
    ownership_path = ROOT/'Completion/Cases/C981/OwnershipDomains.lean'
    ownership = ownership_path.read_text()
    ownership = ownership.replace('import S12.Case976Domains',
        'import Compact.Bridge.C981DomainReuse.Subset')
    ownership = re.sub(r'(?<![\w.])(?:case976Family|single976_\d+_[01](?:_checked)?|query976_\d+(?:_checked)?)(?!\w)',
        lambda match: 'N12Compact.C981DomainSubset.'+match.group(), ownership)
    ownership_path.write_text(ownership)
    print(json.dumps({'selected_queries':len(selected_queries),
        'query_modules':len(chunks),'coverage_module':1}))

if __name__=='__main__':
    main()
