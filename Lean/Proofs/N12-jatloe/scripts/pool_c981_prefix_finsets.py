#!/usr/bin/env python3
"""Share repeated typed Finset literals in the exact C981 prefix data.

--write emits one pool module and rewrites the 22 existing data helpers.
Default mode is a read-only expansion audit. No Lean process is started.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LITERAL_MANIFEST = ROOT/'evidence/c981-prefix-literal-factoring.json'
MANIFEST = ROOT/'evidence/c981-prefix-finset-pool.json'
POOL = Path('Completion/Cases/C981/Coverage/Data/FinsetPool.lean')
OLD_IMPORT = 'import Mathlib.Data.Finset.Insert\n'
POOL_IMPORT = 'import Completion.Cases.C981.Coverage.Data.FinsetPool\n'
OPEN_POOL = 'open S12Completion.C981.Coverage.Data.FinsetPool\n'
NAMESPACE = 'namespace S12Completion.C981.Coverage\n'
TOKEN = re.compile(r'∅|\{[0-9]+(?:,[0-9]+)*\}')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def literal_key(literal):
    return 0 if literal == '∅' else sum(1 << int(x) for x in literal[1:-1].split(','))


def render_pool(constants):
    text = OLD_IMPORT+'\nnamespace S12Completion.C981.Coverage.Data.FinsetPool\n'
    text += 'set_option Elab.async false\n\n'
    text += ''.join(f'def {item["name"]} : Finset Nat := {item["literal"]}\n' for item in constants)
    text += '\nend S12Completion.C981.Coverage.Data.FinsetPool\n'
    return text.encode()


def expand_pooled_helper(path,actual):
    """Validate actual pool/helper bytes, then recover the exact literal source."""
    path = Path(path)
    report = json.loads(MANIFEST.read_text())
    pool = render_pool(report['constants'])
    assert sha(pool) == report['pool_sha256']
    assert (ROOT/POOL).read_bytes() == pool, 'Typed constant pool changed'
    item = next(x for x in report['helpers'] if x['path']==path.as_posix())
    assert sha(actual) == item['pooled_sha256'], f'Pooled helper changed: {path}'
    text = actual.decode()
    assert text.startswith(POOL_IMPORT) and text.count(OPEN_POOL)==1
    text = OLD_IMPORT+text.removeprefix(POOL_IMPORT)
    text = text.replace(NAMESPACE+OPEN_POOL,NAMESPACE,1)
    header,body = text.split(':= [\n',1)
    mapping = {x['name']:x['literal'] for x in report['constants']}
    body = re.sub(r'\bfs\d{2}\b',lambda match:mapping[match[0]],body)
    expanded = (header+':= [\n'+body).encode()
    assert sha(expanded) == item['original_literal_sha256'], 'Literal expansion differs'
    return expanded


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    literal_report = json.loads(LITERAL_MANIFEST.read_text())
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    originals,counts = {},Counter()
    for prefix in literal_report['prefixes']:
        for chunk in prefix['chunks']:
            path = Path(chunk['path'])
            data = (ROOT/path).read_bytes()
            if sha(data) != chunk['sha256']:
                assert previous, f'Original data helper changed: {path}'
                data = expand_pooled_helper(path,data)
            assert sha(data) == chunk['sha256']
            originals[path] = data
            body = data.decode().split(':= [\n',1)[1]
            counts.update(TOKEN.findall(body))
    assert len(originals)==22 and sum(counts.values())==50762 and len(counts)==50
    literals = sorted(counts,key=lambda value:(literal_key(value),value))
    assert len({literal_key(value) for value in literals})==50
    constants = [{'name':f'fs{i:02}','literal':value} for i,value in enumerate(literals)]
    names = {item['literal']:item['name'] for item in constants}
    expected,helper_records = {},[]
    for path,data in originals.items():
        text = data.decode()
        assert text.startswith(OLD_IMPORT) and text.count(NAMESPACE)==1
        text = POOL_IMPORT+text.removeprefix(OLD_IMPORT)
        text = text.replace(NAMESPACE,NAMESPACE+OPEN_POOL,1)
        header,body = text.split(':= [\n',1)
        body = TOKEN.sub(lambda match:names[match[0]],body)
        pooled = (header+':= [\n'+body).encode()
        expected[path] = pooled
        helper_records.append({'path':path.as_posix(),
            'original_literal_sha256':sha(data),'pooled_sha256':sha(pooled)})
    pool = render_pool(constants)
    expected[POOL] = pool
    report = {'original_commit':literal_report['original_commit'],
        'original_literal_manifest':'evidence/c981-prefix-literal-factoring.json',
        'constants':constants,'pool_path':POOL.as_posix(),'pool_sha256':sha(pool),
        'helpers':helper_records,'literal_occurrences':50762,'distinct_literals':50,
        'added_lean_modules':1,'original_rows_preserved':5291,
        'exact_literal_expansion':True,'row_order_unchanged':True,
        'new_proofs':0,'new_native_sites':0,'lean_replayed':False}
    if args.write:
        # Validate everything before replacing any source; no live source may
        # be edited concurrently with this explicit operation.
        for path,data in expected.items():
            if (ROOT/path).exists():
                assert (ROOT/path).read_bytes() in (data,originals.get(path)), \
                    f'Refusing unexpected source edits: {path}'
        for path,data in expected.items():
            (ROOT/path).write_bytes(data)
        MANIFEST.write_text(json.dumps(report,indent=2)+'\n')
    else:
        assert previous == report, 'Pool manifest differs from exact expansion audit'
    for path,data in originals.items():
        assert expand_pooled_helper(path,(ROOT/path).read_bytes()) == data
    print(json.dumps({'audit':'passed','literal_occurrences':50762,'distinct_literals':50,
        'added_lean_modules':1,'original_rows_preserved':5291,
        'output_bytes':sum(len(data) for data in expected.values()),'lean_replayed':False}))


if __name__ == '__main__':
    main()
