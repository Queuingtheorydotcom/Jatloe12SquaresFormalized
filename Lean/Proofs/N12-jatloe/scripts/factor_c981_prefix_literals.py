#!/usr/bin/env python3
"""Factor only C981 prefix09/10 literal data; no proof or Lean invocation.

The default is an inverse audit. --write creates 256-row helpers and replaces
the data declarations by ordered concatenations with the same public types.
Every original literal row and its order are reconstructed byte for byte.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from factor_c981_allowed_data import DATA_HEADER, END

ROOT = Path(__file__).resolve().parents[1]
BASE = Path('Completion/Cases/C981/Coverage/Data')
MANIFEST = ROOT/'evidence/c981-prefix-literal-factoring.json'
PILOT_MANIFEST = ROOT/'evidence/c981-coverage-pilot.json'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def layout(number,declaration,rows_per_module):
    name = f'prefix{number:02}'
    start = f'def {name} : List (List (Finset Nat)) := [\n'
    assert declaration.startswith(start) and declaration.endswith(']\n')
    rows = declaration[len(start):-2].splitlines(keepends=True)
    assert len(rows) == {9:2148,10:3143}[number]
    normalized = []
    for i,row in enumerate(rows):
        assert row.startswith('  [') and row.endswith('\n')
        suffix = ',\n' if i+1 < len(rows) else '\n'
        assert row.endswith(']'+suffix)
        normalized.append(row[:-len(suffix)]+'\n')
    files,parts = {},[]
    for offset in range(0,len(rows),rows_per_module):
        index = offset//rows_per_module
        chunk_name = f'{name}Chunk{index:03}'
        path = BASE/f'Prefix{number:02}Chunks/Chunk{index:03}.lean'
        selected = normalized[offset:offset+rows_per_module]
        body = ',\n'.join(row.removesuffix('\n') for row in selected)+'\n'
        chunk_header = DATA_HEADER+f'def {chunk_name} : List (List (Finset Nat)) := [\n'
        files[path] = (chunk_header+body+']\n'+END).encode()
        parts.append({'path':path.as_posix(),'name':chunk_name,'offset':offset,
            'row_count':len(selected),'sha256':sha(files[path]),'header':chunk_header})
    imports = ''.join('import '+Path(p['path']).with_suffix('').as_posix().replace('/','.')+'\n'
        for p in parts)
    settings = DATA_HEADER.removeprefix('import Mathlib.Data.Finset.Insert\n')
    wrapper = imports+settings+f'def {name} : List (List (Finset Nat)) :=\n  '
    wrapper += ' ++ '.join(p['name'] for p in parts)+'\n'+END
    files[BASE/f'Prefix{number:02}.lean'] = wrapper.encode()
    return files,parts,start,rows


def audit_data_declaration(path,original_declaration):
    """Accept an exact literal or its audited, ordered chunk representation."""
    path = Path(path)
    actual = (ROOT/path).read_bytes()
    direct = (DATA_HEADER+original_declaration+END).encode()
    if actual == direct:
        return original_declaration
    report = json.loads(MANIFEST.read_text())
    number = int(path.stem.removeprefix('Prefix'))
    record = next(x for x in report['prefixes'] if x['number']==number)
    assert record['declaration_sha256'] == sha(original_declaration.encode())
    files,parts,start,rows = layout(number,original_declaration,report['rows_per_module'])
    literal_sources = {}
    for name,data in files.items():
        actual_source = (ROOT/name).read_bytes()
        if actual_source != data and name.parent.name.endswith('Chunks'):
            from pool_c981_prefix_finsets import expand_pooled_helper
            actual_source = expand_pooled_helper(name,actual_source)
        assert actual_source == data, f'Literal factor differs: {name}'
        literal_sources[name] = actual_source.decode()
    assert {p.name for p in (ROOT/BASE/f'Prefix{number:02}Chunks').glob('*.lean')} == \
        {Path(part['path']).name for part in parts}
    inverse_rows = []
    for part in parts:
        source = literal_sources[Path(part['path'])]
        body = source[len(part['header']):-len(']\n'+END)]
        lines = body.splitlines(keepends=True)
        assert len(lines) == part['row_count']
        for local,row in enumerate(lines):
            row = row.removesuffix('\n').removesuffix(',')
            global_index = part['offset']+local
            inverse_rows.append(row+(',\n' if global_index+1<len(rows) else '\n'))
    inverse = start+''.join(inverse_rows)+']\n'
    assert inverse == original_declaration, 'Exact row/order inverse differs'
    assert record['wrapper_sha256'] == sha(actual)
    # These hashes pin the original literal representation. An optional pool's
    # actual bytes are separately pinned before exact expansion above.
    assert record['chunks'] == [{k:v for k,v in p.items() if k!='header'} for p in parts]
    return inverse


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--rows-per-module',type=int,default=256)
    args = parser.parse_args()
    assert 1 <= args.rows_per_module <= 256
    pilot = json.loads(PILOT_MANIFEST.read_text())
    commit = pilot['original_commit']
    prefix = subprocess.check_output(['git','rev-parse','--show-prefix'],cwd=ROOT,text=True).strip()
    previous = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else None
    if previous:
        assert previous['rows_per_module'] == args.rows_per_module, 'Do not mix data chunk sizes'
    expected,records,declarations = {},[],{}
    for number in (9,10):
        source = Path(f'Completion/Cases/C981/Coverage/Prefix{number:02}.lean')
        original = subprocess.check_output(['git','show',f'{commit}:{prefix}{source}'],cwd=ROOT)
        pin = next(x for x in pilot['prefixes'] if x['source']==source.as_posix())
        assert sha(original) == pin['original_sha256']
        text = original.decode()
        declaration = f'def prefix{number:02} '+text.split(f'def prefix{number:02} ',1)[1].split(f'theorem step{number:02} ',1)[0]
        assert sha(declaration.encode()) == pin['declaration_sha256']
        files,parts,_,rows = layout(number,declaration,args.rows_per_module)
        expected.update(files)
        target = BASE/f'Prefix{number:02}.lean'
        declarations[target] = declaration
        records.append({'number':number,'row_count':len(rows),
            'declaration_sha256':sha(declaration.encode()),
            'inverse_declaration_sha256':sha(declaration.encode()),
            'wrapper_sha256':sha(files[target]),
            'chunks':[{k:v for k,v in p.items() if k!='header'} for p in parts]})
    report = {'original_commit':commit,'rows_per_module':args.rows_per_module,'prefixes':records,
        'added_lean_modules':sum(len(r['chunks']) for r in records),
        'public_data_types_unchanged':True,'expanded_rows_byte_identical':True,
        'row_order_unchanged':True,'new_proofs':0,'new_native_sites':0,'lean_replayed':False}
    if args.write:
        for path,data in expected.items():
            if (ROOT/path).exists():
                choices = [data]
                if path in declarations:
                    choices.append((DATA_HEADER+declarations[path]+END).encode())
                assert (ROOT/path).read_bytes() in choices, f'Refusing overwrite: {path}'
        for path,data in expected.items():
            (ROOT/path).parent.mkdir(parents=True,exist_ok=True)
            (ROOT/path).write_bytes(data)
        MANIFEST.parent.mkdir(parents=True,exist_ok=True)
        MANIFEST.write_text(json.dumps(report,indent=2)+'\n')
    else:
        assert previous == report, 'Literal factoring manifest differs'
    for path,declaration in declarations.items():
        audit_data_declaration(path,declaration)
    print(json.dumps({'audit':'passed','rows_per_module':args.rows_per_module,
        'added_lean_modules':report['added_lean_modules'],'original_rows':5291,
        'literal_representation_bytes':sum(len(x) for x in expected.values()),
        'current_source_bytes':sum((ROOT/path).stat().st_size for path in expected),
        'new_proofs':0,'lean_replayed':False}))


if __name__ == '__main__':
    main()
