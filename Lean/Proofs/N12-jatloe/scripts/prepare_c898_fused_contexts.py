#!/usr/bin/env python3
"""Parent-run fusion of exact C898 cyclic contexts and numeric views.

No geometry search, Lean, network, or active-source changes. Authenticated
cycle/fallback payloads and every original route remain unchanged. This
removes repeated references, input wrappers, array indexing and cache proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import signal

ROOT = Path(__file__).resolve().parents[1]
PREFIX = Path('Compact/Cases/C898/CachedPairs')
DEST = ROOT/'evidence/proposals/C898FusedContexts'
NAMESPACE = 'N12Compact.C898Cached.AllPairs'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    if not args.run:
        parser.error('parent must schedule --run')
    stage = DEST.with_name(DEST.name+'.staging')
    assert not DEST.exists() and not stage.exists()
    sources = {}
    outputs = {}
    records = []

    def read(relative):
        raw = (ROOT/relative).read_bytes()
        assert len(raw) < 8*1024**2
        sources[str(relative)] = sha(raw)
        return raw

    def stop(*_):
        raise TimeoutError('bounded source preparation interrupted')

    signal.signal(signal.SIGALRM, stop)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    signal.alarm(25)
    try:
        manifest = json.loads(read('evidence/proposals/C898CyclicContexts/manifest.json'))
        route_doc = json.loads(read('evidence/c898-all-cached-pairs.json'))
        routes = route_doc['routes']
        assert len(routes) == 1002 and len({r['context'] for r in routes}) == 1002
        refs_text = read('Compact/Cases/C898/References.lean').decode()
        refs = [','.join(map(str, map(int, row))) for row in re.findall(
            r'⟨(-?\d+), (-?\d+), (\d+), (-?\d+), (\d+)⟩,', refs_text)]
        assert len(refs) == 64
        common_ids = set()
        for index in range(16):
            relative = PREFIX/f'CommonRaw{index:02}.lean'
            text = read(relative).decode()
            ids = list(map(int, re.findall(r'def commonRaw(\d+) : RawSupportFan.Context', text)))
            assert not common_ids.intersection(ids)
            common_ids.update(ids)
            for rid in ids:
                assert f'materialize_raw_fan% (route{rid}.context.numeric)' in text
                assert f'commonRaw{rid} = route{rid}.context.numeric := rfl' in text
            outputs[str(relative)] = (
                f'import Compact.Cases.C898.CachedPairs.Contexts{index:02}\n'
                'import Compact.Cases.C898.CommonPairGroups\n\n'
                '/- Compatibility import. Exact raw views are built with their original\n'
                'checked contexts, so no second cache declaration or reference is stored. -/\n')
        assert len(common_ids) == 995

        seen_routes, cycles, fallbacks = set(), 0, 0
        for index in range(16):
            relative = PREFIX/f'Contexts{index:02}.lean'
            raw = read(relative)
            assert sha(raw) == manifest['outputs'][str(relative)]['sha256']
            text = raw.decode()
            fans = {int(cid): body.split('\n/-- Exact original support fan retained:')[0].strip() for cid, body in re.findall(
                r'def fan(\d+) : Array \(Entry rowCount\) :=\s*(.*?)(?=\ndef (?:fan\d+|cyclicRecipes))',
                text, re.S)}
            recipe_match = re.search(r'def cyclicRecipes\d+ : Array ContextRecipe := #\[\n(.*?)\n\]', text, re.S)
            assert recipe_match is not None
            recipes = re.findall(r'⟨(\d+),(none|some \d+),(\d+),⟨([^⟩]+)⟩,fan(\d+)⟩,', recipe_match.group(1))
            declarations = re.findall(r'def route(\d+) : PoseContext :=\n'
                r'  \(cyclicRecipes\d+Get (\d+)\).certify \(cyclicRecipes\d+_checked (\d+)\)', text)
            assert len(recipes) == len(declarations) == len(fans)
            lines = ['import Compact.Cases.C898.FusedContextSyntax',
                'import Compact.Cases.C898.CachedPairs.CyclicDirections', '',
                'set_option Elab.async false', 'set_option maxRecDepth 10000',
                'set_option linter.unnecessarySeqFocus false', '',
                f'namespace {NAMESPACE}',
                'open C898Shared CachedSupportFan S12', 'noncomputable section', '']
            for ordinal, (declaration, recipe) in enumerate(zip(declarations, recipes)):
                rid, position, checked_position = map(int, declaration)
                assert ordinal == position == checked_position and rid not in seen_routes
                seen_routes.add(rid)
                pose, block, angle, reference, cid = recipe
                pose, angle, cid = int(pose), int(angle), int(cid)
                block_id = None if block == 'none' else int(block[5:])
                old = routes[rid]
                assert (pose, block_id, angle, cid) == (old['pose'],old['block'],old['angle'],old['context'])
                assert re.sub(r'\s+', '', reference) == refs[angle]
                body = fans[cid]
                cycle = re.fullmatch(r'\(materialize_boundary_fan% \(BoundaryFan.context rows \[\] ⟨[^⟩]+⟩\s+'
                                     r'cyclicDirections (\[[^\]]*\])\)\)\.entries', body)
                if cycle:
                    payload = f'c898_cycle%(cyclicDirections,{cycle.group(1)})'
                    cycles += 1
                else:
                    assert body.startswith('#[') and body.endswith(']')
                    entries = re.findall(r'⟨(\d+),(\d+),(\d+),materialize_basis% '
                        r'VertexSupport.Basis.fromRowsPrimitive \(rows (\d+)\) \(rows (\d+)\)⟩,', body)
                    assert entries and len(entries) == body.count('materialize_basis%')
                    assert all(a == c and b == d for _,a,b,c,d in entries)
                    payload = 'c898_entries%('+body+')'
                    fallbacks += 1
                block_term = '[]' if block_id is None else f'blockRows {block_id}'
                numeric = f'commonRaw{rid}' if rid in common_ids else f'route{rid}Raw'
                lines += [f'checked_c898_fan route{rid} {numeric} :=',
                    f'  ⟨{pose},{block_term},{angle}⟩ using {payload}', '']
                records.append({'route':rid,'context':cid,'pose':pose,'block':block_id,
                    'key_angle':angle,'cycle':bool(cycle),'source_fan_sha256':sha(body.encode())})
            lines += ['end', f'end {NAMESPACE}', '']
            outputs[str(relative)] = '\n'.join(lines)
        assert seen_routes == set(range(1002)) and cycles == 858 and fallbacks == 144
        helper = 'Compact/Cases/C898/FusedContextSyntax.lean'
        outputs[helper] = read(helper).decode()
        total_bytes = sum(len(t.encode()) for t in outputs.values())
        assert total_bytes < 4*1024**2
        old_paths = [p for p in outputs if p != helper]
        before_lines = sum((ROOT/p).read_bytes().count(b'\n') for p in old_paths)
        before_bytes = sum((ROOT/p).stat().st_size for p in old_paths)
        report = {'scope':'All 1002 original nonterminal contexts and 995 production raw bindings; source proposal only.',
            'lean_checked':False,'routes':1002,'cycles':cycles,'exact_fallback_fans':fallbacks,
            'raw_view_bindings':995,'extra_raw_views_for_unused_routes':7,
            'theorem_statements_changed':False,
            'before':{'modules':len(old_paths),'lines':before_lines,'bytes':before_bytes},
            'after':{'modules':len(outputs),'lines':sum(t.count('\n') for t in outputs.values()),'bytes':total_bytes},
            'inputs':sources,'records':records,
            'output_files':{p:{'sha256':sha(t.encode()),'lines':t.count('\n'),'bytes':len(t.encode())} for p,t in outputs.items()},
            'remaining':['Generic command replay','Every emitted context check','Existing actual common-point/fallback and whole-stage replay']}
        stage.mkdir(parents=True)
        for path, text in outputs.items():
            target = stage/path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        (stage/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
        stage.rename(DEST)
        print(json.dumps({k:v for k,v in report.items() if k not in {'records','inputs','output_files'}}))
    except BaseException:
        if stage.exists():
            shutil.rmtree(stage)
        raise
    finally:
        signal.alarm(0)


if __name__ == '__main__':
    main()
