#!/usr/bin/env python3
"""Prepare C713's exact retained relaxation links as original source/target IDs.

Run only in the parent's serial256MiB/120second slot. The nine pair stages
select every original surviving piece and its actual target. Alias target
rows require no numerical certificate; all others retain a checked two-row
support or an explicit failure record. No missing rule proves emptiness.
Cached row/hint materialization avoids serializing redundant per-target support
records. At most16MiB atomic proposal output; no compiler or active mutation.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import argparse, hashlib, json, resource, shutil, signal, sys, time

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'evidence/proposals/C713Relaxation'
NS = 'N12Compact.C713Relaxation'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def supports(a, b, target):
    ax, ay, ac = a['integers']
    bx, by, bc = b['integers']
    tx, ty, tc = target['integers']
    determinant = ax * by - ay * bx
    if determinant == 0:
        return False
    sign = 1 if determinant > 0 else -1
    left, right = sign * (tx * by - ty * bx), sign * (ax * ty - ay * tx)
    slack = abs(determinant) * tc - left * ac - right * bc
    return left >= 0 and right >= 0 and slack >= 0 and (
        not target['strict'] or slack > 0 or
        left > 0 and a['strict'] or right > 0 and b['strict'])


def ids(values):
    return '[' + ','.join(map(str, values)) + ']'


def header(imports, namespace=NS):
    return '\n'.join('import ' + name for name in imports) + f'''

namespace {namespace}
open S12 IntegerSupport IndexedRelaxation HistoricalData C713Shared
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section

'''


def footer(namespace=NS):
    return f'\nend\nend {namespace}\n'


def compact_output(kept):
    outputs = {}
    groups = []
    for number, start in enumerate(range(0, len(kept), 64)):
        records = kept[start:start + 64]
        module = f'Data{number:02}'
        namespace = NS + '.' + module
        source = header(['Compact.Core.RelaxationSyntax',
                         'Compact.Cases.C713.SharedDictionary'], namespace)
        count = (len(records) + 7) // 8
        for part in range(count):
            source += f'def entries{part} : List (RelaxationTable.Entry dictionary) := [\n'
            source += ',\n'.join(f'  cached_relaxation%(dictionary,{r["source"]},{r["target"]})'
                                  for r in records[part * 8:part * 8 + 8]) + ']\n\n'
            source += f'''theorem entries{part}_checked : ∀ entry ∈ entries{part}, entry.Check := by
  letI : Decidable (∀ entry ∈ entries{part}, entry.Check) := List.decidableBAll _ entries{part}
  decide +kernel

'''
        source += 'def data : List (RelaxationTable.Entry dictionary) :=\n  '
        source += ' ++ '.join(f'entries{part}' for part in range(count)) + '\n\n'
        source += 'theorem data_checked : ∀ entry ∈ data, entry.Check := by\n'
        source += '  unfold data\n  simp only [List.forall_mem_append]\n'
        source += '  exact ' + (f'entries0_checked' if count == 1 else
            '⟨' + ', '.join(f'entries{part}_checked' for part in range(count)) + '⟩') + '\n\n'
        source += f'''def get (i : Fin {len(records)}) : RelaxationTable.Entry dictionary :=
  data.get ⟨i.val, by change i.val < {len(records)}; exact i.isLt⟩

theorem checked (i : Fin {len(records)}) : (get i).Check :=
  data_checked _ (List.get_mem _ _)
'''
        outputs[f'Compact/Cases/C713/Relaxation/{module}.lean'] = source + footer(namespace)
        groups.append((module, start, len(records)))
    source = header([f'Compact.Cases.C713.Relaxation.{module}' for module, _, _ in groups])
    source += f'abbrev linksCount : Nat := {len(kept)}\n'
    source += 'def links (i : Fin linksCount) : RelaxationTable.Entry dictionary :=\n'
    for index, (module, start, length) in enumerate(groups):
        value = f'{module}.get ⟨i.val-{start},by omega⟩'
        source += (f'  if h{index} : i.val < {start + length} then {value} else\n'
                   if index + 1 < len(groups) else '  ' + value + '\n')
    source += '\ntheorem links_checked (i : Fin linksCount) : (links i).Check := by\n'
    source += '  unfold links\n  split_ifs\n'
    source += '\n'.join(f'  · exact {module}.checked _' for module, _, _ in groups) + '\n\n'
    source += '''theorem link_sound (i : Fin linksCount) (q : S12Pilot.OpenSquare)
    (h : (C713Shared.poses (links i).spec.source).OrientedRealizes q) :
    (C713Shared.poses (links i).spec.target).OrientedRealizes q :=
  (links i).sound (links_checked i) positive_denominators q h

#print axioms link_sound
'''
    outputs['Compact/Cases/C713/Relaxation/All.lean'] = source + footer()
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    if not parser.parse_args().run:
        parser.error('prepared only; parent serial slot and --run required')
    start = time.monotonic()
    stage = DEST.with_name(DEST.name + '.staging')
    need(not DEST.exists() and not stage.exists(), 'refusing existing proposal')

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
        need(time.monotonic() - start < 115 and rss < 256 * 1024**2, '256MiB/115second limit')

    def stop(*_):
        raise RuntimeError('termination requested')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .2, .2)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    stage.mkdir(parents=True)
    try:
        hashes = {}

        def load(name):
            path = ROOT / 'evidence/historical-compact-data' / name
            raw = path.read_bytes()
            hashes[str(path.relative_to(ROOT))] = hashlib.sha256(raw).hexdigest()
            return json.loads(raw)

        manifest = load('manifest.json')
        need(manifest['status'].startswith('data assembled'), 'incomplete source data')
        data, rows, poses, links = [load(name) for name in ['C713.json', 'rows.json', 'poses.json', 'links.json']]
        selected = sorted({i for plan in data['plans'] for i in plan['links']})
        need(len(selected) == 1620, 'unexpected retained link scope')
        rules, rule_ids, kept, failures, statistics = [], {}, [], [], Counter()
        cache = {}
        for old_id in selected:
            guard()
            link = links[old_id]
            source, target = poses[link['source']], poses[link['target']]
            need(source['angle'] == target['angle'], 'original link changes angle')
            source_ids = list(dict.fromkeys(source['rows']))
            selected_rules = []
            for target_id in target['rows']:
                statistics['target_row_occurrences'] += 1
                if target_id in source_ids:
                    statistics['alias_occurrences'] += 1
                    continue
                key = (tuple(source_ids), target_id)
                if key not in cache:
                    cache[key] = next(((target_id, i, j) for i, j in combinations(source_ids, 2)
                        if supports(rows[i], rows[j], rows[target_id])), None)
                rule = cache[key]
                if rule is None:
                    failures.append({'original_link': old_id, 'source': link['source'],
                        'target': link['target'], 'row': target_id,
                        'reason': 'no two-row support; retain unresolved original obligation'})
                    continue
                if rule not in rule_ids:
                    rule_ids[rule] = len(rules)
                    rules.append(rule)
                index = rule_ids[rule]
                if index not in selected_rules:
                    selected_rules.append(index)
                statistics['supported_occurrences'] += 1
            kept.append({'index': len(kept), 'original_id': old_id, 'source': link['source'],
                         'target': link['target'], 'support_ids': selected_rules})
        outputs = {} if failures else compact_output(kept)
        total = sum(len(source.encode()) for source in outputs.values())
        need(total < 16 * 1024**2, '16MiB source output limit')
        for name, source in outputs.items():
            path = stage / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        report = {'status': 'unresolved original obligations' if failures else
            'complete source proposal; Lean replay pending', 'case': 713,
            'original_links': len(selected), 'unique_support_rules': len(rules),
            'statistics': dict(statistics), 'failure_count': len(failures), 'failures': failures,
            'source_representation': 'one original source/target Spec per link; local rows and hints materialized and kernel checked',
            'serialized_support_rules': 0,
            'source_sha256': hashes, 'lean_modules': len(outputs),
            'lean_lines': sum(source.count('\n') for source in outputs.values()), 'lean_bytes': total,
            'outputs': [{'path': name, 'sha256': hashlib.sha256(source.encode()).hexdigest(),
                         'lines': source.count('\n'), 'bytes': len(source.encode())}
                        for name, source in outputs.items()],
            'elapsed_seconds': time.monotonic() - start}
        (stage / 'links.json').write_text(json.dumps(kept, separators=(',', ':')) + '\n')
        (stage / 'rules.json').write_text(json.dumps(rules, separators=(',', ':')) + '\n')
        (stage / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        need(sum(p.stat().st_size for p in stage.rglob('*') if p.is_file()) < 16 * 1024**2,
             '16MiB total output limit')
        stage.rename(DEST)
        print(json.dumps({key: report[key] for key in ['status', 'original_links', 'unique_support_rules',
            'failure_count', 'lean_modules', 'lean_lines', 'lean_bytes', 'elapsed_seconds']}))
    except BaseException:
        shutil.rmtree(stage)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
