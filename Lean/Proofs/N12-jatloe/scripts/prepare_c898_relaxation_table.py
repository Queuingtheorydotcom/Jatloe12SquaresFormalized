#!/usr/bin/env python3
"""Prepare all 927 retained C898 relaxations as original pose-ID pairs.

No active Lean source is modified. Outputs go to the proposal directory,
with the original retained link order and a source/hash accounting report.
The Lean materializer reconstructs untrusted local support hints; the ordinary
kernel checker validates their coefficients, bounds and strictness later.

Parent serial slot only: --run, 60 seconds, 128 MiB RSS, 4 MiB output.
No solver, generator subprocess, Lean process, or network access is used.
"""
from pathlib import Path
import argparse
import hashlib
import json
import resource
import signal
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'evidence/proposals/C898RelaxationTable'
MODULE = 'Compact.Cases.C898.CompactRelaxation'
NAMESPACE = 'N12Compact.C898CompactRelaxation'
CHUNK_SIZE = 64


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def header(imports, namespace):
    return '\n'.join('import ' + name for name in imports) + f'''

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace {namespace}
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

'''


def footer(namespace):
    return f'\nend\nend {namespace}\n'


def data_source(group, records):
    namespace = f'{NAMESPACE}.Data{group:02d}'
    out = header(['Compact.Core.RelaxationSyntax',
                  'Compact.Core.FiniteCheckChunks',
                  'Compact.Cases.C898.SharedDictionary',
                  'Mathlib.Tactic.FinCases'], namespace)
    # Separate closed definitions keep elaboration local; the array contains
    # references, not one deeply nested term containing all materializers.
    for local, record in enumerate(records):
        out += f'''def entry{local} : Entry dictionary :=
  cached_relaxation%(dictionary, {record['source']}, {record['target']})

'''
    out += 'def data : Array (Entry dictionary) := #[\n'
    out += ',\n'.join(f'  entry{i}' for i in range(len(records))) + '\n]\n\n'
    out += f'''def get (i : Fin {len(records)}) : Entry dictionary :=
  data[i.val]'(by change i.val < {len(records)}; exact i.isLt)

def Claim (i : Fin {len(records)}) : Prop := (get i).Check

instance (i : Fin {len(records)}) : Decidable (Claim i) :=
  inferInstanceAs (Decidable ((get i).Check))

'''
    blocks = (len(records) + 7) // 8
    for block in range(blocks):
        out += f'''theorem block{block} : FiniteCheckChunks.Check Claim {block} := by
  decide +kernel

'''
    out += f'''theorem checked (i : Fin {len(records)}) : (get i).Check := by
  refine FiniteCheckChunks.sound Claim (count := {blocks}) (by decide) ?_ i
  intro part
  fin_cases part
'''
    out += ''.join(f'  · exact block{block}\n' for block in range(blocks))
    return out + footer(namespace)


def all_source(groups):
    out = header([f'{MODULE}.Data{group:02d}' for group, _, _ in groups], NAMESPACE)
    out += '''/-- IDs retain the exact historical non-incoming link order. -/
abbrev linksCount : Nat := 927

def entries (i : Fin linksCount) : Entry dictionary :=
'''
    for k, (group, start, count) in enumerate(groups):
        bound = 'omega' if k + 1 < len(groups) else 'have bound : i.val < 927 := i.isLt; omega'
        value = f'Data{group:02d}.get ⟨i.val - {start}, by {bound}⟩'
        out += (f'  if h{k} : i.val < {start + count} then {value} else\n'
                if k + 1 < len(groups) else f'  {value}\n')
    out += '''
private theorem checkIf {α : Type} (P : α → Prop) (test : Prop) [Decidable test]
    (yes : test → α) (no : ¬test → α)
    (hy : ∀ h, P (yes h)) (hn : ∀ h, P (no h)) :
    P (dite test yes no) := by
  by_cases h : test
  · simpa only [dif_pos h] using hy h
  · simpa only [dif_neg h] using hn h

theorem entries_checked (i : Fin linksCount) : (entries i).Check := by
  unfold entries
'''
    # Apply a generic theorem over an opaque predicate. Both split and
    # split_ifs recursively simplified the rich concrete certificate data.
    for k, (group, _, _) in enumerate(groups):
        indent = ' ' * (2 + 2*k)
        if k + 1 < len(groups):
            out += indent + 'refine checkIf Entry.Check _ _ _ ?_ ?_\n'
            out += indent + f'· intro h{k}; exact Data{group:02d}.checked _\n'
            out += indent + f'· intro h{k}\n'
        else:
            out += indent + f'exact Data{group:02d}.checked _\n'
    out += '''
def links (i : Fin linksCount) : Spec poseCount := (entries i).spec

/-- Exact original oriented-pose implication for every retained link. -/
theorem link_sound (i : Fin linksCount) (q : OpenSquare)
    (holds : (poses (links i).source).OrientedRealizes q) :
    (poses (links i).target).OrientedRealizes q :=
  (entries i).sound (entries_checked i) positive_denominators q holds

#print axioms link_sound
'''
    return out + footer(NAMESPACE)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    if not parser.parse_args().run:
        parser.error('Prepared only; --run requires the parent serial slot.')
    started = time.monotonic()

    def guard(*_):
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if time.monotonic() - started > 60 or rss > 128 * 1024**2:
            raise RuntimeError('Relaxation producer exceeded 60 seconds or 128 MiB RSS')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .1, .1)
    inputs = {
        'witnesses': ROOT / 'evidence/c898-relaxation-two-index-witnesses.json',
        'retained_map': ROOT / 'evidence/c898-retained-relaxation-link-map.json',
    }
    original = json.loads(inputs['witnesses'].read_text())
    retained = json.loads(inputs['retained_map'].read_text())
    assert len(original) == 2048 and len(retained) == 927
    records = []
    for old_index, item in enumerate(original):
        if item['name'].startswith('incoming898ToScout898'):
            assert old_index < 1121
            continue
        index = len(records)
        assert index == old_index - 1121
        assert all(type(item[k]) is int and 0 <= item[k] < 3317
                   for k in ('source', 'target'))
        record = {k: item[k] for k in ('name', 'source', 'target')}
        record.update(index=index, old_index=old_index)
        assert record == retained[index]
        records.append(record)
    assert len(records) == 927
    assert len({item['name'] for item in records}) == 927
    outputs = {}
    groups = []
    for group, start in enumerate(range(0, len(records), CHUNK_SIZE)):
        selected = records[start:start + CHUNK_SIZE]
        outputs[f'Data{group:02d}.lean'] = data_source(group, selected)
        groups.append((group, start, len(selected)))
    outputs['All.lean'] = all_source(groups)
    total_bytes = sum(len(source.encode()) for source in outputs.values())
    assert total_bytes < 4 * 1024**2
    # Rendering is completed before writing; interrupted files are atomically
    # replaced, and the manifest is written last to mark a complete proposal.
    DEST.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = DEST / name
        temporary = path.with_suffix('.lean.tmp')
        temporary.write_text(source)
        temporary.replace(path)
    map_path = DEST / 'link-map.json'
    map_path.write_text(json.dumps(records, separators=(',', ':')) + '\n')
    report = {
        'scope': 'all 927 retained C898 links; source proposal only, not Lean acceptance',
        'namespace': NAMESPACE,
        'production_module': MODULE,
        'links': len(records),
        'unchanged_link_ids': True,
        'removed_source_support_rule_records': 7086,
        'serialized_support_lists': 0,
        'serialized_row_coefficients': 0,
        'source_pairs': len(records),
        'module_count': len(outputs),
        'lines': sum(source.count('\n') for source in outputs.values()),
        'bytes': total_bytes,
        'entries_per_module': CHUNK_SIZE,
        'numeric_batch_size': 8,
        'input_sha256': {key: digest(path) for key, path in inputs.items()},
        'outputs': {name: {'lines': source.count('\n'), 'bytes': len(source.encode()),
                           'sha256': digest(DEST / name)}
                    for name, source in outputs.items()},
        'link_map_sha256': digest(map_path),
        'integration': 'After acceptance, change RetainedRelaxation.All import and namespace to CompactRelaxation.All; links.source, links.target, link IDs and link_sound remain exact. No old IndexedRelaxation.Link.Check is assumed.',
        'remaining_validation': 'The full materializer run must succeed within its row/candidate bounds, every numeric check must pass, and original pair/chord consumers must replay. The authentic first link already passed separately.',
        'elapsed_seconds': time.monotonic() - started,
    }
    guard()
    report_path = ROOT / 'evidence/c898-compact-relaxation-proposal.json'
    temporary = report_path.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(report, indent=2) + '\n')
    temporary.replace(report_path)
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: report[key] for key in
                     ('links', 'module_count', 'lines', 'bytes', 'elapsed_seconds')}))


if __name__ == '__main__':
    main()
