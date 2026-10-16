#!/usr/bin/env python3
"""Reuse authenticated radius values with ordinary quadratic proof terms."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
src=(ROOT/'vendor/S12/AngleChordRadiusData.lean').read_text()
values=re.findall(r'^def angleChordRadius64_(\d+) : .*?⟩,\(([^()]*)\),\(([^()]*)\)⟩$',src,re.M)
assert [int(i) for i,_,_ in values]==list(range(64))
out=['import Compact.Cases.C898.SharedDictionary','import Compact.Bridge.AngleSection','',
     'namespace N12Compact.C898Chord','open S12 AngleSection C898Shared',
     'set_option maxHeartbeats 0','']
for i,b,r in values:
    out += [f'def radius{i} : Radius := ⟨({b}), ({r})⟩',
            f'theorem radius{i}_checked : radius{i}.Check angle64_{i} := by',
            f'  norm_num [radius{i}, Radius.Check, angle64_{i}, supportQuadratic,',
            '    Quadratic.CheckOn, Quadratic.evalRat]','']
out+=['def radiusFor : Fin 64 → Radius :=',
      '  !['+', '.join('radius'+i for i,_,_ in values)+']','',
      'theorem radius_checked (i : Fin 64) : (radiusFor i).Check (dictionary.angles i).val := by',
      '  fin_cases i']
out+=['  · exact radius'+i+'_checked' for i,_,_ in values]
out+=['','#print axioms radius_checked','end N12Compact.C898Chord','']
(ROOT/'Compact/Cases/C898/ChordRadii.lean').write_text('\n'.join(out))
print('wrote64 radius values with exact whole-angle checks')
