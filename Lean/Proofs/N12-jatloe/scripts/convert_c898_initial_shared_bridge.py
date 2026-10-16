#!/usr/bin/env python3
"""Bind exact initial leaves to the one original-model shared pose dictionary."""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'evidence/c898-shared-pose-map.json').read_text())
owners={}
for pose in data['poses']:
    match=re.fullmatch(r'leaf898_(\d+)_(\d+)',pose['name'])
    if match:owners.setdefault(int(match[1]),[]).append((int(match[2]),pose['index']))
assert sum(map(len,owners.values()))==1121
for owner,records in sorted(owners.items()):
    records.sort();assert [i for i,_ in records]==list(range(len(records)))
    ids=', '.join(str(i) for _,i in records)
    text=f'''import Compact.Cases.C898.Initial.Owner{owner:02d}
import Compact.Cases.C898.SharedPoses

namespace N12Compact.C898Initial
open S12 S12Pilot C898Shared
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original leaf order; no enclosure is widened by this dictionary binding. -/
def rawOwner{owner}Ids : List (Fin poseCount) := [{ids}]

theorem owner{owner}_leaves_shared : owner{owner}.leaves = rawOwner{owner}Ids.map poses := by
  decide +kernel

theorem owner{owner}_oriented_cover_shared (q : OpenSquare)
    (ha : 1 < q.side) (hs : q.side ≤ 1001 / 1000) (hb : InsideContainer q)
    (hi : ∀ P ∈ inside{owner}, q.Inside P.1 P.2)
    (ho : ∀ P ∈ outside{owner}, ¬q.Inside P.1 P.2) :
    OrientedPoseCovered (rawOwner{owner}Ids.map poses) q := by
  rw [← owner{owner}_leaves_shared]
  exact owner{owner}_oriented_cover q ha hs hb hi ho

#print axioms owner{owner}_oriented_cover_shared
end N12Compact.C898Initial
'''
    (ROOT/f'Compact/Cases/C898/Initial/SharedOwner{owner:02d}.lean').write_text(text)
(ROOT/'Compact/Cases/C898/Initial/SharedAll.lean').write_text(''.join(
    f'import Compact.Cases.C898.Initial.SharedOwner{owner:02d}\n' for owner in sorted(owners)))
print(json.dumps({'owners':len(owners),'exact_shared_leaves':sum(map(len,owners.values()))}))
