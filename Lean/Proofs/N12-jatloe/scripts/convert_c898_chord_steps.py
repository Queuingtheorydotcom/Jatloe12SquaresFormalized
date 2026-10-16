#!/usr/bin/env python3
"""Assemble both complete vertical transitions from checked interval plans."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'evidence/c898-chord-window-supports.json').read_text())
links=json.loads((ROOT/'evidence/c898-relaxation-link-map.json').read_text())
by_source={r['source']:r for r in links}
def nums(items):return '['+', '.join(map(str,items))+']'
domains={9:('continuousScout898Domain5_0','continuousScout898Domain5_10',
            ['continuousScout898Domain0_9','continuousScout898Domain7_7','continuousScout898Domain11_0']),
         10:('continuousScout898Domain5_10','continuousScout898Domain5_11',
             ['continuousScout898Domain3_3','continuousScout898Domain6_5','continuousScout898Domain9_8'])}
for step in (9,10):
    lo,hi=data['windows'][str(step)];source,target,neighbors=domains[step]
    plans=[p for p in data['plans'] if p['step']==step]
    intermediate=[]
    for p in plans:
        for b in p['branches']:
            if 'piece' in b and b['piece'] not in intermediate:intermediate.append(b['piece'])
    link_ids=[by_source[p]['index'] for p in intermediate]
    out=['import Compact.Cases.C898.ChordPlans','import Compact.Cases.C898.SharedDomains',
         'import Compact.Cases.C898.Relaxation.All','',
         f'namespace N12Compact.C898Chord.Step{step}',
         'open S12 S12Pilot C898Shared C898Relaxation IndexedRelaxation AngleSection',
         'set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
         f'def lo : ℚ := ({lo})',f'def hi : ℚ := ({hi})',
         'theorem ordered : lo ≤ hi := by norm_num [lo, hi]','']
    for n,domain in enumerate(neighbors):
        recs=[w for w in data['neighbors'] if w['step']==step and w['neighbor']==n]
        out+=[f'def neighbors{n} : List Neighbor := [']
        for i,w in enumerate(recs):
            # Audit order is upper support then lower support.
            up,low=w['supports']
            fields=[w['pose'],*low['rows'],*up['rows']]
            out+=['  ⟨'+', '.join(map(str,fields))+'⟩'+(',' if i+1<len(recs) else '')]
        out+=[']',f'theorem neighbors{n}_checked : ∀ w ∈ neighbors{n}, w.Check lo hi := by decide +kernel',
              f'theorem neighbors{n}_covered : NeighborCoverCheck {domain}Ids neighbors{n} := by decide +kernel','']
    out+=['def plans : List Plan := [']
    for i,p in enumerate(plans):
        branches=[]
        for b in p['branches']:
            branches.append('.keep '+str(b['piece']) if 'piece' in b else '.close '+' '.join(map(str,b['excluded_by'])))
        out+=['  ⟨'+str(p['source'])+', '+', '.join(branches)+'⟩'+(',' if i+1<len(plans) else '')]
    out+=[']',f'def intermediateIds : List (Fin poseCount) := {nums(intermediate)}',
          'theorem plans_checked : ∀ w ∈ plans, w.Check lo hi := by decide +kernel',
          f'theorem plans_covered : PlansCoverCheck {source}Ids intermediateIds plans := by decide +kernel','',
          f'def relaxationIds : List (Fin linksCount) := {nums(link_ids)}',
          'def relaxations : List (Link poseCount rulesCount) := relaxationIds.map links',
          'theorem relaxations_checked : ∀ w ∈ relaxations, w.Check dictionary rules := by',
          '  intro w hw','  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw','  exact links_checked i',
          f'theorem relaxations_covered : CoverCheck intermediateIds {target}Ids relaxations := by decide +kernel','',
          f'theorem chordStep{step}_sound (q : Fin 4 → OpenSquare)',
          '    (ha : ∀ i, 1 < (q i).side) (hb : ∀ i, InsideContainer (q i))',
          '    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))',
          f'    (hs : OrientedPoseCovered {source} (q 0))']
    for i,domain in enumerate(neighbors):out+=[f'    (hn{i} : OrientedPoseCovered {domain} (q {i+1}))']
    out+=[f'    : OrientedPoseCovered {target} (q 0) := by',
          '  have neighbor_sections : ∀ x, (lo : ℝ) ≤ x → x ≤ (hi : ℝ) →',
          '      ∀ i : Fin 3, VerticalSection (q i.succ) x := by',
          '    intro x hx0 hx1 i','    fin_cases i']
    for i,domain in enumerate(neighbors):
        out+=[f'    · exact neighbor_cover_sound lo hi {domain}Ids neighbors{i}',
              f'        neighbors{i}_covered neighbors{i}_checked (q {i+1}) (ha {i+1}) hn{i} x hx0 hx1']
    out+=[f'  have hpieces := plans_cover_sound lo hi ordered {source}Ids intermediateIds plans',
          '    plans_covered plans_checked q ha hb hd hs neighbor_sections',
          f'  exact cover_sound dictionary rules intermediateIds {target}Ids relaxations',
          '    relaxations_covered positive_denominators rules_checked relaxations_checked (q 0) hpieces','',
          f'#print axioms chordStep{step}_sound',f'end N12Compact.C898Chord.Step{step}','']
    (ROOT/f'Compact/Cases/C898/ChordStep{step}.lean').write_text('\n'.join(out))
files=[ROOT/f'Compact/Cases/C898/{name}.lean' for name in ['ChordRadii','ChordPlans','ChordStep9','ChordStep10']]
report={'scope':'Both complete original C898 vertical transitions, source assembly pending Lean replay.',
        'plans':len(data['plans']),'neighbor_leaves':len(data['neighbors']),
        'lean_lines':sum(p.read_text().count('\n') for p in files),'lean_bytes':sum(p.stat().st_size for p in files)}
(ROOT/'evidence/c898-chord-conversion.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
