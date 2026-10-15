import S12.To116
import S12.Case577
namespace S12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def afterCase577 : List CoverRow := afterCase84.filter (fun r => decide (r.originalId≠577))
theorem afterCase577_count : afterCase577.length=115 := by native_decide
theorem case577_row_identity : ∀ r∈afterCase84,r.originalId=577 → r.groups=case577Family := by native_decide

theorem packing_reduction_to_115 (p : NormalizedPacking) :
    ∃ t∈allTransforms, ∃ r∈afterCase577,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_116 p
  have hne : r.originalId≠577 := by
    intro he
    exact case577_impossible (t.pullPacking p) (hf.trans (case577_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩

#print axioms packing_reduction_to_115
end S12
