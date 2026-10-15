import S12.To115
import S12.Case585
namespace S12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def afterCase585 : List CoverRow := afterCase577.filter (fun r => decide (r.originalId≠585))
theorem afterCase585_count : afterCase585.length=114 := by native_decide
theorem case585_row_identity : ∀ r∈afterCase577,r.originalId=585 → r.groups=case585Family := by native_decide

theorem packing_reduction_to_114 (p : NormalizedPacking) :
    ∃ t∈allTransforms, ∃ r∈afterCase585,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_115 p
  have hne : r.originalId≠585 := by
    intro he
    exact case585_impossible (t.pullPacking p) (hf.trans (case585_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩

#print axioms packing_reduction_to_114
end S12
