import S12.To114
import S12.Case678
namespace S12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def afterCase678 : List CoverRow := afterCase585.filter (fun r => decide (r.originalId≠678))
theorem afterCase678_count : afterCase678.length=113 := by native_decide
theorem case678_row_identity : ∀ r∈afterCase585,r.originalId=678 → r.groups=case678Family := by native_decide

theorem packing_reduction_to_113 (p : NormalizedPacking) :
    ∃ t∈allTransforms, ∃ r∈afterCase678,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_114 p
  have hne : r.originalId≠678 := by
    intro he
    exact case678_impossible (t.pullPacking p) (hf.trans (case678_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩

#print axioms packing_reduction_to_113
end S12
