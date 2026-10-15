import S12.To94
import S12.Case982
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase982 : List CoverRow := afterCase78.filter (fun r => decide (r.originalId≠982))
theorem afterCase982_count : afterCase982.length=93 := by native_decide
theorem case982_row_identity : ∀ r∈afterCase78,r.originalId=982 → r.groups=case982Family := by native_decide
theorem packing_reduction_to_93 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase982,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_94 p
  have hn : r.originalId≠982 := by
    intro he
    exact case982_impossible (t.pullPacking p) (hf.trans (case982_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_93
end S12
