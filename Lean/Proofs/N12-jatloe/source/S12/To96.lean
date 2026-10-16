import S12.To97
import S12.Case445
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase445 : List CoverRow := afterCase997.filter (fun r => decide (r.originalId≠445))
theorem afterCase445_count : afterCase445.length=96 := by native_decide
theorem case445_row_identity : ∀ r∈afterCase997,r.originalId=445 → r.groups=case445Family := by native_decide
theorem packing_reduction_to_96 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase445,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_97 p
  have hn : r.originalId≠445 := by
    intro he
    exact case445_impossible (t.pullPacking p) (hf.trans (case445_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_96
end S12
