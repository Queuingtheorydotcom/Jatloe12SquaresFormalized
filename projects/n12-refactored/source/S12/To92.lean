import S12.To93
import S12.Case1075
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase1075 : List CoverRow := afterCase982.filter (fun r => decide (r.originalId≠1075))
theorem afterCase1075_count : afterCase1075.length=92 := by native_decide
theorem case1075_row_identity : ∀ r∈afterCase982,r.originalId=1075 → r.groups=case1075Family := by native_decide
theorem packing_reduction_to_92 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase1075,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_93 p
  have hn : r.originalId≠1075 := by
    intro he
    exact case1075_impossible (t.pullPacking p) (hf.trans (case1075_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_92
end S12
