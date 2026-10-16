import S12.To96
import S12.Case454
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase454 : List CoverRow := afterCase445.filter (fun r => decide (r.originalId≠454))
theorem afterCase454_count : afterCase454.length=95 := by native_decide
theorem case454_row_identity : ∀ r∈afterCase445,r.originalId=454 → r.groups=case454Family := by native_decide
theorem packing_reduction_to_95 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase454,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_96 p
  have hn : r.originalId≠454 := by
    intro he
    exact case454_impossible (t.pullPacking p) (hf.trans (case454_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_95
end S12
