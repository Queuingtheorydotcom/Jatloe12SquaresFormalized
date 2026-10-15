import S12.To95
import S12.Case78
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase78 : List CoverRow := afterCase454.filter (fun r => decide (r.originalId≠78))
theorem afterCase78_count : afterCase78.length=94 := by native_decide
theorem case78_row_identity : ∀ r∈afterCase454,r.originalId=78 → r.groups=case78Family := by native_decide
theorem packing_reduction_to_94 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase78,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_95 p
  have hn : r.originalId≠78 := by
    intro he
    exact case78_impossible (t.pullPacking p) (hf.trans (case78_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_94
end S12
