import S12.To100
import S12.Case715
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase715 : List CoverRow := afterCase992.filter (fun r => decide (r.originalId≠715))
theorem afterCase715_count : afterCase715.length=99 := by native_decide
theorem case715_row_identity : ∀ r∈afterCase992,r.originalId=715 → r.groups=case715Family := by native_decide
theorem packing_reduction_to_99 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase715,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_100 p
  have hn : r.originalId≠715 := by
    intro he
    exact case715_impossible (t.pullPacking p) (hf.trans (case715_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_99
end S12
