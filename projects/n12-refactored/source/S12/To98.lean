import S12.To99
import S12.Case1001
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase1001 : List CoverRow := afterCase715.filter (fun r => decide (r.originalId≠1001))
theorem afterCase1001_count : afterCase1001.length=98 := by native_decide
theorem case1001_row_identity : ∀ r∈afterCase715,r.originalId=1001 → r.groups=case1001Family := by native_decide
theorem packing_reduction_to_98 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase1001,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_99 p
  have hn : r.originalId≠1001 := by
    intro he
    exact case1001_impossible (t.pullPacking p) (hf.trans (case1001_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_98
end S12
