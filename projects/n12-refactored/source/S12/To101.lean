import S12.To102
import S12.Case995
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def afterCase995 : List CoverRow := afterLeftPair.filter (fun r => decide (r.originalId≠995))
theorem afterCase995_count : afterCase995.length=101 := by native_decide
theorem case995_row_identity : ∀ r∈afterLeftPair,r.originalId=995 → r.groups=case995Family := by native_decide

theorem packing_reduction_to_101 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase995,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_102 p
  have hn : r.originalId≠995 := by
    intro he
    exact case995_impossible (t.pullPacking p) (hf.trans (case995_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_101
end S12
