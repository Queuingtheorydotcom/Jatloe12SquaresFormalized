import S12.To92
import S12.Case1085
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase1085 : List CoverRow := afterCase1075.filter (fun r => decide (r.originalId≠1085))
theorem afterCase1085_count : afterCase1085.length=91 := by native_decide
theorem case1085_row_identity : ∀ r∈afterCase1075,r.originalId=1085 → r.groups=case1085Family := by native_decide
theorem packing_reduction_to_91 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase1085,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_92 p
  have hn : r.originalId≠1085 := by
    intro he
    exact case1085_impossible (t.pullPacking p) (hf.trans (case1085_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_91
end S12
