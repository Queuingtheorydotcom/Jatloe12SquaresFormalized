import S12.To104
import S12.Case886
import S12.Case887
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def afterLeftPair : List CoverRow := afterCase716.filter (fun r => decide (r.originalId≠886 ∧ r.originalId≠887))
theorem afterLeftPair_count : afterLeftPair.length=102 := by native_decide
theorem case886_row_identity : ∀ r∈afterCase716,r.originalId=886 → r.groups=case886Family := by native_decide
theorem case887_row_identity : ∀ r∈afterCase716,r.originalId=887 → r.groups=case887Family := by native_decide

theorem packing_reduction_to_102 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterLeftPair,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_104 p
  have h0 : r.originalId≠886 := by
    intro he
    exact case886_impossible (t.pullPacking p) (hf.trans (case886_row_identity r hr he))
  have h1 : r.originalId≠887 := by
    intro he
    exact case887_impossible (t.pullPacking p) (hf.trans (case887_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h0,h1⟩⟩,hf⟩
#print axioms packing_reduction_to_102
end S12
