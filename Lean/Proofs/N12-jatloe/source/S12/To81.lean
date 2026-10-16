import S12.To84
import S12.SharedCase567
import S12.SharedCase569
import S12.SharedCase570
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterGeometry28More : List CoverRow := afterGeometry28Group.filter (fun r => decide (r.originalId≠567 ∧ r.originalId≠569 ∧ r.originalId≠570))
theorem afterGeometry28More_count : afterGeometry28More.length=81 := by native_decide
theorem reduction81_case567_identity : ∀ r∈afterGeometry28Group,r.originalId=567 → r.groups=case567Family := by native_decide
theorem reduction81_case569_identity : ∀ r∈afterGeometry28Group,r.originalId=569 → r.groups=case569Family := by native_decide
theorem reduction81_case570_identity : ∀ r∈afterGeometry28Group,r.originalId=570 → r.groups=case570Family := by native_decide
theorem packing_reduction_to_81 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterGeometry28More,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_84 p
  have h567 : r.originalId≠567 := by
    intro he
    exact case567_shared_impossible (t.pullPacking p) (hf.trans (reduction81_case567_identity r hr he))
  have h569 : r.originalId≠569 := by
    intro he
    exact case569_shared_impossible (t.pullPacking p) (hf.trans (reduction81_case569_identity r hr he))
  have h570 : r.originalId≠570 := by
    intro he
    exact case570_shared_impossible (t.pullPacking p) (hf.trans (reduction81_case570_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h567,h569,h570⟩⟩,hf⟩
#print axioms packing_reduction_to_81
end S12
