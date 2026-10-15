import S12.To88
import S12.SharedCase28
import S12.SharedCase537
import S12.SharedCase556
import S12.SharedCase565
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterGeometry28Group : List CoverRow := afterShared1075_1087.filter (fun r => decide (r.originalId≠28 ∧ r.originalId≠537 ∧ r.originalId≠556 ∧ r.originalId≠565))
theorem afterGeometry28Group_count : afterGeometry28Group.length=84 := by native_decide
theorem reduction84_case28_identity : ∀ r∈afterShared1075_1087,r.originalId=28 → r.groups=case28Family := by native_decide
theorem reduction84_case537_identity : ∀ r∈afterShared1075_1087,r.originalId=537 → r.groups=case537Family := by native_decide
theorem reduction84_case556_identity : ∀ r∈afterShared1075_1087,r.originalId=556 → r.groups=case556Family := by native_decide
theorem reduction84_case565_identity : ∀ r∈afterShared1075_1087,r.originalId=565 → r.groups=case565Family := by native_decide
theorem packing_reduction_to_84 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterGeometry28Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_88 p
  have h28 : r.originalId≠28 := by
    intro he
    exact case28_shared_impossible (t.pullPacking p) (hf.trans (reduction84_case28_identity r hr he))
  have h537 : r.originalId≠537 := by
    intro he
    exact case537_shared_impossible (t.pullPacking p) (hf.trans (reduction84_case537_identity r hr he))
  have h556 : r.originalId≠556 := by
    intro he
    exact case556_shared_impossible (t.pullPacking p) (hf.trans (reduction84_case556_identity r hr he))
  have h565 : r.originalId≠565 := by
    intro he
    exact case565_shared_impossible (t.pullPacking p) (hf.trans (reduction84_case565_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h28,h537,h556,h565⟩⟩,hf⟩
#print axioms packing_reduction_to_84
end S12
