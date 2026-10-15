import S12.To78
import S12.SharedCase1081
import S12.SharedCase1083
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterUnion1078Group : List CoverRow := afterGeometry575.filter (fun r => decide (r.originalId≠1081 ∧ r.originalId≠1083))
theorem afterUnion1078Group_count : afterUnion1078Group.length=76 := by native_decide
theorem reduction76_case1081_identity : ∀ r∈afterGeometry575,r.originalId=1081 → r.groups=case1081Family := by native_decide
theorem reduction76_case1083_identity : ∀ r∈afterGeometry575,r.originalId=1083 → r.groups=case1083Family := by native_decide
theorem packing_reduction_to_76 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterUnion1078Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_78 p
  have h1081 : r.originalId≠1081 := by
    intro he
    exact case1081_shared_impossible (t.pullPacking p) (hf.trans (reduction76_case1081_identity r hr he))
  have h1083 : r.originalId≠1083 := by
    intro he
    exact case1083_shared_impossible (t.pullPacking p) (hf.trans (reduction76_case1083_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h1081,h1083⟩⟩,hf⟩
#print axioms packing_reduction_to_76
end S12
