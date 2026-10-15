import S12.To76
import S12.SharedCase1084
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCommon1084 : List CoverRow := afterUnion1078Group.filter (fun r => decide (r.originalId≠1084))
theorem afterCommon1084_count : afterCommon1084.length=75 := by native_decide
theorem reduction75_case1084_identity : ∀ r∈afterUnion1078Group,r.originalId=1084 → r.groups=case1084Family := by native_decide
theorem packing_reduction_to_75 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCommon1084,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_76 p
  have h1084 : r.originalId≠1084 := by
    intro he
    exact case1084_shared_impossible (t.pullPacking p) (hf.trans (reduction75_case1084_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h1084⟩,hf⟩
#print axioms packing_reduction_to_75
end S12
