import S12.To60
import S12.SharedCase1073
import S12.SharedCase1074
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterUnion1073Group : List CoverRow := afterScout670Group.filter (fun r => decide (r.originalId≠1073 ∧ r.originalId≠1074))
theorem afterUnion1073Group_count : afterUnion1073Group.length=58 := by native_decide
theorem reduction58_case1073_identity : ∀ r∈afterScout670Group,r.originalId=1073 → r.groups=case1073Family := by native_decide
theorem reduction58_case1074_identity : ∀ r∈afterScout670Group,r.originalId=1074 → r.groups=case1074Family := by native_decide
theorem packing_reduction_to_58 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterUnion1073Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_60 p
  have h1073 : r.originalId≠1073 := by
    intro he
    exact case1073_shared_impossible (t.pullPacking p) (hf.trans (reduction58_case1073_identity r hr he))
  have h1074 : r.originalId≠1074 := by
    intro he
    exact case1074_shared_impossible (t.pullPacking p) (hf.trans (reduction58_case1074_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h1073,h1074⟩⟩,hf⟩
#print axioms packing_reduction_to_58
end S12
