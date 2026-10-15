import S12.To39
import S12.SharedCase993
import S12.SharedCase1063
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterRecoveryEightExclusions : List CoverRow := afterRecoverySixExclusions.filter (fun r => decide (r.originalId≠993 ∧ r.originalId≠1063))
theorem afterRecoveryEightExclusions_count : afterRecoveryEightExclusions.length=37 := by native_decide
theorem reduction37_case993_identity : ∀ r∈afterRecoverySixExclusions,r.originalId=993 → r.groups=case993Family := by native_decide
theorem reduction37_case1063_identity : ∀ r∈afterRecoverySixExclusions,r.originalId=1063 → r.groups=case1063Family := by native_decide
theorem packing_reduction_to_37 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterRecoveryEightExclusions,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_39 p
  have h993 : r.originalId≠993 := by
    intro he
    exact case993_shared_impossible (t.pullPacking p) (hf.trans (reduction37_case993_identity r hr he))
  have h1063 : r.originalId≠1063 := by
    intro he
    exact case1063_shared_impossible (t.pullPacking p) (hf.trans (reduction37_case1063_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h993,h1063⟩⟩,hf⟩
#print axioms packing_reduction_to_37
end S12
