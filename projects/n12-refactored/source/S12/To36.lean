import S12.To37
import S12.BatchedRecovery697
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterRecoveryNineExclusions : List CoverRow := afterRecoveryEightExclusions.filter (fun r => decide (r.originalId≠697))
theorem afterRecoveryNineExclusions_count : afterRecoveryNineExclusions.length=36 := by native_decide
theorem reduction36_case697_identity : ∀ r∈afterRecoveryEightExclusions,r.originalId=697 → r.groups=case697Family := by native_decide
theorem packing_reduction_to_36 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterRecoveryNineExclusions,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_37 p
  have h697 : r.originalId≠697 := by
    intro he
    exact case697_shared_impossible (t.pullPacking p) (hf.trans (reduction36_case697_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h697⟩,hf⟩
#print axioms packing_reduction_to_36
end S12
