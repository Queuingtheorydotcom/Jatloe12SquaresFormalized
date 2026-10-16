import S12.To34
import S12.BatchedPush985
import S12.BatchedPush990
import S12.BatchedPush998
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushFirstThree : List CoverRow := afterRecoveryElevenExclusions.filter (fun r => decide (r.originalId≠985 ∧ r.originalId≠990 ∧ r.originalId≠998))
theorem afterPushFirstThree_count : afterPushFirstThree.length=31 := by native_decide
theorem reduction31_case985_identity : ∀ r∈afterRecoveryElevenExclusions,r.originalId=985 → r.groups=case985Family := by native_decide
theorem reduction31_case990_identity : ∀ r∈afterRecoveryElevenExclusions,r.originalId=990 → r.groups=case990Family := by native_decide
theorem reduction31_case998_identity : ∀ r∈afterRecoveryElevenExclusions,r.originalId=998 → r.groups=case998Family := by native_decide
theorem packing_reduction_to_31 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushFirstThree,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_34 p
  have h985 : r.originalId≠985 := by
    intro he
    exact case985_shared_impossible (t.pullPacking p) (hf.trans (reduction31_case985_identity r hr he))
  have h990 : r.originalId≠990 := by
    intro he
    exact case990_shared_impossible (t.pullPacking p) (hf.trans (reduction31_case990_identity r hr he))
  have h998 : r.originalId≠998 := by
    intro he
    exact case998_shared_impossible (t.pullPacking p) (hf.trans (reduction31_case998_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h985,h990,h998⟩⟩,hf⟩
#print axioms packing_reduction_to_31
end S12
