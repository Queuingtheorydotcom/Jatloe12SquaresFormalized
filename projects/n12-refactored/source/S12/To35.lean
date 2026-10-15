import S12.To36
import S12.SharedCase1064
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterRecoveryTenExclusions : List CoverRow := afterRecoveryNineExclusions.filter (fun r => decide (r.originalId≠1064))
theorem afterRecoveryTenExclusions_count : afterRecoveryTenExclusions.length=35 := by native_decide
theorem reduction35_case1064_identity : ∀ r∈afterRecoveryNineExclusions,r.originalId=1064 → r.groups=case1064Family := by native_decide
theorem packing_reduction_to_35 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterRecoveryTenExclusions,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_36 p
  have h1064 : r.originalId≠1064 := by
    intro he
    exact case1064_shared_impossible (t.pullPacking p) (hf.trans (reduction35_case1064_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h1064⟩,hf⟩
#print axioms packing_reduction_to_35
end S12
