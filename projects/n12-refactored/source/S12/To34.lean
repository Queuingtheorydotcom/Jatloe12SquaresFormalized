import S12.To35
import S12.BatchedRecovery994

namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def afterRecoveryElevenExclusions : List CoverRow :=
  afterRecoveryTenExclusions.filter (fun r => decide (r.originalId ≠ 994))

theorem afterRecoveryElevenExclusions_count :
    afterRecoveryElevenExclusions.length = 34 := by native_decide

theorem reduction34_case994_identity :
    ∀ r ∈ afterRecoveryTenExclusions,
      r.originalId = 994 → r.groups = case994Family := by native_decide

theorem packing_reduction_to_34 (p : NormalizedPacking) :
    ∃ t ∈ allTransforms, ∃ r ∈ afterRecoveryElevenExclusions,
      codedMarkerFamily (t.pullPacking p) = r.groups := by
  obtain ⟨t, ht, r, hr, hf⟩ := packing_reduction_to_35 p
  have h994 : r.originalId ≠ 994 := by
    intro he
    exact case994_shared_impossible (t.pullPacking p)
      (hf.trans (reduction34_case994_identity r hr he))
  exact ⟨t, ht, r, List.mem_filter.mpr ⟨hr, decide_eq_true h994⟩, hf⟩

#print axioms packing_reduction_to_34
end S12
