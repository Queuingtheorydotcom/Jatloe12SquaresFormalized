import S12.To24
import S12.BatchedPush868
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushCase868 : List CoverRow := afterPushQueue683.filter (fun r => decide (r.originalId≠868))
theorem afterPushCase868_count : afterPushCase868.length=23 := by native_decide
theorem reduction23_case868_identity : ∀ r∈afterPushQueue683,r.originalId=868 → r.groups=case868Family := by native_decide
theorem packing_reduction_to_23 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushCase868,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_24 p
  have h868 : r.originalId≠868 := by
    intro he
    exact case868_shared_impossible (t.pullPacking p) (hf.trans (reduction23_case868_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h868⟩,hf⟩
#print axioms packing_reduction_to_23
end S12
