import S12.To23
import S12.BatchedPush867
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushJoined22 : List CoverRow := afterPushCase868.filter (fun r => decide (r.originalId≠867))
theorem afterPushJoined22_count : afterPushJoined22.length=22 := by native_decide
theorem reduction22_case867_identity : ∀ r∈afterPushCase868,r.originalId=867 → r.groups=case867Family := by native_decide
theorem packing_reduction_to_22 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushJoined22,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_23 p
  have h867 : r.originalId≠867 := by
    intro he
    exact case867_shared_impossible (t.pullPacking p) (hf.trans (reduction22_case867_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h867⟩,hf⟩
#print axioms packing_reduction_to_22
end S12
