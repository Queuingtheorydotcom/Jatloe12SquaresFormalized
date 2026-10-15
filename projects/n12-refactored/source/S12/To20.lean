import S12.To22
import S12.BatchedPush700
import S12.BatchedPush972
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushJoined20 : List CoverRow := afterPushJoined22.filter (fun r => decide (r.originalId≠700 ∧ r.originalId≠972))
theorem afterPushJoined20_count : afterPushJoined20.length=20 := by native_decide
theorem reduction20_case700_identity : ∀ r∈afterPushJoined22,r.originalId=700 → r.groups=case700Family := by native_decide
theorem reduction20_case972_identity : ∀ r∈afterPushJoined22,r.originalId=972 → r.groups=case972Family := by native_decide
theorem packing_reduction_to_20 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushJoined20,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_22 p
  have h700 : r.originalId≠700 := by
    intro he
    exact case700_shared_impossible (t.pullPacking p) (hf.trans (reduction20_case700_identity r hr he))
  have h972 : r.originalId≠972 := by
    intro he
    exact case972_shared_impossible (t.pullPacking p) (hf.trans (reduction20_case972_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h700,h972⟩⟩,hf⟩
#print axioms packing_reduction_to_20
end S12
