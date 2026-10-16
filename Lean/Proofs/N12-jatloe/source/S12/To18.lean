import S12.To20
import S12.BatchedPush896
import S12.BatchedPush975
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushJoined18 : List CoverRow := afterPushJoined20.filter (fun r => decide (r.originalId≠896 ∧ r.originalId≠975))
theorem afterPushJoined18_count : afterPushJoined18.length=18 := by native_decide
theorem reduction18_case896_identity : ∀ r∈afterPushJoined20,r.originalId=896 → r.groups=case896Family := by native_decide
theorem reduction18_case975_identity : ∀ r∈afterPushJoined20,r.originalId=975 → r.groups=case975Family := by native_decide
theorem packing_reduction_to_18 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushJoined18,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_20 p
  have h896 : r.originalId≠896 := by
    intro he
    exact case896_shared_impossible (t.pullPacking p) (hf.trans (reduction18_case896_identity r hr he))
  have h975 : r.originalId≠975 := by
    intro he
    exact case975_shared_impossible (t.pullPacking p) (hf.trans (reduction18_case975_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h896,h975⟩⟩,hf⟩
#print axioms packing_reduction_to_18
end S12
