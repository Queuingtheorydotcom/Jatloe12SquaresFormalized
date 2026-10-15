import S12.To27
import S12.BatchedPush580Tail
import S12.BatchedPush581
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushFirstNine : List CoverRow := afterPushPreparedSeven.filter (fun r => decide (r.originalId≠580 ∧ r.originalId≠581))
theorem afterPushFirstNine_count : afterPushFirstNine.length=25 := by native_decide
theorem reduction25_case580_identity : ∀ r∈afterPushPreparedSeven,r.originalId=580 → r.groups=case580Family := by native_decide
theorem reduction25_case581_identity : ∀ r∈afterPushPreparedSeven,r.originalId=581 → r.groups=case581Family := by native_decide
theorem packing_reduction_to_25 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushFirstNine,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_27 p
  have h580 : r.originalId≠580 := by
    intro he
    exact case580_shared_impossible (t.pullPacking p) (hf.trans (reduction25_case580_identity r hr he))
  have h581 : r.originalId≠581 := by
    intro he
    exact case581_shared_impossible (t.pullPacking p) (hf.trans (reduction25_case581_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h580,h581⟩⟩,hf⟩
#print axioms packing_reduction_to_25
end S12
