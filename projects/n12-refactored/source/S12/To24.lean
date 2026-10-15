import S12.To25
import S12.BatchedPush683
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushQueue683 : List CoverRow := afterPushFirstNine.filter (fun r => decide (r.originalId≠683))
theorem afterPushQueue683_count : afterPushQueue683.length=24 := by native_decide
theorem reduction24_case683_identity : ∀ r∈afterPushFirstNine,r.originalId=683 → r.groups=case683Family := by native_decide
theorem packing_reduction_to_24 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushQueue683,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_25 p
  have h683 : r.originalId≠683 := by
    intro he
    exact case683_shared_impossible (t.pullPacking p) (hf.trans (reduction24_case683_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h683⟩,hf⟩
#print axioms packing_reduction_to_24
end S12
