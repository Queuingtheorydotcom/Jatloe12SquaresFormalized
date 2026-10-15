import S12.To31
import S12.BatchedPush699
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPush699 : List CoverRow := afterPushFirstThree.filter (fun r => decide (r.originalId≠699))
theorem afterPush699_count : afterPush699.length=30 := by native_decide
theorem reduction30_case699_identity : ∀ r∈afterPushFirstThree,r.originalId=699 → r.groups=case699Family := by native_decide
theorem packing_reduction_to_30 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPush699,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_31 p
  have h699 : r.originalId≠699 := by
    intro he
    exact case699_shared_impossible (t.pullPacking p) (hf.trans (reduction30_case699_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h699⟩,hf⟩
#print axioms packing_reduction_to_30
end S12
