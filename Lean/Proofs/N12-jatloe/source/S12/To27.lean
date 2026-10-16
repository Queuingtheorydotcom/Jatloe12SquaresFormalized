import S12.To31
import S12.BatchedPush48Tail
import S12.BatchedPush573574Tail
import S12.BatchedPush699
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterPushPreparedSeven : List CoverRow := afterPushFirstThree.filter (fun r => decide (r.originalId≠48 ∧ r.originalId≠573 ∧ r.originalId≠574 ∧ r.originalId≠699))
theorem afterPushPreparedSeven_count : afterPushPreparedSeven.length=27 := by native_decide
theorem reduction27_case48_identity : ∀ r∈afterPushFirstThree,r.originalId=48 → r.groups=case48Family := by native_decide
theorem reduction27_case573_identity : ∀ r∈afterPushFirstThree,r.originalId=573 → r.groups=case573Family := by native_decide
theorem reduction27_case574_identity : ∀ r∈afterPushFirstThree,r.originalId=574 → r.groups=case574Family := by native_decide
theorem reduction27_case699_identity : ∀ r∈afterPushFirstThree,r.originalId=699 → r.groups=case699Family := by native_decide
theorem packing_reduction_to_27 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterPushPreparedSeven,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_31 p
  have h48 : r.originalId≠48 := by
    intro he
    exact case48_shared_impossible (t.pullPacking p) (hf.trans (reduction27_case48_identity r hr he))
  have h573 : r.originalId≠573 := by
    intro he
    exact case573_shared_impossible (t.pullPacking p) (hf.trans (reduction27_case573_identity r hr he))
  have h574 : r.originalId≠574 := by
    intro he
    exact case574_shared_impossible (t.pullPacking p) (hf.trans (reduction27_case574_identity r hr he))
  have h699 : r.originalId≠699 := by
    intro he
    exact case699_shared_impossible (t.pullPacking p) (hf.trans (reduction27_case699_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h48,h573,h574,h699⟩⟩,hf⟩
#print axioms packing_reduction_to_27
end S12
