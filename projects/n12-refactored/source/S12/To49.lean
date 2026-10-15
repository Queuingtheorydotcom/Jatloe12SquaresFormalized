import S12.To54
import S12.SharedCase405
import S12.SharedCase424
import S12.SharedCase589
import S12.SharedCase590
import S12.SharedCase684
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterScout405684Group : List CoverRow := afterScout71Group.filter (fun r => decide (r.originalId≠405 ∧ r.originalId≠424 ∧ r.originalId≠589 ∧ r.originalId≠590 ∧ r.originalId≠684))
theorem afterScout405684Group_count : afterScout405684Group.length=49 := by native_decide
theorem reduction49_case405_identity : ∀ r∈afterScout71Group,r.originalId=405 → r.groups=case405Family := by native_decide
theorem reduction49_case424_identity : ∀ r∈afterScout71Group,r.originalId=424 → r.groups=case424Family := by native_decide
theorem reduction49_case589_identity : ∀ r∈afterScout71Group,r.originalId=589 → r.groups=case589Family := by native_decide
theorem reduction49_case590_identity : ∀ r∈afterScout71Group,r.originalId=590 → r.groups=case590Family := by native_decide
theorem reduction49_case684_identity : ∀ r∈afterScout71Group,r.originalId=684 → r.groups=case684Family := by native_decide
theorem packing_reduction_to_49 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterScout405684Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_54 p
  have h405 : r.originalId≠405 := by
    intro he
    exact case405_shared_impossible (t.pullPacking p) (hf.trans (reduction49_case405_identity r hr he))
  have h424 : r.originalId≠424 := by
    intro he
    exact case424_shared_impossible (t.pullPacking p) (hf.trans (reduction49_case424_identity r hr he))
  have h589 : r.originalId≠589 := by
    intro he
    exact case589_shared_impossible (t.pullPacking p) (hf.trans (reduction49_case589_identity r hr he))
  have h590 : r.originalId≠590 := by
    intro he
    exact case590_shared_impossible (t.pullPacking p) (hf.trans (reduction49_case590_identity r hr he))
  have h684 : r.originalId≠684 := by
    intro he
    exact case684_shared_impossible (t.pullPacking p) (hf.trans (reduction49_case684_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h405,h424,h589,h590,h684⟩⟩,hf⟩
#print axioms packing_reduction_to_49
end S12
