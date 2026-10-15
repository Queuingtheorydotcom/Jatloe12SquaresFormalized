import S12.To62
import S12.SharedCase670
import S12.SharedCase675
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterScout670Group : List CoverRow := afterUnion669Group.filter (fun r => decide (r.originalId≠670 ∧ r.originalId≠675))
theorem afterScout670Group_count : afterScout670Group.length=60 := by native_decide
theorem reduction60_case670_identity : ∀ r∈afterUnion669Group,r.originalId=670 → r.groups=case670Family := by native_decide
theorem reduction60_case675_identity : ∀ r∈afterUnion669Group,r.originalId=675 → r.groups=case675Family := by native_decide
theorem packing_reduction_to_60 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterScout670Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_62 p
  have h670 : r.originalId≠670 := by
    intro he
    exact case670_shared_impossible (t.pullPacking p) (hf.trans (reduction60_case670_identity r hr he))
  have h675 : r.originalId≠675 := by
    intro he
    exact case675_shared_impossible (t.pullPacking p) (hf.trans (reduction60_case675_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h670,h675⟩⟩,hf⟩
#print axioms packing_reduction_to_60
end S12
