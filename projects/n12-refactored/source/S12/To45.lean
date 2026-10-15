import S12.To49
import S12.SharedCase882
import S12.SharedCase888
import S12.SharedCase889
import S12.SharedCase893
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterFinalWallGroup : List CoverRow := afterScout405684Group.filter (fun r => decide (r.originalId≠882 ∧ r.originalId≠888 ∧ r.originalId≠889 ∧ r.originalId≠893))
theorem afterFinalWallGroup_count : afterFinalWallGroup.length=45 := by native_decide
theorem reduction45_case882_identity : ∀ r∈afterScout405684Group,r.originalId=882 → r.groups=case882Family := by native_decide
theorem reduction45_case888_identity : ∀ r∈afterScout405684Group,r.originalId=888 → r.groups=case888Family := by native_decide
theorem reduction45_case889_identity : ∀ r∈afterScout405684Group,r.originalId=889 → r.groups=case889Family := by native_decide
theorem reduction45_case893_identity : ∀ r∈afterScout405684Group,r.originalId=893 → r.groups=case893Family := by native_decide
theorem packing_reduction_to_45 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterFinalWallGroup,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_49 p
  have h882 : r.originalId≠882 := by
    intro he
    exact case882_shared_impossible (t.pullPacking p) (hf.trans (reduction45_case882_identity r hr he))
  have h888 : r.originalId≠888 := by
    intro he
    exact case888_shared_impossible (t.pullPacking p) (hf.trans (reduction45_case888_identity r hr he))
  have h889 : r.originalId≠889 := by
    intro he
    exact case889_shared_impossible (t.pullPacking p) (hf.trans (reduction45_case889_identity r hr he))
  have h893 : r.originalId≠893 := by
    intro he
    exact case893_shared_impossible (t.pullPacking p) (hf.trans (reduction45_case893_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h882,h888,h889,h893⟩⟩,hf⟩
#print axioms packing_reduction_to_45
end S12
