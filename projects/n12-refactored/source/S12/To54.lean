import S12.To56
import S12.SharedCase71
import S12.SharedCase80
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterScout71Group : List CoverRow := afterUnion999Group.filter (fun r => decide (r.originalId≠71 ∧ r.originalId≠80))
theorem afterScout71Group_count : afterScout71Group.length=54 := by native_decide
theorem reduction54_case71_identity : ∀ r∈afterUnion999Group,r.originalId=71 → r.groups=case71Family := by native_decide
theorem reduction54_case80_identity : ∀ r∈afterUnion999Group,r.originalId=80 → r.groups=case80Family := by native_decide
theorem packing_reduction_to_54 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterScout71Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_56 p
  have h71 : r.originalId≠71 := by
    intro he
    exact case71_shared_impossible (t.pullPacking p) (hf.trans (reduction54_case71_identity r hr he))
  have h80 : r.originalId≠80 := by
    intro he
    exact case80_shared_impossible (t.pullPacking p) (hf.trans (reduction54_case80_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h71,h80⟩⟩,hf⟩
#print axioms packing_reduction_to_54
end S12
