import S12.To58
import S12.SharedCase999
import S12.SharedCase1002
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterUnion999Group : List CoverRow := afterUnion1073Group.filter (fun r => decide (r.originalId≠999 ∧ r.originalId≠1002))
theorem afterUnion999Group_count : afterUnion999Group.length=56 := by native_decide
theorem reduction56_case999_identity : ∀ r∈afterUnion1073Group,r.originalId=999 → r.groups=case999Family := by native_decide
theorem reduction56_case1002_identity : ∀ r∈afterUnion1073Group,r.originalId=1002 → r.groups=case1002Family := by native_decide
theorem packing_reduction_to_56 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterUnion999Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_58 p
  have h999 : r.originalId≠999 := by
    intro he
    exact case999_shared_impossible (t.pullPacking p) (hf.trans (reduction56_case999_identity r hr he))
  have h1002 : r.originalId≠1002 := by
    intro he
    exact case1002_shared_impossible (t.pullPacking p) (hf.trans (reduction56_case1002_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h999,h1002⟩⟩,hf⟩
#print axioms packing_reduction_to_56
end S12
