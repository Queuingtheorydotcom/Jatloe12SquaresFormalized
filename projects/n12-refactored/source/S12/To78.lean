import S12.To80
import S12.SharedCase575
import S12.SharedCase576
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterGeometry575 : List CoverRow := afterGeometry1078.filter (fun r => decide (r.originalId≠575 ∧ r.originalId≠576))
theorem afterGeometry575_count : afterGeometry575.length=78 := by native_decide
theorem reduction78_case575_identity : ∀ r∈afterGeometry1078,r.originalId=575 → r.groups=case575Family := by native_decide
theorem reduction78_case576_identity : ∀ r∈afterGeometry1078,r.originalId=576 → r.groups=case576Family := by native_decide
theorem packing_reduction_to_78 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterGeometry575,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_80 p
  have h575 : r.originalId≠575 := by
    intro he
    exact case575_shared_impossible (t.pullPacking p) (hf.trans (reduction78_case575_identity r hr he))
  have h576 : r.originalId≠576 := by
    intro he
    exact case576_shared_impossible (t.pullPacking p) (hf.trans (reduction78_case576_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h575,h576⟩⟩,hf⟩
#print axioms packing_reduction_to_78
end S12
