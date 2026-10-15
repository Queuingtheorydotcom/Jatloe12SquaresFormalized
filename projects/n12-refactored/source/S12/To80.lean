import S12.To81
import S12.SharedCase1078
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterGeometry1078 : List CoverRow := afterGeometry28More.filter (fun r => decide (r.originalId≠1078))
theorem afterGeometry1078_count : afterGeometry1078.length=80 := by native_decide
theorem reduction80_case1078_identity : ∀ r∈afterGeometry28More,r.originalId=1078 → r.groups=case1078Family := by native_decide
theorem packing_reduction_to_80 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterGeometry1078,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_81 p
  have h1078 : r.originalId≠1078 := by
    intro he
    exact case1078_shared_impossible (t.pullPacking p) (hf.trans (reduction80_case1078_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true h1078⟩,hf⟩
#print axioms packing_reduction_to_80
end S12
