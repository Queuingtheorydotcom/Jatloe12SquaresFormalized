import S12.To105
import S12.Case716
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def afterCase716 : List CoverRow := afterCase705.filter (fun r => decide (r.originalId≠716))
theorem afterCase716_count : afterCase716.length=104 := by native_decide
theorem case716_row_identity : ∀ r∈afterCase705,r.originalId=716 → r.groups=case716Family := by native_decide

theorem packing_reduction_to_104 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase716,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_105 p
  have hne : r.originalId≠716 := by
    intro he
    exact case716_impossible (t.pullPacking p) (hf.trans (case716_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩
#print axioms packing_reduction_to_104
end S12
