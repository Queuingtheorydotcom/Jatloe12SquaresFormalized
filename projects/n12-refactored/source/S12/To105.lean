import S12.To106
import S12.Case705
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def afterCase705 : List CoverRow := afterSharedTopPair.filter (fun r => decide (r.originalId≠705))
theorem afterCase705_count : afterCase705.length=105 := by native_decide
theorem case705_row_identity : ∀ r∈afterSharedTopPair,r.originalId=705 → r.groups=case705Family := by native_decide

theorem packing_reduction_to_105 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase705,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_106 p
  have hne : r.originalId≠705 := by
    intro he
    exact case705_impossible (t.pullPacking p) (hf.trans (case705_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩
#print axioms packing_reduction_to_105
end S12
