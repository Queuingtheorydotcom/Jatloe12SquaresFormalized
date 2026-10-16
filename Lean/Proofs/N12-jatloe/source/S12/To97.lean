import S12.To98
import S12.Case997
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterCase997 : List CoverRow := afterCase1001.filter (fun r => decide (r.originalId≠997))
theorem afterCase997_count : afterCase997.length=97 := by native_decide
theorem case997_row_identity : ∀ r∈afterCase1001,r.originalId=997 → r.groups=case997Family := by native_decide
theorem packing_reduction_to_97 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase997,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_98 p
  have hn : r.originalId≠997 := by
    intro he
    exact case997_impossible (t.pullPacking p) (hf.trans (case997_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_97
end S12
