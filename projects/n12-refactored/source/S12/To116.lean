import S12.Normalization
import S12.Case84

namespace S12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def afterCase84 : List CoverRow := retainedRows.filter (fun r => decide (r.originalId≠84))
theorem afterCase84_count : afterCase84.length=116 := by native_decide
theorem case84_row_identity : ∀ r∈retainedRows,r.originalId=84 → r.groups=case84Family := by native_decide

theorem packing_reduction_to_116 (p : NormalizedPacking) :
    ∃ t∈allTransforms, ∃ r∈afterCase84,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_117 p
  have hne : r.originalId≠84 := by
    intro he
    exact case84_impossible (t.pullPacking p) (hf.trans (case84_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩

#print axioms packing_reduction_to_116
end S12
