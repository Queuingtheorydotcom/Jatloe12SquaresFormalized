import S12.To101
import S12.Case992
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def afterCase992 : List CoverRow := afterCase995.filter (fun r => decide (r.originalId≠992))
theorem afterCase992_count : afterCase992.length=100 := by native_decide
theorem case992_row_identity : ∀ r∈afterCase995,r.originalId=992 → r.groups=case992Family := by native_decide

theorem packing_reduction_to_100 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterCase992,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_101 p
  have hn : r.originalId≠992 := by
    intro he
    exact case992_impossible (t.pullPacking p) (hf.trans (case992_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hf⟩
#print axioms packing_reduction_to_100
end S12
