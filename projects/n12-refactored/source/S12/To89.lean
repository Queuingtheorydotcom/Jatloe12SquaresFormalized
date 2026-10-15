import S12.To92
import S12.SharedCase1085
import S12.SharedCase1086
import S12.SharedCase1087
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def afterShared1085_1087 : List CoverRow := afterCase1075.filter
  (fun r => decide (r.originalId≠1085 ∧ r.originalId≠1086 ∧ r.originalId≠1087))
theorem afterShared1085_1087_count : afterShared1085_1087.length=89 := by native_decide
theorem shared1085_row_identity : ∀ r∈afterCase1075,
    r.originalId=1085 → r.groups=case1085Family := by native_decide
theorem shared1086_row_identity : ∀ r∈afterCase1075,
    r.originalId=1086 → r.groups=case1086Family := by native_decide
theorem shared1087_row_identity : ∀ r∈afterCase1075,
    r.originalId=1087 → r.groups=case1087Family := by native_decide

theorem packing_reduction_to_89 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterShared1085_1087,
      codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_92 p
  have h85 : r.originalId≠1085 := by
    intro he
    exact case1085_shared_impossible (t.pullPacking p)
      (hf.trans (shared1085_row_identity r hr he))
  have h86 : r.originalId≠1086 := by
    intro he
    exact case1086_shared_impossible (t.pullPacking p)
      (hf.trans (shared1086_row_identity r hr he))
  have h87 : r.originalId≠1087 := by
    intro he
    exact case1087_shared_impossible (t.pullPacking p)
      (hf.trans (shared1087_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h85,h86,h87⟩⟩,hf⟩

#print axioms packing_reduction_to_89
end S12
