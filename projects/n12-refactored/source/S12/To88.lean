import S12.To93
import S12.SharedCase1075
import S12.SharedCase1077
import S12.SharedCase1085
import S12.SharedCase1086
import S12.SharedCase1087
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterShared1075_1087 : List CoverRow := afterCase982.filter (fun r => decide (r.originalId≠1075 ∧ r.originalId≠1077 ∧ r.originalId≠1085 ∧ r.originalId≠1086 ∧ r.originalId≠1087))
theorem afterShared1075_1087_count : afterShared1075_1087.length=88 := by native_decide
theorem sharedFinal1075_row_identity : ∀ r∈afterCase982,r.originalId=1075 → r.groups=case1075Family := by native_decide
theorem sharedFinal1077_row_identity : ∀ r∈afterCase982,r.originalId=1077 → r.groups=case1077Family := by native_decide
theorem sharedFinal1085_row_identity : ∀ r∈afterCase982,r.originalId=1085 → r.groups=case1085Family := by native_decide
theorem sharedFinal1086_row_identity : ∀ r∈afterCase982,r.originalId=1086 → r.groups=case1086Family := by native_decide
theorem sharedFinal1087_row_identity : ∀ r∈afterCase982,r.originalId=1087 → r.groups=case1087Family := by native_decide
theorem packing_reduction_to_88 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterShared1075_1087,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_93 p
  have h1075 : r.originalId≠1075 := by
    intro he
    exact case1075_shared_impossible (t.pullPacking p) (hf.trans (sharedFinal1075_row_identity r hr he))
  have h1077 : r.originalId≠1077 := by
    intro he
    exact case1077_shared_impossible (t.pullPacking p) (hf.trans (sharedFinal1077_row_identity r hr he))
  have h1085 : r.originalId≠1085 := by
    intro he
    exact case1085_shared_impossible (t.pullPacking p) (hf.trans (sharedFinal1085_row_identity r hr he))
  have h1086 : r.originalId≠1086 := by
    intro he
    exact case1086_shared_impossible (t.pullPacking p) (hf.trans (sharedFinal1086_row_identity r hr he))
  have h1087 : r.originalId≠1087 := by
    intro he
    exact case1087_shared_impossible (t.pullPacking p) (hf.trans (sharedFinal1087_row_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h1075,h1077,h1085,h1086,h1087⟩⟩,hf⟩
#print axioms packing_reduction_to_88
end S12
