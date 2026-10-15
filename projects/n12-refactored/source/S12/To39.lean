import S12.To45
import S12.SharedCase698
import S12.SharedCase702
import S12.SharedCase890
import S12.SharedCase1069
import S12.SharedCase1070
import S12.SharedCase1072
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterRecoverySixExclusions : List CoverRow := afterFinalWallGroup.filter (fun r => decide (r.originalId≠698 ∧ r.originalId≠702 ∧ r.originalId≠890 ∧ r.originalId≠1069 ∧ r.originalId≠1070 ∧ r.originalId≠1072))
theorem afterRecoverySixExclusions_count : afterRecoverySixExclusions.length=39 := by native_decide
theorem reduction39_case698_identity : ∀ r∈afterFinalWallGroup,r.originalId=698 → r.groups=case698Family := by native_decide
theorem reduction39_case702_identity : ∀ r∈afterFinalWallGroup,r.originalId=702 → r.groups=case702Family := by native_decide
theorem reduction39_case890_identity : ∀ r∈afterFinalWallGroup,r.originalId=890 → r.groups=case890Family := by native_decide
theorem reduction39_case1069_identity : ∀ r∈afterFinalWallGroup,r.originalId=1069 → r.groups=case1069Family := by native_decide
theorem reduction39_case1070_identity : ∀ r∈afterFinalWallGroup,r.originalId=1070 → r.groups=case1070Family := by native_decide
theorem reduction39_case1072_identity : ∀ r∈afterFinalWallGroup,r.originalId=1072 → r.groups=case1072Family := by native_decide
theorem packing_reduction_to_39 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterRecoverySixExclusions,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_45 p
  have h698 : r.originalId≠698 := by
    intro he
    exact case698_shared_impossible (t.pullPacking p) (hf.trans (reduction39_case698_identity r hr he))
  have h702 : r.originalId≠702 := by
    intro he
    exact case702_shared_impossible (t.pullPacking p) (hf.trans (reduction39_case702_identity r hr he))
  have h890 : r.originalId≠890 := by
    intro he
    exact case890_shared_impossible (t.pullPacking p) (hf.trans (reduction39_case890_identity r hr he))
  have h1069 : r.originalId≠1069 := by
    intro he
    exact case1069_shared_impossible (t.pullPacking p) (hf.trans (reduction39_case1069_identity r hr he))
  have h1070 : r.originalId≠1070 := by
    intro he
    exact case1070_shared_impossible (t.pullPacking p) (hf.trans (reduction39_case1070_identity r hr he))
  have h1072 : r.originalId≠1072 := by
    intro he
    exact case1072_shared_impossible (t.pullPacking p) (hf.trans (reduction39_case1072_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h698,h702,h890,h1069,h1070,h1072⟩⟩,hf⟩
#print axioms packing_reduction_to_39
end S12
