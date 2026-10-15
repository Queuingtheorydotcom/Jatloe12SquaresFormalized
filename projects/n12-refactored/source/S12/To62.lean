import S12.To75
import S12.SharedCase669
import S12.SharedCase673
import S12.SharedCase674
import S12.SharedCase841
import S12.SharedCase842
import S12.SharedCase846
import S12.SharedCase847
import S12.SharedCase848
import S12.SharedCase849
import S12.SharedCase850
import S12.SharedCase851
import S12.SharedCase852
import S12.SharedCase853
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def afterUnion669Group : List CoverRow := afterCommon1084.filter (fun r => decide (r.originalId≠669 ∧ r.originalId≠673 ∧ r.originalId≠674 ∧ r.originalId≠841 ∧ r.originalId≠842 ∧ r.originalId≠846 ∧ r.originalId≠847 ∧ r.originalId≠848 ∧ r.originalId≠849 ∧ r.originalId≠850 ∧ r.originalId≠851 ∧ r.originalId≠852 ∧ r.originalId≠853))
theorem afterUnion669Group_count : afterUnion669Group.length=62 := by native_decide
theorem reduction62_case669_identity : ∀ r∈afterCommon1084,r.originalId=669 → r.groups=case669Family := by native_decide
theorem reduction62_case673_identity : ∀ r∈afterCommon1084,r.originalId=673 → r.groups=case673Family := by native_decide
theorem reduction62_case674_identity : ∀ r∈afterCommon1084,r.originalId=674 → r.groups=case674Family := by native_decide
theorem reduction62_case841_identity : ∀ r∈afterCommon1084,r.originalId=841 → r.groups=case841Family := by native_decide
theorem reduction62_case842_identity : ∀ r∈afterCommon1084,r.originalId=842 → r.groups=case842Family := by native_decide
theorem reduction62_case846_identity : ∀ r∈afterCommon1084,r.originalId=846 → r.groups=case846Family := by native_decide
theorem reduction62_case847_identity : ∀ r∈afterCommon1084,r.originalId=847 → r.groups=case847Family := by native_decide
theorem reduction62_case848_identity : ∀ r∈afterCommon1084,r.originalId=848 → r.groups=case848Family := by native_decide
theorem reduction62_case849_identity : ∀ r∈afterCommon1084,r.originalId=849 → r.groups=case849Family := by native_decide
theorem reduction62_case850_identity : ∀ r∈afterCommon1084,r.originalId=850 → r.groups=case850Family := by native_decide
theorem reduction62_case851_identity : ∀ r∈afterCommon1084,r.originalId=851 → r.groups=case851Family := by native_decide
theorem reduction62_case852_identity : ∀ r∈afterCommon1084,r.originalId=852 → r.groups=case852Family := by native_decide
theorem reduction62_case853_identity : ∀ r∈afterCommon1084,r.originalId=853 → r.groups=case853Family := by native_decide
theorem packing_reduction_to_62 (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈afterUnion669Group,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_75 p
  have h669 : r.originalId≠669 := by
    intro he
    exact case669_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case669_identity r hr he))
  have h673 : r.originalId≠673 := by
    intro he
    exact case673_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case673_identity r hr he))
  have h674 : r.originalId≠674 := by
    intro he
    exact case674_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case674_identity r hr he))
  have h841 : r.originalId≠841 := by
    intro he
    exact case841_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case841_identity r hr he))
  have h842 : r.originalId≠842 := by
    intro he
    exact case842_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case842_identity r hr he))
  have h846 : r.originalId≠846 := by
    intro he
    exact case846_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case846_identity r hr he))
  have h847 : r.originalId≠847 := by
    intro he
    exact case847_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case847_identity r hr he))
  have h848 : r.originalId≠848 := by
    intro he
    exact case848_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case848_identity r hr he))
  have h849 : r.originalId≠849 := by
    intro he
    exact case849_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case849_identity r hr he))
  have h850 : r.originalId≠850 := by
    intro he
    exact case850_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case850_identity r hr he))
  have h851 : r.originalId≠851 := by
    intro he
    exact case851_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case851_identity r hr he))
  have h852 : r.originalId≠852 := by
    intro he
    exact case852_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case852_identity r hr he))
  have h853 : r.originalId≠853 := by
    intro he
    exact case853_shared_impossible (t.pullPacking p) (hf.trans (reduction62_case853_identity r hr he))
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true ⟨h669,h673,h674,h841,h842,h846,h847,h848,h849,h850,h851,h852,h853⟩⟩,hf⟩
#print axioms packing_reduction_to_62
end S12
