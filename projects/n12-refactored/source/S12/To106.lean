import S12.To110
import S12.Case680
import S12.Case711
import S12.Case862
import S12.Case864
namespace S12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedTopPairIds : List Nat := [680,711,862,864]
def sharedTopPairFamilies : List (Finset Nat) := [case680Family,case711Family,case862Family,case864Family]
def afterSharedTopPair : List CoverRow := afterSharedPair.filter (fun r => decide (r.originalId∉sharedTopPairIds))
theorem afterSharedTopPair_count : afterSharedTopPair.length=106 := by native_decide
theorem sharedTopPair_row_identity : ∀ r∈afterSharedPair,r.originalId∈sharedTopPairIds → r.groups∈sharedTopPairFamilies := by native_decide

theorem sharedTopPair_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p∈sharedTopPairFamilies) : False := by
  simp only [sharedTopPairFamilies,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with h | h | h | h
  · exact case680_impossible p h
  · exact case711_impossible p h
  · exact case862_impossible p h
  · exact case864_impossible p h

theorem packing_reduction_to_106 (p : NormalizedPacking) :
    ∃ t∈allTransforms, ∃ r∈afterSharedTopPair,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_110 p
  have hne : r.originalId∉sharedTopPairIds := by
    intro he
    exact sharedTopPair_impossible (t.pullPacking p) (by rw [hf]; exact sharedTopPair_row_identity r hr he)
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩
#print axioms packing_reduction_to_106
end S12
