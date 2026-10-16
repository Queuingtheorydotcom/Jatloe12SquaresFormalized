import S12.To113
import S12.Case690
import S12.Case691
import S12.Case694
namespace S12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedPairIds : List Nat := [690,691,694]
def sharedPairFamilies : List (Finset Nat) := [case690Family,case691Family,case694Family]
def afterSharedPair : List CoverRow := afterCase678.filter (fun r => decide (r.originalId∉sharedPairIds))
theorem afterSharedPair_count : afterSharedPair.length=110 := by native_decide
theorem sharedPair_row_identity : ∀ r∈afterCase678,r.originalId∈sharedPairIds → r.groups∈sharedPairFamilies := by native_decide

theorem sharedPair_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p∈sharedPairFamilies) : False := by
  simp only [sharedPairFamilies,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with h | h | h
  · exact case690_impossible p h
  · exact case691_impossible p h
  · exact case694_impossible p h

theorem packing_reduction_to_110 (p : NormalizedPacking) :
    ∃ t∈allTransforms, ∃ r∈afterSharedPair,codedMarkerFamily (t.pullPacking p)=r.groups := by
  obtain ⟨t,ht,r,hr,hf⟩ := packing_reduction_to_113 p
  have hne : r.originalId∉sharedPairIds := by
    intro he
    exact sharedPair_impossible (t.pullPacking p) (by rw [hf]; exact sharedPair_row_identity r hr he)
  exact ⟨t,ht,r,List.mem_filter.mpr ⟨hr,decide_eq_true hne⟩,hf⟩
#print axioms packing_reduction_to_110
end S12
