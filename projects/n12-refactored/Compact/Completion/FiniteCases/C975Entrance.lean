import Compact.Completion.FiniteCases.C975FiniteCuts

/-! Original C975 compulsory points. Every label belongs to its actual
owner under the full F3/G3 budget. In particular the merged top retains
F3, F5 and F7 until a genuine geometric ending removes an alternative. -/
namespace N12Compact.FiniteCases.C975Entrance
open S12 S12Pilot C975Domains
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

structure Compulsory (p : NormalizedPacking) : Prop where
  southwest : 2∈auxiliaries p 1 ∧ 12∈auxiliaries p 1
  leftSingleton : 0∈auxiliaries p 2 ∧ 10∈auxiliaries p 2
  bottom : 6∈auxiliaries p 8192 ∧ 15∈auxiliaries p 8192
  southwestCentral : 4∈auxiliaries p 256 ∧ 13∈auxiliaries p 256
  leftWall : 1∈auxiliaries p 4096 ∧ 11∈auxiliaries p 4096
  southeast : 8∈auxiliaries p 512 ∧ (16∈auxiliaries p 512 ∨ 18∈auxiliaries p 512)
  rightWall : 9∈auxiliaries p 16384 ∧ 19∈auxiliaries p 16384
  top : 14∈auxiliaries p 34816
  northeast : (5∈auxiliaries p 1024 ∨ 7∈auxiliaries p 1024) ∧
    (16∈auxiliaries p 1024 ∨ 17∈auxiliaries p 1024)

private theorem g_combined (p : NormalizedPacking) (mask j : Nat) :
    j∈natAuxOwners p 1 (ownerIndex p mask) ↔ j+10∈auxiliaries p mask := by
  unfold auxiliaries natCombinedOwners
  simpa only [Nat.add_sub_cancel] using
    (mem_combined_high _ _ (nat_aux_subset p 0 _) (j+10) (by omega)).symm

theorem compulsory (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Compulsory p := by
  have foreign (m n index : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
      (owned : index∈auxiliaries p n) : index∉auxiliaries p m :=
    fun h => Finset.disjoint_left.mp (auxiliary_disjoint _ p hf m n hm hn different) h owned
  have sw := C975FiniteCuts.southwest _
    (domain _ C975Domains.southwest p hf (by decide +kernel))
  have singleton := C975FiniteCuts.leftSingleton _
    (domain _ C975Domains.leftSingleton p hf (by decide +kernel))
  have bottom := C975FiniteCuts.bottom _
    (domain _ C975Domains.bottom p hf (by decide +kernel))
    (foreign 8192 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) sw.1)
  have southwest := C975FiniteCuts.southwestCentral _
    (domain _ C975Domains.southwestCentral p hf (by decide +kernel))
    (foreign 256 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) singleton.1)
    (foreign 256 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) sw.1)
    (foreign 256 2 10 (by decide +kernel) (by decide +kernel) (by decide +kernel) singleton.2)
    (foreign 256 1 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) sw.2)
  have left := C975FiniteCuts.leftWall _
    (domain _ C975Domains.left p hf (by decide +kernel))
    (foreign 4096 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) singleton.1)
    (foreign 4096 256 13 (by decide +kernel) (by decide +kernel) (by decide +kernel) southwest.2)
  have southeast := C975FiniteCuts.southeast _
    (domain _ C975Domains.southeast p hf (by decide +kernel))
    (foreign 512 256 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) southwest.1)
    (foreign 512 8192 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) bottom.1)
    (foreign 512 8192 15 (by decide +kernel) (by decide +kernel) (by decide +kernel) bottom.2)
  have right := C975FiniteCuts.rightWall _
    (domain _ C975Domains.right p hf (by decide +kernel))
    (foreign 16384 512 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) southeast.1)
  have top : 14∈auxiliaries p 34816 := by
    apply (g_combined p 34816 4).mp
    apply C975FiniteCuts.top _ (C975Domains.topG.sound p _ hf
      (code _ p hf 34816 (by decide +kernel)))
    · intro own
      exact foreign 34816 4096 11 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) left.2 ((g_combined p 34816 1).mp own)
    · intro own
      exact foreign 34816 256 13 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) southwest.2 ((g_combined p 34816 3).mp own)
  have northeast := C975FiniteCuts.northeast _
    (domain _ C975Domains.northeast p hf (by decide +kernel))
    (foreign 1024 16384 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) right.1)
    (foreign 1024 256 13 (by decide +kernel) (by decide +kernel) (by decide +kernel) southwest.2)
    (foreign 1024 34816 14 (by decide +kernel) (by decide +kernel) (by decide +kernel) top)
    (foreign 1024 16384 19 (by decide +kernel) (by decide +kernel) (by decide +kernel) right.2)
  exact ⟨sw,singleton,bottom,southwest,left,southeast,right,top,northeast⟩

/-- The seven other real F owners leave precisely these three possibilities.
The true top owner may own two of them; no exact-one conclusion is used. -/
theorem top_alternatives (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    3∈auxiliaries p 34816 ∨ 5∈auxiliaries p 34816 ∨ 7∈auxiliaries p 34816 := by
  classical
  have points := compulsory p hf
  have foreign (n index : Nat) (hn : n∈family) (different : 34816≠n)
      (owned : index∈auxiliaries p n) : index∉auxiliaries p 34816 :=
    fun h => Finset.disjoint_left.mp (auxiliary_disjoint _ p hf 34816 n
      (by decide +kernel) hn different) h owned
  have budget := nat_aux_budget p 0 (ownerIndex p 34816)
  rw [code _ p hf 34816 (by decide +kernel)] at budget
  have non : 34816∉auxExempt 0 := by decide +kernel
  simp only [non,if_false] at budget
  have positive : 0<(natAuxOwners p 0 (ownerIndex p 34816)).card := by omega
  obtain ⟨j,hj⟩ := Finset.card_pos.mp positive
  have bound := Finset.mem_range.mp (nat_aux_subset p 0 _ hj)
  have own : j∈auxiliaries p 34816 := (mem_combined_low _ _ j bound).mpr hj
  interval_cases j
  · exact False.elim (foreign 2 0 (by decide +kernel) (by decide +kernel) points.leftSingleton.1 own)
  · exact False.elim (foreign 4096 1 (by decide +kernel) (by decide +kernel) points.leftWall.1 own)
  · exact False.elim (foreign 1 2 (by decide +kernel) (by decide +kernel) points.southwest.1 own)
  · exact Or.inl own
  · exact False.elim (foreign 256 4 (by decide +kernel) (by decide +kernel) points.southwestCentral.1 own)
  · exact Or.inr (Or.inl own)
  · exact False.elim (foreign 8192 6 (by decide +kernel) (by decide +kernel) points.bottom.1 own)
  · exact Or.inr (Or.inr own)
  · exact False.elim (foreign 512 8 (by decide +kernel) (by decide +kernel) points.southeast.1 own)
  · exact False.elim (foreign 16384 9 (by decide +kernel) (by decide +kernel) points.rightWall.1 own)

#print axioms compulsory
#print axioms top_alternatives
end
end N12Compact.FiniteCases.C975Entrance
