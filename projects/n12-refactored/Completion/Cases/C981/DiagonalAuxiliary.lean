import Completion.Cases.C981.CornerReduction
import Completion.Cases.C981.Ownership

namespace S12Completion.C981
open S12 S12Pilot

/-- Transposition swaps the original F and G tables, preserving their actual
sorted indexing rather than simply adding or subtracting ten. -/
def auxiliaryTranspose : Fin 20 → Fin 20 :=
  ![12,15,10,18,13,16,11,19,14,17,2,6,0,4,8,1,5,9,3,7]

theorem auxiliaryTranspose_point (i : Fin 20) :
    (auxPoints 2)[(auxiliaryTranspose i).val]! =
      (((auxPoints 2)[i.val]!).2, ((auxPoints 2)[i.val]!).1) := by
  fin_cases i <;> rfl

theorem auxiliaryTranspose_pattern (i : Fin 20) :
    (auxiliaryTranspose i).val ∈ ({4,6,15} : Finset Nat) ↔
      i.val ∈ ({1,11,13} : Finset Nat) := by
  fin_cases i <;> decide

theorem auxiliary_transpose_exact (q : OpenSquare)
    (h : AuxExact q 2 {4,6,15}) : AuxExact (pullSwap q) 2 {1,11,13} := by
  intro k hk
  have hk20 : k < 20 := by simpa using List.mem_range.mp hk
  let i : Fin 20 := ⟨k, hk20⟩
  have hp := h (auxiliaryTranspose i).val
    (List.mem_range.mpr (by change (auxiliaryTranspose i).val < 20; exact (auxiliaryTranspose i).isLt))
  rw [auxiliaryTranspose_point] at hp
  rw [inside_pullSwap]
  exact hp.trans (auxiliaryTranspose_pattern i)

theorem nat_combined_subset20 (p : NormalizedPacking) (i : Fin 12) :
    natCombinedOwners p i ⊆ Finset.range 20 := by
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · have h := Finset.mem_range.mp (nat_aux_subset p 0 i hj)
    exact Finset.mem_range.mpr (by omega)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have h := Finset.mem_range.mp (nat_aux_subset p 1 i hk)
    exact Finset.mem_range.mpr (by omega)

theorem nat_combined_eq_of_exact (p : NormalizedPacking) (i : Fin 12)
    (owned : Finset Nat) (hsub : owned ⊆ Finset.range 20)
    (h : AuxExact (p.square i) 2 owned) : natCombinedOwners p i = owned := by
  apply Finset.ext
  intro j
  by_cases hj : j < 20
  · have hm : j ∈ List.range (auxPoints 2).length :=
      List.mem_range.mpr (by simpa using hj)
    exact (nat_combined_exact p i j hm).symm.trans (h j hm)
  · have hn : j ∉ Finset.range 20 := by simpa using hj
    exact iff_of_false (fun hm => hn (nat_combined_subset20 p i hm))
      (fun hm => hn (hsub hm))

def ownerTranspose : Fin 12 → Fin 12 := ![1,0,4,3,2,7,6,5,9,8,11,10]

theorem ownerMasks_transpose (i : Fin 12) :
    diagonal.maskAction (ownerMasks i) = ownerMasks (ownerTranspose i) := by
  fin_cases i <;> decide

theorem ownerMasks_candidate : ∀ i, ownerMasks i ∈ candidateMasks := by decide

theorem diagonal_ownerIndex (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (owner : Fin 12) :
    ownerIndex (diagonal.pullPacking p) (ownerMasks owner) =
      ownerIndex p (ownerMasks (ownerTranspose owner)) := by
  let i := ownerIndex p (ownerMasks (ownerTranspose owner))
  have hc : markerCode p i = ownerMasks (ownerTranspose owner) :=
    ownerIndex_spec p _ (by rw [hf]; exact ownerMasks_mem _)
  have he : ExactMarkers (p.square i) (maskSupport (diagonal.maskAction (ownerMasks owner))) := by
    simpa only [ownerMasks_transpose, hc] using coded_exact p i
  have ht := exact_markers_pull diagonal diagonal_mem (p.square i) (ownerMasks owner)
    (ownerMasks_candidate owner) he
  have hs : maskSupport (markerCode (diagonal.pullPacking p) i) = maskSupport (ownerMasks owner) := by
    apply Finset.ext
    intro j
    exact (coded_exact (diagonal.pullPacking p) i j).symm.trans (ht j)
  have hn := candidate_support_injective _ _
    (markerCode_spec (diagonal.pullPacking p) i).1 (ownerMasks_candidate owner) hs
  apply markerCode_injective (diagonal.pullPacking p)
  exact (ownerIndex_spec (diagonal.pullPacking p) (ownerMasks owner)
    (by rw [diagonal_packing_family p hf]; exact ownerMasks_mem owner)).trans hn.symm

theorem diagonal_auxiliary_mem (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (owner : Fin 12) (j : Fin 20) :
    j.val ∈ natCombinedOwners (diagonal.pullPacking p)
      (ownerIndex (diagonal.pullPacking p) (ownerMasks owner)) ↔
    (auxiliaryTranspose j).val ∈ natCombinedOwners p
      (ownerIndex p (ownerMasks (ownerTranspose owner))) := by
  rw [diagonal_ownerIndex p hf owner]
  apply (nat_combined_exact (diagonal.pullPacking p) _ j.val
    (List.mem_range.mpr (by change j.val < 20; exact j.isLt))).symm.trans
  change (pullSwap (p.square (ownerIndex p (ownerMasks (ownerTranspose owner))))).Inside
    ((auxPoints 2)[j.val]!).1 ((auxPoints 2)[j.val]!).2 ↔ _
  rw [inside_pullSwap]
  have h := nat_combined_exact p (ownerIndex p (ownerMasks (ownerTranspose owner)))
    (auxiliaryTranspose j).val
    (List.mem_range.mpr (by change (auxiliaryTranspose j).val < 20; exact (auxiliaryTranspose j).isLt))
  rw [auxiliaryTranspose_point] at h
  exact h

theorem diagonal_auxiliary_eq (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (owner : Fin 12) (a b : Finset Nat)
    (hb : b ⊆ Finset.range 20)
    (hab : ∀ j : Fin 20, (auxiliaryTranspose j).val ∈ a ↔ j.val ∈ b)
    (ho : natCombinedOwners p (ownerIndex p (ownerMasks (ownerTranspose owner))) = a) :
    natCombinedOwners (diagonal.pullPacking p)
      (ownerIndex (diagonal.pullPacking p) (ownerMasks owner)) = b := by
  apply Finset.ext
  intro j
  by_cases hj : j < 20
  · have h := diagonal_auxiliary_mem p hf owner ⟨j, hj⟩
    rw [ho] at h
    exact h.trans (hab ⟨j, hj⟩)
  · have hn : j ∉ Finset.range 20 := by simpa using hj
    exact iff_of_false (fun hm => hn (nat_combined_subset20 _ _ hm)) (fun hm => hn (hb hm))

theorem diagonal_auxiliary_subset (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (owner : Fin 12) (a b : Finset Nat)
    (hb : b ⊆ Finset.range 20)
    (hab : ∀ j : Fin 20, (auxiliaryTranspose j).val ∈ a ↔ j.val ∈ b)
    (ho : a ⊆ natCombinedOwners p (ownerIndex p (ownerMasks (ownerTranspose owner)))) :
    b ⊆ natCombinedOwners (diagonal.pullPacking p)
      (ownerIndex (diagonal.pullPacking p) (ownerMasks owner)) := by
  intro j hj
  have hj20 := Finset.mem_range.mp (hb hj)
  exact (diagonal_auxiliary_mem p hf owner ⟨j, hj20⟩).mpr (ho ((hab ⟨j, hj20⟩).mpr hj))

theorem diagonal_left_owner (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ownerIndex (diagonal.pullPacking p) 4096 = ownerIndex p 8192 :=
  diagonal_ownerIndex p hf 8

theorem diagonal_pattern (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (ho : natCombinedOwners p (ownerIndex p 8192) = {4,6,15}) :
    natCombinedOwners (diagonal.pullPacking p)
      (ownerIndex (diagonal.pullPacking p) 4096) = {1,11,13} :=
  diagonal_auxiliary_eq p hf 8 {4,6,15} {1,11,13}
    (by decide) auxiliaryTranspose_pattern ho

end S12Completion.C981
