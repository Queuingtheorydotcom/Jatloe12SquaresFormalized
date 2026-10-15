import Compact.Completion.FiniteCases.C972Domains

/-! Original C972 physical owners in ascending mask order. Marker 15
is genuinely absent, while marker 11 belongs to actual owner 8. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
set_option Elab.async false
noncomputable section

abbrev family := C972Domains.family
def masks : Fin 12 → Nat := ![1,2,12,48,192,256,512,1024,2048,4096,8192,16384]
def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  CommonCases.OriginalOwners.owner p (masks i)
def actual (p : NormalizedPacking) (i : Fin 12) : Finset Nat :=
  CommonCases.OriginalOwners.auxiliaries p (masks i)
theorem member (i : Fin 12) : masks i∈family := by
  have all : ∀ j : Fin 12,masks j∈family := by decide +kernel
  exact all i
theorem injective : Function.Injective masks := by decide +kernel
theorem side (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side :=
  CommonCases.OriginalOwners.side p (masks i)
theorem same (p : NormalizedPacking) (i j : Fin 12) : (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm
theorem box (p : NormalizedPacking) (i : Fin 12) : InsideContainer (owners p i) :=
  CommonCases.OriginalOwners.box p (masks i)
theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) :=
  CommonCases.OriginalOwners.apart family p hf (masks i) (masks j)
    (member i) (member j) (fun equal => different (injective equal))
theorem foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) (x y : ℝ) (own : (owners p j).Inside x y) :
    ¬(owners p i).Inside x y := fun other => apart p hf i j different x y ⟨other,own⟩
theorem foreign_aux (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) (k : Nat) (own : k∈actual p j) :
    k∉actual p i :=
  fun other => Finset.disjoint_left.mp
    (CommonCases.OriginalOwners.auxiliary_disjoint family p hf (masks i) (masks j)
      (member i) (member j) (fun equal => different (injective equal))) other own
theorem missing_top (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) : ¬(owners p i).Inside 2 (1543/500) := by
  have absent : ∀ j : Fin 12,(15 : Marker)∉maskSupport (masks j) := by decide +kernel
  simpa [marker] using CommonCases.OriginalOwners.missing_marker family p hf
    (masks i) (member i) 15 (absent i)
theorem seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport (masks i))) :
    (owners p i).Inside P.1 P.2 :=
  CommonCases.OriginalOwners.seed family p hf (masks i) (member i) P checked
theorem aux (p : NormalizedPacking) (i : Fin 12) (j : Nat) (bound : j<20) :
    (owners p i).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 ↔ j∈actual p i :=
  CommonCases.OriginalOwners.auxiliary_exact p (masks i) j bound
theorem domain (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (d : CertifiedDomain family) (i : Fin 12) (equal : d.mask=masks i) :
    actual p i∈d.allowed := by
  have h := CommonCases.OriginalOwners.domain family d p hf (by rw [equal]; exact member i)
  change CommonCases.OriginalOwners.auxiliaries p (masks i)∈d.allowed
  simpa only [equal] using h

theorem singleton_horizontal (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (x : ℝ) (low : 28/25≤x) (high : x≤87/50) : (owners p 0).Inside x 1 := by
  apply CommonCases.OriginalOwners.horizontal_segment _ (28/25) (87/50) 1 x
  · convert seed p hf 0 (28/25,1) (by decide +kernel) using 1 <;> norm_num
  · convert seed p hf 0 (87/50,1) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · exact low
  · exact high
theorem singleton_vertical (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : 28/25≤y) (high : y≤87/50) : (owners p 1).Inside 1 y := by
  apply CommonCases.OriginalOwners.vertical_segment _ 1 (28/25) (87/50) y
  · convert seed p hf 1 (1,28/25) (by decide +kernel) using 1 <;> norm_num
  · convert seed p hf 1 (1,87/50) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · exact low
  · exact high

end
end N12Compact.FiniteCases.C972
