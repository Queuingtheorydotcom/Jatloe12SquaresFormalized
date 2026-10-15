import Compact.Completion.OtherCases.C974.Domains
import Compact.Completion.CommonCases.SingletonMissing

/-! Actual ascending-mask C974 owners and their unaltered physical square
geometry. In particular marker11 is omitted; no owner is invented for it. -/
namespace N12Compact.Completion.OtherCases.C974.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

abbrev family := Domains.family
def masks : Fin 12 → Nat := ![1,2,12,48,192,256,512,1024,4096,8192,16384,32768]
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
theorem cap (p : NormalizedPacking) (i : Fin 12) : (owners p i).side≤1001/1000 := by
  change (p.square (ownerIndex p (masks i))).side≤1001/1000
  rw [p.congruent]; exact p.side_le
theorem same (p : NormalizedPacking) (i j : Fin 12) : (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm
theorem box (p : NormalizedPacking) (i : Fin 12) : InsideContainer (owners p i) :=
  CommonCases.OriginalOwners.box p (masks i)
theorem markers (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) : ExactMarkers (owners p i) (maskSupport (masks i)) := by
  have hc := CommonCases.OriginalOwners.code family p hf (masks i) (member i)
  simpa only [hc] using coded_exact p (ownerIndex p (masks i))
theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) :=
  CommonCases.OriginalOwners.apart family p hf (masks i) (masks j)
    (member i) (member j) (fun equal => different (injective equal))
theorem foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) (x y : ℝ) (own : (owners p j).Inside x y) :
    ¬(owners p i).Inside x y := fun other => apart p hf i j different x y ⟨other,own⟩
theorem missing_northwest (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) : ¬(owners p i).Inside (33/20) (47/20) := by
  have absent : ∀ j : Fin 12,(11 : Marker)∉maskSupport (masks j) := by decide +kernel
  simpa [marker] using CommonCases.OriginalOwners.missing_marker family p hf
    (masks i) (member i) 11 (absent i)
theorem seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport (masks i))) :
    (owners p i).Inside P.1 P.2 :=
  CommonCases.OriginalOwners.seed family p hf (masks i) (member i) P checked
theorem aux (p : NormalizedPacking) (i : Fin 12) (j : Nat) (bound : j<20) :
    (owners p i).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 ↔ j∈actual p i :=
  CommonCases.OriginalOwners.auxiliary_exact p (masks i) j bound
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
theorem missing_zero (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 0).Inside 1 1) :
    (owners p 0).Inside (91/50) 1 ∧ (owners p 0).Inside (49/25) (19/25) := by
  apply CommonCases.SingletonMissing.zero_missing_points _ (side p 0) (cap p 0) (box p 0) _ missing
  convert markers p hf 0 using 1 <;> decide +kernel
theorem missing_one (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 1).Inside 1 1) :
    (owners p 1).Inside 1 (91/50) ∧ (owners p 1).Inside (19/25) (49/25) := by
  apply CommonCases.SingletonMissing.one_missing_points _ (side p 1) (cap p 1) (box p 1) _ missing
  convert markers p hf 1 using 1 <;> decide +kernel

end
end N12Compact.Completion.OtherCases.C974.OriginalData
