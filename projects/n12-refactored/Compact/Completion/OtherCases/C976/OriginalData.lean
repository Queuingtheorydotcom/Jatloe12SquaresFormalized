import Compact.Completion.CommonCases.OriginalOwners
import S12.Case976Domains

/-! The literal C976 family and its actual ascending-mask owners. The
existing direct local certificates are reused; no old interval-module
forest, reported vector catalogue or foreign family theorem is imported. -/
namespace N12Compact.Completion.OtherCases.C976.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

abbrev family := case976Family
def masks : Fin 12 → Nat := ![1,2,12,48,192,256,512,1024,6144,8192,16384,32768]
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

end
end N12Compact.Completion.OtherCases.C976.OriginalData
