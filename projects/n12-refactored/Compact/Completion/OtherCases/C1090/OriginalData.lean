import Compact.Completion.OtherCases.C1090.EarlyGeometry
import Compact.Completion.CommonCases.OriginalOwners

/-! Literal original-owner entrance boundary for the new C1090 proof.
The actual packing proves all original markers, true singleton seeds,
paired-corner points, walls, common side and disjointness. The remaining
finite auxiliary consequences are collected separately. In particular
marker 1 is strict in the one merged Q8 and omitted only by other owners.
This module does not assert that the finite entrance has been supplied.
The historical auxiliary catalogue and new reported replay counts are not
used as unexplained proof receipts. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1090.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

def family : Finset Nat := {1,12,48,192,256,512,1024,2048,4098,8192,16384,32768}

def masks : Fin 12 → Nat := ![1,12,48,192,256,512,1024,2048,4098,8192,16384,32768]

def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  CommonCases.OriginalOwners.owner p (masks i)

private theorem mask_member (i : Fin 12) : masks i∈family := by
  have checked : ∀ j : Fin 12,masks j∈family := by decide +kernel
  exact checked i

private theorem masks_injective : Function.Injective masks := by decide +kernel

/-- Only genuine remaining finite conclusions occur here. No wall reach,
crosspoint, center, angle, singleton inner corner or terminal support is an
entrance field. The covering alternatives retain additional ownership. -/
structure AuxiliaryEntrance (q : Fin 12 → OpenSquare) : Prop where
  southwestF4 : (q 4).Inside 2 (87/50)
  southwestG3 : (q 4).Inside (87/50) 2
  southeastF8 : (q 5).Inside 3 (87/50)
  bottomF6 : (q 9).Inside (12/5) 1
  bottomG5 : (q 9).Inside (113/50) 1
  rightF9 : (q 10).Inside 3 (113/50)
  rightG9 : (q 10).Inside 3 (12/5)
  southeastGCover : (q 5).Inside (113/50) 1 ∨
    (q 5).Inside (113/50) 2 ∨ (q 5).Inside 3 (8/5)
  northeastFCover : (q 6).Inside 2 (113/50) ∨
    (q 6).Inside (12/5) 3 ∨ (q 6).Inside 3 (113/50)
  northeastGCover : (q 6).Inside (113/50) 2 ∨
    (q 6).Inside (113/50) 3 ∨ (q 6).Inside 3 (12/5)
  northwestFCover : (q 7).Inside 1 (113/50) ∨
    (q 7).Inside (8/5) 3 ∨ (q 7).Inside 2 (113/50)
  northwestGCover : (q 7).Inside 1 (12/5) ∨
    (q 7).Inside (87/50) 2 ∨ (q 7).Inside (87/50) 3
  topComponent : (q 11).Inside (113/50) 3 ∨
    ((q 11).Inside (8/5) 3 ∧ (q 11).Inside (87/50) 3)

theorem seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport (masks i))) :
    (owners p i).Inside P.1 P.2 :=
  CommonCases.OriginalOwners.seed family p hf (masks i) (mask_member i) P checked

theorem marker1_owned (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside (457/500) 1 := by
  have result := seed p hf 8 (457/500,1) (by decide +kernel)
  norm_num at result
  exact result

theorem marker1_omitted_by_singleton (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : ¬(owners p 0).Inside (457/500) 1 := by
  have result := CommonCases.OriginalOwners.missing_marker family p hf (masks 0)
    (mask_member 0) 1 (by decide +kernel)
  simpa [owners,marker] using result

/-- The complete geometric input is produced from the original packing
and only the separately identified finite auxiliary entrance. The Q0 seeds
are the true horizontal and off-row seeds in S12.Seeds. -/
theorem early_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (h : AuxiliaryEntrance (owners p)) : Early.Input (owners p) := by
  have side (i : Fin 12) : 1<(owners p i).side :=
    CommonCases.OriginalOwners.side p (masks i)
  have same (i j : Fin 12) : (owners p i).side=(owners p j).side := by
    change (p.square (ownerIndex p (masks i))).side=(p.square (ownerIndex p (masks j))).side
    exact (p.congruent _).trans (p.congruent _).symm
  have box (i : Fin 12) : InsideContainer (owners p i) :=
    CommonCases.OriginalOwners.box p (masks i)
  have apart (i j : Fin 12) (different : i≠j) :
      ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) :=
    CommonCases.OriginalOwners.apart family p hf (masks i) (masks j)
      (mask_member i) (mask_member j) (fun equal => different (masks_injective equal))
  exact {
    side := side
    same := same
    box := box
    apart := apart
    singletonNear := by
      have own := seed p hf 0 (28/25,1) (by decide +kernel)
      norm_num at own
      exact own
    singletonFar := by
      have own := seed p hf 0 (87/50,1) (by decide +kernel)
      norm_num at own
      exact own
    singletonSeed := by
      have own := seed p hf 0 (187/100,19/25) (by decide +kernel)
      norm_num at own
      exact own
    southeastCornerBottom := by
      have own := seed p hf 1 (3,457/500) (by decide +kernel)
      norm_num at own
      exact own
    southeastCornerRight := by
      have own := seed p hf 1 (1543/500,1) (by decide +kernel)
      norm_num at own
      exact own
    southeastCorner := by
      have own := seed p hf 1 (3,1) (by decide +kernel)
      norm_num at own
      exact own
    northeastCorner := by
      have own := seed p hf 2 (3,3) (by decide +kernel)
      norm_num at own
      exact own
    northwestCornerMarker := by
      have own := seed p hf 3 (1,1543/500) (by decide +kernel)
      norm_num at own
      exact own
    northwestCorner := by
      have own := seed p hf 3 (1,3) (by decide +kernel)
      norm_num at own
      exact own
    southwestMarker := by
      have own := seed p hf 4 (33/20,33/20) (by decide +kernel)
      norm_num at own
      exact own
    southwestF4 := h.southwestF4
    southwestG3 := h.southwestG3
    southeastMarker := by
      have own := seed p hf 5 (47/20,33/20) (by decide +kernel)
      norm_num at own
      exact own
    southeastF8 := h.southeastF8
    northeastMarker := by
      have own := seed p hf 6 (47/20,47/20) (by decide +kernel)
      norm_num at own
      exact own
    northwestMarker := by
      have own := seed p hf 7 (33/20,47/20) (by decide +kernel)
      norm_num at own
      exact own
    mergedMarker1 := marker1_owned p hf
    mergedMarker12 := by
      have own := seed p hf 8 (457/500,2) (by decide +kernel)
      norm_num at own
      exact own
    bottomMarker := by
      have own := seed p hf 9 (2,457/500) (by decide +kernel)
      norm_num at own
      exact own
    bottomF6 := h.bottomF6
    bottomG5 := h.bottomG5
    rightMarker := by
      have own := seed p hf 10 (1543/500,2) (by decide +kernel)
      norm_num at own
      exact own
    rightF9 := h.rightF9
    rightG9 := h.rightG9
    topMarker := by
      have own := seed p hf 11 (2,1543/500) (by decide +kernel)
      norm_num at own
      exact own
    southeastGCover := h.southeastGCover
    northeastFCover := h.northeastFCover
    northeastGCover := h.northeastGCover
    northwestFCover := h.northwestFCover
    northwestGCover := h.northwestGCover
    topComponent := h.topComponent }

end
#print axioms marker1_owned
#print axioms marker1_omitted_by_singleton
#print axioms early_input
end N12Compact.Completion.OtherCases.C1090.OriginalData
