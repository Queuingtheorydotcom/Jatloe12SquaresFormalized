import Compact.Completion.OtherCases.C1089.SingletonCorner

/-! The literal original C1089 owners. Q0 is exactly singleton1; marker1
is absent from every actual owner. The other three corners are paired.
Only actual seeds, walls, congruence and disjointness are collected here.
Source only: no compiler or certificate generation has been run. -/
namespace N12Compact.Completion.OtherCases.C1089.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

abbrev family := SingletonCorner.family
abbrev masks := SingletonCorner.masks
abbrev owners := SingletonCorner.owners

theorem mask_member (i : Fin 12) : masks i∈family := by
  have checked : ∀ j : Fin 12,masks j∈family := by decide +kernel
  exact checked i

theorem masks_injective : Function.Injective masks := by decide +kernel

theorem seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport (masks i))) :
    (owners p i).Inside P.1 P.2 :=
  CommonCases.OriginalOwners.seed family p hf (masks i) (mask_member i) P checked

structure Frame (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  same : ∀ i j,(q i).side=(q j).side
  box : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  absentMarker : ∀ i,¬(q i).Inside (457/500) 1
  singletonMarker : (q 0).Inside 1 (457/500)
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  singletonSeed : (q 0).Inside (187/100) (19/25)
  southeastCornerBottom : (q 1).Inside 3 (457/500)
  southeastCornerRight : (q 1).Inside (1543/500) 1
  southeastCorner : (q 1).Inside 3 1
  northeastCornerRight : (q 2).Inside (1543/500) 3
  northeastCornerTop : (q 2).Inside 3 (1543/500)
  northeastCorner : (q 2).Inside 3 3
  northwestCornerTop : (q 3).Inside 1 (1543/500)
  northwestCornerLeft : (q 3).Inside (457/500) 3
  northwestCorner : (q 3).Inside 1 3
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southeastMarker : (q 5).Inside (47/20) (33/20)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  leftMarker : (q 8).Inside (457/500) 2
  bottomMarker : (q 9).Inside 2 (457/500)
  rightMarker : (q 10).Inside (1543/500) 2
  topMarker : (q 11).Inside 2 (1543/500)

theorem frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Frame (owners p) := by
  have side (i : Fin 12) : 1<(owners p i).side :=
    CommonCases.OriginalOwners.side p (masks i)
  have same (i j : Fin 12) : (owners p i).side=(owners p j).side := by
    change (p.square (ownerIndex p (masks i))).side=(p.square (ownerIndex p (masks j))).side
    exact (p.congruent _).trans (p.congruent _).symm
  have apart (i j : Fin 12) (different : i≠j) :
      ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) :=
    CommonCases.OriginalOwners.apart family p hf (masks i) (masks j)
      (mask_member i) (mask_member j) (fun equal => different (masks_injective equal))
  refine {
    side := side
    same := same
    box := fun i => CommonCases.OriginalOwners.box p (masks i)
    apart := apart
    absentMarker := SingletonCorner.absent_marker p hf
    singletonMarker := ?_
    singletonNear := ?_
    singletonFar := ?_
    singletonSeed := ?_
    southeastCornerBottom := ?_
    southeastCornerRight := ?_
    southeastCorner := ?_
    northeastCornerRight := ?_
    northeastCornerTop := ?_
    northeastCorner := ?_
    northwestCornerTop := ?_
    northwestCornerLeft := ?_
    northwestCorner := ?_
    southwestMarker := ?_
    southeastMarker := ?_
    northeastMarker := ?_
    northwestMarker := ?_
    leftMarker := ?_
    bottomMarker := ?_
    rightMarker := ?_
    topMarker := ?_ }
  · have own := seed p hf 0 (1,457/500) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 0 (28/25,1) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 0 (87/50,1) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 0 (187/100,19/25) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 1 (3,457/500) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 1 (1543/500,1) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 1 (3,1) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 2 (1543/500,3) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 2 (3,1543/500) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 2 (3,3) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 3 (1,1543/500) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 3 (457/500,3) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 3 (1,3) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 4 (33/20,33/20) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 8 (457/500,2) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 9 (2,457/500) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at own
    exact own
  · have own := seed p hf 11 (2,1543/500) (by decide +kernel)
    norm_num at own
    exact own

end
#print axioms frame
end N12Compact.Completion.OtherCases.C1089.OriginalData
