import Compact.Completion.OtherCases.C1091.EntranceDomains

/-! Actual C1091 points used by the continuous entrance. The additional
merged marker is owned by Q4; there is no globally absent-marker premise. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceFrame
open S12 S12Pilot OriginalData
set_option Elab.async false
noncomputable section

structure Frame (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  same : ∀ i j,(q i).side=(q j).side
  box : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
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
  northwestCorner : (q 3).Inside 1 3
  mergedLeft : (q 4).Inside (457/500) 1
  southwestMarker : (q 4).Inside (33/20) (33/20)
  mergedLow : (q 4).Inside 1 (87/50)
  southeastMarker : (q 5).Inside (47/20) (33/20)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  leftMarker : (q 8).Inside (457/500) 2
  bottomMarker : (q 9).Inside 2 (457/500)
  rightMarker : (q 10).Inside (1543/500) 2
  topMarker : (q 11).Inside 2 (1543/500)

theorem frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Frame (owners p) where
  side := OriginalData.side p
  same := OriginalData.same p
  box := OriginalData.box p
  apart := OriginalData.apart p hf
  singletonMarker := by
    have h := seed p hf 0 (1,457/500) (by decide +kernel); norm_num at h; exact h
  singletonNear := by
    have h := seed p hf 0 (28/25,1) (by decide +kernel); norm_num at h; exact h
  singletonFar := by
    have h := seed p hf 0 (87/50,1) (by decide +kernel); norm_num at h; exact h
  singletonSeed := by
    have h := seed p hf 0 (187/100,19/25) (by decide +kernel); norm_num at h; exact h
  southeastCornerBottom := by
    have h := seed p hf 1 (3,457/500) (by decide +kernel); norm_num at h; exact h
  southeastCornerRight := by
    have h := seed p hf 1 (1543/500,1) (by decide +kernel); norm_num at h; exact h
  southeastCorner := by
    have h := seed p hf 1 (3,1) (by decide +kernel); norm_num at h; exact h
  northeastCornerRight := by
    have h := seed p hf 2 (1543/500,3) (by decide +kernel); norm_num at h; exact h
  northeastCornerTop := by
    have h := seed p hf 2 (3,1543/500) (by decide +kernel); norm_num at h; exact h
  northeastCorner := by
    have h := seed p hf 2 (3,3) (by decide +kernel); norm_num at h; exact h
  northwestCornerTop := by
    have h := seed p hf 3 (1,1543/500) (by decide +kernel); norm_num at h; exact h
  northwestCorner := by
    have h := seed p hf 3 (1,3) (by decide +kernel); norm_num at h; exact h
  mergedLeft := (merged_markers p hf).1
  southwestMarker := (merged_markers p hf).2
  mergedLow := EntranceMergedLow.original p hf
  southeastMarker := by
    have h := seed p hf 5 (47/20,33/20) (by decide +kernel); norm_num at h; exact h
  northeastMarker := by
    have h := seed p hf 6 (47/20,47/20) (by decide +kernel); norm_num at h; exact h
  northwestMarker := by
    have h := seed p hf 7 (33/20,47/20) (by decide +kernel); norm_num at h; exact h
  leftMarker := by
    have h := seed p hf 8 (457/500,2) (by decide +kernel); norm_num at h; exact h
  bottomMarker := by
    have h := seed p hf 9 (2,457/500) (by decide +kernel); norm_num at h; exact h
  rightMarker := by
    have h := seed p hf 10 (1543/500,2) (by decide +kernel); norm_num at h; exact h
  topMarker := by
    have h := seed p hf 11 (2,1543/500) (by decide +kernel); norm_num at h; exact h

end
#print axioms frame
end N12Compact.Completion.OtherCases.C1091.EntranceFrame
