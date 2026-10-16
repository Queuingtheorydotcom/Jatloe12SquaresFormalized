import Compact.Completion.OtherCases.MergedPending.CentralPoints
import Compact.Completion.OtherCases.MergedPending.C700FullCornerOrigin
import Compact.Completion.OtherCases.C983.C974LocalEnding
import Compact.Completion.CommonCases.SingletonMissing

/-! C700's actual bottom singleton owns the southwest corner. The full
three-square theorem uses precisely singleton1, bottom8192 and paired12.
Its foreign middle and outer points remain in southwest256 and right16384.
The strong singleton seeds are produced only under the actual missing-corner
assumption; no central orientation or merged-square support is assumed. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem c700_bottom_singleton_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 1).Inside 1 1 := by
  by_contra missing
  have cap : (owner p 1).side≤1001/1000 := by
    change (p.square (ownerIndex p 1)).side≤1001/1000
    rw [p.congruent]
    exact p.side_le
  have exactMask : ExactMarkers (owner p 1) (maskSupport 1) := by
    have code1 := code _ p hf 1 (by decide +kernel)
    simpa only [owner,code1] using coded_exact p (ownerIndex p 1)
  have singleton : ExactMarkers (owner p 1) {0} := by
    convert exactMask using 1; decide +kernel
  have strong := CommonCases.SingletonMissing.zero_missing_points
    _ (side p 1) cap (box p 1) singleton missing
  have singletonMarker := seed _ p hf 1 (by decide +kernel)
    (1,457/500) (by decide +kernel)
  have bottomMarker := seed _ p hf 8192 (by decide +kernel)
    (2,457/500) (by decide +kernel)
  have cornerPoint := seed _ p hf 12 (by decide +kernel)
    (3,1) (by decide +kernel)
  have absentMarker := missing_marker _ p hf 8192 (by decide +kernel)
    9 (by decide +kernel)
  norm_num [S12.marker] at singletonMarker bottomMarker cornerPoint absentMarker
  have southwestMiddle := (southwest_crosspoints .c700 p hf).1
  have rightMiddle := (c700_right_reach p hf).2 (3/2) (by norm_num) (by norm_num)
  let K := (owner p 1).translated 1 1
  let W := (owner p 8192).translated 1 1
  let C := (owner p 12).translated 1 1
  have input : C983.C974LocalData.Input K W C := {
    sideLarge := side p 1
    sameKW := (p.congruent _).trans (p.congruent _).symm
    sameKC := (p.congruent _).trans (p.congruent _).symm
    lowerWall := by
      intro x y own
      have actual := (inside_translated_iff (owner p 1) 1 1 x y).mp own
      have wall := (box p 1 _ _ actual).2.2.1
      linarith only [wall]
    markerK := by
      dsimp only [K]
      norm_num only [inside_translated_iff]
      exact singletonMarker
    pointK := by
      dsimp only [K]
      norm_num only [inside_translated_iff]
      exact strong.1
    seedK := by
      dsimp only [K]
      norm_num only [inside_translated_iff]
      exact strong.2
    missingK := by
      dsimp only [K]
      norm_num only [inside_translated_iff]
      exact missing
    originW := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact c700_bottom_origin p hf
    markerW := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact bottomMarker
    farW := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact (bottom_reach .c700 p hf).2 (14/5) (by norm_num) le_rfl
    missingMarker := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact absentMarker
    missingMiddle := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 8192 256
        (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨own,southwestMiddle⟩
    missingOuter := by
      dsimp only [W]
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 8192 16384
        (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨own,rightMiddle⟩
    cornerWalls := by
      intro x y own
      have actual := (inside_translated_iff (owner p 12) 1 1 x y).mp own
      have wall := box p 12 _ _ actual
      exact ⟨by linarith only [wall.2.1],by linarith only [wall.2.2.1]⟩
    corner := by
      dsimp only [C]
      norm_num only [inside_translated_iff]
      exact cornerPoint
    missingCorner := by
      dsimp only [C]
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 12 16384
        (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨own,rightMiddle⟩
    apartKW := by
      intro x y both
      exact apart _ p hf 1 8192 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
          (inside_translated_iff _ _ _ _ _).mp both.2⟩
    apartKC := by
      intro x y both
      exact apart _ p hf 1 12 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
          (inside_translated_iff _ _ _ _ _).mp both.2⟩
    apartWC := by
      intro x y both
      exact apart _ p hf 8192 12 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
          (inside_translated_iff _ _ _ _ _).mp both.2⟩ }
  exact C983.C974LocalEnding.impossible K W C input

end
#print axioms c700_bottom_singleton_corner
end N12Compact.MergedPending
