import Compact.Completion.OtherCases.C974.LeftOrigin
import Compact.Completion.OtherCases.C983.C974LocalEnding

/-! Both literal C974 missing-corner roots are discharged by the full
raw three-square theorem. All stronger singleton seeds, actual origins,
crosspoints and corners are produced by the original family entrance. -/
namespace N12Compact.Completion.OtherCases.C974.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem bottom_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 0).Inside 1 1) :
    C983.C974LocalData.Input ((owners p 0).translated 1 1)
      ((owners p 9).translated 1 1) ((owners p 2).translated 1 1) := by
  have h := fixed p hf
  have seeds := missing_zero p hf missing
  have marker : (owners p 0).Inside 1 (457/500) := by
    convert seed p hf 0 (1,457/500) (by decide +kernel) using 1 <;> norm_num
  refine {
    sideLarge := side p 0
    sameKW := same p 0 9
    sameKC := same p 0 2
    lowerWall := ?_
    markerK := ?_
    pointK := ?_
    seedK := ?_
    missingK := ?_
    originW := ?_
    markerW := ?_
    farW := ?_
    missingMarker := ?_
    missingMiddle := ?_
    missingOuter := ?_
    cornerWalls := ?_
    corner := ?_
    missingCorner := ?_
    apartKW := ?_
    apartKC := ?_
    apartWC := ?_ }
  · intro x y own
    have wall := (box p 0 _ _ ((inside_translated_iff _ _ _ _ _).mp own)).2.2.1
    linarith only [wall]
  · norm_num [inside_translated_iff]; exact marker
  · norm_num [inside_translated_iff]; exact seeds.1
  · norm_num [inside_translated_iff]; exact seeds.2
  · norm_num [inside_translated_iff]; exact missing
  · norm_num [inside_translated_iff]; exact bottom_origin p hf
  · norm_num [inside_translated_iff]; exact h.bottomMarker
  · norm_num [inside_translated_iff]; exact (bottom_reach p hf).1
  · norm_num [inside_translated_iff]; exact foreign p hf 9 6 (by decide) _ _ h.southeastMarker
  · norm_num [inside_translated_iff]; exact foreign p hf 9 5 (by decide) _ _ (southwest_south p hf)
  · norm_num [inside_translated_iff]; exact foreign p hf 9 6 (by decide) _ _ (southeast_lower p hf)
  · intro x y own
    have wall := box p 2 _ _ ((inside_translated_iff _ _ _ _ _).mp own)
    constructor <;> linarith only [wall.2.1,wall.2.2.1]
  · norm_num [inside_translated_iff]; exact h.southeastCorner
  · norm_num [inside_translated_iff]; exact foreign p hf 2 6 (by decide) _ _ (southeast_lower p hf)
  · intro x y both
    exact apart p hf 0 9 (by decide) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
  · intro x y both
    exact apart p hf 0 2 (by decide) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
  · intro x y both
    exact apart p hf 9 2 (by decide) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩

theorem left_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 1).Inside 1 1) :
    C983.C974LocalData.Input ((pullSwap (owners p 1)).translated 1 1)
      ((pullSwap (owners p 8)).translated 1 1) ((pullSwap (owners p 4)).translated 1 1) := by
  have h := fixed p hf
  have seeds := missing_one p hf missing
  have marker : (owners p 1).Inside (457/500) 1 := by
    convert seed p hf 1 (457/500,1) (by decide +kernel) using 1 <;> norm_num
  refine {
    sideLarge := side p 1
    sameKW := same p 1 8
    sameKC := same p 1 4
    lowerWall := ?_
    markerK := ?_
    pointK := ?_
    seedK := ?_
    missingK := ?_
    originW := ?_
    markerW := ?_
    farW := ?_
    missingMarker := ?_
    missingMiddle := ?_
    missingOuter := ?_
    cornerWalls := ?_
    corner := ?_
    missingCorner := ?_
    apartKW := ?_
    apartKC := ?_
    apartWC := ?_ }
  · intro x y own
    have original : (owners p 1).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := (box p 1 _ _ original).1
    linarith only [wall]
  · norm_num [inside_translated_iff,inside_pullSwap]; exact marker
  · norm_num [inside_translated_iff,inside_pullSwap]; exact seeds.1
  · norm_num [inside_translated_iff,inside_pullSwap]; exact seeds.2
  · norm_num [inside_translated_iff,inside_pullSwap]; exact missing
  · norm_num [inside_translated_iff,inside_pullSwap]; exact left_origin p hf
  · norm_num [inside_translated_iff,inside_pullSwap]; exact h.leftMarker
  · norm_num [inside_translated_iff,inside_pullSwap]; exact left_reach p hf
  · norm_num [inside_translated_iff,inside_pullSwap]; exact missing_northwest p hf 8
  · norm_num [inside_translated_iff,inside_pullSwap]
    exact foreign p hf 8 5 (by decide) _ _ (southwest_west p hf)
  · norm_num [inside_translated_iff,inside_pullSwap]
    exact foreign p hf 8 11 (by decide) _ _ (top_halfpoint p hf)
  · intro x y own
    have original : (owners p 4).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := box p 4 _ _ original
    constructor <;> linarith only [wall.2.2.2,wall.1]
  · norm_num [inside_translated_iff,inside_pullSwap]; exact h.northwestCorner
  · norm_num [inside_translated_iff,inside_pullSwap]
    exact foreign p hf 4 11 (by decide) _ _ (top_halfpoint p hf)
  · intro x y both
    have first : (owners p 1).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owners p 8).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact apart p hf 1 8 (by decide) _ _ ⟨first,last⟩
  · intro x y both
    have first : (owners p 1).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owners p 4).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact apart p hf 1 4 (by decide) _ _ ⟨first,last⟩
  · intro x y both
    have first : (owners p 8).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owners p 4).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact apart p hf 8 4 (by decide) _ _ ⟨first,last⟩

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  by_cases first : (owners p 0).Inside 1 1
  · have second : ¬(owners p 1).Inside 1 1 := foreign p hf 1 0 (by decide) _ _ first
    exact C983.C974LocalEnding.impossible _ _ _ (left_input p hf second)
  · exact C983.C974LocalEnding.impossible _ _ _ (bottom_input p hf first)

end
#print axioms impossible
end N12Compact.Completion.OtherCases.C974.OriginalData
