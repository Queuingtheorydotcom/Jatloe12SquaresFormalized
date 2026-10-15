import Compact.Completion.OtherCases.C983.F4CentralFinal
import Compact.Completion.OtherCases.C983.WallOrigins
import Compact.Completion.OtherCases.TopOnlyLeftPoint
import Compact.Completion.OtherCases.MergedElementary

/-! Complete original-owner point entrance for the F4 top-only ending,
and the elementary merged points available before any ending. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem merged_horizontal_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside (3/2) 2 := by
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 7).Inside (87/50) 2 := by
    have h := auxiliary_inside p 7 13 (by decide +kernel) (merged_g3 p hf)
    simpa [auxPoints,fPoints,gPoints] using h
  have southeast : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have northeast : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  exact MergedElementary.horizontal_original (owners p 7) (owners_side p 7) south north inner
    (fun h => owners_apart p hf 7 5 (by decide +kernel) _ _ ⟨h,southeast⟩)
    (fun h => owners_apart p hf 7 6 (by decide +kernel) _ _ ⟨h,northeast⟩)

theorem two_inward_merged_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (f5 : 5∈actual p 7) : (owners p 7).Inside 2 2 := by
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 7).Inside (87/50) 2 := by
    have h := auxiliary_inside p 7 13 (by decide +kernel) (merged_g3 p hf)
    simpa [auxPoints,fPoints,gPoints] using h
  have lower : (owners p 7).Inside 2 (87/50) := by
    have h := auxiliary_inside p 7 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  have upper : (owners p 7).Inside 2 (113/50) := by
    have h := auxiliary_inside p 7 5 (by decide +kernel) f5
    simpa [auxPoints,fPoints,gPoints] using h
  exact MergedElementary.two_inward_center_original (owners p 7) south north inner lower upper

theorem northeast_left_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (g7 : 17∈actual p 6) (noF5 : 5∉actual p 6)
    (sharp : (owners p 6).Inside (101/40) (17/8))
    (topOrigin : (owners p 11).Inside 2 3)
    (rightBar : ∀ y : ℝ,113/50≤y → y≤64/25 → (owners p 10).Inside 3 y) :
    (owners p 6).Inside 2 (131/50) := by
  have marker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have top : (owners p 6).Inside (113/50) 3 := by
    have h := auxiliary_inside p 6 17 (by decide +kernel) g7
    simpa [auxPoints,fPoints,gPoints] using h
  have missingL : ¬(owners p 6).Inside 2 (113/50) := by
    have h := missing_auxiliary p 6 5 (by decide +kernel) noF5
    simpa [auxPoints,fPoints,gPoints] using h
  have corner : (owners p 3).Inside 3 3 := by
    have h := seed_inside p hf 3 (3,3) (by decide +kernel)
    norm_num at h
    exact h
  exact TopOnlyLeftPoint.point_original (owners p 6) (owners_side p 6) marker top sharp missingL
    (fun h => owners_apart p hf 6 11 (by decide +kernel) _ _ ⟨h,topOrigin⟩)
    (fun h => owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨h,corner⟩)
    (fun y lower upper h => owners_apart p hf 6 10 (by decide +kernel) _ _
      ⟨h,rightBar y lower upper⟩)

theorem f4_top_only_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (noF5 : 5∉actual p 6) :
    (owners p 6).Inside (101/40) (17/8) ∧ (owners p 6).Inside (5/2) 3 ∧
      (owners p 6).Inside 2 (131/50) ∧ (owners p 10).Inside 3 2 := by
  have f7 := f4_northeast_f7 p hf f4
  have g7 := f4_northeast_g7 p hf f4
  have top := f4_top_origin p hf f4
  have bar := f4_right_bar p hf f4
  have sharp := northeast_upper_point p hf f7 noF5 top bar
  have extension := northeast_top_extension p hf f7 noF5 top (f4_southeast_crosspoint p hf f4)
  exact ⟨sharp,extension,northeast_left_point p hf g7 noF5 sharp top bar,
    right_origin_of_upper_extension p hf (f4_right p hf f4).2 extension⟩

end
#print axioms merged_horizontal_point
#print axioms two_inward_merged_center
#print axioms f4_top_only_points
end N12Compact.Completion.OtherCases.C983

