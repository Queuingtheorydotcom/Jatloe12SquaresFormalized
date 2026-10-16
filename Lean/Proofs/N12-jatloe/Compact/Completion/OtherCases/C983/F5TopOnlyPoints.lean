import Compact.Completion.OtherCases.C983.F5RightFinal
import Compact.Completion.OtherCases.C983.TopOnlyPoints
import Compact.Completion.OtherCases.TopOnlyQuadrantProfile

/-! Genuine original-owner point and full-profile entrance for the F5
upper-right ending. Its final right component omits the lower auxiliary
itself, so the wall advance does not presume that another chosen square
owns that auxiliary. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem right_advance_of_omitted_lower (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (g9 : 19∈actual p 10)
    (noF8 : 8∉actual p 10) : (owners p 10).Inside 3 (64/25) := by
  have marker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have upper : (owners p 10).Inside 3 (12/5) := by
    have h := auxiliary_inside p 10 19 (by decide +kernel) g9
    simpa [auxPoints,fPoints,gPoints] using h
  have missingF : ¬(owners p 10).Inside 3 (87/50) := by
    have h := missing_auxiliary p 10 8 (by decide +kernel) noF8
    simpa [auxPoints,fPoints,gPoints] using h
  have northeast : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have advance := WallUpperMissingReach.point (pullX (owners p 10))
    (owners_side p 10) (container_pullX _ (owners_contained p 10))
    (by norm_num only [inside_pullX]; exact marker)
    (by norm_num only [inside_pullX]; exact upper)
    (by norm_num only [inside_pullX]; exact missingF)
    (by
      norm_num only [inside_pullX]
      exact fun h => owners_apart p hf 10 6 (by decide +kernel) _ _ ⟨h,northeast⟩)
  norm_num only [inside_pullX] at advance
  exact advance

theorem f5_right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    ∀ y : ℝ,113/50≤y → y≤64/25 → (owners p 10).Inside 3 y := by
  have final := f5_right_final p hf f5
  have low : (owners p 10).Inside 3 (113/50) := by
    have f9 : 9∈actual p 10 := by rw [final]; decide +kernel
    have h := auxiliary_inside p 10 9 (by decide +kernel) f9
    simpa [auxPoints,fPoints,gPoints] using h
  have g9 : 19∈actual p 10 := by rw [final]; decide +kernel
  have noF8 : 8∉actual p 10 := by rw [final]; decide +kernel
  intro y lower upper
  exact CommonCases.OriginalOwners.vertical_segment (owners p 10) 3 (113/50) (64/25) y
    low (right_advance_of_omitted_lower p hf g9 noF8) (by norm_num) lower upper

theorem f5_top_only_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    (owners p 6).Inside (101/40) (17/8) ∧ (owners p 6).Inside (5/2) 3 ∧
      (owners p 6).Inside 2 (131/50) ∧ (owners p 10).Inside 3 2 := by
  have final := f5_final_central p hf f5
  have f7 : 7∈actual p 6 := by rw [final.2.1]; decide +kernel
  have g7 : 17∈actual p 6 := by rw [final.2.1]; decide +kernel
  have noF5 := absent_of_foreign p hf 7 6 5 (by decide +kernel) f5
  have top := f5_top_origin p hf f5
  have bar := f5_right_bar p hf f5
  have sharp := northeast_upper_point p hf f7 noF5 top bar
  have extension := northeast_top_extension p hf f7 noF5 top (f5_southeast_crosspoint p hf f5)
  exact ⟨sharp,extension,northeast_left_point p hf g7 noF5 sharp top bar,
    f5_right_origin p hf f5⟩

theorem northeast_quadrant_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (g7 : 17∈actual p 6) (noF5 : 5∉actual p 6)
    (sharp : (owners p 6).Inside (101/40) (17/8))
    (topOrigin : (owners p 11).Inside 2 3)
    (rightBar : ∀ y : ℝ,113/50≤y → y≤64/25 → (owners p 10).Inside 3 y) :
    ∃ r : OpenSquare,r.side=(owners p 6).side ∧
      (∀ x y,r.Inside x y ↔ (owners p 6).Inside (x+2) (y+2)) ∧
      TopOnlyQuadrantProfile.Data r ∧ r.Inside 0 (31/50) := by
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
  have missingP : ¬(owners p 6).Inside 2 3 :=
    fun h => owners_apart p hf 6 11 (by decide +kernel) _ _ ⟨h,topOrigin⟩
  have missingC : ¬(owners p 6).Inside 3 3 :=
    fun h => owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨h,corner⟩
  have bar : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬((owners p 6).translated 2 2).Inside 1 y := by
    intro y lower upper own
    have original : (owners p 6).Inside 3 (y+2) := by
      convert (inside_translated_iff (owners p 6) 2 2 1 y).mp own using 1 <;> ring
    exact owners_apart p hf 6 10 (by decide +kernel) _ _
      ⟨original,rightBar (y+2) (by linarith only [lower]) (by linarith only [upper])⟩
  obtain ⟨r,side,same,profile⟩ := TopOnlyQuadrantProfile.frame ((owners p 6).translated 2 2)
    (owners_side p 6)
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact top)
    (by norm_num [inside_translated_iff]; exact sharp)
    (by norm_num [inside_translated_iff]; exact missingL)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingC) bar
  have sameOriginal : ∀ x y,r.Inside x y ↔ (owners p 6).Inside (x+2) (y+2) := by
    intro x y
    simpa only [inside_translated_iff,add_comm] using same x y
  refine ⟨r,side,sameOriginal,profile,?_⟩
  apply (sameOriginal _ _).mpr
  norm_num
  exact northeast_left_point p hf g7 noF5 sharp topOrigin rightBar

end
#print axioms f5_top_only_points
#print axioms northeast_quadrant_profile
end N12Compact.Completion.OtherCases.C983
