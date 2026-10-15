import Compact.Completion.OtherCases.C983.InwardAlternativeEntrance
import Compact.Completion.OtherCases.TwoChordHull
import Compact.Completion.OtherCases.ShortCornerAdvance
import Compact.Completion.OtherCases.ShorterCornerWall

/-! Complete exclusion of the original merged owner with neither inward
point. The strict hull, actual corner reach, and actual left wall are
proved from their own original owners before the local ending is applied. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem no_merged_f5_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noF5 : 5∉actual p 7) :
    (owners p 4).Inside (39/50) 3 := by
  have origin : (owners p 4).Inside 1 3 := by
    have h := seed_inside p hf 4 (1,3) (by decide +kernel)
    norm_num at h
    exact h
  have top : (owners p 11).Inside (8/5) 3 := by
    have h := auxiliary_inside p 11 3 (by decide +kernel) (no_merged_f5_top p hf noF5).1
    simpa [auxPoints,fPoints,gPoints] using h
  have missingTop : ¬(owners p 4).Inside (8/5) 3 :=
    fun h => owners_apart p hf 4 11 (by decide +kernel) _ _ ⟨h,top⟩
  have missingLeft : ¬(owners p 4).Inside 1 (14/5) :=
    fun h => owners_apart p hf 4 8 (by decide +kernel) _ _ ⟨h,left_advance p hf⟩
  let corner := (pullX (owners p 4)).translated 3 3
  have wall : ∀ x y,corner.Inside x y → y≤1 := by
    intro x y own
    have back := own
    simp only [corner,inside_translated_iff,inside_pullX] at back
    have bound := owners_contained p 4 _ _ back
    linarith only [bound.2.2.2]
  have point := ShortCornerAdvance.point corner (owners_side p 4) wall
    (by norm_num [corner,inside_translated_iff,inside_pullX]; exact origin)
    (by norm_num [corner,inside_translated_iff,inside_pullX]; exact missingTop)
    (by norm_num [corner,inside_translated_iff,inside_pullX]; exact missingLeft)
  norm_num [corner,inside_translated_iff,inside_pullX] at point
  exact point

theorem merged_west_hull (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noF4 : 4∉actual p 7) (noF5 : 5∉actual p 7) :
    (owners p 7).Inside (49/50) 2 ∧ (owners p 7).Inside (49/50) (101/50) ∧
      (owners p 7).Inside (26/25) (211/100) := by
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have low : (owners p 1).Inside 1 (87/50) := by
    have h := seed_inside p hf 1 (1,87/50) (by decide +kernel)
    norm_num at h
    exact h
  have marker : (owners p 8).Inside (457/500) 2 := by
    have h := seed_inside p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have missing4 : ¬(owners p 7).Inside 2 (87/50) := by
    have h := missing_auxiliary p 7 4 (by decide +kernel) noF4
    simpa [auxPoints,fPoints,gPoints] using h
  have missing5 : ¬(owners p 7).Inside 2 (113/50) := by
    have h := missing_auxiliary p 7 5 (by decide +kernel) noF5
    simpa [auxPoints,fPoints,gPoints] using h
  have missingLow : ¬(owners p 7).Inside 1 (87/50) :=
    fun h => owners_apart p hf 7 1 (by decide +kernel) _ _ ⟨h,low⟩
  have missingHigh : ¬(owners p 7).Inside 1 (113/50) :=
    fun h => owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨h,(left_aux p hf).1⟩
  let west := (pullX (owners p 7)).translated 2 2
  have hull := TwoChordHull.points west (owners_side p 7)
    (by norm_num [west,inside_translated_iff,inside_pullX]; exact south)
    (by norm_num [west,inside_translated_iff,inside_pullX]; exact north)
    (by norm_num [west,inside_translated_iff,inside_pullX]; exact missing4)
    (by norm_num [west,inside_translated_iff,inside_pullX]; exact missing5)
    (by norm_num [west,inside_translated_iff,inside_pullX]; exact missingLow)
    (by norm_num [west,inside_translated_iff,inside_pullX]; exact missingHigh)
    (by
      intro z low high own
      have back := own
      simp only [west,inside_translated_iff,inside_pullX] at back
      have sameOwner := inside_segment (owners p 8) (457/500) 2 1 (113/50) z
        marker (left_aux p hf).1 low high
      have duplicate : (owners p 7).Inside
          ((1-z)*(457/500)+z*1) ((1-z)*2+z*(113/50)) := by
        convert back using 1 <;> ring
      exact owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨duplicate,sameOwner⟩)
  norm_num [west,inside_translated_iff,inside_pullX] at hull
  exact hull

private theorem no_inward_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noF4 : 4∉actual p 7) (noF5 : 5∉actual p 7) :
    False := by
  have hull := merged_west_hull p hf noF4 noF5
  have corner := no_merged_f5_corner p hf noF5
  have marker : (owners p 8).Inside (457/500) 2 := by
    have h := seed_inside p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have missing0 : ¬(owners p 8).Inside (49/50) 2 :=
    fun h => owners_apart p hf 8 7 (by decide +kernel) _ _ ⟨h,hull.1⟩
  have missing1 : ¬(owners p 8).Inside (49/50) (101/50) :=
    fun h => owners_apart p hf 8 7 (by decide +kernel) _ _ ⟨h,hull.2.1⟩
  have missing2 : ¬(owners p 8).Inside (26/25) (211/100) :=
    fun h => owners_apart p hf 8 7 (by decide +kernel) _ _ ⟨h,hull.2.2⟩
  have missingCorner : ¬(owners p 8).Inside (39/50) 3 :=
    fun h => owners_apart p hf 8 4 (by decide +kernel) _ _ ⟨h,corner⟩
  let left := (pullX (owners p 8)).translated 3 2
  apply ShorterCornerWall.impossible left (owners_side p 8)
  · intro x y own
    have back := own
    simp only [left,inside_translated_iff,inside_pullX] at back
    have bound := owners_contained p 8 _ _ back
    linarith only [bound.1]
  · norm_num [left,inside_translated_iff,inside_pullX]
    exact marker
  · norm_num [left,inside_translated_iff,inside_pullX]
    exact (left_aux p hf).1
  · norm_num [left,inside_translated_iff,inside_pullX]
    exact left_advance p hf
  · norm_num [left,inside_translated_iff,inside_pullX]
    exact missing0
  · norm_num [left,inside_translated_iff,inside_pullX]
    exact missing1
  · norm_num [left,inside_translated_iff,inside_pullX]
    exact missing2
  · norm_num [left,inside_translated_iff,inside_pullX]
    exact missingCorner

theorem merged_inward_alternative (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    4∈actual p 7 ∨ 5∈actual p 7 := by
  by_cases f4 : 4∈actual p 7
  · exact Or.inl f4
  · by_cases f5 : 5∈actual p 7
    · exact Or.inr f5
    · exact False.elim (no_inward_impossible p hf f4 f5)

end
#print axioms merged_inward_alternative
end N12Compact.Completion.OtherCases.C983

