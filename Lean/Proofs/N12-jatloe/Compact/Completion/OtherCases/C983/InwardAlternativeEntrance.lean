import Compact.Completion.OtherCases.C983.SharpApplications
import Compact.Completion.OtherCases.InwardShortBarPoint
import Compact.Completion.CommonCases.MergedNearPoint

/-! The actual-owner entrance when the merged F5 is absent. Optional
southeast F4 ownership is retained in the full inward/outward duplicate. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem merged_near_when_no_inward (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noF4 : 4∉actual p 7) (noF5 : 5∉actual p 7) :
    (owners p 7).Inside (41/20) (39/20) := by
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have leftLow : (owners p 1).Inside 1 (87/50) := by
    have h := seed_inside p hf 1 (1,87/50) (by decide +kernel)
    norm_num at h
    exact h
  have leftMarker : (owners p 8).Inside (457/500) 2 := by
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
    fun h => owners_apart p hf 7 1 (by decide +kernel) _ _ ⟨h,leftLow⟩
  have missingHigh : ¬(owners p 7).Inside 1 (113/50) :=
    fun h => owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨h,(left_aux p hf).1⟩
  have missingMarker : ¬(owners p 7).Inside (457/500) 2 :=
    fun h => owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨h,leftMarker⟩
  have points := CommonCases.MergedNearPoint.points_original (pullX (owners p 7)) (owners_side p 7)
    (by norm_num [inside_pullX]; exact south)
    (by norm_num [inside_pullX]; exact north)
    (by norm_num [inside_pullX]; exact missing4)
    (by norm_num [inside_pullX]; exact missing5)
    (by norm_num [inside_pullX]; exact missingLow)
    (by norm_num [inside_pullX]; exact missingHigh)
    (by norm_num [inside_pullX]; exact missingMarker)
  norm_num [inside_pullX] at points
  exact points.1

theorem southeast_inward_forces_merged_f5 (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 5) (g6 : 16∈actual p 5) (noF8 : 8∉actual p 5) :
    5∈actual p 7 := by
  by_contra noF5
  have noF4 := absent_of_foreign p hf 5 7 4 (by decide +kernel) f4
  have west := merged_near_when_no_inward p hf noF4 noF5
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have elbow : (owners p 5).Inside (113/50) 2 := by
    have h := auxiliary_inside p 5 16 (by decide +kernel) g6
    simpa [auxPoints,fPoints,gPoints] using h
  have inner : (owners p 5).Inside 2 (87/50) := by
    have h := auxiliary_inside p 5 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  have missing : ¬(owners p 5).Inside 3 (87/50) := by
    have h := missing_auxiliary p 5 8 (by decide +kernel) noF8
    simpa [auxPoints,fPoints,gPoints] using h
  have point := InwardShortBarPoint.point ((owners p 5).translated 2 2) (owners_side p 5)
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact inner)
    (by norm_num [inside_translated_iff]; exact missing)
    (by
      intro x low high own
      rw [inside_translated_iff] at own
      norm_num at own
      have foreign := bottom_bar p hf (x+2) (by linarith only [low]) (by linarith only [high])
      exact owners_apart p hf 5 9 (by decide +kernel) _ _ ⟨own,by simpa only [add_comm] using foreign⟩)
  norm_num [inside_translated_iff] at point
  exact owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨point,west⟩

private theorem southeast_no_f8_check :
    ∀ owned∈originalComponents 5,8∉owned → 4∈owned ∧ (16∈owned ∨ 18∈owned) := by
  decide +kernel

theorem no_merged_f5_southeast_f8 (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noF5 : 5∉actual p 7) : 8∈actual p 5 := by
  by_contra noF8
  have labels := southeast_no_f8_check _ (original_actual_mem p hf 5) noF8
  by_cases g6 : 16∈actual p 5
  · exact noF5 (southeast_inward_forces_merged_f5 p hf labels.1 g6 noF8)
  · exact southeast_inward_outward_exclusion p hf labels.1 (labels.2.resolve_left g6) g6

private theorem right_no_f8_check :
    ∀ owned∈originalComponents 10,8∉owned → 9∈owned ∧ 19∈owned := by decide +kernel

theorem no_merged_f5_right (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noF5 : 5∉actual p 7) :
    9∈actual p 10 ∧ 19∈actual p 10 :=
  right_no_f8_check _ (original_actual_mem p hf 10)
    (absent_of_foreign p hf 5 10 8 (by decide +kernel) (no_merged_f5_southeast_f8 p hf noF5))

private theorem northeast_no_right_check :
    ∀ owned∈originalComponents 6,9∉owned → 19∉owned → 13∉owned →
      (5∈owned ∨ 7∈owned) ∧ (16∈owned ∨ 17∈owned) := by decide +kernel
private theorem top_f7_g7_check :
    ∀ owned∈originalComponents 11,7∈owned → 17∈owned := by decide +kernel
private theorem southeast_no_g6_check :
    ∀ owned∈originalComponents 5,16∉owned → 18∈owned := by decide +kernel

private theorem actual_inward_outward (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (nF5 : 5∈actual p 6) (nG6 : 16∈actual p 6) (nNoF7 : 7∉actual p 6)
    (eF8 : 8∈actual p 5) (eG8 : 18∈actual p 5) : False := by
  have nm : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have nf : (owners p 6).Inside 2 (113/50) := by
    have h := auxiliary_inside p 6 5 (by decide +kernel) nF5
    simpa [auxPoints,fPoints,gPoints] using h
  have ng : (owners p 6).Inside (113/50) 2 := by
    have h := auxiliary_inside p 6 16 (by decide +kernel) nG6
    simpa [auxPoints,fPoints,gPoints] using h
  have missing : ¬(owners p 6).Inside (12/5) 3 := by
    have h := missing_auxiliary p 6 7 (by decide +kernel) nNoF7
    simpa [auxPoints,fPoints,gPoints] using h
  have em : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have ef : (owners p 5).Inside 3 (87/50) := by
    have h := auxiliary_inside p 5 8 (by decide +kernel) eF8
    simpa [auxPoints,fPoints,gPoints] using h
  have eg : (owners p 5).Inside 3 (8/5) := by
    have h := auxiliary_inside p 5 18 (by decide +kernel) eG8
    simpa [auxPoints,fPoints,gPoints] using h
  have wm : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have rm : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have cc : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have cm : (owners p 2).Inside (1543/500) 1 := by
    have h := seed_inside p hf 2 (1543/500,1) (by decide +kernel)
    norm_num at h
    exact h
  exact inward_outward_impossible (owners p 6) (owners p 5) (owners p 9) (owners p 2)
    (owners p 10) (owners p 7) (owners_side p 6) (owners_same_side p 6 5)
    nm nf ng missing em ef eg wm rm cc cm (bottom_bar p hf)
    (owners_apart p hf 6 5 (by decide +kernel)) (owners_apart p hf 6 7 (by decide +kernel))
    (owners_apart p hf 5 10 (by decide +kernel)) (owners_apart p hf 5 2 (by decide +kernel))
    (owners_apart p hf 5 9 (by decide +kernel))

private theorem top_no_f7_check :
    ∀ owned∈originalComponents 11,7∉owned → 3∈owned ∧ 14∈owned := by decide +kernel

theorem no_merged_f5_top (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (noF5 : 5∉actual p 7) :
    3∈actual p 11 ∧ 14∈actual p 11 := by
  apply top_no_f7_check _ (original_actual_mem p hf 11)
  intro topF7
  have topG7 := top_f7_g7_check _ (original_actual_mem p hf 11) topF7
  have noF7 := absent_of_foreign p hf 11 6 7 (by decide +kernel) topF7
  have noG7 := absent_of_foreign p hf 11 6 17 (by decide +kernel) topG7
  have right := no_merged_f5_right p hf noF5
  have cover := northeast_no_right_check _ (original_actual_mem p hf 6)
    (absent_of_foreign p hf 10 6 9 (by decide +kernel) right.1)
    (absent_of_foreign p hf 10 6 19 (by decide +kernel) right.2)
    (absent_of_foreign p hf 7 6 13 (by decide +kernel) (merged_g3 p hf))
  have nF5 := cover.1.resolve_right noF7
  have nG6 := cover.2.resolve_right noG7
  have eG8 := southeast_no_g6_check _ (original_actual_mem p hf 5)
    (absent_of_foreign p hf 6 5 16 (by decide +kernel) nG6)
  exact actual_inward_outward p hf nF5 nG6 noF7 (no_merged_f5_southeast_f8 p hf noF5) eG8

end
#print axioms southeast_inward_forces_merged_f5
#print axioms no_merged_f5_top
end N12Compact.Completion.OtherCases.C983

