import Compact.Completion.OtherCases.C983.MergedCenterF5
import Compact.Completion.OtherCases.C983.MergedReduction
import Compact.Geometry.CentralWallCenter

/-! The actual two-wall center theorem removes the pure lower right
component for every merged F5 owner. Its ownership consequence also
closes the entire merged G4 branch without an extra two-square calculus. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem southeast_without_f8_check :
    ∀ owned∈f5SoutheastComponents,8∉owned → 4∈owned := by decide +kernel

theorem f5_right_not_lower (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : actual p 10≠{8,18} := by
  intro lower
  have rF8 : 8∈actual p 10 := by rw [lower]; decide +kernel
  have rG8 : 18∈actual p 10 := by rw [lower]; decide +kernel
  have rNoF9 : 9∉actual p 10 := by rw [lower]; decide +kernel
  have eF4 := southeast_without_f8_check _ (f5_southeast_components p hf f5)
    (absent_of_foreign p hf 10 5 8 (by decide +kernel) rF8)
  have eG6 := f5_southeast_g6 p hf f5
  have inner : (owners p 5).Inside 2 (87/50) := by
    have h := auxiliary_inside p 5 4 (by decide +kernel) eF4
    simpa [auxPoints,fPoints,gPoints] using h
  have elbow : (owners p 5).Inside (113/50) 2 := by
    have h := auxiliary_inside p 5 16 (by decide +kernel) eG6
    simpa [auxPoints,fPoints,gPoints] using h
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have northeast : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have southwest : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have missingN : ¬(owners p 5).Inside (47/20) (47/20) :=
    fun h => owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨h,northeast⟩
  have missingW : ¬(owners p 5).Inside (33/20) (33/20) :=
    fun h => owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨h,southwest⟩
  have rMarker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have rHigh : (owners p 10).Inside 3 (8/5) := by
    have h := auxiliary_inside p 10 18 (by decide +kernel) rG8
    simpa [auxPoints,fPoints,gPoints] using h
  have rMissing : ¬(owners p 10).Inside 3 (113/50) := by
    have h := missing_auxiliary p 10 9 (by decide +kernel) rNoF9
    simpa [auxPoints,fPoints,gPoints] using h
  have bMarker : (owners p 9).Inside 2 (457/500) := by
    have h := seed_inside p hf 9 (2,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have bHigh := (bottom_aux p hf).1
  have singleton : (owners p 0).Inside (87/50) 1 := by
    have h := seed_inside p hf 0 (87/50,1) (by decide +kernel)
    norm_num at h
    exact h
  have bMissing : ¬(owners p 9).Inside (87/50) 1 :=
    fun h => owners_apart p hf 9 0 (by decide +kernel) _ _ ⟨h,singleton⟩
  have point := CentralWallCenter.point (pullY (owners p 5)) (pullY (owners p 10))
    (pullY (owners p 9)) (owners_side p 5) (owners_same_side p 5 10) (owners_same_side p 5 9)
    (container_pullY _ (owners_contained p 10)) (container_pullY _ (owners_contained p 9))
    (by norm_num [inside_pullY]; exact inner)
    (by norm_num [inside_pullY]; exact elbow)
    (by norm_num [inside_pullY]; exact marker)
    (by norm_num [inside_pullY]; exact missingN)
    (by norm_num [inside_pullY]; exact missingW)
    (by norm_num [inside_pullY]; exact rMarker)
    (by norm_num [inside_pullY]; exact rHigh)
    (by norm_num [inside_pullY]; exact rMissing)
    (by norm_num [inside_pullY]; exact bMarker)
    (by norm_num [inside_pullY]; exact bHigh)
    (by norm_num [inside_pullY]; exact bMissing)
    (fun x y own => owners_apart p hf 5 10 (by decide +kernel) x (4-y)
      ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩)
    (fun x y own => owners_apart p hf 5 9 (by decide +kernel) x (4-y)
      ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩)
  norm_num [inside_pullY] at point
  exact owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨point,f5_merged_center p hf f5⟩

private theorem right_after_lower_check :
    ∀ owned∈f5RightComponents,owned≠{8,18} → 9∈owned := by decide +kernel

theorem f5_right_f9 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : 9∈actual p 10 :=
  right_after_lower_check _ (f5_right_components p hf f5) (f5_right_not_lower p hf f5)

theorem f5_northeast_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : 7∈actual p 6 :=
  (f5_northeast_cover p hf f5).1.resolve_right
    (absent_of_foreign p hf 10 6 9 (by decide +kernel) (f5_right_f9 p hf f5))

private theorem top_without_f7_check :
    ∀ owned∈originalComponents 11,7∉owned → 3∈owned ∧ 14∈owned := by decide +kernel

theorem f5_top_f3_g4 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : 3∈actual p 11 ∧ 14∈actual p 11 :=
  top_without_f7_check _ (original_actual_mem p hf 11)
    (absent_of_foreign p hf 6 11 7 (by decide +kernel) (f5_northeast_f7 p hf f5))

theorem merged_no_g4 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    14∉actual p 7 := by
  intro g4
  have f5 := merged_g4_implies_f5 p hf g4
  have foreign := (f5_top_f3_g4 p hf f5).2
  exact absent_of_foreign p hf 11 7 14 (by decide +kernel) foreign g4

end
#print axioms f5_right_not_lower
#print axioms merged_no_g4
end N12Compact.Completion.OtherCases.C983

