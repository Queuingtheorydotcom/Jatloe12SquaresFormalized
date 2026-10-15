import Compact.Completion.OtherCases.C983.F5Crosspoint
import Compact.Completion.CommonCases.CentralPair
import Compact.Completion.C981.TopReach

/-! Universal actual top origin in the merged-F5 branch. The rightward
top alternative uses its own complete bar and the original central pair. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem top_cover_check : ∀ owned∈originalComponents 11,3∈owned ∨ 7∈owned := by
  decide +kernel
private theorem top_outward_check : ∀ owned∈originalComponents 11,7∈owned → 17∈owned := by
  decide +kernel
private theorem northeast_rightward_check :
    ∀ owned∈f5NortheastComponents,7∉owned → 17∉owned → owned={9,19} := by decide +kernel
private theorem right_lower_check :
    ∀ owned∈f5RightComponents,9∉owned → 19∉owned → owned={8,18} := by decide +kernel
private theorem southeast_inward_check :
    ∀ owned∈f5SoutheastComponents,8∉owned → 18∉owned → 9∉owned → owned={4,16} := by
  decide +kernel

theorem f5_top_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : (owners p 11).Inside 2 3 := by
  by_cases leftward : 3∈actual p 11
  · exact top_origin_of_f3 p hf leftward
  have topF7 := (top_cover_check _ (original_actual_mem p hf 11)).resolve_left leftward
  have topG7 := top_outward_check _ (original_actual_mem p hf 11) topF7
  have nExact := northeast_rightward_check _ (f5_northeast_components p hf f5)
    (absent_of_foreign p hf 11 6 7 (by decide +kernel) topF7)
    (absent_of_foreign p hf 11 6 17 (by decide +kernel) topG7)
  have nF9 : 9∈actual p 6 := by rw [nExact]; decide +kernel
  have nG9 : 19∈actual p 6 := by rw [nExact]; decide +kernel
  have rExact := right_lower_check _ (f5_right_components p hf f5)
    (absent_of_foreign p hf 6 10 9 (by decide +kernel) nF9)
    (absent_of_foreign p hf 6 10 19 (by decide +kernel) nG9)
  have rF8 : 8∈actual p 10 := by rw [rExact]; decide +kernel
  have rG8 : 18∈actual p 10 := by rw [rExact]; decide +kernel
  have eExact := southeast_inward_check _ (f5_southeast_components p hf f5)
    (absent_of_foreign p hf 10 5 8 (by decide +kernel) rF8)
    (absent_of_foreign p hf 10 5 18 (by decide +kernel) rG8)
    (absent_of_foreign p hf 6 5 9 (by decide +kernel) nF9)
  have eF4 : 4∈actual p 5 := by rw [eExact]; decide +kernel
  by_contra missingOrigin
  have topMarker : (owners p 11).Inside 2 (1543/500) := by
    have h := seed_inside p hf 11 (2,1543/500) (by decide +kernel)
    norm_num at h
    exact h
  have topAnchor : (owners p 11).Inside (12/5) 3 := by
    have h := auxiliary_inside p 11 7 (by decide +kernel) topF7
    simpa [auxPoints,fPoints,gPoints] using h
  have extended := C981CompletionTopReach.origin_alternative ((owners p 11).translated 2 3)
    (owners_side p 11)
    (by
      intro x y h
      have original := (inside_translated_iff (owners p 11) 2 3 x y).mp h
      have box := owners_contained p 11 (x+2) (y+3) original
      linarith only [box.2.2.2])
    (by norm_num [inside_translated_iff]; exact topMarker)
    (by norm_num [inside_translated_iff]; exact topAnchor)
    (by norm_num [inside_translated_iff]; exact missingOrigin)
  have topHigh : (owners p 11).Inside (14/5) 3 := by
    norm_num [inside_translated_iff] at extended
    exact extended
  have topLow : (owners p 11).Inside (113/50) 3 := by
    have h := auxiliary_inside p 11 17 (by decide +kernel) topG7
    simpa [auxPoints,fPoints,gPoints] using h
  have topBar : ∀ x : ℝ,113/50≤x → x≤14/5 → (owners p 11).Inside x 3 := by
    intro x lower upper
    exact CommonCases.OriginalOwners.horizontal_segment (owners p 11) (113/50) (14/5) 3 x
      topLow topHigh (by norm_num) lower upper
  have eMarker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have eInward : (owners p 5).Inside 2 (87/50) := by
    have h := auxiliary_inside p 5 4 (by decide +kernel) eF4
    simpa [auxPoints,fPoints,gPoints] using h
  have eElbow : (owners p 5).Inside (113/50) 2 := by
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f5_southeast_g6 p hf f5)
    simpa [auxPoints,fPoints,gPoints] using h
  have southwest : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have nMarker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have nOuter : (owners p 6).Inside 3 (113/50) := by
    have h := auxiliary_inside p 6 9 (by decide +kernel) nF9
    simpa [auxPoints,fPoints,gPoints] using h
  have nUpper : (owners p 6).Inside 3 (12/5) := by
    have h := auxiliary_inside p 6 19 (by decide +kernel) nG9
    simpa [auxPoints,fPoints,gPoints] using h
  have rightMarker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have corner : (owners p 3).Inside 3 3 := by
    have h := seed_inside p hf 3 (3,3) (by decide +kernel)
    norm_num at h
    exact h
  have cornerMarker : (owners p 3).Inside (1543/500) 3 := by
    have h := seed_inside p hf 3 (1543/500,3) (by decide +kernel)
    norm_num at h
    exact h
  exact CommonCases.CentralPair.impossible (owners p 5) (owners p 6)
    (owners_side p 5) (owners_side p 6) eMarker eInward eElbow
    (fun h => owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨h,southwest⟩)
    (fun h => owners_apart p hf 5 9 (by decide +kernel) _ _
      ⟨h,bottom_bar p hf (12/5) (by norm_num) (by norm_num)⟩)
    nMarker (Or.inr ⟨nOuter,nUpper⟩)
    (fun h => owners_apart p hf 6 10 (by decide +kernel) _ _ ⟨h,rightMarker⟩)
    (fun h => owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨h,corner⟩)
    (fun h => owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨h,cornerMarker⟩)
    (fun z lower upper h => owners_apart p hf 6 11 (by decide +kernel) _ _
      ⟨h,topBar z lower upper⟩)
    (owners_apart p hf 5 6 (by decide +kernel))

end
#print axioms f5_top_origin
end N12Compact.Completion.OtherCases.C983

