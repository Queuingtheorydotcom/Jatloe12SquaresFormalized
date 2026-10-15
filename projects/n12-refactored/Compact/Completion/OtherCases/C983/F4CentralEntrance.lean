import Compact.Completion.OtherCases.C983.F5Filters
import Compact.Completion.C981.UpperPoint

/-! The F4 central entrance through the exact top owner. Each exclusion
uses an actual square obstruction; all metadata cuts concern one literal
component list, so no twelve-owner product catalogue is introduced. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f4_northeast_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 17∈actual p 6 := by
  by_contra noG7
  have cover := f4_northeast p hf f4
  have g6 := cover.2.resolve_right noG7
  by_cases f5 : 5∈actual p 6
  · by_cases f7 : 7∈actual p 6
    · have outward := f4_inward_forces_outward p hf f4 f5 g6
      have eG8 : 18∈actual p 5 := by rw [outward]; decide +kernel
      have eNoG6 := absent_of_foreign p hf 6 5 16 (by decide +kernel) g6
      have lower := southeast_outward_point p hf (f4_southeast p hf f4) eG8 eNoG6
      have upper := northeast_inward_top_point p hf f5 g6 f7 noG7
      exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨lower,upper⟩
    · exact f4_inward_outward_exclusion p hf f4 f5 g6 f7
  · have f7 := cover.1.resolve_left f5
    have right := f4_right p hf f4
    exact northeast_mixed_exclusion p hf g6 f7 f5 noG7 right.1 right.2

theorem f4_top_avoids_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 17∉actual p 11 :=
  absent_of_foreign p hf 6 11 17 (by decide +kernel) (f4_northeast_g7 p hf f4)

/-- An actual top F5 supplies its entire vertical segment. The actual
upper-square point then duplicates a strict point of that same segment. -/
theorem f4_top_avoids_f5 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 5∉actual p 11 := by
  intro topF5
  have marker : (owners p 11).Inside 2 (1543/500) := by
    have h := seed_inside p hf 11 (2,1543/500) (by decide +kernel)
    norm_num at h
    exact h
  have inward : (owners p 11).Inside 2 (113/50) := by
    have h := auxiliary_inside p 11 5 (by decide +kernel) topF5
    simpa [auxPoints,fPoints,gPoints] using h
  have topBar : ∀ y : ℝ,113/50≤y → y≤1543/500 → (owners p 11).Inside 2 y := by
    intro y lower upper
    exact CommonCases.OriginalOwners.vertical_segment (owners p 11) 2 (113/50) (1543/500) y
      inward marker (by norm_num) lower upper
  have nMarker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have nTop : (owners p 6).Inside (113/50) 3 := by
    have h := auxiliary_inside p 6 17 (by decide +kernel) (f4_northeast_g7 p hf f4)
    simpa [auxPoints,fPoints,gPoints] using h
  have corner : (owners p 3).Inside 3 3 := by
    have h := seed_inside p hf 3 (3,3) (by decide +kernel)
    norm_num at h
    exact h
  have point := C981CompletionUpperPoint.point (owners p 6) (owners_side p 6) nMarker nTop
    (fun h => owners_apart p hf 6 11 (by decide +kernel) _ _
      ⟨h,topBar (12/5) (by norm_num) (by norm_num)⟩)
    (fun h => owners_apart p hf 6 11 (by decide +kernel) _ _
      ⟨h,topBar 3 (by norm_num) (by norm_num)⟩)
    (fun h => owners_apart p hf 6 10 (by decide +kernel) _ _
      ⟨h,f4_right_bar p hf f4 (12/5) (by norm_num) (by norm_num)⟩)
    (fun h => owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨h,corner⟩)
    (fun h => owners_apart p hf 6 10 (by decide +kernel) _ _
      ⟨h,f4_right_bar p hf f4 (64/25) (by norm_num) le_rfl⟩)
  exact owners_apart p hf 6 11 (by decide +kernel) _ _
    ⟨point,topBar (131/50) (by norm_num) (by norm_num)⟩

private theorem top_exact_check :
    ∀ owned∈originalComponents 11,7∉owned → 17∉owned → 5∉owned → owned={3,14} := by
  decide +kernel

theorem f4_top_exact (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : actual p 11={3,14} :=
  top_exact_check _ (original_actual_mem p hf 11)
    (f4_top_avoids_f7 p hf f4) (f4_top_avoids_g7 p hf f4) (f4_top_avoids_f5 p hf f4)

private theorem southeast_outward_g8_check :
    ∀ owned∈originalComponents 5,16∉owned → 18∈owned := by decide +kernel

/-- The one remaining outward southeast alternative has an inward
northeast neighbor; this records its genuine coupled-support entrance. -/
theorem f4_outward_northeast_f5 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (noG6 : 16∉actual p 5) : 5∈actual p 6 := by
  by_contra noF5
  have nF7 := (f4_northeast p hf f4).1.resolve_left noF5
  have g8 := southeast_outward_g8_check _ (original_actual_mem p hf 5) noG6
  have lower := southeast_outward_point p hf (f4_southeast p hf f4) g8 noG6
  have upper := northeast_upper_point p hf nF7 noF5
    (f4_top_origin p hf f4) (f4_right_bar p hf f4)
  exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨lower,upper⟩

private theorem two_inward_southeast_check :
    ∀ owned∈f5SoutheastComponents,4∉owned → 8∈owned →
      owned={8,16} ∨ owned={8,16,18} := by decide +kernel

theorem two_inward_central (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (f5 : 5∈actual p 7) :
    (actual p 5={8,16} ∨ actual p 5={8,16,18}) ∧
      actual p 6={7,17} ∧ actual p 11={3,14} := by
  have upper := f5_upper_of_right_g9 p hf f5 (f4_right p hf f4).2
  exact ⟨two_inward_southeast_check _ (f5_southeast_components p hf f5)
    (absent_of_foreign p hf 7 5 4 (by decide +kernel) f4) (f4_southeast p hf f4),upper⟩

end
#print axioms f4_top_exact
#print axioms two_inward_central
end N12Compact.Completion.OtherCases.C983

