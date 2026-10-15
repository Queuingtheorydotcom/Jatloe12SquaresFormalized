import Compact.Completion.OtherCases.C983.F4OutwardJoin
import Compact.Completion.OtherCases.F4PointTransfers
import Compact.Completion.OtherCases.ElbowPoint

/-! Complete actual central and peripheral reduction in the C983 F4
branch. This joins every local support and point proof to the original
component entrance; no full ownership-vector catalogue is a premise. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f4_southeast_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : (owners p 5).Inside (5/2) 2 := by
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have elbow : (owners p 5).Inside (113/50) 2 := by
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f4_southeast_g6 p hf f4)
    simpa [auxPoints,fPoints,gPoints] using h
  have outer : (owners p 5).Inside 3 (87/50) := by
    have h := auxiliary_inside p 5 8 (by decide +kernel) (f4_southeast p hf f4)
    simpa [auxPoints,fPoints,gPoints] using h
  have foreignF : (owners p 7).Inside 2 (87/50) := by
    have h := auxiliary_inside p 7 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  exact F4PointTransfers.horizontal_original (owners p 5) (owners_side p 5) marker elbow outer
    (fun h => owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨h,foreignF⟩)
    (fun h => owners_apart p hf 5 9 (by decide +kernel) _ _
      ⟨h,bottom_bar p hf (5/2) (by norm_num) (by norm_num)⟩)

private theorem northeast_candidates_check : ∀ owned∈originalComponents 6,
    4∉owned → 13∉owned → 8∉owned → 9∉owned → 19∉owned → 16∉owned →
      3∉owned → 14∉owned → owned={5,17} ∨ owned={7,17} ∨ owned={5,7,17} := by
  decide +kernel

theorem f4_northeast_candidates (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) :
    actual p 6={5,17} ∨ actual p 6={7,17} ∨ actual p 6={5,7,17} := by
  have top := f4_top p hf f4
  have right := f4_right p hf f4
  exact northeast_candidates_check _ (original_actual_mem p hf 6)
    (absent_of_foreign p hf 7 6 4 (by decide +kernel) f4)
    (absent_of_foreign p hf 7 6 13 (by decide +kernel) (merged_g3 p hf))
    (absent_of_foreign p hf 5 6 8 (by decide +kernel) (f4_southeast p hf f4))
    (absent_of_foreign p hf 10 6 9 (by decide +kernel) right.1)
    (absent_of_foreign p hf 10 6 19 (by decide +kernel) right.2)
    (absent_of_foreign p hf 5 6 16 (by decide +kernel) (f4_southeast_g6 p hf f4))
    (absent_of_foreign p hf 11 6 3 (by decide +kernel) top.1)
    (absent_of_foreign p hf 11 6 14 (by decide +kernel) top.2)

theorem f4_northeast_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 7∈actual p 6 := by
  by_contra noF7
  have f5 : 5∈actual p 6 := by
    rcases f4_northeast_candidates p hf f4 with h | h | h
    · rw [h]; decide +kernel
    · exact False.elim (noF7 (by rw [h]; decide +kernel))
    · exact False.elim (noF7 (by rw [h]; decide +kernel))
  have marker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have inward : (owners p 6).Inside 2 (113/50) := by
    have h := auxiliary_inside p 6 5 (by decide +kernel) f5
    simpa [auxPoints,fPoints,gPoints] using h
  have upper : (owners p 6).Inside (113/50) 3 := by
    have h := auxiliary_inside p 6 17 (by decide +kernel) (f4_northeast_g7 p hf f4)
    simpa [auxPoints,fPoints,gPoints] using h
  have missingOuter : ¬(owners p 6).Inside (12/5) 3 := by
    have h := missing_auxiliary p 6 7 (by decide +kernel) noF7
    simpa [auxPoints,fPoints,gPoints] using h
  have northwest : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have top : (owners p 11).Inside 2 (1543/500) := by
    have h := seed_inside p hf 11 (2,1543/500) (by decide +kernel)
    norm_num at h
    exact h
  have missingN : ¬(owners p 6).Inside (33/20) (47/20) :=
    fun h => owners_apart p hf 6 7 (by decide +kernel) _ _ ⟨h,northwest⟩
  have missingR : ¬(owners p 6).Inside 2 (1543/500) :=
    fun h => owners_apart p hf 6 11 (by decide +kernel) _ _ ⟨h,top⟩
  have points := ElbowPoint.points_original (pullSwap (pullX (owners p 6))) (owners_side p 6)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact marker)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact inward)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact upper)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact missingN)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact missingOuter)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact missingR)
  have northPoint : (owners p 6).Inside (5/2) 2 := by
    have point := points.1
    norm_num only [inside_pullSwap,inside_pullX] at point
    exact point
  exact owners_apart p hf 5 6 (by decide +kernel) _ _
    ⟨f4_southeast_crosspoint p hf f4,northPoint⟩

theorem f4_southeast_avoids_f5 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 5∉actual p 5 := by
  intro southeastF5
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have elbow : (owners p 5).Inside (113/50) 2 := by
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f4_southeast_g6 p hf f4)
    simpa [auxPoints,fPoints,gPoints] using h
  have outer : (owners p 5).Inside 3 (87/50) := by
    have h := auxiliary_inside p 5 8 (by decide +kernel) (f4_southeast p hf f4)
    simpa [auxPoints,fPoints,gPoints] using h
  have upper : (owners p 5).Inside 2 (113/50) := by
    have h := auxiliary_inside p 5 5 (by decide +kernel) southeastF5
    simpa [auxPoints,fPoints,gPoints] using h
  have foreignF : (owners p 7).Inside 2 (87/50) := by
    have h := auxiliary_inside p 7 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  have lowerPoint := F4PointTransfers.upper_original (owners p 5) (owners_side p 5)
    marker elbow outer upper
    (fun h => owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨h,foreignF⟩)
  have upperPoint := northeast_upper_point p hf (f4_northeast_f7 p hf f4)
    (absent_of_foreign p hf 5 6 5 (by decide +kernel) southeastF5)
    (f4_top_origin p hf f4) (f4_right_bar p hf f4)
  exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨lowerPoint,upperPoint⟩

private theorem southeast_final_check : ∀ owned∈originalComponents 5,
    4∉owned → 9∉owned → 5∉owned → 8∈owned → 16∈owned →
      owned={8,16} ∨ owned={8,16,18} := by decide +kernel

theorem f4_southeast_final (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : actual p 5={8,16} ∨ actual p 5={8,16,18} :=
  southeast_final_check _ (original_actual_mem p hf 5)
    (absent_of_foreign p hf 7 5 4 (by decide +kernel) f4)
    (absent_of_foreign p hf 10 5 9 (by decide +kernel) (f4_right p hf f4).1)
    (f4_southeast_avoids_f5 p hf f4) (f4_southeast p hf f4) (f4_southeast_g6 p hf f4)

theorem f4_northeast_final (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : actual p 6={7,17} ∨ actual p 6={5,7,17} := by
  rcases f4_northeast_candidates p hf f4 with first | second | third
  · have member := f4_northeast_f7 p hf f4
    rw [first] at member
    norm_num at member
  · exact Or.inl second
  · exact Or.inr third

private theorem right_final_check : ∀ owned∈originalComponents 10,
    8∉owned → 16∉owned → 7∉owned → owned={9,19} := by decide +kernel

theorem f4_right_final (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : actual p 10={9,19} :=
  right_final_check _ (original_actual_mem p hf 10)
    (absent_of_foreign p hf 5 10 8 (by decide +kernel) (f4_southeast p hf f4))
    (absent_of_foreign p hf 5 10 16 (by decide +kernel) (f4_southeast_g6 p hf f4))
    (absent_of_foreign p hf 6 10 7 (by decide +kernel) (f4_northeast_f7 p hf f4))

end
#print axioms f4_southeast_final
#print axioms f4_northeast_final
#print axioms f4_right_final
end N12Compact.Completion.OtherCases.C983

