import Compact.Completion.OtherCases.C983.F4Origins
import Compact.Completion.OtherCases.OutwardBarPoint
import Compact.Completion.OtherCases.UpperBarPoint
import Compact.Completion.OtherCases.InwardTopPoint
import Compact.Completion.C1092.MixedSpan
import Compact.Completion.C981.OutwardAnchor

/-! The sharp single-square theorems instantiated with the original C983
owners. Every foreign segment remains in its one named actual owner. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem missing_auxiliary (p : NormalizedPacking) (i : Fin 12) (j : Nat)
    (bound : j<20) (missing : j∉actual p i) :
    ¬(owners p i).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 :=
  fun h => missing ((point_exact p i j bound).mp h)

/-- The actual southeast outward square reaches the sharp point, for
either of its physical orientations before canonical face reindexing. -/
theorem southeast_outward_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f8 : 8∈actual p 5) (g8 : 18∈actual p 5) (noG6 : 16∉actual p 5) :
    (owners p 5).Inside (101/40) (17/8) := by
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have outward : (owners p 5).Inside 3 (87/50) := by
    have h := auxiliary_inside p 5 8 (by decide +kernel) f8
    simpa [auxPoints,fPoints,gPoints] using h
  have upper : (owners p 5).Inside 3 (8/5) := by
    have h := auxiliary_inside p 5 18 (by decide +kernel) g8
    simpa [auxPoints,fPoints,gPoints] using h
  have missingG : ¬(owners p 5).Inside (113/50) 2 := by
    have h := missing_auxiliary p 5 16 (by decide +kernel) noG6
    simpa [auxPoints,fPoints,gPoints] using h
  have right : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have corner : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have cornerMarker : (owners p 2).Inside (1543/500) 1 := by
    have h := seed_inside p hf 2 (1543/500,1) (by decide +kernel)
    norm_num at h
    exact h
  have missingR : ¬(owners p 5).Inside (1543/500) 2 :=
    fun h => owners_apart p hf 5 10 (by decide +kernel) _ _ ⟨h,right⟩
  have missingP : ¬(owners p 5).Inside 3 1 :=
    fun h => owners_apart p hf 5 2 (by decide +kernel) _ _ ⟨h,corner⟩
  have missingH : ¬(owners p 5).Inside (1543/500) 1 :=
    fun h => owners_apart p hf 5 2 (by decide +kernel) _ _ ⟨h,cornerMarker⟩
  have point := OutwardBarPoint.point_original (pullY (owners p 5)) (owners_side p 5)
    (by norm_num only [inside_pullY]; exact marker)
    (by norm_num only [inside_pullY]; exact outward)
    (by norm_num only [inside_pullY]; exact upper)
    (by norm_num only [inside_pullY]; exact missingG)
    (by norm_num only [inside_pullY]; exact missingR)
    (by norm_num only [inside_pullY]; exact missingP)
    (by norm_num only [inside_pullY]; exact missingH)
    (by
      intro z lower upper h
      have own : (owners p 5).Inside z 1 := by
        norm_num only [inside_pullY] at h
        exact h
      exact owners_apart p hf 5 9 (by decide +kernel) z 1
        ⟨own,bottom_bar p hf z lower upper⟩)
  norm_num only [inside_pullY] at point
  exact point

theorem northeast_upper_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f7 : 7∈actual p 6) (noF5 : 5∉actual p 6)
    (topOrigin : (owners p 11).Inside 2 3)
    (rightBar : ∀ y : ℝ,113/50≤y → y≤64/25 → (owners p 10).Inside 3 y) :
    (owners p 6).Inside (101/40) (17/8) := by
  have marker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have anchor : (owners p 6).Inside (12/5) 3 := by
    have h := auxiliary_inside p 6 7 (by decide +kernel) f7
    simpa [auxPoints,fPoints,gPoints] using h
  have missingL : ¬(owners p 6).Inside 2 (113/50) := by
    have h := missing_auxiliary p 6 5 (by decide +kernel) noF5
    simpa [auxPoints,fPoints,gPoints] using h
  have corner : (owners p 3).Inside 3 3 := by
    have h := seed_inside p hf 3 (3,3) (by decide +kernel)
    norm_num at h
    exact h
  exact UpperBarPoint.point_original (owners p 6) (owners_side p 6) marker anchor missingL
    (fun h => owners_apart p hf 6 11 (by decide +kernel) _ _ ⟨h,topOrigin⟩)
    (fun h => owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨h,corner⟩)
    (fun y lower upper h => owners_apart p hf 6 10 (by decide +kernel) _ _
      ⟨h,rightBar y lower upper⟩)

theorem northeast_inward_top_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 6) (g6 : 16∈actual p 6) (f7 : 7∈actual p 6)
    (noG7 : 17∉actual p 6) : (owners p 6).Inside (101/40) (17/8) := by
  have marker : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have inward : (owners p 6).Inside 2 (113/50) := by
    have h := auxiliary_inside p 6 5 (by decide +kernel) f5
    simpa [auxPoints,fPoints,gPoints] using h
  have elbow : (owners p 6).Inside (113/50) 2 := by
    have h := auxiliary_inside p 6 16 (by decide +kernel) g6
    simpa [auxPoints,fPoints,gPoints] using h
  have top : (owners p 6).Inside (12/5) 3 := by
    have h := auxiliary_inside p 6 7 (by decide +kernel) f7
    simpa [auxPoints,fPoints,gPoints] using h
  have missingF : ¬(owners p 6).Inside (113/50) 3 := by
    have h := missing_auxiliary p 6 17 (by decide +kernel) noG7
    simpa [auxPoints,fPoints,gPoints] using h
  have northwest : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have southeast : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  exact InwardTopPoint.point_original (owners p 6) (owners_side p 6)
    marker inward elbow top missingF
    (fun h => owners_apart p hf 6 7 (by decide +kernel) _ _ ⟨h,northwest⟩)
    (fun h => owners_apart p hf 6 5 (by decide +kernel) _ _ ⟨h,southeast⟩)

theorem northeast_mixed_exclusion (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (g6 : 16∈actual p 6) (f7 : 7∈actual p 6)
    (noF5 : 5∉actual p 6) (noG7 : 17∉actual p 6)
    (f9 : 9∈actual p 10) (g9 : 19∈actual p 10) : False := by
  have elbow : (owners p 6).Inside (113/50) 2 := by
    have h := auxiliary_inside p 6 16 (by decide +kernel) g6
    simpa [auxPoints,fPoints,gPoints] using h
  have top : (owners p 6).Inside (12/5) 3 := by
    have h := auxiliary_inside p 6 7 (by decide +kernel) f7
    simpa [auxPoints,fPoints,gPoints] using h
  have missingD : ¬(owners p 6).Inside 2 (113/50) := by
    have h := missing_auxiliary p 6 5 (by decide +kernel) noF5
    simpa [auxPoints,fPoints,gPoints] using h
  have missingH : ¬(owners p 6).Inside (113/50) 3 := by
    have h := missing_auxiliary p 6 17 (by decide +kernel) noG7
    simpa [auxPoints,fPoints,gPoints] using h
  have rightLow : (owners p 10).Inside 3 (113/50) := by
    have h := auxiliary_inside p 10 9 (by decide +kernel) f9
    simpa [auxPoints,fPoints,gPoints] using h
  have rightHigh : (owners p 10).Inside 3 (12/5) := by
    have h := auxiliary_inside p 10 19 (by decide +kernel) g9
    simpa [auxPoints,fPoints,gPoints] using h
  have missingF : ¬(owners p 6).Inside 3 (113/50) :=
    fun h => owners_apart p hf 6 10 (by decide +kernel) _ _ ⟨h,rightLow⟩
  have missingT : ¬(owners p 6).Inside 3 (12/5) :=
    fun h => owners_apart p hf 6 10 (by decide +kernel) _ _ ⟨h,rightHigh⟩
  exact C1092MixedSpan.impossible (pullSwap (pullX (owners p 6))) (owners_side p 6)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact elbow)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact top)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact missingD)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact missingH)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact missingF)
    (by norm_num only [inside_pullSwap,inside_pullX]; exact missingT)

theorem southeast_inward_outward_exclusion (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 5) (g8 : 18∈actual p 5) (noG6 : 16∉actual p 5) : False := by
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have inward : (owners p 5).Inside 2 (87/50) := by
    have h := auxiliary_inside p 5 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  have outward : (owners p 5).Inside 3 (8/5) := by
    have h := auxiliary_inside p 5 18 (by decide +kernel) g8
    simpa [auxPoints,fPoints,gPoints] using h
  have missingG : ¬(owners p 5).Inside (113/50) 2 := by
    have h := missing_auxiliary p 5 16 (by decide +kernel) noG6
    simpa [auxPoints,fPoints,gPoints] using h
  have corner : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have wall : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  exact C981CompletionOutwardAnchor.impossible (owners p 5) (owners_side p 5)
    marker inward outward
    (fun h => owners_apart p hf 5 2 (by decide +kernel) _ _ ⟨h,corner⟩)
    (fun h => owners_apart p hf 5 10 (by decide +kernel) _ _ ⟨h,wall⟩)
    missingG
    (fun z lower upper h => owners_apart p hf 5 9 (by decide +kernel) _ _
      ⟨h,bottom_bar p hf z lower upper⟩)

end
#print axioms southeast_outward_point
#print axioms northeast_mixed_exclusion
#print axioms southeast_inward_outward_exclusion
end N12Compact.Completion.OtherCases.C983

