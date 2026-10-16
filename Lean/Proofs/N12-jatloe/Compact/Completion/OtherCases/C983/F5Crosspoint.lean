import Compact.Completion.OtherCases.C983.F5Filters
import Compact.Completion.OtherCases.F4PointTransfers
import Compact.Completion.C981.Crosspoint

/-! The actual southeast horizontal crosspoint throughout merged-F5.
When F4 is absent it remains an exact local absence, never a guessed owner. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem southeast_no_f4_check :
    ∀ owned∈f5SoutheastComponents,4∉owned → 8∈owned := by decide +kernel

theorem f5_southeast_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : (owners p 5).Inside (5/2) 2 := by
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have elbow : (owners p 5).Inside (113/50) 2 := by
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f5_southeast_g6 p hf f5)
    simpa [auxPoints,fPoints,gPoints] using h
  have bottomLow := bottom_bar p hf (12/5) (by norm_num) (by norm_num)
  have bottomHigh := bottom_bar p hf (5/2) (by norm_num) (by norm_num)
  have noHigh : ¬(owners p 5).Inside (5/2) 1 :=
    fun h => owners_apart p hf 5 9 (by decide +kernel) _ _ ⟨h,bottomHigh⟩
  by_cases f4 : 4∈actual p 5
  · have inward : (owners p 5).Inside 2 (87/50) := by
      have h := auxiliary_inside p 5 4 (by decide +kernel) f4
      simpa [auxPoints,fPoints,gPoints] using h
    have southwest : (owners p 7).Inside (33/20) (33/20) := by
      have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
      norm_num at h
      exact h
    have northeast : (owners p 6).Inside (47/20) (47/20) := by
      have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
      norm_num at h
      exact h
    have noSW : ¬(owners p 5).Inside (33/20) (33/20) :=
      fun h => owners_apart p hf 5 7 (by decide +kernel) _ _ ⟨h,southwest⟩
    have noNE : ¬(owners p 5).Inside (47/20) (47/20) :=
      fun h => owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨h,northeast⟩
    have noLow : ¬(owners p 5).Inside (12/5) 1 :=
      fun h => owners_apart p hf 5 9 (by decide +kernel) _ _ ⟨h,bottomLow⟩
    have point := C981CompletionCrosspoint.point (pullSwap (pullY (owners p 5))) (owners_side p 5)
      (by norm_num only [inside_pullSwap,inside_pullY]; exact elbow)
      (by norm_num only [inside_pullSwap,inside_pullY]; exact inward)
      (by norm_num only [inside_pullSwap,inside_pullY]; exact marker)
      (by norm_num only [inside_pullSwap,inside_pullY]; exact noSW)
      (by norm_num only [inside_pullSwap,inside_pullY]; exact noNE)
      (by norm_num only [inside_pullSwap,inside_pullY]; exact noLow)
      (by norm_num only [inside_pullSwap,inside_pullY]; exact noHigh)
    norm_num only [inside_pullSwap,inside_pullY] at point
    exact point
  · have f8 := southeast_no_f4_check _ (f5_southeast_components p hf f5) f4
    have outer : (owners p 5).Inside 3 (87/50) := by
      have h := auxiliary_inside p 5 8 (by decide +kernel) f8
      simpa [auxPoints,fPoints,gPoints] using h
    have noF4 : ¬(owners p 5).Inside 2 (87/50) := by
      have h := missing_auxiliary p 5 4 (by decide +kernel) f4
      simpa [auxPoints,fPoints,gPoints] using h
    exact F4PointTransfers.horizontal_original (owners p 5) (owners_side p 5)
      marker elbow outer noF4 noHigh

end
#print axioms f5_southeast_crosspoint
end N12Compact.Completion.OtherCases.C983

