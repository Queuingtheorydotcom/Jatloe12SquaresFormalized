import Compact.Completion.OtherCases.C983.MergedTopExclusion
import Compact.Completion.OtherCases.C983.MergedG6Exclusion
import Compact.Completion.OtherCases.C983.F4CentralEntrance
import Compact.Completion.OtherCases.MergedNearTopPoint

/-! Initial merged-owner reductions from the original C983 entrance.
Only one local component list is inspected at a time; each geometric
deletion is supplied separately by its actual owned and foreign points. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem merged_g7_check :
    ∀ owned∈(domains 7).allowed,17∉owned := by decide +kernel

theorem merged_no_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    17∉actual p 7 :=
  merged_g7_check _ (actual_mem p hf 7)

theorem merged_g4_implies_f5 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (g4 : 14∈actual p 7) : 5∈actual p 7 := by
  have marker : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have top : (owners p 7).Inside (87/50) 3 := by
    have h := auxiliary_inside p 7 14 (by decide +kernel) g4
    simpa [auxPoints,fPoints,gPoints] using h
  have point := MergedNearTopPoint.point (owners p 7) (owners_side p 7) (owners_cap p 7)
    marker top
    (fun h => owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨h,(left_aux p hf).1⟩)
  have exactPoint := point_exact p 7 5 (by decide +kernel)
  apply exactPoint.mp
  simpa [auxPoints,fPoints,gPoints] using point

theorem merged_f4_no_g4 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 14∉actual p 7 := by
  have top : 14∈actual p 11 := by rw [f4_top_exact p hf f4]; decide +kernel
  exact absent_of_foreign p hf 11 7 14 (by decide +kernel) top

def mergedInitialComponents : List (Finset Nat) :=
  [{13},{4,13},{5,13},{4,5,13},{5,13,14}]

private theorem merged_reduction_check :
    ∀ owned∈originalComponents 7,3∉owned → 16∉owned → 17∉owned →
      (14∈owned → 5∈owned) → (4∈owned → 14∉owned) →
      owned∈mergedInitialComponents := by decide +kernel

theorem merged_initial_components (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : actual p 7∈mergedInitialComponents :=
  merged_reduction_check _ (original_actual_mem p hf 7)
    (merged_no_f3 p hf) (merged_no_g6 p hf) (merged_no_g7 p hf)
    (merged_g4_implies_f5 p hf) (merged_f4_no_g4 p hf)

end
#print axioms merged_initial_components
end N12Compact.Completion.OtherCases.C983

