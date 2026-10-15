import Compact.Completion.OtherCases.C983.Entrance
import Compact.Completion.C981.WallAdvance
import Compact.Completion.CommonCases.OriginalOwners

/-! Unconditional actual C983 left and bottom wall bars. The singleton
corner seeds and central markers supply every foreign point separately.
Convexity is used only within the single displayed wall owner. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem left_labels : ∀ owned∈originalComponents 8,1∈owned ∧ 11∈owned := by
  decide +kernel

private theorem bottom_labels : ∀ owned∈originalComponents 9,6∈owned ∧ 15∈owned := by
  decide +kernel

theorem left_aux (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 1 (113/50) ∧ (owners p 8).Inside 1 (12/5) := by
  have labels := left_labels _ (original_actual_mem p hf 8)
  constructor
  · have point := auxiliary_inside p 8 1 (by decide +kernel) labels.1
    simpa [auxPoints,fPoints,gPoints] using point
  · have point := auxiliary_inside p 8 11 (by decide +kernel) labels.2
    simpa [auxPoints,fPoints,gPoints] using point

theorem bottom_aux (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (12/5) 1 ∧ (owners p 9).Inside (113/50) 1 := by
  have labels := bottom_labels _ (original_actual_mem p hf 9)
  constructor
  · have point := auxiliary_inside p 9 6 (by decide +kernel) labels.1
    simpa [auxPoints,fPoints,gPoints] using point
  · have point := auxiliary_inside p 9 15 (by decide +kernel) labels.2
    simpa [auxPoints,fPoints,gPoints] using point

theorem left_advance (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 1 (14/5) := by
  have marker : (owners p 8).Inside (457/500) 2 := by
    have h := seed_inside p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have low : (owners p 1).Inside 1 (87/50) := by
    have h := seed_inside p hf 1 (1,87/50) (by decide +kernel)
    norm_num at h
    exact h
  have seed : (owners p 1).Inside (19/25) (187/100) := by
    have h := seed_inside p hf 1 (19/25,187/100) (by decide +kernel)
    norm_num at h
    exact h
  have central : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  exact C981CompletionWallAdvance.point (owners p 8) (owners_side p 8) (owners_contained p 8)
    marker (left_aux p hf).2
    (fun h => owners_apart p hf 8 1 (by decide +kernel) _ _ ⟨h,low⟩)
    (fun h => owners_apart p hf 8 1 (by decide +kernel) _ _ ⟨h,seed⟩)
    (fun h => owners_apart p hf 8 7 (by decide +kernel) _ _ ⟨h,central⟩)

theorem bottom_advance (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (14/5) 1 := by
  have marker : (owners p 9).Inside 2 (457/500) := by
    have h := seed_inside p hf 9 (2,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have low : (owners p 0).Inside (87/50) 1 := by
    have h := seed_inside p hf 0 (87/50,1) (by decide +kernel)
    norm_num at h
    exact h
  have seed : (owners p 0).Inside (187/100) (19/25) := by
    have h := seed_inside p hf 0 (187/100,19/25) (by decide +kernel)
    norm_num at h
    exact h
  have central : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have missingLow : ¬(owners p 9).Inside (87/50) 1 :=
    fun h => owners_apart p hf 9 0 (by decide +kernel) _ _ ⟨h,low⟩
  have missingSeed : ¬(owners p 9).Inside (187/100) (19/25) :=
    fun h => owners_apart p hf 9 0 (by decide +kernel) _ _ ⟨h,seed⟩
  have missingCentral : ¬(owners p 9).Inside (47/20) (33/20) :=
    fun h => owners_apart p hf 9 5 (by decide +kernel) _ _ ⟨h,central⟩
  have point := C981CompletionWallAdvance.point (pullSwap (owners p 9))
    (owners_side p 9) (container_pullSwap _ (owners_contained p 9))
    (by simpa only [inside_pullSwap] using marker)
    (by simpa only [inside_pullSwap] using (bottom_aux p hf).1)
    (by simpa only [inside_pullSwap] using missingLow)
    (by simpa only [inside_pullSwap] using missingSeed)
    (by simpa only [inside_pullSwap] using missingCentral)
  simpa only [inside_pullSwap] using point

theorem left_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∀ y : ℝ,113/50 ≤ y → y ≤ 14/5 → (owners p 8).Inside 1 y := by
  intro y lower upper
  exact CommonCases.OriginalOwners.vertical_segment (owners p 8) 1 (113/50) (14/5) y
    (left_aux p hf).1 (left_advance p hf) (by norm_num) lower upper

theorem bottom_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∀ x : ℝ,113/50 ≤ x → x ≤ 14/5 → (owners p 9).Inside x 1 := by
  intro x lower upper
  exact CommonCases.OriginalOwners.horizontal_segment (owners p 9) (113/50) (14/5) 1 x
    (bottom_aux p hf).2 (bottom_advance p hf) (by norm_num) lower upper

end
#print axioms left_bar
#print axioms bottom_bar
end N12Compact.Completion.OtherCases.C983

