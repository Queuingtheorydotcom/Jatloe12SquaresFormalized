import Compact.Completion.OtherCases.C983.F5TopOnlyPoints

/-! The actual left origin follows from a top-wall advance and the original
paired northwest corner. No southwest corner assignment is needed here. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem top_left_advance (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f3 : 3∈actual p 11) (g7 : 17∈actual p 6) :
    (owners p 11).Inside (36/25) 3 := by
  let T := pullSwap (pullY (pullX (owners p 11)))
  have box := container_pullSwap _ (container_pullY _ (container_pullX _ (owners_contained p 11)))
  have marker : (owners p 11).Inside 2 (1543/500) := by
    have h := seed_inside p hf 11 (2,1543/500) (by decide +kernel)
    norm_num at h
    exact h
  have anchor : (owners p 11).Inside (8/5) 3 := by
    have h := auxiliary_inside p 11 3 (by decide +kernel) f3
    simpa [auxPoints,fPoints,gPoints] using h
  have foreign : (owners p 6).Inside (113/50) 3 := by
    have h := auxiliary_inside p 6 17 (by decide +kernel) g7
    simpa [auxPoints,fPoints,gPoints] using h
  have west : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have advance := WallUpperMissingReach.point T (owners_side p 11) box
    (by dsimp only [T]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact marker)
    (by dsimp only [T]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact anchor)
    (by
      dsimp only [T]
      norm_num only [inside_pullSwap,inside_pullY,inside_pullX]
      exact fun h => owners_apart p hf 11 6 (by decide +kernel) _ _ ⟨h,foreign⟩)
    (by
      dsimp only [T]
      norm_num only [inside_pullSwap,inside_pullY,inside_pullX]
      exact fun h => owners_apart p hf 11 7 (by decide +kernel) _ _ ⟨h,west⟩)
  dsimp only [T] at advance
  norm_num only [inside_pullSwap,inside_pullY,inside_pullX] at advance
  exact advance

theorem left_origin_of_top_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f3 : 3∈actual p 11) (g7 : 17∈actual p 6) : (owners p 8).Inside 1 2 := by
  have topAnchor : (owners p 11).Inside (8/5) 3 := by
    have h := auxiliary_inside p 11 3 (by decide +kernel) f3
    simpa [auxPoints,fPoints,gPoints] using h
  have topPoint := CommonCases.OriginalOwners.horizontal_segment (owners p 11)
    (36/25) (8/5) 3 (3/2) (top_left_advance p hf f3 g7) topAnchor
    (by norm_num) (by norm_num) (by norm_num)
  let B := pullSwap (pullY (owners p 8))
  let K := pullSwap (pullY (owners p 4))
  have boxB := container_pullSwap _ (container_pullY _ (owners_contained p 8))
  have boxK := container_pullSwap _ (container_pullY _ (owners_contained p 4))
  have marker : (owners p 8).Inside (457/500) 2 := by
    have h := seed_inside p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have cornerMarker : (owners p 4).Inside (457/500) 3 := by
    have h := seed_inside p hf 4 (457/500,3) (by decide +kernel)
    norm_num at h
    exact h
  have cornerPoint : (owners p 4).Inside 1 3 := by
    have h := seed_inside p hf 4 (1,3) (by decide +kernel)
    norm_num at h
    exact h
  have missing : ¬(owners p 4).Inside (3/2) 3 :=
    fun h => owners_apart p hf 4 11 (by decide +kernel) _ _ ⟨h,topPoint⟩
  have origin := WallProfile.boundary_origin B K (457/500) (8/5)
    (owners_side p 8) (owners_same_side p 8 4)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullY]; exact marker)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullY]; exact (left_aux p hf).2)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY]; exact cornerMarker)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY]; exact cornerPoint)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY]; exact missing)
    (by
      intro x y h
      have hK : (owners p 4).Inside y (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY] using h.1
      have hB : (owners p 8).Inside y (4-x) := by
        simpa only [B,inside_pullSwap,inside_pullY] using h.2
      exact owners_apart p hf 4 8 (by decide +kernel) _ _ ⟨hK,hB⟩)
  dsimp only [B] at origin
  norm_num only [inside_pullSwap,inside_pullY] at origin
  exact origin

theorem left_full_bar_of_top_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f3 : 3∈actual p 11) (g7 : 17∈actual p 6) :
    ∀ y : ℝ,2≤y → y≤14/5 → (owners p 8).Inside 1 y := by
  intro y lower upper
  exact CommonCases.OriginalOwners.vertical_segment (owners p 8) 1 2 (14/5) y
    (left_origin_of_top_g7 p hf f3 g7) (left_advance p hf) (by norm_num) lower upper

theorem f5_left_full_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    ∀ y : ℝ,2≤y → y≤14/5 → (owners p 8).Inside 1 y := by
  have final := f5_final_central p hf f5
  apply left_full_bar_of_top_g7 p hf
  · rw [final.2.2.2]
    decide +kernel
  · rw [final.2.1]
    decide +kernel

end
#print axioms left_origin_of_top_g7
#print axioms f5_left_full_bar
end N12Compact.Completion.OtherCases.C983
