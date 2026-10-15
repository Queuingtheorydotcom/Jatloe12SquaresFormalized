import Compact.Completion.OtherCases.C983.F5TopOrigin
import Compact.Completion.OtherCases.TopOnlyExtension

/-! Both genuine corner/right-wall transfers and their universal F5 join.
The lower and upper corners remain the original paired squares throughout. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem right_origin_of_lower_aux (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f8 : 8∈actual p 10) : (owners p 10).Inside 3 2 := by
  let B := pullSwap (pullX (owners p 10))
  let K := pullSwap (pullX (owners p 2))
  have boxB := container_pullSwap _ (container_pullX _ (owners_contained p 10))
  have boxK := container_pullSwap _ (container_pullX _ (owners_contained p 2))
  have marker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 10).Inside 3 (87/50) := by
    have h := auxiliary_inside p 10 8 (by decide +kernel) f8
    simpa [auxPoints,fPoints,gPoints] using h
  have cornerMarker : (owners p 2).Inside (1543/500) 1 := by
    have h := seed_inside p hf 2 (1543/500,1) (by decide +kernel)
    norm_num at h
    exact h
  have cornerPoint : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have missing : ¬(owners p 2).Inside (5/2) 1 :=
    fun h => owners_apart p hf 2 9 (by decide +kernel) _ _
      ⟨h,bottom_bar p hf (5/2) (by norm_num) (by norm_num)⟩
  have origin := WallProfile.boundary_origin B K (457/500) (87/50)
    (owners_side p 10) (owners_same_side p 10 2)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullX]; exact marker)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullX]; exact inner)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullX]; exact cornerMarker)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullX]; exact cornerPoint)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullX]; exact missing)
    (by
      intro x y h
      have hK : (owners p 2).Inside (4-y) x := by
        simpa only [K,inside_pullSwap,inside_pullX] using h.1
      have hB : (owners p 10).Inside (4-y) x := by
        simpa only [B,inside_pullSwap,inside_pullX] using h.2
      exact owners_apart p hf 2 10 (by decide +kernel) _ _ ⟨hK,hB⟩)
  dsimp only [B] at origin
  norm_num only [inside_pullSwap,inside_pullX] at origin
  exact origin

theorem northeast_top_extension (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f7 : 7∈actual p 6) (noF5 : 5∉actual p 6)
    (topOrigin : (owners p 11).Inside 2 3)
    (southeastPoint : (owners p 5).Inside (5/2) 2) :
    (owners p 6).Inside (5/2) 3 := by
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
  exact TopOnlyExtension.point_original (owners p 6) (owners_side p 6) marker anchor missingL
    (fun h => owners_apart p hf 6 11 (by decide +kernel) _ _ ⟨h,topOrigin⟩)
    (fun h => owners_apart p hf 6 5 (by decide +kernel) _ _ ⟨h,southeastPoint⟩)

theorem right_origin_of_upper_extension (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (g9 : 19∈actual p 10) (extension : (owners p 6).Inside (5/2) 3) :
    (owners p 10).Inside 3 2 := by
  let B := pullSwap (pullY (pullX (owners p 10)))
  let K := pullSwap (pullY (pullX (owners p 3)))
  have boxB := container_pullSwap _ (container_pullY _ (container_pullX _ (owners_contained p 10)))
  have boxK := container_pullSwap _ (container_pullY _ (container_pullX _ (owners_contained p 3)))
  have marker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 10).Inside 3 (12/5) := by
    have h := auxiliary_inside p 10 19 (by decide +kernel) g9
    simpa [auxPoints,fPoints,gPoints] using h
  have cornerMarker : (owners p 3).Inside (1543/500) 3 := by
    have h := seed_inside p hf 3 (1543/500,3) (by decide +kernel)
    norm_num at h
    exact h
  have cornerPoint : (owners p 3).Inside 3 3 := by
    have h := seed_inside p hf 3 (3,3) (by decide +kernel)
    norm_num at h
    exact h
  have missing : ¬(owners p 3).Inside (5/2) 3 :=
    fun h => owners_apart p hf 3 6 (by decide +kernel) _ _ ⟨h,extension⟩
  have origin := WallProfile.boundary_origin B K (457/500) (8/5)
    (owners_side p 10) (owners_same_side p 10 3)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact marker)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact inner)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact cornerMarker)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact cornerPoint)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact missing)
    (by
      intro x y h
      have hK : (owners p 3).Inside (4-y) (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY,inside_pullX] using h.1
      have hB : (owners p 10).Inside (4-y) (4-x) := by
        simpa only [B,inside_pullSwap,inside_pullY,inside_pullX] using h.2
      exact owners_apart p hf 3 10 (by decide +kernel) _ _ ⟨hK,hB⟩)
  dsimp only [B] at origin
  norm_num only [inside_pullSwap,inside_pullY,inside_pullX] at origin
  exact origin

private theorem right_origin_cover_check :
    ∀ owned∈f5RightComponents,8∈owned ∨ 19∈owned := by decide +kernel

theorem f5_right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : (owners p 10).Inside 3 2 := by
  rcases right_origin_cover_check _ (f5_right_components p hf f5) with lower | upper
  · exact right_origin_of_lower_aux p hf lower
  · have exactUpper := f5_upper_of_right_g9 p hf f5 upper
    have f7 : 7∈actual p 6 := by rw [exactUpper.1]; decide +kernel
    have noF5 := absent_of_foreign p hf 7 6 5 (by decide +kernel) f5
    have extension := northeast_top_extension p hf f7 noF5
      (f5_top_origin p hf f5) (f5_southeast_crosspoint p hf f5)
    exact right_origin_of_upper_extension p hf upper extension

end
#print axioms right_origin_of_lower_aux
#print axioms right_origin_of_upper_extension
#print axioms f5_right_origin
end N12Compact.Completion.OtherCases.C983

