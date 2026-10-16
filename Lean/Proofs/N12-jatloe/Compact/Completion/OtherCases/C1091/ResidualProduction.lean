import Compact.Completion.OtherCases.C1091.DirectDomains
import Compact.Completion.OtherCases.C1091.ResidualEnding
import Compact.Completion.OtherCases.C1089.ContinuousActual
import Compact.Completion.OtherCases.C1089.ContinuousBottom
import Compact.Completion.C981.Crosspoint
import Compact.Geometry.WallUpperMissingReach

/-! Authentic C1091 residual producer. Six literal points are the
remaining entrance boundary; all markers, auxiliary component cuts,
bottom reach, right-center sign/origin/bar, two southeast crosspoints,
and southeast center are proved here. The absent C1091-PROGRESS chapter
is not treated as a certificate for those six earlier point producers
or the exclusion of its other sectors. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1091.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

structure ResidualEntrance (q : Fin 12 → OpenSquare) : Prop where
  cornerSW : (q 0).Inside 1 1
  mergedLow : (q 4).Inside 1 (87/50)
  southeastF4 : (q 5).Inside 2 (87/50)
  southeastG6 : (q 5).Inside (113/50) 2
  northeastF9 : (q 6).Inside 3 (113/50)
  northwestF3 : (q 7).Inside (8/5) 3

theorem residual_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (h : ResidualEntrance (owners p)) : Residual.Input (owners p) := by
  have merged := merged_markers p hf
  have se : (owners p 5).Inside (47/20) (33/20) := by
    have own := seed p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at own
    exact own
  have ne : (owners p 6).Inside (47/20) (47/20) := by
    have own := seed p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at own
    exact own
  have nw : (owners p 7).Inside (33/20) (47/20) := by
    have own := seed p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at own
    exact own
  have leftMarker : (owners p 8).Inside (457/500) 2 := by
    have own := seed p hf 8 (457/500,2) (by decide +kernel)
    norm_num at own
    exact own
  have bottomMarker : (owners p 9).Inside 2 (457/500) := by
    have own := seed p hf 9 (2,457/500) (by decide +kernel)
    norm_num at own
    exact own
  have rightMarker : (owners p 10).Inside (1543/500) 2 := by
    have own := seed p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at own
    exact own
  have topMarker : (owners p 11).Inside 2 (1543/500) := by
    have own := seed p hf 11 (2,1543/500) (by decide +kernel)
    norm_num at own
    exact own
  have singletonFar : (owners p 0).Inside (87/50) 1 := by
    have own := seed p hf 0 (87/50,1) (by decide +kernel)
    norm_num at own
    exact own
  have singletonSeed : (owners p 0).Inside (187/100) (19/25) := by
    have own := seed p hf 0 (187/100,19/25) (by decide +kernel)
    norm_num at own
    exact own
  have seCorner : (owners p 1).Inside 3 1 := by
    have own := seed p hf 1 (3,1) (by decide +kernel)
    norm_num at own
    exact own
  have seCornerMarker : (owners p 1).Inside (1543/500) 1 := by
    have own := seed p hf 1 (1543/500,1) (by decide +kernel)
    norm_num at own
    exact own
  have neCorner : (owners p 2).Inside 3 3 := by
    have own := seed p hf 2 (3,3) (by decide +kernel)
    norm_num at own
    exact own
  have foreign (i j : Fin 12) (different : i≠j) (x y : ℝ)
      (point : (owners p j).Inside x y) : ¬(owners p i).Inside x y :=
    fun own => apart p hf i j different x y ⟨own,point⟩
  have left := DirectDomains.left_pair p hf h.mergedLow
  have bottomFar := DirectDomains.bottom_far p hf h.southeastF4
  have right := DirectDomains.right_pair p hf h.northeastF9
  have top := DirectDomains.top_pair p hf h.northwestF3
  have bottomReach := C1089.ContinuousBottom.reach_of_far (owners p 9)
    (side p 9) (box p 9) bottomMarker bottomFar
    (foreign 9 0 (by decide) _ _ singletonFar)
    (foreign 9 0 (by decide) _ _ singletonSeed)
    (foreign 9 5 (by decide) _ _ se)
  let R := pullX (pullY (owners p 10))
  have rbox : InsideContainer R := container_pullX _ (container_pullY _ (box p 10))
  have rMarker : R.Inside (457/500) 2 := by
    norm_num [R,inside_pullX,inside_pullY]
    exact rightMarker
  have rHigh : R.Inside 1 (12/5) := by
    norm_num [R,inside_pullX,inside_pullY]
    exact right.2
  have rMissingLow : ¬R.Inside 1 (87/50) := by
    norm_num [R,inside_pullX,inside_pullY]
    exact foreign 10 6 (by decide) _ _ h.northeastF9
  have rMissingCenter : ¬R.Inside (33/20) (47/20) := by
    norm_num [R,inside_pullX,inside_pullY]
    exact foreign 10 5 (by decide) _ _ se
  have rightSign : centerY (owners p 10)≤2 := by
    have high := WallLowerCenterBarrier.center_above R (side p 10) rbox
      rMarker rHigh rMissingLow rMissingCenter
    simp only [R,center_pullX_y,center_pullY_y] at high
    linarith only [high]
  have rightLow : (owners p 10).Inside 3 (36/25) := by
    have point := WallUpperMissingReach.point R (side p 10) rbox
      rMarker rHigh rMissingLow rMissingCenter
    norm_num [R,inside_pullX,inside_pullY] at point
    exact point
  have centers := C1089.ContinuousActual.southeast (owners p) (side p) (same p)
    (box p) (apart p hf) se h.southeastF4 h.southeastG6 merged.2
    rightMarker right.1 rightSign bottomMarker bottomFar singletonFar seCornerMarker seCorner
  have rightBar : ∀ y : ℝ,36/25≤y → y≤2 → (owners p 10).Inside 3 y := by
    intro y low high
    exact CommonCases.OriginalOwners.vertical_segment _ _ _ _ _ rightLow centers.2
      (by norm_num) low high
  have south : (owners p 5).Inside 2 (3/2) := by
    have point := C981CompletionCrosspoint.point (pullY (owners p 5)) (side p 5)
      (by norm_num [inside_pullY]; exact h.southeastF4)
      (by norm_num [inside_pullY]; exact h.southeastG6)
      (by norm_num [inside_pullY]; exact se)
      (by norm_num [inside_pullY]; exact foreign 5 6 (by decide) _ _ ne)
      (by norm_num [inside_pullY]; exact foreign 5 4 (by decide) _ _ merged.2)
      (by norm_num [inside_pullY]; exact foreign 5 10 (by decide) _ _ (rightBar (8/5) (by norm_num) (by norm_num)))
      (by norm_num [inside_pullY]; exact foreign 5 10 (by decide) _ _ (rightBar (3/2) (by norm_num) (by norm_num)))
    norm_num [inside_pullY] at point
    exact point
  have east : (owners p 5).Inside (5/2) 2 := by
    have point := C981CompletionCrosspoint.point (pullSwap (pullY (owners p 5))) (side p 5)
      (by norm_num [inside_pullSwap,inside_pullY]; exact h.southeastG6)
      (by norm_num [inside_pullSwap,inside_pullY]; exact h.southeastF4)
      (by norm_num [inside_pullSwap,inside_pullY]; exact se)
      (by norm_num [inside_pullSwap,inside_pullY]; exact foreign 5 4 (by decide) _ _ merged.2)
      (by norm_num [inside_pullSwap,inside_pullY]; exact foreign 5 6 (by decide) _ _ ne)
      (by norm_num [inside_pullSwap,inside_pullY]; exact foreign 5 9 (by decide) _ _ (bottomReach.2.2 (12/5) (by norm_num) (by norm_num)))
      (by norm_num [inside_pullSwap,inside_pullY]; exact foreign 5 9 (by decide) _ _ (bottomReach.2.2 (5/2) (by norm_num) (by norm_num)))
    norm_num [inside_pullSwap,inside_pullY] at point
    exact point
  exact {
    side := side p
    cap := cap p
    same := same p
    box := box p
    apart := apart p hf
    cornerSW := h.cornerSW
    singletonFar := singletonFar
    cornerNE := neCorner
    mergedLeft := merged.1
    mergedMarker := merged.2
    mergedLow := h.mergedLow
    southeastMarker := se
    center := centers.1
    south := south
    east := east
    northeastMarker := ne
    northeastF9 := h.northeastF9
    northeastG9 := DirectDomains.northeast_outer p hf h.southeastG6 top.2
    northwestMarker := nw
    northwestF3 := h.northwestF3
    northwestG := DirectDomains.northwest_cover p hf left.2
    leftMarker := leftMarker
    leftF1 := left.1
    leftG1 := left.2
    bottomBar := bottomReach.2.2
    rightMarker := rightMarker
    rightBar := rightBar
    topMarker := topMarker
    topF7 := top.1 }

theorem impossible_of_residual_entrance (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (h : ResidualEntrance (owners p)) : False :=
  Residual.impossible (owners p) (residual_input p hf h)

end
#print axioms residual_input
#print axioms impossible_of_residual_entrance
end N12Compact.Completion.OtherCases.C1091.OriginalData
