import Compact.Completion.C1092.MPPMOmissionCenter
import Compact.Completion.C1092.InwardCenterDiagonal
import Compact.Completion.C1092.MixedWideCrosspoint
import Compact.Completion.C981.Crosspoint

/-! Genuine point core and full strict rectangle for the MPPM
bottom-omission owner, retaining the actual wide wall's center direction. -/
namespace N12Compact.C1092MPPMPointCore
open S12 S12Pilot C1092WallCycle C1092MPPMEntrance C1092RigidCharts
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_cap (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side≤1001/1000 := by
  change (p.square _).side≤1001/1000
  rw [p.congruent]
  exact p.side_le

private def chart (q : OpenSquare) : OpenSquare := translate (pullSwap (pullY q)) 2 2

private theorem inside_chart (q : OpenSquare) (x y : ℝ) :
    (chart q).Inside x y ↔ q.Inside (2+y) (2-x) := by
  change (translate (pullSwap (pullY q)) 2 2).Inside x y ↔ _
  rw [inside_translate,inside_pullSwap,inside_pullY]
  rw [show y+2=2+y by ring,show 4-(x+2)=2-x by ring]

private theorem center_chart (q : OpenSquare) : centerY (chart q)=centerX q-2 := by
  dsimp [chart,translate,pullSwap,pullY,centerY,centerX]
  nlinarith only [q.unit_normal]

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem right_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 10).Inside 3 (3/2) := by
  have h := inside_segment (owners p 10) 3 (36/25) 3 (8/5) (3/8)
    (C1092MPPMOmissionCenter.right_far p hf hb omitted)
    (omitted_bottom_neighbors p hf hb omitted).2.2 (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem bottom_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 5).Inside 2 (3/2) := by
  have inward := omitted_bottom_inward p hf hb omitted
  have neighbor := omitted_bottom_neighbors p hf hb omitted
  have m5 : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have m4 : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have m6 : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have h := C981CompletionCrosspoint.point (pullY (owners p 5)) (side_gt p 5)
    (by norm_num [inside_pullY]; exact inward.1)
    (by norm_num [inside_pullY]; exact inward.2)
    (by norm_num [inside_pullY]; exact m5)
    (by
      norm_num [inside_pullY]
      exact fun h => owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,m6⟩)
    (by
      norm_num [inside_pullY]
      exact fun h => owners_disjoint p hf 5 4 (by decide) _ _ ⟨h,m4⟩)
    (by
      norm_num [inside_pullY]
      exact fun h => owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,neighbor.2.2⟩)
    (by
      norm_num [inside_pullY]
      exact fun h => owners_disjoint p hf 5 10 (by decide) _ _
        ⟨h,right_halfpoint p hf hb omitted⟩)
  norm_num [inside_pullY] at h
  exact h

theorem diagonal (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 5).Inside (5/2) (3/2) ∧
      (owners p 5).Inside (261/100) (139/100) := by
  let C := translate (pullY (owners p 5)) 2 2
  have origin : C.Inside 0 0 := by
    norm_num [C,inside_translate,inside_pullY]
    exact C1092MPPMOmissionCenter.bottom_center p hf hb omitted
  have mark : C.Inside (7/20) (7/20) := by
    norm_num [C,inside_translate,inside_pullY]
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have north : ¬C.Inside (-7/20) (7/20) := by
    norm_num [C,inside_translate,inside_pullY]
    intro h
    have foreign : (owners p 4).Inside (33/20) (33/20) := by
      simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
    exact owners_disjoint p hf 5 4 (by decide) _ _ ⟨h,foreign⟩
  have east : ¬C.Inside (7/20) (-7/20) := by
    norm_num [C,inside_translate,inside_pullY]
    intro h
    have foreign : (owners p 6).Inside (47/20) (47/20) := by
      simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,foreign⟩
  have half := C1092InwardCenterDiagonal.point C (side_gt p 5) origin mark north east
  have long := C1092InwardCenterDiagonal.long_point C (side_gt p 5) origin mark north east
  norm_num [C,inside_translate,inside_pullY] at half long
  exact ⟨half,long⟩

theorem right_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 5).Inside (5/2) 2 := by
  let C := chart (owners p 5)
  let W := chart (owners p 9)
  have inward := omitted_bottom_inward p hf hb omitted
  have bar := omitted_bottom_bar p hf hb omitted
  have actual (x y : ℝ) : C.Inside x y ↔ (owners p 5).Inside (2+y) (2-x) :=
    inside_chart _ x y
  have wallActual (x y : ℝ) : W.Inside x y ↔ (owners p 9).Inside (2+y) (2-x) :=
    inside_chart _ x y
  have origin : C.Inside 0 0 := by
    apply (actual _ _).mpr
    norm_num
    exact C1092MPPMOmissionCenter.bottom_center p hf hb omitted
  have mark : C.Inside (7/20) (7/20) := by
    apply (actual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have north : ¬C.Inside (-7/20) (7/20) := by
    intro h
    have h' := (actual _ _).mp h
    norm_num at h'
    have foreign : (owners p 6).Inside (47/20) (47/20) := by
      simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨h',foreign⟩
  have east : ¬C.Inside (7/20) (-7/20) := by
    intro h
    have h' := (actual _ _).mp h
    norm_num at h'
    have foreign : (owners p 4).Inside (33/20) (33/20) := by
      simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
    exact owners_disjoint p hf 5 4 (by decide) _ _ ⟨h',foreign⟩
  have same : C.side=W.side := by
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have h := C1092MixedWideCrosspoint.point C W (side_gt p 5) (side_cap p 5) same
    origin mark
    (by apply (actual _ _).mpr; norm_num; exact inward.2)
    (by apply (actual _ _).mpr; norm_num; exact inward.1) north east
    (by
      apply (wallActual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 9 13 (by decide +kernel))
    (by
      intro y yn yu
      apply (wallActual _ _).mpr
      norm_num
      exact bar (2+y) (by linarith only [yn]) (by linarith only [yu]))
    (by intro h; have h' := (wallActual _ _).mp h; norm_num at h'; exact omitted h')
    (by
      intro x y h
      have box := p.contained _ _ _ ((wallActual _ _).mp h)
      linarith only [box.2.2.1])
    (by
      have cut := (hb 1).1
      have original : centerX (owners p 9)≤2 := by
        simpa [mppm,C1092WallCycle.wallFrame,C1092WallCycle.localFrame,
          C1092WallCycle.wallOwner] using cut
      change centerY (chart (owners p 9))≤0
      rw [center_chart]
      linarith only [original])
    (fun x y h => owners_disjoint p hf 5 9 (by decide) _ _
      ⟨(actual _ _).mp h.1,(wallActual _ _).mp h.2⟩)
  have result := (actual _ _).mp h
  norm_num at result
  exact result

theorem rectangle (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (x y : ℝ) (xl : 2≤x) (xu : x≤5/2) (yl : 3/2≤y) (yu : y≤2) :
    (owners p 5).Inside x y := by
  have lower := CommonCases.OriginalOwners.horizontal_segment (owners p 5) 2 (5/2)
    (3/2) x (bottom_crosspoint p hf hb omitted) (diagonal p hf hb omitted).1
    (by norm_num) xl xu
  have upper := CommonCases.OriginalOwners.horizontal_segment (owners p 5) 2 (5/2)
    2 x (C1092MPPMOmissionCenter.bottom_center p hf hb omitted)
    (right_crosspoint p hf hb omitted) (by norm_num) xl xu
  exact CommonCases.OriginalOwners.vertical_segment (owners p 5) x (3/2) 2 y
    lower upper (by norm_num) yl yu

#print axioms bottom_crosspoint
#print axioms diagonal
#print axioms right_crosspoint
#print axioms rectangle
end N12Compact.C1092MPPMPointCore
