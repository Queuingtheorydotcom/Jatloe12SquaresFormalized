import Compact.Completion.C1092.MPPMEntrance
import Compact.Completion.C1092.InwardBarCenter
import Compact.Completion.C1092.InwardMissingProfile
import Compact.Completion.C1092.MixedWideCrossing
import Compact.Completion.C1092.InwardCrossingConflict
import Compact.Completion.C1092.RigidCharts
import Compact.Geometry.WallLowerReach

/-! An actual omitted MPPM wall auxiliary forces the strict central
origin in its genuine inward owner. All component-cover and mixed-wall
premises are derived from the original packing before using local lemmas. -/
namespace N12Compact.C1092MPPMOmissionCenter
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance C1092RigidCharts
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_cap (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side ≤ 1001/1000 := by
  change (p.square _).side ≤ 1001/1000
  rw [p.congruent]
  exact p.side_le

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem right_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 10).Inside 3 (36/25) := by
  have inward := omitted_bottom_inward p hf hb omitted
  have neighbor := omitted_bottom_neighbors p hf hb omitted
  have marker : (owners p 10).Inside (1543/500) 2 := by
    simpa [S12.marker] using marker_point p hf 10 14 (by decide +kernel)
  have h := WallLowerReach.point (pullY (pullX (owners p 10))) (side_gt p 10)
    (container_pullY _ (container_pullX _ (p.contained _)))
    (by norm_num [inside_pullY,inside_pullX]; exact marker)
    (by norm_num [inside_pullY,inside_pullX]; exact neighbor.2.2)
    (by
      norm_num [inside_pullY,inside_pullX]
      exact fun h => owners_disjoint p hf 10 6 (by decide) _ _ ⟨h,neighbor.1.1⟩)
    (by
      norm_num [inside_pullY,inside_pullX]
      exact fun h => owners_disjoint p hf 10 5 (by decide) _ _ ⟨h,inward.2⟩)
  norm_num [inside_pullY,inside_pullX] at h
  exact h

private def chart (q : OpenSquare) : OpenSquare := translate (pullSwap (pullY q)) 2 2

private theorem inside_chart (q : OpenSquare) (x y : ℝ) :
    (chart q).Inside x y ↔ q.Inside (2+y) (2-x) := by
  change (translate (pullSwap (pullY q)) 2 2).Inside x y ↔ _
  rw [inside_translate,inside_pullSwap,inside_pullY]
  rw [show y+2=2+y by ring,show 4-(x+2)=2-x by ring]

private theorem center_chart (q : OpenSquare) : centerY (chart q)=centerX q-2 := by
  dsimp [chart,translate,pullSwap,pullY,centerY,centerX]
  nlinarith only [q.unit_normal]

/-- The full original bottom-omission implication, including all
orientations of the actual inward square and both actual wall squares. -/
theorem bottom_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 5).Inside 2 2 := by
  classical
  have inward := omitted_bottom_inward p hf hb omitted
  have neighbor := omitted_bottom_neighbors p hf hb omitted
  have bottom := omitted_bottom_bar p hf hb omitted
  have m5 : (owners p 5).Inside (47/20) (33/20) := by
    simpa [S12.marker] using marker_point p hf 5 9 (by decide +kernel)
  have m6 : (owners p 6).Inside (47/20) (47/20) := by
    simpa [S12.marker] using marker_point p hf 6 10 (by decide +kernel)
  have m9 : (owners p 9).Inside 2 (457/500) := by
    simpa [S12.marker] using marker_point p hf 9 13 (by decide +kernel)
  obtain ⟨C,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame (chart (owners p 5))
  have actual (x y : ℝ) : C.Inside x y ↔ (owners p 5).Inside (2+y) (2-x) :=
    (inside x y).trans (inside_chart _ x y)
  have side : 1<C.side := by
    rw [shape]
    exact side_gt p 5
  have cap : C.side ≤ 1001/1000 := by rw [shape]; exact side_cap p 5
  have M : C.Inside (7/20) (7/20) := by
    apply (actual _ _).mpr
    norm_num
    exact m5
  have P : C.Inside 0 (13/50) := by
    apply (actual _ _).mpr
    norm_num
    exact inward.2
  have Q : C.Inside (13/50) 0 := by
    apply (actual _ _).mpr
    norm_num
    exact inward.1
  have missingA : ¬C.Inside (2/5) 1 := by
    intro h
    have h' := (actual _ _).mp h
    norm_num at h'
    exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h',neighbor.2.2⟩
  have missingN : ¬C.Inside (-7/20) (7/20) := by
    intro h
    have h' := (actual _ _).mp h
    norm_num at h'
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨h',m6⟩
  have missingR : ¬C.Inside 1 (2/5) := by
    intro h
    have h' := (actual _ _).mp h
    norm_num at h'
    exact owners_disjoint p hf 5 9 (by decide) _ _
      ⟨h',bottom _ (by norm_num) (by norm_num)⟩
  have center : C.Inside 0 0 := by
    by_cases sign : 0≤C.s
    · apply C1092InwardBarCenter.point C side cp sign (abs_le.mp range).2 M P Q missingA
      · intro h
        have h' := (actual _ _).mp h
        norm_num at h'
        exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h',right_far p hf hb omitted⟩
      · intro y yn yu h
        have h' := (actual _ _).mp h
        norm_num at h'
        exact owners_disjoint p hf 5 9 (by decide) _ _
          ⟨h',bottom (2+y) (by linarith only [yn]) (by linarith only [yu])⟩
    · apply Classical.byContradiction
      intro missing
      have profile := C1092InwardMissingProfile.profile C side cp
        (lt_of_not_ge sign).le (by linarith only [(abs_le.mp range).1])
        M P Q missing missingR missingA missingN
      let z := C1092WallProfileScalars.half C.c (-C.s)
      have denominator : 0<1+C.c := by linarith only [cp]
      have zp : 0≤z := by
        dsimp [z,C1092WallProfileScalars.half]
        exact div_nonneg (by linarith only [profile.sine]) denominator.le
      have angle : z*(1+C.c)=-C.s := by
        dsimp [z,C1092WallProfileScalars.half]
        field_simp [denominator.ne']
      have unitAngle : (-C.s)*z=1-C.c := by
        dsimp [z,C1092WallProfileScalars.half]
        field_simp [denominator.ne']
        nlinarith only [C.unit_normal]
      let W := chart (owners p 9)
      have sameW : C.side=W.side := shape.trans (side_same p 5 9)
      have wallW : ∀ x y, W.Inside x y → x≤2 := by
        intro x y h
        have h' := (inside_chart (owners p 9) x y).mp h
        have box := p.contained _ _ _ h'
        linarith only [box.2.2.1]
      have bottomCut : centerX (owners p 9)≤2 := by
        have h := (hb 1).1
        simpa [mppm,wallFrame,localFrame,wallOwner] using h
      have cutW : centerY W≤0 := by
        dsimp [W]
        rw [center_chart]
        linarith only [bottomCut]
      have S : W.Inside (543/500) 0 := by
        apply (inside_chart _ _ _).mpr
        norm_num
        exact m9
      have T : W.Inside 1 (-39/100) := by
        apply (inside_chart _ _ _).mpr
        norm_num
        exact bottom _ (by norm_num) (by norm_num)
      have B : W.Inside 1 (2/5) := by
        apply (inside_chart _ _ _).mpr
        norm_num
        exact bottom _ (by norm_num) (by norm_num)
      have E : ¬W.Inside 1 (-2/5) := by
        intro h
        have h' := (inside_chart (owners p 9) _ _).mp h
        norm_num at h'
        exact omitted h'
      have apartW : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y) :=
        fun x y h => owners_disjoint p hf 5 9 (by decide) _ _
          ⟨(actual _ _).mp h.1,(inside_chart _ _ _).mp h.2⟩
      have crossing := C1092MixedWideCrossing.point C W C.c (-C.s) z rfl (by ring)
        side cap sameW cp (by linarith only [profile.sine])
        (by linarith only [(abs_le.mp range).1]) angle unitAngle P Q M profile.lowerV
        S T B E wallW cutW apartW
      let A := translate (swap C) (-2) (-2)
      have aInside (x y : ℝ) : A.Inside x y ↔ (owners p 5).Inside x (4-y) := by
        change (translate (swap C) (-2) (-2)).Inside x y ↔ _
        rw [inside_translate,inside_swap,actual]
        rw [show 2+(x+-2)=x by ring,show 2-(y+-2)=4-y by ring]
      have escape : 2*A.c+2*A.s≤A.loU := by
        dsimp [A,translate,swap]
        linarith only [profile.lowerV]
      have lowerV : -(47/20)*A.s+(33/20)*A.c≤A.loV := by
        dsimp [A,translate,swap]
        linarith only [profile.lowerU]
      have aQ : A.Inside (113/50) 2 := by
        apply (aInside _ _).mpr
        norm_num
        exact inward.2
      have outer : A.Inside (47/20) (53/20) := by
        change (translate (swap C) (-2) (-2)).Inside _ _
        rw [inside_translate,inside_swap]
        norm_num
        exact profile.outer
      have aCross : A.Inside 3 (2+z) := by
        change (translate (swap C) (-2) (-2)).Inside _ _
        rw [inside_translate,inside_swap]
        convert crossing.2 using 1 <;> ring
      have markerR : (pullY (owners p 10)).Inside (1543/500) 2 := by
        norm_num [inside_pullY]
        simpa [S12.marker] using marker_point p hf 10 14 (by decide +kernel)
      have highR : (pullY (owners p 10)).Inside 3 (12/5) := by
        norm_num [inside_pullY]
        exact neighbor.2.2
      exact C1092InwardCrossingConflict.impossible A (pullY (owners p 10)) side
        (shape.trans (side_same p 5 10)) cp (by dsimp [A,translate,swap]; linarith only [profile.sine])
        escape lowerV aQ outer z zp profile.halfSmall
        (by simpa only [A,translate,swap,mul_comm] using angle)
        (by simpa only [A,translate,swap] using unitAngle) aCross
        (container_pullY _ (p.contained _)) markerR highR
        (fun x y h => owners_disjoint p hf 5 10 (by decide) _ _
          ⟨(aInside _ _).mp h.1,(inside_pullY _ _ _).mp h.2⟩)
  have h := (actual 0 0).mp center
  norm_num at h
  exact h

#print axioms bottom_center
end N12Compact.C1092MPPMOmissionCenter
