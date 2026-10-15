import Compact.Completion.C1092.MPPMCentralCover
import Compact.Completion.OtherCases.ElbowPoint
import Compact.Completion.C981.Crosspoint
import Compact.Geometry.WallLowerReach

/-! An actual inward southwest owner in the zero-omission entrance has
two actual ordinary neighbors. The genuine bottom advance and southwest
crosspoint are proved before the northwest elbow is contradicted. -/
namespace N12Compact.C1092MPPMInwardNeighbors
open S12 S12Pilot C1092WallCycle C1092AuxiliaryCover C1092WallSymmetry
open C1092MPPMEntrance C1092MPPMOmissions C1092MPPMCentralCover
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem southeast_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (empty : ∀ k, ¬Missing p k)
    (inward : Inward (owners p 4)) :
    (owners p 5).Inside (12/5) 1 ∧ (owners p 5).Inside (113/50) 1 := by
  have walls := ordinary_walls p hb empty
  have rightF := walls.2.2.1.1
  have rightG := walls.2.2.1.2
  have f : (owners p 5).Inside (12/5) 1 := by
    rcases C1092MMMMEntrance.southeast_f_cover p hf with foreign | ordinary | wall
    · exact (owners_disjoint p hf 5 4 (by decide) _ _ ⟨foreign,inward.1⟩).elim
    · exact ordinary
    · exact (owners_disjoint p hf 5 10 (by decide) _ _ ⟨wall,rightF⟩).elim
  have g : (owners p 5).Inside (113/50) 1 := by
    by_contra absent
    have cross : (owners p 5).Inside (113/50) 2 := by
      rcases southeast_g_cover p hf with ordinary | cross | wall
      · exact (absent ordinary).elim
      · exact cross
      · exact (owners_disjoint p hf 5 10 (by decide) _ _ ⟨wall,rightG⟩).elim
    let g : Transform := ⟨true,true,true⟩
    apply C1092MixedSpan.impossible (g.pull (owners p 5)) (side_gt p 5)
    · norm_num [g,Transform.pull,inside_pullSwap,inside_pullY,inside_pullX]; exact cross
    · norm_num [g,Transform.pull,inside_pullSwap,inside_pullY,inside_pullX]; exact f
    · norm_num [g,Transform.pull,inside_pullSwap,inside_pullY,inside_pullX]
      exact fun h => owners_disjoint p hf 5 4 (by decide) _ _ ⟨h,inward.1⟩
    · norm_num [g,Transform.pull,inside_pullSwap,inside_pullY,inside_pullX]; exact absent
    · norm_num [g,Transform.pull,inside_pullSwap,inside_pullY,inside_pullX]
      exact fun h => owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,rightF⟩
    · norm_num [g,Transform.pull,inside_pullSwap,inside_pullY,inside_pullX]
      exact fun h => owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,rightG⟩
  exact ⟨f,g⟩

theorem bottom_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (empty : ∀ k, ¬Missing p k)
    (inward : Inward (owners p 4)) : (owners p 9).Inside (36/25) 1 := by
  have pair := southeast_pair p hf hb empty inward
  have bottom := (ordinary_walls p hb empty).2.1
  have mark : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  let W := pullSwap (pullX (owners p 9))
  have h := WallLowerReach.point W (side_gt p 9)
    (container_pullSwap _ (container_pullX _ (p.contained _)))
    (by norm_num [W,inside_pullSwap,inside_pullX]; exact mark)
    (by norm_num [W,inside_pullSwap,inside_pullX]; exact bottom.1)
    (by
      norm_num [W,inside_pullSwap,inside_pullX]
      exact fun h => owners_disjoint p hf 9 5 (by decide) _ _ ⟨h,pair.2⟩)
    (by
      norm_num [W,inside_pullSwap,inside_pullX]
      exact fun h => owners_disjoint p hf 9 4 (by decide) _ _ ⟨h,inward.1⟩)
  norm_num [W,inside_pullSwap,inside_pullX] at h
  exact h

theorem bottom_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (empty : ∀ k, ¬Missing p k)
    (inward : Inward (owners p 4)) : (owners p 9).Inside (3/2) 1 := by
  have h := inside_segment (owners p 9) (36/25) 1 (8/5) 1 (3/8)
    (bottom_far p hf hb empty inward) (ordinary_walls p hb empty).2.1.1
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem southwest_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (empty : ∀ k, ¬Missing p k)
    (inward : Inward (owners p 4)) : (owners p 4).Inside (3/2) 2 := by
  let g : Transform := ⟨true,true,true⟩
  have actual (x y : ℝ) : (g.pull (owners p 4)).Inside x y ↔
      (owners p 4).Inside (4-y) (4-x) := by
    simp only [g,Transform.pull,inside_pullSwap,inside_pullY,inside_pullX]
  have m4 : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have m5 : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have m7 : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have h := C981CompletionCrosspoint.point (g.pull (owners p 4)) (side_gt p 4)
    (by rw [actual]; norm_num; exact inward.2)
    (by rw [actual]; norm_num; exact inward.1)
    (by rw [actual]; norm_num; exact m4)
    (by
      rw [actual]
      norm_num
      exact fun h => owners_disjoint p hf 4 5 (by decide) _ _ ⟨h,m5⟩)
    (by
      rw [actual]
      norm_num
      exact fun h => owners_disjoint p hf 4 7 (by decide) _ _ ⟨h,m7⟩)
    (by
      rw [actual]
      norm_num
      exact fun h => owners_disjoint p hf 4 9 (by decide) _ _
        ⟨h,(ordinary_walls p hb empty).2.1.1⟩)
    (by
      rw [actual]
      norm_num
      exact fun h => owners_disjoint p hf 4 9 (by decide) _ _
        ⟨h,bottom_halfpoint p hf hb empty inward⟩)
  rw [actual] at h
  norm_num at h
  exact h

theorem northwest_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (empty : ∀ k, ¬Missing p k)
    (inward : Inward (owners p 4)) :
    (owners p 7).Inside (8/5) 3 ∧ (owners p 7).Inside (87/50) 3 := by
  have walls := ordinary_walls p hb empty
  have g : (owners p 7).Inside (87/50) 3 := by
    rcases northwest_g_cover p hf with wall | foreign | ordinary
    · exact (owners_disjoint p hf 7 8 (by decide) _ _ ⟨wall,walls.1.2⟩).elim
    · exact (owners_disjoint p hf 7 4 (by decide) _ _ ⟨foreign,inward.2⟩).elim
    · exact ordinary
  have f : (owners p 7).Inside (8/5) 3 := by
    by_contra absent
    have elbow : (owners p 7).Inside 2 (113/50) := by
      rcases northwest_f_cover p hf with wall | ordinary | inward
      · exact (owners_disjoint p hf 7 8 (by decide) _ _ ⟨wall,walls.1.1⟩).elim
      · exact (absent ordinary).elim
      · exact inward
    have mark : (owners p 7).Inside (33/20) (47/20) := by
      simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
    have ne : (owners p 6).Inside (47/20) (47/20) := by
      simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
    have top : (owners p 11).Inside 2 (1543/500) := by
      simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
    have h := (Completion.OtherCases.ElbowPoint.points_original (pullSwap (owners p 7))
      (side_gt p 7)
      (by rw [inside_pullSwap]; exact mark)
      (by rw [inside_pullSwap]; exact elbow)
      (by rw [inside_pullSwap]; exact g)
      (by rw [inside_pullSwap]; exact fun h => owners_disjoint p hf 7 6 (by decide) _ _ ⟨h,ne⟩)
      (by rw [inside_pullSwap]; exact absent)
      (by rw [inside_pullSwap]; exact fun h => owners_disjoint p hf 7 11 (by decide) _ _ ⟨h,top⟩)).1
    rw [inside_pullSwap] at h
    exact owners_disjoint p hf 7 4 (by decide) _ _
      ⟨h,southwest_crosspoint p hf hb empty inward⟩
  exact ⟨f,g⟩

#print axioms southeast_pair
#print axioms southwest_crosspoint
#print axioms northwest_pair
end N12Compact.C1092MPPMInwardNeighbors
