import Compact.Completion.C1092.MPPMCentralCover
import Compact.Completion.C1092.ElbowProfile

/-! Literal residual-elbow profile in its actual southwest owner. The
foreign markers and bottom auxiliary come from their original owners. -/
namespace N12Compact.C1092MPPMElbows
open S12 S12Pilot C1092WallCycle C1092MPPMEntrance C1092MPPMOmissions
open C1092MPPMCentralCover C1092RigidCharts
set_option Elab.async false

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem southwest_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (empty : ∀ k, ¬Missing p k)
    (elbow : Elbow (owners p 4)) :
    ∃ C : OpenSquare, C.side=(owners p 4).side ∧
      (∀ x y, C.Inside x y ↔ (owners p 4).Inside (x+2) (y+2)) ∧
      C1092ElbowProfile.Profile C := by
  let A := translate (owners p 4) 2 2
  have side : 1<A.side := by
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have marker : A.Inside (-7/20) (-7/20) := by
    norm_num [A,inside_translate]
    simpa [S12.marker] using marker_point p hf 4 8 (by decide +kernel)
  have P : A.Inside (-1) (-13/50) := by
    norm_num [A,inside_translate]
    exact elbow.1
  have Q : A.Inside (-13/50) 0 := by
    norm_num [A,inside_translate]
    exact elbow.2.1
  have N : ¬A.Inside (-7/20) (7/20) := by
    norm_num [A,inside_translate]
    have foreign : (owners p 7).Inside (33/20) (47/20) := by
      simpa [S12.marker] using marker_point p hf 7 11 (by decide +kernel)
    exact fun h => owners_disjoint p hf 4 7 (by decide) _ _ ⟨h,foreign⟩
  have G : ¬A.Inside (-1) (-2/5) := by
    norm_num [A,inside_translate]
    exact elbow.2.2.1
  have R : ¬A.Inside (-543/500) 0 := by
    norm_num [A,inside_translate]
    have foreign : (owners p 8).Inside (457/500) 2 := by
      simpa [S12.marker] using marker_point p hf 8 12 (by decide +kernel)
    exact fun h => owners_disjoint p hf 4 8 (by decide) _ _ ⟨h,foreign⟩
  have T : ¬A.Inside 0 (-13/50) := by
    norm_num [A,inside_translate]
    exact elbow.2.2.2
  have B : ¬A.Inside (-2/5) (-1) := by
    norm_num [A,inside_translate]
    exact fun h => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨h,(ordinary_walls p hb empty).2.1.1⟩
  obtain ⟨C,shape,inside,profile⟩ := C1092ElbowProfile.exists_profile A side marker P Q N G R T B
  refine ⟨C,shape,?_,profile⟩
  intro x y
  exact (inside x y).trans (inside_translate _ _ _ _ _)

#print axioms southwest_profile
end N12Compact.C1092MPPMElbows
