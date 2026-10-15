import Compact.Completion.C1092.MMMMEntrance
import Compact.Completion.C1092.OppositePair
import Compact.Completion.C981.Crosspoint
import Compact.Geometry.CentralWallCenter

/-! The whole MMMM entrance has its genuine northeast center and both
half-unit crosspoints. The two wall advances use the actual ordinary
auxiliary pairs already proved in MMMMEntrance, not vacant points. -/
namespace N12Compact.C1092MMMMStrictCore
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092ActualEntrance C1092MMMMEntrance
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem right_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 10).Inside 3 (5/2) := by
  have ordinary := C1092MMMMEntrance.southeast_pair p hf hb
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have marker : (owners p 10).Inside (1543/500) 2 := by
    have h : Owns (owners p 10) 14 := (owners_markers p hf 10 14).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  exact CentralWallCenter.right_high (owners p 10) (side_gt p 10) (p.contained _)
    marker (right_g p hf hb)
    (fun h => owners_disjoint p hf 10 5 (by decide) _ _ ⟨h,ordinary.1⟩)
    (fun h => owners_disjoint p hf 10 6 (by decide) _ _ ⟨h,inward.2⟩)

theorem top_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 11).Inside (5/2) 3 := by
  have ordinary := C1092MMMMEntrance.northwest_pair p hf hb
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have marker : (owners p 11).Inside 2 (1543/500) := by
    have h : Owns (owners p 11) 15 := (owners_markers p hf 11 15).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have strong := CentralWallCenter.right_high (pullSwap (owners p 11)) (side_gt p 11)
    (container_pullSwap _ (p.contained _))
    ((inside_pullSwap _ _ _).mpr marker) ((inside_pullSwap _ _ _).mpr (top_f p hf hb))
    (fun h => owners_disjoint p hf 11 7 (by decide) _ _
      ⟨(inside_pullSwap _ _ _).mp h,ordinary.2⟩)
    (fun h => owners_disjoint p hf 11 6 (by decide) _ _
      ⟨(inside_pullSwap _ _ _).mp h,inward.1⟩)
  exact (inside_pullSwap _ _ _).mp strong

theorem northeast_halfpoints (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) :
    (owners p 6).Inside 2 (5/2) ∧ (owners p 6).Inside (5/2) 2 := by
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have marker : (owners p 6).Inside (47/20) (47/20) := by
    have h : Owns (owners p 6) 10 := (owners_markers p hf 6 10).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have missingSE : ¬ (owners p 6).Inside (47/20) (33/20) := by
    have h : ¬ Owns (owners p 6) 9 := fun h =>
      (by decide +kernel : (9 : Marker) ∉ maskSupport (ownerCode 6))
        ((owners_markers p hf 6 9).mp h)
    simpa [Owns,S12.marker] using h
  have missingNW : ¬ (owners p 6).Inside (33/20) (47/20) := by
    have h : ¬ Owns (owners p 6) 11 := fun h =>
      (by decide +kernel : (11 : Marker) ∉ maskSupport (ownerCode 6))
        ((owners_markers p hf 6 11).mp h)
    simpa [Owns,S12.marker] using h
  have rightLow : ¬ (owners p 6).Inside 3 (12/5) :=
    fun h => owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,right_g p hf hb⟩
  have rightHigh : ¬ (owners p 6).Inside 3 (5/2) :=
    fun h => owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,right_halfpoint p hf hb⟩
  have topLow : ¬ (owners p 6).Inside (12/5) 3 :=
    fun h => owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,top_f p hf hb⟩
  have topHigh : ¬ (owners p 6).Inside (5/2) 3 :=
    fun h => owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,top_halfpoint p hf hb⟩
  constructor
  · exact C981CompletionCrosspoint.point (owners p 6) (side_gt p 6) inward.1 inward.2 marker
      missingSE missingNW rightLow rightHigh
  · have h := C981CompletionCrosspoint.point (pullSwap (owners p 6)) (side_gt p 6)
      ((inside_pullSwap _ _ _).mpr inward.2) ((inside_pullSwap _ _ _).mpr inward.1)
      ((inside_pullSwap _ _ _).mpr marker)
      (fun h => missingNW ((inside_pullSwap _ _ _).mp h))
      (fun h => missingSE ((inside_pullSwap _ _ _).mp h))
      (fun h => topLow ((inside_pullSwap _ _ _).mp h))
      (fun h => topHigh ((inside_pullSwap _ _ _).mp h))
    exact (inside_pullSwap _ _ _).mp h

theorem northeast_triangle (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) :
    (owners p 6).Inside 2 2 ∧ (owners p 6).Inside (5/2) 2 ∧ (owners p 6).Inside 2 (5/2) :=
  ⟨C1092OppositePair.northeast_center p hf mmmm hb rfl rfl,
    (northeast_halfpoints p hf hb).2,(northeast_halfpoints p hf hb).1⟩

#print axioms northeast_triangle
end N12Compact.C1092MMMMStrictCore
