import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry
import Compact.Completion.C1092.MPPMActualRetaining
import Compact.Completion.C1092.MPPMSteepPositiveSuccessorFarCap

/-! Literal OOOO ledger in STEEP-POSITIVE-THREE-SQUARE-REDUCTION §5.
The central upper face, steep entrance and the recipient's far cap are
derived. Q10 owns the whole right segment; Q9 owns its origin, marker and
outer point. No owner is reassigned to an omitted forward point.
Scalar nonnegativity is a separate source theorem. Source only. -/
namespace N12Compact.C1092MPPMSteepPositiveThreeSquare
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMActualRetaining
open C1092MPPMCrosspointSupport
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

/-- Both endpoints, and every point between them, are in actual Q10.
The far endpoint is the ordinary-wall advance, not a new auxiliary owner. -/
theorem right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (y : ℝ) (low : -(14/25)≤y) (high : y≤-(2/5)) :
    (owners p 10).Inside 3 (2+y) :=
  CommonCases.OriginalOwners.vertical_segment (owners p 10) 3 (36/25) (8/5) (2+y)
    (far_points p hf hb h).2.2.1
    (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.2
    (by norm_num) (by linarith only [low]) (by linarith only [high])

/-- The exact actual-square input for the three-square reduction. The
successor D is supplied in its own sector of the simultaneously rotated
packing. E=clockwise D restores the common physical translated chart. -/
theorem actual_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (tp : 0<D.s)
    (next : (owners p 5).Inside 2 (3/2)) :
    Input C (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2) := by
  let E := C1092MMMPEndingAxes.clockwise D
  let B := (owners p 9).translated 2 2
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have side : 1<C.side := by rw [frame.side]; exact side_gt p 4
  have sameE : C.side=E.side := frame.side.trans ((side_same p 4 5).trans ef.side.symm)
  have sameB : C.side=B.side := frame.side.trans (side_same p 4 9)
  have f := missing_profile p hf hb h.southwest.1 h.southwest.2 forward
    (far_points p hf hb h).2.1 C frame cn
  have cap := actual_missing_crosspoint_caps p hf hb h forward missing C frame cn sp
  have steep := (steep_sine cn cap.2).le
  have markerC : C.Inside (-7/20) (-7/20) := by
    apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  have ordinaryC : C.Inside (-1) (-13/50) := by
    apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
  have markerE : E.Inside (7/20) (-7/20) := by
    apply (ef.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  have bottomE : E.Inside (2/5) (-1) := by
    apply (ef.actual _ _).mpr; norm_num; exact h.southeast.1
  have crosspointE : E.Inside 0 (-1/2) := by
    apply (ef.actual _ _).mpr; norm_num; exact next
  have apartCE : ∀ x y,¬(C.Inside x y ∧ E.Inside x y) :=
    fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  have df := positive_faces ((rotation 1).pullPacking p)
    (family_transport (rotation 1) p hf) (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) D dframe dn tp
  have farInput : C1092MPPMSteepPositiveSuccessorFarCap.Input C E := by
    refine ⟨side,sameE,cn,steep,dn,markerC,markerE,bottomE,
      f.lowerU,?_,f.lowerV,f.upperV,df.2,?_,apartCE⟩
    · have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
      linarith only [cap.1,cp]
    · intro y low high own
      have original := (ef.actual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 10 (by decide) _ _
        ⟨original,right_bar p hf hb h y low high⟩
  have farCap := C1092MPPMSteepPositiveSuccessorFarCap.upper_cap C E farInput
  have origin := bottom_origin_of_missing p hf hb
    (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    h.southwest.1 h.southwest.2 forward
  refine ⟨side,sameE,sameB,cn,dn,steep,f.lowerU,cap.1,f.upperV,
    markerC,ordinaryC,farCap,bottomE,crosspointE,?_,?_,?_,?_,?_,?_⟩
  · apply (bactual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  · apply (bactual _ _).mpr; norm_num
    exact C1092MPPMActualWallReduction.bottom_ordinary p hf hb
  · apply (bactual _ _).mpr; norm_num; exact origin
  · intro x y own
    have floor := (p.contained _ _ _ ((bactual _ _).mp own)).2.2.1
    linarith only [floor]
  · exact fun x y both => owners_disjoint p hf 9 4 (by decide) _ _
      ⟨(bactual _ _).mp both.1,(frame.actual _ _).mp both.2⟩
  · exact fun x y both => owners_disjoint p hf 9 5 (by decide) _ _
      ⟨(bactual _ _).mp both.1,(ef.actual _ _).mp both.2⟩

/-- The actual omitted-crosspoint branch requires a strictly negative
scalar mode at one orientation of its actual Q9. All geometric inputs
are supplied above; scalar positivity remains the separate final join. -/
theorem actual_negative_mode (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (tp : 0<D.s)
    (next : (owners p 5).Inside 2 (3/2)) :
    ∃ Q : OpenSquare,Q.side=(owners p 9).side ∧
      (∀ x y,Q.Inside x y↔(owners p 9).Inside (2+x) (2+y)) ∧ Quarter Q.c Q.s ∧
      (G00 C.c C.s D.c D.s Q.c Q.s<0 ∨ G01 C.c C.s D.c D.s Q.c Q.s<0 ∨
       G10 C.c C.s D.c D.s Q.c Q.s<0 ∨ G11 C.c C.s D.c D.s Q.c Q.s<0) := by
  obtain ⟨Q,shape,inside,quarter,negative⟩ := one_mode_negative C
    (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2)
    (actual_input p hf hb h forward missing C frame cn sp D dframe dn tp next)
  exact ⟨Q,shape,fun x y => (inside x y).trans
    (inside_translated_iff (owners p 9) 2 2 x y),quarter,negative⟩

end
#print axioms actual_input
#print axioms actual_negative_mode
end N12Compact.C1092MPPMSteepPositiveThreeSquare
