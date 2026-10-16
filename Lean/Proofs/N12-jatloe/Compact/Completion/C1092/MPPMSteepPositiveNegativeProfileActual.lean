import Compact.Completion.C1092.MPPMSteepPositiveNegativeProfile
import Compact.Completion.C1092.MPPMActualRetaining

/-! Literal Q4/Q5 adapter for the steep-positive/negative-retaining
profile. Q9's origin is derived from Q4's own missing-forward halfpoint;
Q1 owns the genuine southeast inner corner. Universal positive faces
supply the preceding-origin cap without asserting any owner for it.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMSteepPositiveNegativeProfile
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem actual_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (retaining : (owners p 5).Inside 2 (87/50)) :
    Input C (C1092MMMPEndingAxes.clockwise D) := by
  let E := C1092MMMPEndingAxes.clockwise D
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have side : 1<C.side := by
    rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have same : C.side=E.side := frame.side.trans
    (((p.congruent _).trans (p.congruent _).symm).trans ef.side.symm)
  have faces := positive_faces p hf hb h C frame cn sp
  have caps := actual_missing_crosspoint_caps p hf hb h forward missing C frame cn sp
  have origin := bottom_origin_of_missing p hf hb
    (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    h.southwest.1 h.southwest.2 forward
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  refine ⟨side,same,cn,(steep_sine cn caps.2).le,dn,faces.1.lowerU,caps.1,
    faces.1.upperV,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
  · apply (ef.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.2
  · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.1
  · apply (ef.actual _ _).mpr; norm_num; exact retaining
  · intro own
    have original := (ef.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨original,origin⟩
  · intro own
    have original := (ef.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨original,corner⟩
  · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩

theorem actual_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (retaining : (owners p 5).Inside 2 (87/50)) :
    Faces (C1092MMMPEndingAxes.clockwise D) :=
  profile C (C1092MMMPEndingAxes.clockwise D)
    (actual_input p hf hb h forward missing C frame cn sp D dframe dn retaining)

end
#print axioms actual_input
#print axioms actual_profile
end N12Compact.C1092MPPMSteepPositiveNegativeProfile
