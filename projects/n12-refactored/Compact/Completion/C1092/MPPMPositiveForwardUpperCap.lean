import Compact.Completion.C1092.MPPMPositiveOverlap

/-! POSITIVE-FORWARD-UPPER-CAP on the original OOOO MPPM owners. The
backward-owned and backward-excluded alternatives are both checked in
this same actual square. The centered overlap theorem supplies the former
case; the latter is an elementary excluded-face inference. Uncompiled. -/
namespace N12Compact.C1092MPPMPositiveForwardUpperCap
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C977CornerCubic
set_option Elab.async false

theorem cap_of_backward_absent (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (h : C1092MPPMPositiveCrosspointSeeds.ForwardCore C)
    (missing : ¬C.Inside 0 (-13/50)) : C.loU+C.side≤-(13/50)*C.s := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have faces := C1092MPPMPositiveCrosspointSeeds.forward_profile C side cn h
  have short : C.s+(13/50)*C.c<1 := by
    linarith only [cb.2.2.2.2.2,cn.2.1]
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [high,h.marker.1,h.forward.2.2.2,faces.upperV,side,short,cp,cn.1]

theorem upper_cap (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s)
    (positive : 0<C.s) : C.loU+C.side≤0 := by
  have side : 1<C.side := by
    rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have previous := C1092MPPMPositiveOverlap.previous_absent p hf hb ordinary forward C frame normal
  have core := forward_core p hf (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    ordinary.southwest.1 ordinary.southwest.2 forward previous C frame
  by_cases backward : (owners p 4).Inside 2 (87/50)
  · have absent := C1092MPPMPositiveOverlap.original_center_absent p hf hb ordinary forward backward C frame normal
    have I : C.Inside 0 (-13/50) := by
      apply (frame.actual _ _).mpr; norm_num; exact backward
    have cp : 0<C.c := by linarith only [(normal_bounds normal).1]
    apply le_of_not_gt
    intro high
    apply absent
    have center : C.Inside 0 0 := by
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,core.forward.1,I.2.2.1,core.forward.2.2.2,cp,positive]
    have original := (frame.actual _ _).mp center
    norm_num at original
    exact original
  · have missing : ¬C.Inside 0 (-13/50) := by
      intro own
      have original := (frame.actual _ _).mp own
      norm_num at original
      exact backward original
    have cap := cap_of_backward_absent C side normal core missing
    linarith only [cap,positive]

/-- The complete simultaneous face table; all four bounds are conclusions
of the same actual positive forward-owned square. -/
theorem faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s)
    (positive : 0<C.s) :
    C1092MPPMPositiveCrosspointSeeds.ForwardFaces C ∧ C.loU+C.side≤0 := by
  have side : 1<C.side := by
    rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have previous := C1092MPPMPositiveOverlap.previous_absent p hf hb ordinary forward C frame normal
  have core := forward_core p hf (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    ordinary.southwest.1 ordinary.southwest.2 forward previous C frame
  exact ⟨C1092MPPMPositiveCrosspointSeeds.forward_profile C side normal core,
    upper_cap p hf hb ordinary forward C frame normal positive⟩

theorem sharp_upper_cap (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside 2 (87/50))
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s) :
    C.loU+C.side≤-(13/50)*C.s := by
  have side : 1<C.side := by
    rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have previous := C1092MPPMPositiveOverlap.previous_absent p hf hb ordinary forward C frame normal
  have core := forward_core p hf (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    ordinary.southwest.1 ordinary.southwest.2 forward previous C frame
  apply cap_of_backward_absent C side normal core
  intro own
  have original := (frame.actual _ _).mp own
  norm_num at original
  exact missing original

theorem center_absent (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s)
    (positive : 0<C.s) : ¬(owners p 4).Inside 2 2 := by
  have cap := upper_cap p hf hb ordinary forward C frame normal positive
  intro own
  have center : C.Inside 0 0 := by
    apply (frame.actual _ _).mpr
    norm_num
    exact own
  linarith only [cap,center.2.1]

#print axioms upper_cap
#print axioms faces
#print axioms sharp_upper_cap
#print axioms center_absent
end N12Compact.C1092MPPMPositiveForwardUpperCap
