import Compact.Completion.C1092.MPPMOnePositiveMissingEnding
import Compact.Completion.C1092.MPPMPositiveNegativeRetainingActual
import Compact.Completion.C1092.MPPMNonpositivePredecessorActual
import Compact.Completion.C1092.MPPMOnePositiveRetainingEnding
import Compact.Completion.C1092.MPPMActualCrosspoints

/-! Original-owner applications of the narrow negative local endings.
The scalar narrow profile is named separately, while every ordinary
point, crosspoint, simultaneous missing-positive face and whole actual
boundary bar is produced here from the literal packing. Source only. -/
namespace N12Compact.C1092MPPMOnePositive
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem actual_positive_missing_input (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (close : 97/100<C.c) (small : 4*(-C.s)<C.c) (height : C.loV+C.side<43/500)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (positive : 0<D.s)
    (missing : ¬(owners p 5).Inside 2 (87/50))
    (crosspoint : (owners p 5).Inside 2 (3/2)) :
    PositiveMissingInput C (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2) := by
  let E := C1092MMMPEndingAxes.clockwise D
  let B := (owners p 9).translated 2 2
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have missing' : ¬(owners ((rotation 1).pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport (rotation 1) p hf 4]
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact missing
  have data := C1092MPPMActualBoundaryOrigin.missing_positive_data ((rotation 1).pullPacking p)
    (family_transport (rotation 1) p hf) (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) missing' D dframe dn positive
  have sideD : 1<D.side := by
    change 1<E.side
    rw [ef.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have df := C1092MPPMMissingPositiveBoundaries.profile D sideD data
  refine ⟨C1092MPPMActualNonpositive.actual_core p hf hb h C frame cn forward,
    frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans ef.side.symm),
    close,small,height,dn,?_,?_,df.lowerU,?_,df.halfLow.le,?_,?_,?_⟩
  · apply (ef.actual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  · apply (ef.actual _ _).mpr; norm_num; exact crosspoint
  · change -D.loV≤D.c-(14/25)*D.s
    linarith only [df.lowerV]
  · intro x low high
    apply (bactual _ _).mpr
    norm_num
    exact C1092MPPMActualNonpositive.bottom_bar p hf hb h C frame cn (2+x)
      (by linarith only [low]) (by linarith only [high])
  · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  · exact fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(bactual _ _).mp both.2⟩

theorem positive_missing_of_narrow (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (close : 97/100<C.c) (small : 4*(-C.s)<C.c) (height : C.loV+C.side<43/500)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (positive : 0<D.s)
    (missing : ¬(owners p 5).Inside 2 (87/50))
    (crosspoint : (owners p 5).Inside 2 (3/2)) : False :=
  positive_missing_impossible C (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2)
    (actual_positive_missing_input p hf hb h C frame cn forward close small height
      D dframe dn positive missing crosspoint)

/-- The actual P,N-retaining,P-missing local cycle is impossible once
the genuine positive successor crosspoint is supplied. The predecessor
produces the narrow profile, rather than assuming its terminal bounds. -/
theorem positive_sandwich_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (W : OpenSquare) (wframe : ActualFrame ((rotation 3).pullPacking p) W)
    (wn : Normal W.c W.s) (previousPositive : 0<W.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (nextPositive : 0<D.s)
    (missing : ¬(owners p 5).Inside 2 (87/50))
    (crosspoint : (owners p 5).Inside 2 (3/2)) : False := by
  have narrow := C1092MPPMPositiveNegativeRetaining.narrow_of_positive_predecessor
    p hf hb h C frame cn forward W wframe wn previousPositive crosspoint
  exact positive_missing_of_narrow p hf hb h C frame cn forward narrow.1 narrow.2.1 narrow.2.2
    D dframe dn nextPositive missing crosspoint

/-- The other genuine source of a narrow negative owner: an actual
missing-negative predecessor. It has no sign premise on the fourth
central, and its positive recipient contributes only its true data. -/
theorem missing_predecessor_positive_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (W : OpenSquare) (wframe : ActualFrame ((rotation 3).pullPacking p) W)
    (wn : Normal W.c (-W.s)) (previousMissing : ¬(owners p 7).Inside 2 (113/50))
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (nextPositive : 0<D.s)
    (missing : ¬(owners p 5).Inside 2 (87/50))
    (crosspoint : (owners p 5).Inside 2 (3/2)) : False := by
  have narrow := C1092MPPMAllNonpositive.narrow_of_missing_predecessor
    p hf hb h C frame cn forward W wframe wn previousMissing
  exact positive_missing_of_narrow p hf hb h C frame cn forward narrow.close narrow.slope narrow.height
    D dframe dn nextPositive missing crosspoint

/-- Actual Lemma 3 after either genuine producer of the narrow source
profile. The next foreign crosspoint stays in Q6, and the entire bar
used to clear D is in the rotated copy of the one actual Q10. -/
theorem retaining_of_narrow (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (close : 97/100<C.c) (small : 4*(-C.s)<C.c) (height : C.loV+C.side<43/500)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (nextForward : (owners p 5).Inside 2 (87/50))
    (nextCrosspoint : (owners p 6).Inside (5/2) 2) : False := by
  let E := C1092MMMPEndingAxes.clockwise D
  let p' := (rotation 1).pullPacking p
  have family' := family_transport (rotation 1) p hf
  have context := rotation_context p hf hb 1
  have ordinary := Ordinary.rotated p hf h 1
  have ef := successor_frame p hf D dframe
  have retaining : C1092MPPMActualPositiveCycle.Forward p' :=
    (C1092MPPMActualCrosspoints.next_forward_iff p hf).mpr nextForward
  have core := C1092MPPMActualNonpositive.actual_core p' family' context ordinary D dframe dn retaining
  have input : RetainingPairInput C E := by
    refine ⟨C1092MPPMActualNonpositive.actual_core p hf hb h C frame cn forward,
      frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans ef.side.symm),
      close,small,height,dn,?_,?_,?_,?_⟩
    · apply (ef.actual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
    · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.2
    · apply (ef.actual _ _).mpr; norm_num; exact nextForward
    · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
        ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  have foreign : ¬D.Inside 0 (-1/2) := by
    intro own
    have common : E.Inside (1/2) 0 := (C1092MMMPEndingAxes.inside_clockwise D _ _).mpr own
    have original := (ef.actual _ _).mp common
    norm_num at original
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨original,nextCrosspoint⟩
  let R := (owners p' 9).translated 2 2
  have ractual (x y : ℝ) : R.Inside x y↔(owners p' 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p' 9) 2 2 x y
  apply retaining_successor_impossible C D R input core foreign
  · intro x low high
    apply (ractual _ _).mpr
    norm_num
    exact C1092MPPMActualNonpositive.bottom_bar p' family' context ordinary D dframe dn (2+x)
      (by linarith only [low]) (by linarith only [high])
  · exact fun x y both => owners_disjoint p' family' 4 9 (by decide) _ _
      ⟨(dframe.actual _ _).mp both.1,(ractual _ _).mp both.2⟩

theorem missing_predecessor_retaining_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (W : OpenSquare) (wframe : ActualFrame ((rotation 3).pullPacking p) W)
    (wn : Normal W.c (-W.s)) (previousMissing : ¬(owners p 7).Inside 2 (113/50))
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (nextForward : (owners p 5).Inside 2 (87/50))
    (nextCrosspoint : (owners p 6).Inside (5/2) 2) : False := by
  have narrow := C1092MPPMAllNonpositive.narrow_of_missing_predecessor
    p hf hb h C frame cn forward W wframe wn previousMissing
  exact retaining_of_narrow p hf hb h C frame cn forward narrow.close narrow.slope narrow.height
    D dframe dn nextForward nextCrosspoint

theorem positive_predecessor_retaining_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (W : OpenSquare) (wframe : ActualFrame ((rotation 3).pullPacking p) W)
    (wn : Normal W.c W.s) (positive : 0<W.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (nextForward : (owners p 5).Inside 2 (87/50))
    (nextCrosspoint : (owners p 6).Inside (5/2) 2) : False := by
  have retaining := (C1092MPPMActualCrosspoints.next_forward_iff p hf).mpr nextForward
  have next := C1092MPPMActualCrosspoints.nonpositive_retaining_crosspoint ((rotation 1).pullPacking p)
    (family_transport (rotation 1) p hf) (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) D dframe dn retaining
  have actualNext := C1092MPPMActualPositiveCycle.next_crosspoint p hf next
  have narrow := C1092MPPMPositiveNegativeRetaining.narrow_of_positive_predecessor
    p hf hb h C frame cn forward W wframe wn positive actualNext
  exact retaining_of_narrow p hf hb h C frame cn forward narrow.1 narrow.2.1 narrow.2.2
    D dframe dn nextForward nextCrosspoint

end
#print axioms actual_positive_missing_input
#print axioms positive_sandwich_impossible
#print axioms missing_predecessor_positive_impossible
#print axioms retaining_of_narrow
#print axioms positive_predecessor_retaining_impossible
end N12Compact.C1092MPPMOnePositive
