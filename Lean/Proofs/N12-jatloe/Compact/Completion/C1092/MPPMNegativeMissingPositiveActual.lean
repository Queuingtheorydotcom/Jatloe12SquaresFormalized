import Compact.Completion.C1092.MPPMNegativeMissingPositiveCeiling
import Compact.Completion.C1092.MPPMNegativeMissingPositiveSharedWall
import Compact.Completion.C1092.MPPMPositiveMissingLeftCenter
import Compact.Completion.C1092.MPPMNegativeOwnedPositiveActual

/-! The original missing-negative to positive-retaining edge. The
negative predecessor supplies the positive angle ceiling and the same
actual left boundary supplies both contradictory center inequalities.
Its required origin is produced from the predecessor's own omission.
No boundary-origin membership is assumed. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeMissingPositiveActual
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem positive_half_angle (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (forward : (owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 3).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (previousMissing : ¬(owners p 7).Inside 2 (113/50)) :
    C.s/(1+C.c)<7/24 := by
  let g := rotation 3
  let p' := g.pullPacking p
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 3
  have ordinary := Ordinary.rotated p hf h 3
  have missing : ¬(owners p' 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact previousMissing
  have strong := C1092MPPMActualCentralOrigin.missing_strong_profile
    p' family' context ordinary missing D dframe dn
  have bounds := C1092MPPMNegativeRecipientWall.Scalars.weak_bounds dn
    (show 237/763<C1092WallProfileScalars.half D.c (-D.s) by
      linarith only [strong.halfLow])
  have product : 23/50<D.c*(-D.s) := by
    have square := mul_pos (show 0<D.c-D.s-139/100 by linarith only [bounds.2.2.2.2])
      (show 0<D.c-D.s+139/100 by linarith only [(normal_bounds dn).1,dn.1])
    nlinarith only [square,D.unit_normal]
  let W := C1092MMMPEndingAxes.clockwise
    (C1092MMMPEndingAxes.clockwise (C1092MMMPEndingAxes.clockwise D))
  have wactual (x y : ℝ) : W.Inside x y↔(owners p 7).Inside (2+x) (2+y) := by
    simp only [W,C1092MMMPEndingAxes.inside_clockwise,neg_neg]
    rw [dframe.actual,owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    ring
  have wside : W.side=(owners p 7).side := by
    change D.side=(owners p 7).side
    rw [dframe.side,owners_transport g p hf 4]
    rfl
  have wu : W.loU=D.loV := by dsimp [W,C1092MMMPEndingAxes.clockwise]; ring
  have wv : W.loV= -D.loU-D.side := rfl
  have faces := C1092MPPMActualBoundaryOrigin.positive_faces p hf hb h C frame cn positive
  have input : C1092MPPMNegativeMissingPositiveCeiling.Input C W := by
    refine ⟨?_,frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans wside.symm),
      cn,positive,dn,bounds.2.1,bounds.2.2.1,product,?_,?_,?_,faces.1.lowerV,?_,?_,?_,?_,?_⟩
    · rw [frame.side]
      change 1<(p.square _).side
      rw [p.congruent]
      exact p.side_gt_one
    · apply (frame.actual _ _).mpr
      norm_num
      simpa [marker] using mark p hf 4 8 (by decide +kernel)
    · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
    · apply (frame.actual _ _).mpr; norm_num; exact forward
    · apply (wactual _ _).mpr
      norm_num
      simpa [marker] using mark p hf 7 11 (by decide +kernel)
    · rw [wu]
      change -D.c+D.s≤D.loV
      linarith only [strong.lowerV]
    · rw [wu]
      exact strong.upperV
    · rw [wv]
      change -D.loU-D.side+D.side≤(543/500)*D.c
      linarith only [strong.lowerU,(normal_bounds dn).1]
    · exact fun x y both => owners_disjoint p hf 4 7 (by decide) _ _
        ⟨(frame.actual _ _).mp both.1,(wactual _ _).mp both.2⟩
  exact C1092MPPMNegativeMissingPositiveCeiling.half_lt C W input

/-- The positive retained-forward face needed by the shared-wall
theorem is produced from the actual foreign far point in Q9. -/
theorem positive_lowerV (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (small : C.s/(1+C.c)≤3/10) : (14/25)*C.s-C.c≤C.loV := by
  have bounds := C1092MPPMNegativeMissingPositiveSharedWall.Scalars.bounds cn small
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have G : C.Inside (-1) (-2/5) := by
    apply (frame.actual _ _).mpr; norm_num; exact h.southwest.2
  have P : C.Inside (-1) (-13/50) := by
    apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
  have M : C.Inside (-7/20) (-7/20) := by
    apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  apply le_of_not_gt
  intro low
  have own : C.Inside (-14/25) (-1) := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [G.1,M.2.1,P.2.2.2,bounds.1,bounds.2,cp,positive,low]
  have original := (frame.actual _ _).mp own
  norm_num at original
  exact owners_disjoint p hf 4 9 (by decide) _ _
    ⟨original,(far_points p hf hb h).2.1⟩

theorem missing_predecessor_retaining_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (forward : (owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 3).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (previousMissing : ¬(owners p 7).Inside 2 (113/50)) : False := by
  have ceiling := positive_half_angle p hf hb h C frame cn positive forward D dframe dn previousMissing
  have small : C.s/(1+C.c)≤3/10 := by linarith only [ceiling]
  have faces := C1092MPPMActualBoundaryOrigin.positive_faces p hf hb h C frame cn positive
  have point := forward_crosspoint p hf hb h forward C frame cn positive
  let g := rotation 3
  let p' := g.pullPacking p
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 3
  have ordinary := Ordinary.rotated p hf h 3
  have missing : ¬(owners p' 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact previousMissing
  have origin := bottom_origin_of_missing p' family' context
    (C1092MPPMActualWallReduction.bottom_ordinary p' family' context)
    ordinary.southwest.1 ordinary.southwest.2 missing
  have leftOrigin : (owners p 8).Inside 1 2 := by
    rw [owners_transport g p hf 9] at origin
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY] at origin
    exact origin
  let L := (owners p 8).translated 2 2
  have actual (x y : ℝ) : L.Inside x y↔(owners p 8).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 8) 2 2 x y
  have data : C1092MPPMNegativeMissingPositiveSharedWall.Data C := by
    refine ⟨cn,positive,small,?_,?_,faces.1.lowerU,faces.2,
      positive_lowerV p hf hb h C frame cn positive small⟩
    · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
    · apply (frame.actual _ _).mpr; norm_num; exact point
  have first := C1092MPPMNegativeMissingPositiveSharedWall.left_order C L
    (by rw [frame.side]; change 1<(p.square _).side; rw [p.congruent]; exact p.side_gt_one)
    (frame.side.trans ((p.congruent _).trans (p.congruent _).symm)) data
    (by
      apply (actual _ _).mpr
      norm_num
      simpa [marker] using mark p hf 8 12 (by decide +kernel))
    (by apply (actual _ _).mpr; norm_num; exact leftOrigin)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((actual _ _).mp own)).1
      linarith only [wall])
    (fun x y both => owners_disjoint p hf 4 8 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(actual _ _).mp both.2⟩)
  have center : centerY L=centerY (owners p 8)-2 := center_translate_y _ _ _
  rw [center] at first
  have last := C1092MPPMMissingNegativeCenters.actual_bottom_order
    p' family' context ordinary missing D dframe dn
  rw [owners_transport g p hf 9] at last
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    center_pullSwap_x,center_pullSwap_y,center_pullY_x,center_pullY_y] at last
  linarith only [first,last]

/-- The same edge in the normalized Q4-to-Q5 direction. Both frames
are transported together, including the preceding missing membership. -/
theorem successor_retaining_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (positive : 0<D.s)
    (forward : (owners p 5).Inside 2 (87/50)) : False := by
  have family' := family_transport (rotation 1) p hf
  have previous : ActualFrame ((rotation 3).pullPacking ((rotation 1).pullPacking p)) C := by
    apply rotated_frame p hf 1 3 C
    change ActualFrame ((rotation 0).pullPacking p) C
    exact identity_frame p hf C frame
  have forward' : (owners ((rotation 1).pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport (rotation 1) p hf 4]
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact forward
  have missing' : ¬(owners ((rotation 1).pullPacking p) 7).Inside 2 (113/50) := by
    rw [owners_transport (rotation 1) p hf 7]
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact missing
  exact missing_predecessor_retaining_impossible ((rotation 1).pullPacking p) family'
    (rotation_context p hf hb 1) (Ordinary.rotated p hf h 1)
    D dframe dn positive forward' C previous cn missing'

end
#print axioms positive_half_angle
#print axioms missing_predecessor_retaining_impossible
#print axioms successor_retaining_impossible
end N12Compact.C1092MPPMNegativeMissingPositiveActual
