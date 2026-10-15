import Compact.Completion.C1092.MPPMActualRetaining

/-! NEGATIVE-FORWARD-POSITIVE-H Theorem 1. The actual missing-wall
producer already yields U>=-c-s/2 and H<=s for the preceding positive
square. These stronger simultaneous faces give a short exact disk-free
proof of the same recipient exclusion. The excluded origin is not
assigned to a wall. All canonical signs, including zero, are retained.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualCentralOrigin
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092TwoFifths.Support
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

/-- A negative retaining successor cannot take its own preceding
origin from a positive predecessor with the actual missing-wall faces.
Only one actual C and one actual E occur in these support comparisons. -/
theorem local_exclusion (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cn : Normal C.c C.s) (sp : 0<C.s) (en : Normal E.c (-E.s))
    (floor : -C.c-C.s/2≤C.loU) (cap : C.loV+C.side≤C.s)
    (markerC : C.Inside (-7/20) (-7/20))
    (markerE : E.Inside (7/20) (-7/20))
    (bottomE : E.Inside (13/50) (-1)) (forwardE : E.Inside 0 (-13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) : ¬E.Inside 0 (-1) := by
  intro origin
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<C.c := by linarith only [cb.1]
  have dp : 0<E.c := by linarith only [eb.1]
  have sn : E.s≤0 := by linarith only [en.1]
  have cf : C1092MPPMOrdinaryNegativeHalfpoint.Frame C.c C.s :=
    ⟨cp,cn.1,cn.2.1,cn.2.2⟩
  have ef : C1092MPPMOrdinaryNegativeHalfpoint.Frame E.c (-E.s) :=
    ⟨dp,en.1,en.2.1,en.2.2⟩
  rcases C1092MPPMNonpositivePredecessor.positive_axes C E same cf ef
      markerC markerE bottomE apart with current|transverse|recipient
  · have last := (strict_bounds E 0 (-1) C.c C.s C.unit_normal origin).1
    linarith only [current,last,floor,side,cb.2.1,cn.1]
  · have unit : C.s^2+(-C.c)^2=1 := by nlinarith only [C.unit_normal]
    have last := (strict_bounds E 0 (-13/50) C.s (-C.c) unit forwardE).1
    have sine := (C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds cn).2.2.2.1
    linarith only [transverse,last,cap,side,cb.2.1,sine]
  · let k := C.c*E.c+C.s*E.s
    let ell := -C.c*E.s+C.s*E.c
    have first := mul_nonneg (sub_nonneg.mpr cn.2.1) dp.le
    have last := mul_nonneg cn.1
      (show 0≤E.c+E.s by linarith only [en.2.1])
    have kn : 0≤k := by dsimp [k]; nlinarith only [first,last]
    have ln : 0<ell := by
      have a := mul_nonneg cp.le en.1
      have b := mul_pos sp dp
      dsimp [ell]
      nlinarith only [a,b]
    have formula := upper_pos_neg C E.c E.s k (-ell)
      (by dsimp [k]; ring) (by dsimp [ell]; ring) kn (by linarith only [ln])
    have lower := mul_le_mul_of_nonneg_left floor kn
    have upper := mul_le_mul_of_nonneg_left cap ln.le
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<k+ell by linarith only [kn,ln])
    let A := C.c+C.s-1-C.c*C.s/2
    let B := C.c-C.s+C.s^2/2-13/50
    have cs := mul_nonneg cp.le cn.1
    have chord := mul_nonneg
      (show 0≤C.c+C.s-1 by linarith only [cb.2.2.2.2.1])
      (show 0≤17/7-(1+C.c+C.s) by linarith only [cb.2.2.2.2.2])
    have An : 0≤A := by
      dsimp [A]
      nlinarith only [chord,cn.2.2,cs]
    have square := mul_nonneg cp.le (show 0≤1-C.c by linarith only [cb.2.1])
    have joint : 0<A+B := by
      dsimp [A,B]
      nlinarith only [square,cn.2.2,sq_nonneg (C.c-C.s),cb.1]
    have margin0 := mul_nonneg An
      (show 0≤E.c+E.s by linarith only [en.2.1])
    have margin1 := mul_nonneg joint.le en.1
    have margin : 0≤A*E.c+B*(-E.s) := by nlinarith only [margin0,margin1]
    have identity : k*(C.side-C.c-C.s/2)-ell*(C.s-C.side)+(13/50)*E.s=
        A*E.c+B*(-E.s)+(C.side-1)*(k+ell) := by
      dsimp [k,ell,A,B]
      linear_combination -E.c*C.unit_normal
    have own : E.loU< -(13/50)*E.s := by linarith only [forwardE.1]
    nlinarith only [formula,lower,upper,strict,margin,identity,own,recipient]

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

/-- If Q5 owned its preceding origin, actual Q9 would omit that origin.
The positive source is then a theorem about the genuine preceding Q4;
its stronger faces and the local exclusion give the contradiction. -/
theorem successor_retaining_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (E : OpenSquare) (frame : SuccessorFrame p E) (en : Normal E.c (-E.s))
    (forward : (owners p 5).Inside 2 (87/50)) : ¬(owners p 5).Inside 2 1 := by
  intro own
  have absent : ¬(owners p 9).Inside 2 1 := fun foreign =>
    owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,foreign⟩
  obtain ⟨C,source⟩ := positive_source p hf hb h absent
  have side : 1<C.side := by
    rw [source.frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have same : C.side=E.side := source.frame.side.trans
    (((p.congruent _).trans (p.congruent _).symm).trans frame.side.symm)
  apply local_exclusion C E side same source.normal source.positive en source.lowerU source.upperV
  · apply (source.frame.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  · apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  · apply (frame.actual _ _).mpr; norm_num; exact h.southeast.2
  · apply (frame.actual _ _).mpr; norm_num; exact forward
  · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(source.frame.actual _ _).mp both.1,(frame.actual _ _).mp both.2⟩
  · apply (frame.actual _ _).mpr; norm_num; exact own

/-- The actual nonpositive Q4 retaining exclusion, including the axis.
The complete packing is rotated, with its true paired corners and walls. -/
theorem nonpositive_retaining_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2) : ¬(owners p 4).Inside 1 2 := by
  let g := rotation 3
  have family' := family_transport g p hf
  have target : ActualFrame ((rotation 1).pullPacking (g.pullPacking p)) C := by
    apply rotated_frame p hf 3 1 C
    change ActualFrame ((rotation 0).pullPacking p) C
    exact identity_frame p hf C frame
  have ef := successor_frame (g.pullPacking p) family' C target
  have forward' : (owners (g.pullPacking p) 5).Inside 2 (87/50) := by
    rw [owners_transport g p hf 5]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact forward
  have excluded := successor_retaining_excluded (g.pullPacking p) family'
    (rotation_context p hf hb 3) (Ordinary.rotated p hf h 3)
    (C1092MMMPEndingAxes.clockwise C) ef cn forward'
  intro own
  apply excluded
  rw [owners_transport g p hf 5]
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullY]
  exact own

/-- Every retaining central excludes its own preceding origin for all
canonical signs. Missing-forward nonpositive owners remain a separate
producer; positive owners of either membership are already covered. -/
theorem retaining_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cp : 0<C.c) (canonical : |C.s|≤C.c)
    (forward : (owners p 4).Inside (87/50) 2) : ¬(owners p 4).Inside 1 2 := by
  by_cases positive : 0<C.s
  · exact positive_previous_excluded p hf hb h C frame
      ⟨positive.le,by simpa only [abs_of_pos positive] using canonical,C.unit_normal⟩ positive
  · have nonpositive : C.s≤0 := le_of_not_gt positive
    apply nonpositive_retaining_excluded p hf hb h C frame
      ⟨by linarith only [nonpositive],?_,by nlinarith only [C.unit_normal]⟩ forward
    simpa only [abs_of_nonpos nonpositive] using canonical

end
#print axioms local_exclusion
#print axioms nonpositive_retaining_excluded
#print axioms retaining_excluded
end N12Compact.C1092MPPMActualCentralOrigin
