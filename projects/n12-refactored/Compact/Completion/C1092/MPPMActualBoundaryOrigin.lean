import Compact.Completion.C1092.MPPMActualNegativeHalfpoint
import Compact.Completion.C1092.MPPMMissingBoundaryShallowActual
import Compact.Completion.C1092.MPPMPositiveBoundaryOrigin
import Compact.Completion.C1092.MPPMPositiveForwardUpperCap
import Compact.Completion.C1092.MPPMPositiveOriginWallAngle

/-! Actual positive-predecessor production under a missing Q9 origin.
The Q4 sign, forward point, halfpoint exclusion and all three required
faces are conclusions. A whole original Q0 corner segment remains in that
one actual owner. The completed upper-cap and origin arguments force the
same actual missing-origin boundary to be strictly negative and shallow.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualBoundaryOrigin
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

/-- The lower-u alternative is forced by the actual halfpoint and NW
marker exclusions. The other candidate exit would make the square's
transverse width at most .85c−.65s<1. -/
theorem halfpoint_floor (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (positive : 0<C.s)
    (M : C.Inside (-7/20) (-7/20))
    (P : C.Inside (-1) (-13/50)) (G : C.Inside (-1) (-2/5))
    (T : C.Inside (-13/50) 0)
    (H : ¬C.Inside (-1) (-1/2)) (N : ¬C.Inside (-7/20) (7/20)) :
    -C.c-C.s/2≤C.loU := by
  have bounds := normal_bounds cn
  have cp : 0<C.c := by linarith only [bounds.1]
  apply le_of_not_gt
  intro low
  have lowerV : C.s-C.c/2≤C.loV := by
    apply le_of_not_gt
    intro lowV
    apply H
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,lowV,G.2.1,G.2.2.2,positive,cp]
  have shallow : 13*C.s<3*C.c := by linarith only [lowerV,M.2.2.1]
  have upperV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt
    intro high
    apply N
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [P.1,T.2.1,M.2.2.1,high,shallow,cp,positive]
  linarith only [lowerV,upperV,side,bounds.2.1,cn.1]

/-- A physical-coordinate frame for the same actual Q4. It merely
undoes the common translation; canonical coefficients do not change. -/
theorem owner_frame (p : NormalizedPacking) (C : OpenSquare) (frame : ActualFrame p C) :
    C1092MPPMForwardPositiveD.OwnerFrame p 4 (C.translated (-2) (-2)) := by
  constructor
  · exact frame.side
  · intro x y
    rw [inside_translated_iff,frame.actual]
    rw [show (2:ℝ)+(-2+x)=x by ring,show (2:ℝ)+(-2+y)=y by ring]

structure PositiveSource (p : NormalizedPacking) (C : OpenSquare) : Prop where
  frame : ActualFrame p C
  normal : Normal C.c C.s
  positive : 0<C.s
  forward : (owners p 4).Inside (87/50) 2
  previous : ¬(owners p 4).Inside 1 2
  lowerU : -C.c-C.s/2≤C.loU
  upperV : C.loV+C.side≤C.s

theorem positive_source (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 9).Inside 2 1) : ∃ C : OpenSquare,PositiveSource p C := by
  have bottom := C1092MPPMActualWallReduction.bottom_ordinary p hf hb
  have forward : (owners p 4).Inside (87/50) 2 := by
    apply Classical.byContradiction
    intro absent
    exact missing (bottom_origin_of_missing p hf hb bottom h.southwest.1 h.southwest.2 absent)
  obtain ⟨C,frame,cp,range⟩ := exists_canonical_frame p
  have physical := owner_frame p C frame
  have positive : 0<C.s := by
    apply lt_of_not_ge
    intro nonpositive
    exact missing (C1092MPPMActualNegativeHalfpoint.bottom_origin p hf hb h
      (C.translated (-2) (-2)) physical cp range nonpositive)
  have normal : Normal C.c C.s :=
    ⟨positive.le,by simpa only [abs_of_pos positive] using range,C.unit_normal⟩
  have previous := C1092MPPMActualNegativeHalfpoint.southwest_positive_previous_excluded
    p hf hb h forward (C.translated (-2) (-2)) physical cp positive.le
  have core := forward_core p hf bottom h.southwest.1 h.southwest.2 forward previous C frame
  have faces := C1092MPPMPositiveCrosspointSeeds.forward_profile C
    (by rw [frame.side]; exact side_gt p 4) normal core
  have half := C1092MPPMForwardPositiveD.corner_halfpoint_of_missing_bottom_origin
    p hf bottom missing
  have northwest : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using mark p hf 7 11 (by decide +kernel)
  have halfMissing : ¬C.Inside (-1) (-1/2) := by
    intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨original,half⟩
  have northMissing : ¬C.Inside (-7/20) (7/20) := by
    intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 4 7 (by decide) _ _ ⟨original,northwest⟩
  have floor := halfpoint_floor C (by rw [frame.side]; exact side_gt p 4)
    normal positive core.marker core.ordinaryP core.ordinaryG core.forward halfMissing northMissing
  exact ⟨C,frame,normal,positive,forward,previous,floor,faces.upperV⟩

theorem corner_segment (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : -543/500≤y) (high : y≤-1) : (owners p 0).Inside 1 (2+y) := by
  have M : (owners p 0).Inside 1 (457/500) := by
    simpa [marker] using mark p hf 0 0 (by decide +kernel)
  have K : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  exact CommonCases.OriginalOwners.vertical_segment _ _ _ _ _ M K
    (by norm_num) (by linarith only [low]) (by linarith only [high])

theorem PositiveSource.complete (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (C : OpenSquare) (source : PositiveSource p C) :
    C1092MPPMMissingBoundaryShallow.CentralProfile C :=
  ⟨source.normal,source.positive,source.lowerU,
    C1092MPPMPositiveForwardUpperCap.upper_cap p hf hb h source.forward C source.frame
      source.normal source.positive,source.upperV⟩

structure NegativeBoundary (p : NormalizedPacking) (B : OpenSquare) : Prop where
  side : B.side=(owners p 9).side
  actual : ∀ x y,B.Inside x y↔(owners p 9).Inside (2+x) (2+y)
  normal : Normal B.c (-B.s)
  negative : 0< -B.s
  shallow : (-B.s)/B.c<1/4

/-- Full POSITIVE-BOUNDARY-ORIGIN §§6--7 and missing-boundary shallow
application. The raw positive-source profile, its upper cap, the actual
negative boundary sign and the shallow bound are all derived here. -/
theorem missing_bottom_negative (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 9).Inside 2 1) : ∃ B : OpenSquare,NegativeBoundary p B := by
  obtain ⟨C,source⟩ := positive_source p hf hb h missing
  have central := PositiveSource.complete p hf hb h C source
  let Q := (owners p 9).translated 2 2
  obtain ⟨B,bp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame Q
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    (inside x y).trans (inside_translated_iff (owners p 9) 2 2 x y)
  have frames : C1092MPPMMissingBoundaryShallow.ActualFrames p C B :=
    ⟨source.frame.side,shape,source.frame.actual,bactual⟩
  have negative : 0< -B.s := by
    apply lt_of_not_ge
    intro bad
    have positive : Normal B.c B.s :=
      ⟨by linarith only [bad],(le_abs_self B.s).trans canonical,B.unit_normal⟩
    have bm : (owners p 9).Inside 2 (457/500) := by
      simpa [marker] using mark p hf 9 13 (by decide +kernel)
    have input : C1092MPPMPositiveBoundaryOrigin.Input C B := by
      refine ⟨?_,?_,source.normal,positive,central.lowerU,central.upperU,
        central.upperV,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · rw [source.frame.side]; exact side_gt p 4
      · exact source.frame.side.trans
          (((p.congruent _).trans (p.congruent _).symm).trans shape.symm)
      · apply (source.frame.actual _ _).mpr; norm_num; exact h.southwest.2
      · apply (source.frame.actual _ _).mpr; norm_num; exact source.forward
      · apply (bactual _ _).mpr; norm_num; exact bm
      · apply (bactual _ _).mpr; norm_num
        exact C1092MPPMActualWallReduction.bottom_ordinary p hf hb
      · apply (bactual _ _).mpr; norm_num; exact (wall_auxiliaries p hb).2.1
      · intro x y own
        have wall := (p.contained _ _ _ ((bactual _ _).mp own)).2.2.1
        linarith only [wall]
      · intro y low high own
        have original := (bactual _ _).mp own
        norm_num at original
        exact owners_disjoint p hf 9 0 (by decide) _ _
          ⟨original,corner_segment p hf y low high⟩
      · exact fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
          ⟨(source.frame.actual _ _).mp both.1,(bactual _ _).mp both.2⟩
    have original := (bactual _ _).mp (C1092MPPMPositiveBoundaryOrigin.origin C B input)
    norm_num at original
    exact missing original
  have normal : Normal B.c (-B.s) := ⟨negative.le,
    by simpa only [abs_of_neg (show B.s<0 by linarith only [negative])] using canonical,
    by nlinarith only [B.unit_normal]⟩
  have small := C1092MPPMMissingBoundaryShallow.actual_shallow p hf hb h.southwest.2
    source.forward missing C B frames central normal negative
  exact ⟨B,shape,bactual,normal,negative,small.2⟩

/-- A positive missing-forward Q4 cannot take Q8's origin. If it did,
the same actual Q8 would have slope below 1/4 and above 5/12. -/
theorem missing_positive_previous_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s) :
    ¬(owners p 4).Inside 1 2 := by
  intro own
  have absent : ¬(owners p 8).Inside 1 2 := fun foreign =>
    owners_disjoint p hf 4 8 (by decide) _ _ ⟨own,foreign⟩
  let g := rotation 3
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 3
  have absentB : ¬(owners (g.pullPacking p) 9).Inside 2 1 := by
    rw [owners_transport g p hf 9]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact absent
  obtain ⟨B,b⟩ := missing_bottom_negative (g.pullPacking p) family' context
    (Ordinary.rotated p hf h 3) absentB
  let L := C1092MMMPEndingAxes.clockwise
    (C1092MMMPEndingAxes.clockwise (C1092MMMPEndingAxes.clockwise B))
  have lActual (x y : ℝ) : L.Inside x y↔(owners p 8).Inside (2+x) (2+y) := by
    simp only [L,C1092MMMPEndingAxes.inside_clockwise,neg_neg]
    rw [b.actual,owners_transport g p hf 9]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY] <;> congr 1 <;> ring
  have lSide : L.side=(owners p 8).side := by
    change B.side=(owners p 8).side
    rw [b.side,owners_transport g p hf 9]
    rfl
  have steep := C1092MPPMPositiveOriginWallAngle.actual_steep p hf hb h missing own
    C frame cn sp L ⟨lSide,lActual⟩ b.normal
  have bp : 0<B.c := by linarith only [(normal_bounds b.normal).1]
  have shallow := (div_lt_iff₀ bp).mp b.shallow
  change 5*B.c<12*(-B.s) at steep
  nlinarith only [steep,shallow,bp]

/-- The complete ordinary positive-central preceding-origin exclusion,
including both literal forward memberships and ordinary/inward overlap. -/
theorem positive_previous_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s) :
    ¬(owners p 4).Inside 1 2 := by
  by_cases forward : (owners p 4).Inside (87/50) 2
  · have physical := owner_frame p C frame
    exact C1092MPPMActualNegativeHalfpoint.southwest_positive_previous_excluded p hf hb h
      forward (C.translated (-2) (-2)) physical
      (by linarith only [(normal_bounds cn).1]) sp.le
  · exact missing_positive_previous_excluded p hf hb h forward C frame cn sp

/-- Every missing-positive face is available from an actual preceding-D
exclusion. No owner of that excluded D is asserted or required. -/
theorem missing_positive_data (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s) :
    C1092MPPMMissingPositiveBoundaries.Data C := by
  have inputs := missing_inputs p hf hb h.southwest.1 h.southwest.2 missing
    (far_points p hf hb h).2.1 C frame
  apply C1092MPPMMissingPositiveBoundaries.Data.of_inputs C cn inputs
  intro own
  have original := (frame.actual _ _).mp own
  norm_num at original
  exact positive_previous_excluded p hf hb h C frame cn sp original

/-- The universal positive face table, including every ordinary/inward
overlap and both forward memberships. All four faces are conclusions. -/
theorem positive_faces (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s) :
    C1092MPPMPositiveCrosspointSeeds.ForwardFaces C ∧ C.loU+C.side≤0 := by
  by_cases forward : (owners p 4).Inside (87/50) 2
  · exact C1092MPPMPositiveForwardUpperCap.faces p hf hb h forward C frame cn sp
  · have input := missing_positive_data p hf hb h forward C frame cn sp
    have faces := C1092MPPMMissingPositiveBoundaries.profile C
      (by rw [frame.side]; exact side_gt p 4) input
    have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
    exact ⟨⟨faces.lowerU,by linarith only [faces.lowerV,sp],faces.upperV⟩,
      by linarith only [faces.upperU,cp]⟩

/-- An omitted positive missing-forward crosspoint forces its actual
upper-u face and the strict half-angle entrance above 1/3. -/
theorem missing_crosspoint_caps (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (f : C1092MPPMMissingPositiveFaces.Faces C)
    (G : C.Inside (-1) (-2/5)) (missing : ¬C.Inside (-1/2) 0) :
    C.loU+C.side≤-C.c/2 ∧ 1+C.c<3*C.s := by
  have bounds := normal_bounds cn
  have cp : 0<C.c := by linarith only [bounds.1]
  have cap : C.loU+C.side≤-C.c/2 := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,G.1,f.upperV,f.lowerV,side,cp,f.positive,bounds.2.1,
        bounds.2.2.2.1]
  have width : 1<C.c/2+C.s := by linarith only [side,cap,f.lowerU]
  let q := C1092WallProfileScalars.half C.c C.s
  have data := C1092WallProfileScalars.quarter_data C.c C.s cp.le cn.1 cn.2.2
  have qp : 0<q := div_pos f.positive (by linarith only [cp])
  have high : q<1 := by
    apply (div_lt_one (show 0<1+C.c by linarith only [cp])).mpr
    linarith only [cn.2.1]
  have identity : (1+q^2)*(C.c/2+C.s-1)=(1-q)*(3*q-1)/2 := by
    linear_combination (1/2)*data.2.2.2.1+data.2.2.2.2
  have positive := mul_pos (show 0<1+q^2 by positivity)
    (show 0<C.c/2+C.s-1 by linarith only [width])
  have steep : 1/3<q := by
    apply lt_of_not_ge
    intro low
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1-q by linarith only [high])
      (show 3*q-1≤0 by linarith only [low])
    nlinarith only [identity,positive,bad]
  have angle := (lt_div_iff₀ (show 0<1+C.c by linarith only [cp])).mp
    (show (1/3:ℝ)<C.s/(1+C.c) from steep)
  exact ⟨cap,by linarith only [angle]⟩

theorem actual_missing_crosspoint_caps (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (crosspoint : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s) :
    C.loU+C.side≤-C.c/2 ∧ 1+C.c<3*C.s := by
  have f := missing_profile p hf hb h.southwest.1 h.southwest.2 forward
    (far_points p hf hb h).2.1 C frame cn
  apply missing_crosspoint_caps C (by rw [frame.side]; exact side_gt p 4) cn f
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.2
  · intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact crosspoint original

theorem steep_sine {c s : ℝ} (normal : Normal c s) (steep : 1+c<3*s) : 3/5<s := by
  apply lt_of_not_ge
  intro small
  have cosine := C977CornerSectorBounds.cosine_order
    (show Normal (4/5) (3/5) by norm_num [Normal]) normal small
  linarith only [steep,cosine,small]

end
#print axioms halfpoint_floor
#print axioms positive_source
#print axioms corner_segment
#print axioms missing_bottom_negative
#print axioms positive_previous_excluded
#print axioms positive_faces
#print axioms actual_missing_crosspoint_caps
end N12Compact.C1092MPPMActualBoundaryOrigin
