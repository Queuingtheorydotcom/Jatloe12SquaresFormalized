import Compact.Completion.C1092.MPPMNegativeOwnedPositiveCeiling
import Compact.Completion.C1092.MPPMActualNonpositiveCore
import Compact.Completion.C1092.MPPMNegativeOwnedPositiveExclusion

/-! The genuine negative-retaining to positive-retaining angle entrance.
The predecessor's vertex clearance is produced from its whole actual Q8
bar, in its own simultaneously rotated chart. Its physical reframe W
then retains all those same faces and the same actual marker. Source only. -/
namespace N12Compact.C1092MPPMNegativeOwnedPositiveActual
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

/-- Corollary 2 of NEGATIVE-OWNED-POSITIVE-CEILING, with every
predecessor face and strict clearance obtained from the original owners. -/
theorem positive_half_angle (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (forward : (owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 3).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (previousForward : (owners p 7).Inside 2 (113/50)) :
    C.s/(1+C.c)<11/100 := by
  let g := rotation 3
  let p' := g.pullPacking p
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 3
  have ordinary := Ordinary.rotated p hf h 3
  have retaining : (owners p' 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact previousForward
  have next : (owners p' 5).Inside 2 (87/50) := by
    rw [owners_transport g p hf 5]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact forward
  have core := C1092MPPMActualNonpositive.actual_core p' family' context ordinary D dframe dn retaining
  let B := (owners p' 9).translated 2 2
  have bactual (x y : ℝ) : B.Inside x y↔(owners p' 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p' 9) 2 2 x y
  have nextMissing : ¬D.Inside 0 (-13/50) := by
    intro own
    have original := (dframe.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p' family' 4 5 (by decide) _ _ ⟨original,next⟩
  have bar (x : ℝ) (low : -(14/25)≤x) (high : x≤0) : B.Inside x (-1) := by
    apply (bactual _ _).mpr
    norm_num
    exact C1092MPPMActualNonpositive.bottom_bar p' family' context ordinary D dframe dn (2+x)
      (by linarith only [low]) (by linarith only [high])
  have apart : ∀ x y,¬(D.Inside x y ∧ B.Inside x y) :=
    fun x y both => owners_disjoint p' family' 4 9 (by decide) _ _
      ⟨(dframe.actual _ _).mp both.1,(bactual _ _).mp both.2⟩
  have cleared := C1092MPPMAllNonpositive.clearance D B core nextMissing
    (by simpa only [neg_div] using bar) apart
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
  have input : C1092MPPMNegativeOwnedPositiveCeiling.Input C W := by
    refine ⟨?_,frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans wside.symm),
      cn,positive,dn,?_,?_,?_,?_,faces.1.lowerV,?_,?_,?_,?_,?_⟩
    · rw [frame.side]
      change 1<(p.square _).side
      rw [p.congruent]
      exact p.side_gt_one
    · change 87/100<D.c
      linarith only [cleared.close]
    · apply (frame.actual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
    · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
    · apply (frame.actual _ _).mpr; norm_num; exact forward
    · apply (wactual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
    · rw [wv]
      change -D.loU-D.side+D.side≤D.c
      linarith only [cleared.lowerU]
    · rw [wu]
      exact cleared.upperV
    · rw [wu,wv]
      change -1<D.c*D.loV-D.s*(-D.loU-D.side)
      nlinarith only [cleared.vertex]
    · exact fun x y both => owners_disjoint p hf 4 7 (by decide) _ _
        ⟨(frame.actual _ _).mp both.1,(wactual _ _).mp both.2⟩
  exact C1092MPPMNegativeOwnedPositiveCeiling.half_lt C W input

/-- The same angle ceiling normalized as a Q4-to-Q5 signed edge. -/
theorem recipient_half_angle (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (positive : 0<D.s)
    (nextForward : (owners p 5).Inside 2 (87/50)) : D.s/(1+D.c)<11/100 := by
  let g := rotation 1
  have family' := family_transport g p hf
  have previous : ActualFrame ((rotation 3).pullPacking (g.pullPacking p)) C := by
    apply rotated_frame p hf 1 3 C
    change ActualFrame ((rotation 0).pullPacking p) C
    exact identity_frame p hf C frame
  have forward' : (owners (g.pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact nextForward
  have previousForward : (owners (g.pullPacking p) 7).Inside 2 (113/50) := by
    rw [owners_transport g p hf 7]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact forward
  exact positive_half_angle (g.pullPacking p) family' (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) D dframe dn positive forward' C previous cn previousForward

/-- The full genuine raw forward input shared with the retaining-edge
obstruction. Its preceding-D and northwest omissions come from Core;
the full foreign segment remains in one actual Q9. -/
theorem forward_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (nextForward : (owners p 5).Inside 2 (87/50)) :
    C1092MPPMNegativeForward.Input C (C1092MMMPEndingAxes.clockwise D)
      ((owners p 9).translated 2 2) := by
  let E := C1092MMMPEndingAxes.clockwise D
  let B := (owners p 9).translated 2 2
  have ef := successor_frame p hf D dframe
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have core := C1092MPPMActualNonpositive.actual_core p hf hb h C frame cn forward
  refine ⟨core.side,
    frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans ef.side.symm),
    cn,dn,core.marker,core.ordinary,core.outer,core.forward,core.origin,core.northwest,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · apply (ef.actual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.2
  · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.1
  · apply (ef.actual _ _).mpr; norm_num; exact nextForward
  · intro x low high
    apply (bactual _ _).mpr
    norm_num
    exact C1092MPPMActualNonpositive.bottom_bar p hf hb h C frame cn (2+x)
      (by linarith only [low]) (by linarith only [high])
  · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  · exact fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(bactual _ _).mp both.2⟩

/-- The full actual retaining-negative to retaining-positive edge is
impossible. Its angle ceiling, source clearance and all target face
inputs have been derived from the same named actual squares. -/
theorem retaining_edge_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (positive : 0<D.s)
    (nextForward : (owners p 5).Inside 2 (87/50)) : False := by
  let E := C1092MMMPEndingAxes.clockwise D
  let B := (owners p 9).translated 2 2
  have ef := successor_frame p hf D dframe
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have ceiling := recipient_half_angle p hf hb h C frame cn forward D dframe dn positive nextForward
  have input : C1092MPPMNegativeOwnedPositiveExclusion.Input C E B := by
    refine ⟨forward_input p hf hb h C frame cn forward D dframe dn nextForward,
      positive,?_,?_,?_,?_⟩
    · change D.s/(1+D.c)≤7/32
      linarith only [ceiling]
    · intro own
      have original := (ef.actual _ _).mp own
      norm_num at original
      have corner : (owners p 1).Inside 3 1 := by
        simpa [cornerOwner,cornerPoint] using corner_points p hf 1
      exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨original,corner⟩
    · intro own
      have original := (ef.actual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 10 (by decide) _ _
        ⟨original,(far_points p hf hb h).2.2.1⟩
    · exact fun x y both => owners_disjoint p hf 5 9 (by decide) _ _
        ⟨(ef.actual _ _).mp both.1,(bactual _ _).mp both.2⟩
  exact C1092MPPMNegativeOwnedPositiveExclusion.impossible C E B input

end
#print axioms positive_half_angle
#print axioms recipient_half_angle
#print axioms forward_input
#print axioms retaining_edge_impossible
end N12Compact.C1092MPPMNegativeOwnedPositiveActual
