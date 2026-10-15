import Compact.Completion.C1092.MPPMMissingNegativeCrosspointGeometry
import Compact.Completion.C1092.MPPMActualRetaining

/-! Actual-owner entrance for the positive-to-missing-negative
crosspoint transfer. The same actual Q10 owns the whole foreign right
bar, and the same actual Q9 supplies its marker, outer point, derived
origin and real floor. No owner is assigned to an omitted forward point.
Only the four explicit continuous scalar inequalities remain separate.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMActualRetaining
open C1092MPPMMissingNegativeCrosspointSupport
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

/-- Both endpoints of this entire excluded successor bar belong to
actual Q10, including the retained wall endpoint at 1.74. -/
theorem right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (y : ℝ) (low : -(14/25)≤y) (high : y≤-(13/50)) :
    (owners p 10).Inside 3 (2+y) :=
  CommonCases.OriginalOwners.vertical_segment (owners p 10) 3 (36/25) (87/50) (2+y)
    (far_points p hf hb h).2.2.1
    (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.1
    (by norm_num) (by linarith only [low]) (by linarith only [high])

theorem actual_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (nextMissing : ¬(owners p 5).Inside 2 (87/50)) :
    Input C (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2) := by
  let E := C1092MMMPEndingAxes.clockwise D
  let B := (owners p 9).translated 2 2
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have f := missing_profile p hf hb h.southwest.1 h.southwest.2 forward
    (far_points p hf hb h).2.1 C frame cn
  have cap := actual_missing_crosspoint_caps p hf hb h forward missing C frame cn sp
  have origin := bottom_origin_of_missing p hf hb
    (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    h.southwest.1 h.southwest.2 forward
  have bOrigin : B.Inside 0 (-1) := by
    apply (bactual _ _).mpr; norm_num; exact origin
  have recipient : RecipientInput E B := by
    refine ⟨?_,dn,?_,?_,?_,?_,?_,?_,?_,bOrigin,?_⟩
    · rw [ef.side]; exact side_gt p 5
    · apply (ef.actual _ _).mpr
      norm_num
      simpa [marker] using mark p hf 5 9 (by decide +kernel)
    · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.2
    · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.1
    · apply (ef.actual _ _).mpr; norm_num
      exact C1092MPPMActualNegativeHalfpoint.southeast_of_missing p hf hb h nextMissing
    · intro own
      have original := (ef.actual _ _).mp own
      norm_num at original
      have corner : (owners p 1).Inside 3 1 := by
        simpa [cornerOwner,cornerPoint] using corner_points p hf 1
      exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨original,corner⟩
    · intro own
      have original := (ef.actual _ _).mp own
      norm_num at original
      exact nextMissing original
    · intro y low high own
      have original := (ef.actual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 10 (by decide) _ _
        ⟨original,right_bar p hf hb h y low high⟩
    · exact fun x y both => owners_disjoint p hf 9 5 (by decide) _ _
        ⟨(bactual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  refine ⟨?_,frame.side.trans ((side_same p 4 5).trans ef.side.symm),
    frame.side.trans (side_same p 4 9),cn,(steep_sine cn cap.2).le,
    f.lowerU,cap.1,f.upperV,?_,?_,recipient,?_,?_,?_,?_⟩
  · rw [frame.side]; exact side_gt p 4
  · apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
  · apply (bactual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  · apply (bactual _ _).mpr; norm_num
    exact C1092MPPMActualWallReduction.bottom_ordinary p hf hb
  · intro x y own
    have floor := (p.contained _ _ _ ((bactual _ _).mp own)).2.2.1
    linarith only [floor]
  · exact fun x y both => owners_disjoint p hf 9 4 (by decide) _ _
      ⟨(bactual _ _).mp both.1,(frame.actual _ _).mp both.2⟩

theorem actual_negative_mode (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (nextMissing : ¬(owners p 5).Inside 2 (87/50)) :
    ∃ Q : OpenSquare,Q.side=(owners p 9).side ∧
      (∀ x y,Q.Inside x y↔(owners p 9).Inside (2+x) (2+y)) ∧ Quarter Q.c Q.s ∧
      NegativeMode C.c C.s D.c (-D.s) Q.c Q.s := by
  obtain ⟨Q,side,inside,quarter,negative⟩ := one_mode_negative C
    (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2)
    (actual_input p hf hb h forward missing C frame cn sp D dframe dn nextMissing)
  exact ⟨Q,side,fun x y => (inside x y).trans
    (inside_translated_iff (owners p 9) 2 2 x y),quarter,negative⟩

def ScalarProof : Prop := ∀ c s d t : ℝ,Normal c s→Normal d t→3/5≤s→252/373≤t→
  ModesNonnegative c s d t

/-- The missing-negative case has no requested successor crosspoint:
its actual omitted forward point already forces the full strong profile.
The only separate dependency is the displayed continuous scalar theorem. -/
theorem crosspoint_of_scalars (scalar : ScalarProof)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (nextMissing : ¬(owners p 5).Inside 2 (87/50)) :
    (owners p 4).Inside (3/2) 2 := by
  apply Classical.byContradiction
  intro missing
  have input := actual_input p hf hb h forward missing C frame cn sp D dframe dn nextMissing
  have faces := recipient_faces (C1092MMMPEndingAxes.clockwise D)
    ((owners p 9).translated 2 2) input.recipient
  exact impossible_of_modes C (C1092MMMPEndingAxes.clockwise D)
    ((owners p 9).translated 2 2) input
    (scalar C.c C.s D.c (-D.s) cn dn input.steep faces.large)

end
#print axioms actual_input
#print axioms actual_negative_mode
#print axioms crosspoint_of_scalars
end N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
