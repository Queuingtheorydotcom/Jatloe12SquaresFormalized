import Compact.Completion.C1092.MPPMNegativeCrosspointGeometry
import Compact.Completion.C1092.MPPMSteepPositiveNegativeProfileActual

/-! Literal OOOO adapter for retaining-negative crosspoint transfer.
The same actual Q9 supplies its strict origin, marker, outer point and
real floor; the common-chart Q5 is clockwise of its own-sector frame.
The four negative scalar modes remain a separately named dependency.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeCrosspointGeometry
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMActualRetaining
open C1092MPPMNegativeCrosspointSupport
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
    Input C (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2) := by
  let E := C1092MMMPEndingAxes.clockwise D
  let B := (owners p 9).translated 2 2
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have origin := bottom_origin_of_missing p hf hb
    (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    h.southwest.1 h.southwest.2 forward
  refine ⟨C1092MPPMSteepPositiveNegativeProfile.actual_input p hf hb h forward missing
      C frame cn sp D dframe dn retaining,
    frame.side.trans ((p.congruent _).trans (p.congruent _).symm),?_,?_,?_,?_,?_,?_⟩
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

theorem actual_negative_mode (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 4).Inside (3/2) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (retaining : (owners p 5).Inside 2 (87/50)) :
    ∃ Q : OpenSquare,Q.side=(owners p 9).side ∧
      (∀ x y,Q.Inside x y↔(owners p 9).Inside (2+x) (2+y)) ∧ Quarter Q.c Q.s ∧
      NegativeMode C.c C.s D.c (-D.s) Q.c Q.s := by
  obtain ⟨Q,side,inside,quarter,negative⟩ := one_mode_negative C
    (C1092MMMPEndingAxes.clockwise D) ((owners p 9).translated 2 2)
    (actual_input p hf hb h forward missing C frame cn sp D dframe dn retaining)
  exact ⟨Q,side,fun x y => (inside x y).trans
    (inside_translated_iff (owners p 9) 2 2 x y),quarter,negative⟩

def ScalarProof : Prop := ∀ c s d t : ℝ,Normal c s→Normal d t→3/5≤s→8*t≤3*d→
  ModesNonnegative c s d t

/-- The retaining-negative successor transfers the strict crosspoint
once its separately proved four continuous scalar modes are supplied.
The preceding-origin exclusion is derived by the existing positive
producer; no named owner for that excluded origin is required. -/
theorem crosspoint_of_scalars (scalar : ScalarProof)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (retaining : (owners p 5).Inside 2 (87/50)) :
    (owners p 4).Inside (3/2) 2 := by
  apply Classical.byContradiction
  intro missing
  have input := actual_input p hf hb h forward missing C frame cn sp D dframe dn retaining
  have faces := C1092MPPMSteepPositiveNegativeProfile.profile C
    (C1092MMMPEndingAxes.clockwise D) input.central
  have dp : 0<D.c := by linarith only [(normal_bounds dn).1]
  have shallow := (div_lt_iff₀ dp).mp faces.shallow
  change -D.s < 3/8*D.c at shallow
  have modes := scalar C.c C.s D.c (-D.s) cn dn input.central.steep
    (by linarith only [shallow])
  exact impossible_of_modes C (C1092MMMPEndingAxes.clockwise D)
    ((owners p 9).translated 2 2) input modes

end
#print axioms actual_input
#print axioms actual_negative_mode
#print axioms crosspoint_of_scalars
end N12Compact.C1092MPPMNegativeCrosspointGeometry
