import Compact.Completion.C1092.MPPMNegativeRecipientWall
import Compact.Completion.C1092.MPPMMissingNegativeActual

/-! The remaining universal preceding-origin exclusion. A nonpositive
missing-forward central uses only its weak profile; no preceding-origin
omission is fed into that producer. Hypothetical ownership forces two
incompatible slopes of the same actual preceding boundary. Simultaneous
whole-packing turns supply all four literal sectors. Source only. -/
namespace N12Compact.C1092MPPMActualCentralOrigin
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

/-- The missing-negative Q5 cannot take Q9's origin. Both angle
comparisons concern the same reframe B of that actual Q9. -/
theorem successor_missing_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (D : OpenSquare) (frame : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (missing : ¬(owners p 5).Inside 2 (87/50)) :
    ¬(owners p 5).Inside 2 1 := by
  intro own
  have absent : ¬(owners p 9).Inside 2 1 := fun foreign =>
    owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,foreign⟩
  obtain ⟨B,b⟩ := missing_bottom_negative p hf hb h absent
  let E := C1092MMMPEndingAxes.clockwise D
  have ef : SuccessorFrame p E := successor_frame p hf D frame
  have missing' : ¬(owners ((rotation 1).pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport (rotation 1) p hf 4]
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact missing
  have weak := C1092MPPMMissingNegativeProfile.actual_weak ((rotation 1).pullPacking p)
    (family_transport (rotation 1) p hf) (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) missing' D frame dn
  have bounds := C1092MPPMNegativeRecipientWall.Scalars.weak_bounds dn weak.halfLow
  have input : C1092MPPMNegativeRecipientWall.Input E B := by
    refine ⟨?_,ef.side.trans ((side_same p 5 9).trans b.side.symm),dn,b.normal,b.negative,
      ?_,?_,weak.upperU,bounds,?_,?_,?_,?_,?_⟩
    · rw [ef.side]; exact side_gt p 5
    · apply (ef.actual _ _).mpr; norm_num; exact own
    · dsimp [E,C1092MMMPEndingAxes.clockwise]
      linarith only [weak.upperV]
    · apply (b.actual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
    · apply (b.actual _ _).mpr; norm_num
      exact (wall_auxiliaries p hb).2.1
    · intro point
      have original := (b.actual _ _).mp point
      norm_num at original
      have foreign : (owners p 0).Inside 1 (457/500) := by
        simpa [marker] using marker_point p hf 0 0 (by decide +kernel)
      exact owners_disjoint p hf 9 0 (by decide) _ _ ⟨original,foreign⟩
    · intro x y point
      have wall := (p.contained _ _ _ ((b.actual _ _).mp point)).2.2.1
      linarith only [wall]
    · exact fun x y both => owners_disjoint p hf 9 5 (by decide) _ _
        ⟨(b.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  have steep := C1092MPPMNegativeRecipientWall.steep E B input
  have bp : 0<B.c := by linarith only [(normal_bounds b.normal).1]
  have shallow := (div_lt_iff₀ bp).mp b.shallow
  linarith only [steep,shallow]

/-- The same missing-negative producer on the literal original Q4.
The quarter turn transports all twelve actual owners at once. -/
theorem nonpositive_missing_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (missing : ¬(owners p 4).Inside (87/50) 2) : ¬(owners p 4).Inside 1 2 := by
  let g := rotation 3
  have family' := family_transport g p hf
  have target : ActualFrame ((rotation 1).pullPacking (g.pullPacking p)) C := by
    apply rotated_frame p hf 3 1 C
    change ActualFrame ((rotation 0).pullPacking p) C
    exact identity_frame p hf C frame
  have missing' : ¬(owners (g.pullPacking p) 5).Inside 2 (87/50) := by
    rw [owners_transport g p hf 5]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact missing
  have excluded := successor_missing_excluded (g.pullPacking p) family'
    (rotation_context p hf hb 3) (Ordinary.rotated p hf h 3) C target cn missing'
  intro own
  apply excluded
  rw [owners_transport g p hf 5]
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullY]
  exact own

/-- Every ordinary canonical central excludes its preceding origin,
for every sign and both strict forward memberships. No ownership of
that excluded origin by a boundary is asserted. -/
theorem previous_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (canonical : |C.s|≤C.c) :
    ¬(owners p 4).Inside 1 2 := by
  by_cases positive : 0<C.s
  · exact positive_previous_excluded p hf hb h C frame
      ⟨positive.le,(abs_le.mp canonical).2,C.unit_normal⟩ positive
  · have nonpositive := le_of_not_gt positive
    have cn : Normal C.c (-C.s) :=
      ⟨by linarith only [nonpositive],by linarith only [(abs_le.mp canonical).1],
        by nlinarith only [C.unit_normal]⟩
    by_cases forward : (owners p 4).Inside (87/50) 2
    · exact nonpositive_retaining_excluded p hf hb h C frame cn forward
    · exact nonpositive_missing_excluded p hf hb h C frame cn forward

/-- The stronger missing-negative profile now has its actual omitted
origin produced, instead of carrying it as an entrance hypothesis. -/
theorem missing_strong_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) :
    C1092MPPMMissingNegativeProfile.StrongFaces C := by
  have canonical : |C.s|≤C.c := by
    rw [abs_of_nonpos (show C.s≤0 by linarith only [cn.1])]
    exact cn.2.1
  exact C1092MPPMMissingNegativeProfile.actual_strong p hf hb h missing
    (previous_excluded p hf hb h C frame canonical) C frame cn

end
#print axioms successor_missing_excluded
#print axioms previous_excluded
#print axioms missing_strong_profile
end N12Compact.C1092MPPMActualCentralOrigin
