import Compact.Bridge.C977Residual
import Compact.Bridge.C977NextBottomWall
import Compact.Geometry.OwnedWestBottomAngle
import Compact.Geometry.PositiveWallPositiveLeft

/-! The entire original C977 missing-center signed escape is impossible.
The actual southwest O/A pair forces a shallow negative bottom frame in
both west-point alternatives; the original next-wall/paired-corner chain
then supplies the contradiction. Center ownership is still a separate
whole-case obligation. Source only, uncompiled. -/
namespace N12Compact.C977SignedEscapeClosure

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

/-- Both west-point alternatives use the same original O/A squares.
No independent pose domains or ownership-vector cases enter the bound. -/
theorem small_bottom (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (t : ℝ) (os : (q 0).s=-t) (on : Normal (q 0).c t)
    (an : Normal (q 5).c (q 5).s)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (missingCenter : ¬(p.square (orderedOwner p 5)).Inside 2 2) : t<1/5 := by
  have same : (q 0).side=(q 5).side := by rw [shape,shape,p.congruent,p.congruent]
  have side : 1<(q 5).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have box : InsideContainer (q 0) := fun x y h =>
    p.contained _ x y ((equivalent 0 x y).mp h)
  have anchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have om := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at om
  have oMarker : (q 0).Inside 1 (457/500) := (equivalent 0 _ _).mpr (by
    have h := (om 0).mpr (by decide)
    simpa [Owns,marker] using h)
  have oNear := (equivalent 0 _ _).mpr anchors.near_point
  have oFar := (equivalent 0 _ _).mpr anchors.lower_point
  have oCorner : ¬(q 0).Inside 1 1 := fun h => missingCorner ((equivalent 0 _ _).mp h)
  have oMissing : ¬(q 0).Inside 2 (457/500) := by
    intro h
    have absent : (13 : Marker)∉maskSupport (auxiliaryCode 0) := by decide
    exact absent ((om 13).mp (by simpa [Owns,marker] using (equivalent 0 _ _).mp h))
  obtain ⟨marker0,d0,e0,_,northwest0,_⟩ := C977CentralReach.central_data p hf
  have aMarker := (equivalent 5 _ _).mpr marker0
  have aD := (equivalent 5 _ _).mpr d0
  have aE := (equivalent 5 _ _).mpr e0
  have cross := C977CentralReach.central_points p hf
  have aLow := (equivalent 5 _ _).mpr cross.1
  have aLeft := (equivalent 5 _ _).mpr cross.2
  have missingNW : ¬(q 5).Inside (33/20) (47/20) :=
    fun h => northwest0 ((equivalent 5 _ _).mp h)
  have lowOriginal : (p.square (orderedOwner p 1)).Inside 1 (8/5) := by
    have check : ∀ owned∈pruningDomain4 1, 10∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 1)
    have point := (nat_combined_exact p (orderedOwner p 1) 10 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have foreignLow : ¬(q 5).Inside 1 (8/5) := fun h =>
    apart p hf 5 1 (by decide) _ _ ⟨(equivalent 5 _ _).mp h,lowOriginal⟩
  have ab := normal_bounds an
  have cap : (q 5).loU+(q 5).side≤2*((q 5).c+(q 5).s) := by
    apply le_of_not_gt
    intro high
    apply missingCenter
    apply (equivalent 5 2 2).mp
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [aMarker.1,aD.2.2.1,aE.2.2.2,ab.1,an.1,high]
  have oa : ∀ x y, ¬((q 0).Inside x y ∧ (q 5).Inside x y) := fun x y h =>
    apart p hf 0 5 (by decide) x y
      ⟨(equivalent 0 _ _).mp h.1,(equivalent 5 _ _).mp h.2⟩
  by_cases west : (q 5).Inside 1 2
  · exact OwnedWestBottomAngle.small_bottom (q 0) (q 5) t os on an same side box
      oMarker oNear oFar oCorner oMissing aMarker aD aLeft aLow west cap missingNW foreignLow oa
  · exact (PositiveWallPositiveLeft.cuts (q 0) (q 5) t os on an same side box
      oMarker oNear oFar oCorner oMissing aMarker aD aLeft aLow cap west missingNW foreignLow oa).small

/-- Complete exclusion of the signed missing-center branch, in the
same original packing and with the genuine missing-corner premise. -/
theorem signed_escape_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (escape : C977Residual.SignedEscape p) : False := by
  rcases escape with ⟨missingCenter,q,canonical,shape,equivalent,negative,positive,_,_⟩
  let t : ℝ := -(q 0).s
  have os : (q 0).s=-t := by dsimp [t]; ring
  have on : Normal (q 0).c t := ⟨by dsimp [t]; linarith only [negative],
    by simpa only [t,abs_of_neg negative] using (canonical 0).2,
    by dsimp [t]; nlinarith only [(q 0).unit_normal]⟩
  have an : Normal (q 5).c (q 5).s :=
    ⟨positive.le,(le_abs_self _).trans (canonical 5).2,(q 5).unit_normal⟩
  have bound := small_bottom p hf q shape equivalent t os on an missingCorner missingCenter
  exact C977NextBottomWall.excludes_of_small_bottom p hf (q 0) t os on bound.le
    (shape 0) (equivalent 0) missingCorner

/-- Every genuine missing-corner realization of C977 therefore has the
southwest central owner at (2,2). This is not the whole-case exclusion. -/
theorem center_owned (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1) :
    (p.square (orderedOwner p 5)).Inside 2 2 := by
  rcases C977Residual.alternatives p hf missingCorner with center | escape
  · exact center
  · exact False.elim (signed_escape_excludes p hf missingCorner escape)

/-- The unchanged original case contract now needs only the center-owned
ending, with all genuine wall and auxiliary-vector premises retained. -/
theorem excludes_case_of_center_ending
    (ending : ∀ p : NormalizedPacking, codedMarkerFamily p=family →
      StrengthenedMissingCorner (p.square (orderedOwner p 0)) →
      CanonicalCornerBounds (p.square (orderedOwner p 0)) →
      ∀ w : WallOwners p,
        WallHalfSpaces p w (C977WallCenters.expandWallBranch (false,false)) →
        actualAuxiliaryVector p∈C977OuterWings.remainingVectors →
        (p.square (orderedOwner p 5)).Inside 2 2 → False) : ExcludesCase 977 := by
  apply C977Residual.excludes_case_of_two_endings
  intro p hf missing bounds w walls vector
  exact ⟨ending p hf missing bounds w walls vector,
    signed_escape_excludes p hf missing.entrance.corner_missing⟩

#print axioms small_bottom
#print axioms signed_escape_excludes
#print axioms center_owned
#print axioms excludes_case_of_center_ending
end N12Compact.C977SignedEscapeClosure
