import Compact.Bridge.C977OuterWings
import Compact.Bridge.C977PositiveBottomWest

/-! The exact remaining original C977 cover. Owning the container center
is retained as a separate obligation; it is not excluded by the signed
missing-center argument. No whole-case exclusion is asserted here. -/
namespace N12Compact.C977Residual
open S12 S12Pilot S12Completion.C977
set_option Elab.async false

/-- Every canonical frame is a representation of the same actual square.
The missing-center branch also fixes the southwest auxiliary signature. -/
def SignedEscape (p : NormalizedPacking) : Prop :=
  ¬(p.square (orderedOwner p 5)).Inside 2 2 ∧
  ∃ q : Fin 12 → OpenSquare,
    (∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c) ∧
    (∀ i, (q i).side=(p.square (orderedOwner p i)).side) ∧
    (∀ i x y, (q i).Inside x y ↔ (p.square (orderedOwner p i)).Inside x y) ∧
    (q 0).s<0 ∧ 0<(q 5).s ∧ (p.square (orderedOwner p 1)).Inside 1 1 ∧
    natCombinedOwners p (orderedOwner p 5)={4,13}

def Alternatives (p : NormalizedPacking) : Prop :=
  (p.square (orderedOwner p 5)).Inside 2 2 ∨ SignedEscape p

private theorem escape_signature (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (A : OpenSquare)
    (an : Normal A.c A.s) (strict : 0<A.s)
    (equivalent : ∀ x y, A.Inside x y ↔ (p.square (orderedOwner p 5)).Inside x y)
    (missing : ¬(p.square (orderedOwner p 5)).Inside 2 2) :
    natCombinedOwners p (orderedOwner p 5)={4,13} := by
  obtain ⟨marker0,d0,e0,_,_,_⟩ := C977CentralReach.central_data p hf
  have marker := (equivalent _ _).mpr marker0
  have d := (equivalent _ _).mpr d0
  have e := (equivalent _ _).mpr e0
  have ab := normal_bounds an
  have cap : A.loU+A.side≤2*(A.c+A.s) := by
    apply le_of_not_gt
    intro high
    apply missing
    apply (equivalent 2 2).mp
    exact ⟨by linarith only [marker.1,ab.1,an.1],by linarith only [high],
      by linarith only [d.2.2.1,ab.1],by linarith only [e.2.2.2,an.1]⟩
  have noTop : 5∉natCombinedOwners p (orderedOwner p 5) := by
    intro h
    have point := (nat_combined_exact p (orderedOwner p 5) 5 (by decide)).mpr h
    have inside : A.Inside 2 (113/50) := (equivalent _ _).mpr (by
      simpa [auxPoints,fPoints,gPoints] using point)
    linarith only [inside.2.1,cap,strict]
  have noRight : 16∉natCombinedOwners p (orderedOwner p 5) := by
    intro h
    have point := (nat_combined_exact p (orderedOwner p 5) 16 (by decide)).mpr h
    have inside : A.Inside (113/50) 2 := (equivalent _ _).mpr (by
      simpa [auxPoints,fPoints,gPoints] using point)
    linarith only [inside.2.1,cap,ab.1]
  have check : ∀ owned ∈ pruningDomain4 5,
      5∉owned → 16∉owned → owned={4,13} := by decide
  exact check _ (pruned_auxiliary_domain_actual p hf 5) noTop noRight

/-- The missing southwest corner does not imply that the central point
is missing. This disjunction retains both actual possibilities. -/
theorem alternatives (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1) : Alternatives p := by
  classical
  by_cases center : (p.square (orderedOwner p 5)).Inside 2 2
  · exact Or.inl center
  · choose q hc canonical shape equivalent closed using
      fun (i : Fin 12) => ClosedFrames.canonical_frame (p.square (orderedOwner p i))
    obtain ⟨negative,positive,corner⟩ := C977PositiveBottomWest.frame_residual
      p hf q shape equivalent (canonical 0) (canonical 5) missingCorner center
    have an : Normal (q 5).c (q 5).s :=
      ⟨positive.le,by simpa only [abs_of_pos positive] using canonical 5,
        (q 5).unit_normal⟩
    exact Or.inr ⟨center,q,fun i => ⟨hc i,canonical i⟩,shape,equivalent,
      negative,positive,corner,escape_signature p hf (q 5) an positive (equivalent 5) center⟩

/-- Every original packing reaches one of the two residual alternatives
while preserving the original canonical root, all wall constraints and
the entire surviving auxiliary vector. -/
theorem canonical_remaining_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) :
    ∃ q : NormalizedPacking,
      (q=p ∨ q=transposePacking p) ∧ codedMarkerFamily q=family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q,
        WallHalfSpaces q w (C977WallCenters.expandWallBranch (false,false)) ∧
        actualAuxiliaryVector q∈C977OuterWings.remainingVectors ∧ Alternatives q := by
  obtain ⟨q,frame,familyQ,missing,bounds,w,walls,vector⟩ :=
    C977OuterWings.canonical_remaining_cover p hf
  exact ⟨q,frame,familyQ,missing,bounds,w,walls,vector,
    alternatives q familyQ missing.entrance.corner_missing⟩

/-- A whole ending must discharge both alternatives in the same original
context. Supplying only the signed escape ending does not exclude C977. -/
theorem excludes_case_of_two_endings
    (endings : ∀ p : NormalizedPacking, codedMarkerFamily p=family →
      StrengthenedMissingCorner (p.square (orderedOwner p 0)) →
      CanonicalCornerBounds (p.square (orderedOwner p 0)) →
      ∀ w : WallOwners p,
        WallHalfSpaces p w (C977WallCenters.expandWallBranch (false,false)) →
        actualAuxiliaryVector p∈C977OuterWings.remainingVectors →
        ((p.square (orderedOwner p 5)).Inside 2 2 → False) ∧
          (SignedEscape p → False)) : ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨q,_,familyQ,missing,bounds,w,walls,vector,remaining⟩ :=
    canonical_remaining_cover p hf
  have finish := endings q familyQ missing bounds w walls vector
  exact remaining.elim finish.1 finish.2

#print axioms alternatives
#print axioms canonical_remaining_cover
#print axioms excludes_case_of_two_endings
end N12Compact.C977Residual
