import Compact.Geometry.SouthwestCentralReach
import Completion.Cases.C977.AuxiliaryContext
import Completion.Cases.C977.Anchors

/-! Two simultaneous strict points of the original C977 southwest central
owner. The hypotheses are only the original normalized packing and family;
in particular no wall branch, missing-corner root, or saved pose is chosen. -/
namespace N12Compact.C977CentralReach

open S12 S12Pilot S12Completion.C977
set_option Elab.async false

private theorem forced_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (n : Nat)
    (h : ∀ owned ∈ pruningDomain4 5, n ∈ owned) :
    n ∈ natCombinedOwners p (orderedOwner p 5) :=
  h _ (pruned_auxiliary_domain_actual p hf 5)

/-- The southwest central owner's actual three-point triangle, together
with its absence from each of the other central markers. -/
theorem central_data (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (p.square (orderedOwner p 5)).Inside (33/20) (33/20) ∧
    (p.square (orderedOwner p 5)).Inside 2 (87/50) ∧
    (p.square (orderedOwner p 5)).Inside (87/50) 2 ∧
    ¬ (p.square (orderedOwner p 5)).Inside (47/20) (47/20) ∧
    ¬ (p.square (orderedOwner p 5)).Inside (33/20) (47/20) ∧
    ¬ (p.square (orderedOwner p 5)).Inside (47/20) (33/20) := by
  have markers := coded_exact p (orderedOwner p 5)
  rw [ordered_owner_code p hf 5] at markers
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have h := (markers 8).mpr (by decide)
    simpa [Owns,marker] using h
  · have h := (nat_combined_exact p (orderedOwner p 5) 4 (by decide)).mpr
      (forced_auxiliary p hf 4 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  · have h := (nat_combined_exact p (orderedOwner p 5) 13 (by decide)).mpr
      (forced_auxiliary p hf 13 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  · intro h
    have absent : (10 : Marker) ∉ maskSupport (auxiliaryCode 5) := by decide
    exact absent ((markers 10).mp (by simpa [Owns,marker] using h))
  · intro h
    have absent : (11 : Marker) ∉ maskSupport (auxiliaryCode 5) := by decide
    exact absent ((markers 11).mp (by simpa [Owns,marker] using h))
  · intro h
    have absent : (9 : Marker) ∉ maskSupport (auxiliaryCode 5) := by decide
    exact absent ((markers 9).mp (by simpa [Owns,marker] using h))

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (j : Fin 12) (different : (5 : Fin 12) ≠ j) :
    ∀ x y, ¬ ((p.square (orderedOwner p 5)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

/-- The two strict crosspoints needed by the complete-square corner
interaction. This is a uniform geometric consequence, not a case exclusion. -/
theorem central_points (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (p.square (orderedOwner p 5)).Inside 2 (3/2) ∧
    (p.square (orderedOwner p 5)).Inside (3/2) 2 := by
  obtain ⟨hP,hD,hE,hNE,hNW,hSE⟩ := central_data p hf
  have ha : 1 < (p.square (orderedOwner p 5)).side := by
    rw [p.congruent]; exact p.side_gt_one
  have leftAnchors := code_two_original_anchors p (orderedOwner p 1)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 1)
  have bottomAnchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  exact ⟨SouthwestCentralReach.below _ _ ha hP hD hE hNE hNW hSE
      leftAnchors.1 leftAnchors.2.1 (apart p hf 1 (by decide)),
    SouthwestCentralReach.left _ _ ha hP hD hE hNE hNW hSE
      bottomAnchors.near_point bottomAnchors.horizontal_point
      (apart p hf 0 (by decide))⟩

#print axioms central_points

end N12Compact.C977CentralReach
