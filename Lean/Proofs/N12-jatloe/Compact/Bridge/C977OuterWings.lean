import Compact.Geometry.CentralOuterWing
import Compact.Bridge.C977CentralReach
import Compact.Bridge.C977CentralWingReach

/-! Both outer wing points have unique, uniform central owners in C977.
This is a consequence of the original packing, including the southwest
central square's two genuine crosspoints. No saved enclosure is used.
The reduced finite cover is not a whole-case exclusion. -/
namespace N12Compact.C977OuterWings
open S12 S12Pilot S12Completion.C977
set_option Elab.async false

private theorem forced (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) (n : Nat)
    (h : ∀ owned ∈ pruningDomain4 i, n ∈ owned) :
    n ∈ natCombinedOwners p (orderedOwner p i) :=
  h _ (pruned_auxiliary_domain_actual p hf i)

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (different : i ≠ j) : orderedOwner p i ≠ orderedOwner p j :=
  fun h => different (ordered_owner_injective p hf h)

/-- The inward top auxiliary point forces the outer top wing, because
the original southwest owner strictly contains `(1.5,2)`. -/
theorem top_of_inner (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (inner : 5 ∈ natCombinedOwners p (orderedOwner p 7)) :
    (p.square (orderedOwner p 7)).Inside (8/5) 3 := by
  have markers := coded_exact p (orderedOwner p 7)
  rw [ordered_owner_code p hf 7] at markers
  have hp : (p.square (orderedOwner p 7)).Inside (33/20) (47/20) := by
    have h := (markers 11).mpr (by decide)
    simpa [Owns,marker] using h
  have hd : (p.square (orderedOwner p 7)).Inside 2 (113/50) := by
    have h := (nat_combined_exact p (orderedOwner p 7) 5 (by decide)).mpr inner
    simpa [auxPoints,fPoints,gPoints] using h
  have hw : (p.square (orderedOwner p 7)).Inside (87/50) 3 := by
    have h := (nat_combined_exact p (orderedOwner p 7) 14 (by decide)).mpr
      (forced p hf 7 14 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have ht : ¬ (p.square (orderedOwner p 7)).Inside (47/20) (47/20) := by
    simpa [Owns,marker] using unused_marker_ten p hf (orderedOwner p 7)
  have hz := (C977CentralReach.central_points p hf).2
  exact CentralOuterWing.point _ (by rw [p.congruent]; exact p.side_gt_one)
    hp hd hw ht (fun h => p.disjoint _ _ (apart p hf 7 5 (by decide)) _ _ ⟨h,hz⟩)

/-- The exact transposed statement uses the other actual crosspoint; it
does not transpose or renormalize the original packing. -/
theorem right_of_inner (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (inner : 16 ∈ natCombinedOwners p (orderedOwner p 6)) :
    (p.square (orderedOwner p 6)).Inside 3 (8/5) := by
  have markers := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at markers
  have hp : (p.square (orderedOwner p 6)).Inside (47/20) (33/20) := by
    have h := (markers 9).mpr (by decide)
    simpa [Owns,marker] using h
  have hd : (p.square (orderedOwner p 6)).Inside (113/50) 2 := by
    have h := (nat_combined_exact p (orderedOwner p 6) 16 (by decide)).mpr inner
    simpa [auxPoints,fPoints,gPoints] using h
  have hw : (p.square (orderedOwner p 6)).Inside 3 (87/50) := by
    have h := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr
      (forced p hf 6 8 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have ht : ¬ (p.square (orderedOwner p 6)).Inside (47/20) (47/20) := by
    simpa [Owns,marker] using unused_marker_ten p hf (orderedOwner p 6)
  have hz := (C977CentralReach.central_points p hf).1
  have result := CentralOuterWing.point (pullSwap (p.square (orderedOwner p 6)))
    (by change 1 < (p.square (orderedOwner p 6)).side
        rw [p.congruent]; exact p.side_gt_one)
    ((inside_pullSwap _ _ _).mpr hp) ((inside_pullSwap _ _ _).mpr hd)
    ((inside_pullSwap _ _ _).mpr hw)
    (fun h => ht ((inside_pullSwap _ _ _).mp h))
    (fun h => p.disjoint _ _ (apart p hf 6 5 (by decide)) _ _
      ⟨(inside_pullSwap _ _ _).mp h,hz⟩)
  exact (inside_pullSwap _ _ _).mp result

/-- Both boundary wing assignments are forced in every original packing
with this marker family. In particular, the paired corners and wall
squares cannot independently take either of these auxiliary points. -/
theorem owned (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    18 ∈ natCombinedOwners p (orderedOwner p 6) ∧
      3 ∈ natCombinedOwners p (orderedOwner p 7) := by
  constructor
  · have check : ∀ owned ∈ pruningDomain4 6, 18 ∈ owned ∨ 16 ∈ owned := by decide
    rcases check _ (pruned_auxiliary_domain_actual p hf 6) with h | h
    · exact h
    · apply (nat_combined_exact p (orderedOwner p 6) 18 (by decide)).mp
      simpa [auxPoints,fPoints,gPoints] using right_of_inner p hf h
  · have check : ∀ owned ∈ pruningDomain4 7, 3 ∈ owned ∨ 5 ∈ owned := by decide
    rcases check _ (pruned_auxiliary_domain_actual p hf 7) with h | h
    · exact h
    · apply (nat_combined_exact p (orderedOwner p 7) 3 (by decide)).mp
      simpa [auxPoints,fPoints,gPoints] using top_of_inner p hf h

theorem points (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (p.square (orderedOwner p 6)).Inside 3 (8/5) ∧
      (p.square (orderedOwner p 7)).Inside (8/5) 3 := by
  have h := owned p hf
  constructor
  · have x := (nat_combined_exact p (orderedOwner p 6) 18 (by decide)).mpr h.1
    simpa [auxPoints,fPoints,gPoints] using x
  · have x := (nat_combined_exact p (orderedOwner p 7) 3 (by decide)).mpr h.2
    simpa [auxPoints,fPoints,gPoints] using x

def OuterConditions (v : List (Finset Nat)) : Prop :=
  18 ∈ v[6]! ∧ 3 ∈ v[7]!

instance (v : List (Finset Nat)) : Decidable (OuterConditions v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem actual_outer_conditions (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : OuterConditions (actualAuxiliaryVector p) := by
  unfold OuterConditions
  erw [actual_auxiliary_slot p 6,actual_auxiliary_slot p 7]
  exact owned p hf

def remainingVectors : List (List (Finset Nat)) :=
  C977CentralWingReach.remainingVectors.filter fun v => decide (OuterConditions v)

/-- This retains every actual vector after the new geometric implications.
No count or terminal contradiction is asserted before the whole replay. -/
theorem canonical_remaining_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q,
        WallHalfSpaces q w (C977WallCenters.expandWallBranch (false,false)) ∧
        actualAuxiliaryVector q ∈ remainingVectors := by
  obtain ⟨q,hframe,hq,hm,hbounds,w,hb,hv⟩ :=
    C977CentralWingReach.canonical_remaining_cover p hf
  refine ⟨q,hframe,hq,hm,hbounds,w,hb,?_⟩
  exact List.mem_filter.mpr ⟨hv,decide_eq_true (actual_outer_conditions q hq)⟩

#print axioms owned
#print axioms canonical_remaining_cover
end N12Compact.C977OuterWings
