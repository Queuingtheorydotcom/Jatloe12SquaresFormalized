import Compact.Geometry.CentralWingReach
import Compact.Bridge.C977OppositeWallExtras

/-! Two uniform central ownership implications in the original C977 family.
They use the actual lower-left central square as a foreign segment, so the
result does not combine independently saved pose domains. -/
namespace N12Compact.C977CentralWingReach
open S12 S12Pilot S12Completion.C977 FourSquareAnchors
open C977WallCenters C977OppositeWallCenters
set_option Elab.async false

private theorem forced_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) (n : Nat)
    (h : ∀ owned ∈ pruningDomain4 i, n ∈ owned) :
    n ∈ natCombinedOwners p (orderedOwner p i) :=
  h _ (pruned_auxiliary_domain_actual p hf i)

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (hij : i ≠ j) : orderedOwner p i ≠ orderedOwner p j :=
  fun h => hij (ordered_owner_injective p hf h)

private theorem closed_of_inside (q : OpenSquare) (x y : ℝ)
    (h : q.Inside x y) : ClosedInside q x y :=
  ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

/-- An inward top point in the right central square forces its lower
boundary point, using the two fixed points of the lower-left central owner. -/
theorem right_wing_point (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (extra : 5 ∈ natCombinedOwners p (orderedOwner p 6)) :
    (p.square (orderedOwner p 6)).Inside 3 (3/2) := by
  have markers := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at markers
  have hp : (p.square (orderedOwner p 6)).Inside (47/20) (33/20) := by
    have h := (markers 9).mpr (by decide)
    simpa [Owns,marker] using h
  have hd : (p.square (orderedOwner p 6)).Inside 2 (113/50) := by
    have h := (nat_combined_exact p (orderedOwner p 6) 5 (by decide)).mpr extra
    simpa [auxPoints,fPoints,gPoints] using h
  have hw : (p.square (orderedOwner p 6)).Inside 3 (87/50) := by
    have h := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr
      (forced_auxiliary p hf 6 8 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have ht : ¬ (p.square (orderedOwner p 6)).Inside (47/20) (47/20) := by
    simpa [Owns,marker] using unused_marker_ten p hf (orderedOwner p 6)
  have he : (p.square (orderedOwner p 5)).Inside 2 (87/50) := by
    have h := (nat_combined_exact p (orderedOwner p 5) 4 (by decide)).mpr
      (forced_auxiliary p hf 5 4 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have hm : (p.square (orderedOwner p 5)).Inside (87/50) 2 := by
    have h := (nat_combined_exact p (orderedOwner p 5) 13 (by decide)).mpr
      (forced_auxiliary p hf 5 13 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have rp : (pullX (p.square (orderedOwner p 6))).Inside (33/20) (33/20) := by
    rw [inside_pullX]; norm_num only; exact hp
  have rd : (pullX (p.square (orderedOwner p 6))).Inside 2 (113/50) := by
    rw [inside_pullX]; norm_num only; exact hd
  have hW : (pullX (p.square (orderedOwner p 6))).Inside 1 (87/50) := by
    rw [inside_pullX]; norm_num only; exact hw
  have rt : ¬ (pullX (p.square (orderedOwner p 6))).Inside (33/20) (47/20) := by
    rw [inside_pullX]; norm_num only; exact ht
  have re : ClosedInside (pullX (p.square (orderedOwner p 5))) 2 (87/50) := by
    apply closed_of_inside
    rw [inside_pullX]; norm_num only; exact he
  have rm : ClosedInside (pullX (p.square (orderedOwner p 5))) (113/50) 2 := by
    apply closed_of_inside
    rw [inside_pullX]; norm_num only; exact hm
  have reach := CentralWingReach.point_low _ _
    (by change 1 < (p.square (orderedOwner p 6)).side
        rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square (orderedOwner p 6)).side ≤ 1001/1000
        rw [p.congruent]; exact p.side_le)
    rp rd hW rt re rm
    (fun x y h => p.disjoint _ _ (apart p hf 6 5 (by decide)) (4-x) y
      ⟨(inside_pullX _ _ _).mp h.1,(inside_pullX _ _ _).mp h.2⟩)
  rw [inside_pullX] at reach
  norm_num only at reach
  exact reach

theorem right_wing (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (extra : 5 ∈ natCombinedOwners p (orderedOwner p 6)) :
    18 ∈ natCombinedOwners p (orderedOwner p 6) := by
  have low := right_wing_point p hf extra
  have w : (p.square (orderedOwner p 6)).Inside 3 (87/50) := by
    have h := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr
      (forced_auxiliary p hf 6 8 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have reach : (p.square (orderedOwner p 6)).Inside 3 (8/5) :=
    ⟨by linarith only [low.1,w.1],by linarith only [low.2.1,w.2.1],
      by linarith only [low.2.2.1,w.2.2.1],
      by linarith only [low.2.2.2,w.2.2.2]⟩
  apply (nat_combined_exact p (orderedOwner p 6) 18 (by decide)).mp
  simpa [auxPoints,fPoints,gPoints] using reach

/-- The transposed implication is transported at the square level, leaving
the original packing and its missing-corner normalization unchanged. -/
theorem top_wing_point (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (extra : 16 ∈ natCombinedOwners p (orderedOwner p 7)) :
    (p.square (orderedOwner p 7)).Inside (3/2) 3 := by
  have markers := coded_exact p (orderedOwner p 7)
  rw [ordered_owner_code p hf 7] at markers
  have hp : (p.square (orderedOwner p 7)).Inside (33/20) (47/20) := by
    have h := (markers 11).mpr (by decide)
    simpa [Owns,marker] using h
  have hd : (p.square (orderedOwner p 7)).Inside (113/50) 2 := by
    have h := (nat_combined_exact p (orderedOwner p 7) 16 (by decide)).mpr extra
    simpa [auxPoints,fPoints,gPoints] using h
  have hw : (p.square (orderedOwner p 7)).Inside (87/50) 3 := by
    have h := (nat_combined_exact p (orderedOwner p 7) 14 (by decide)).mpr
      (forced_auxiliary p hf 7 14 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have ht : ¬ (p.square (orderedOwner p 7)).Inside (47/20) (47/20) := by
    simpa [Owns,marker] using unused_marker_ten p hf (orderedOwner p 7)
  have he : (p.square (orderedOwner p 5)).Inside (87/50) 2 := by
    have h := (nat_combined_exact p (orderedOwner p 5) 13 (by decide)).mpr
      (forced_auxiliary p hf 5 13 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have hm : (p.square (orderedOwner p 5)).Inside 2 (87/50) := by
    have h := (nat_combined_exact p (orderedOwner p 5) 4 (by decide)).mpr
      (forced_auxiliary p hf 5 4 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have rp : (pullX (pullSwap (p.square (orderedOwner p 7)))).Inside
      (33/20) (33/20) := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hp
  have rd : (pullX (pullSwap (p.square (orderedOwner p 7)))).Inside 2 (113/50) := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hd
  have hW : (pullX (pullSwap (p.square (orderedOwner p 7)))).Inside 1 (87/50) := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hw
  have rt : ¬ (pullX (pullSwap (p.square (orderedOwner p 7)))).Inside
      (33/20) (47/20) := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact ht
  have re : ClosedInside (pullX (pullSwap (p.square (orderedOwner p 5))))
      2 (87/50) := by
    apply closed_of_inside
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact he
  have rm : ClosedInside (pullX (pullSwap (p.square (orderedOwner p 5))))
      (113/50) 2 := by
    apply closed_of_inside
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hm
  have reach := CentralWingReach.point_low _ _
    (by change 1 < (p.square (orderedOwner p 7)).side
        rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square (orderedOwner p 7)).side ≤ 1001/1000
        rw [p.congruent]; exact p.side_le)
    rp rd hW rt re rm (by
      intro x y h
      apply p.disjoint _ _ (apart p hf 7 5 (by decide)) y (4-x)
      simpa only [inside_pullX,inside_pullSwap] using h)
  rw [inside_pullX,inside_pullSwap] at reach
  norm_num only at reach
  exact reach

theorem top_wing (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (extra : 16 ∈ natCombinedOwners p (orderedOwner p 7)) :
    3 ∈ natCombinedOwners p (orderedOwner p 7) := by
  have low := top_wing_point p hf extra
  have w : (p.square (orderedOwner p 7)).Inside (87/50) 3 := by
    have h := (nat_combined_exact p (orderedOwner p 7) 14 (by decide)).mpr
      (forced_auxiliary p hf 7 14 (by decide))
    simpa [auxPoints,fPoints,gPoints] using h
  have reach : (p.square (orderedOwner p 7)).Inside (8/5) 3 :=
    ⟨by linarith only [low.1,w.1],by linarith only [low.2.1,w.2.1],
      by linarith only [low.2.2.1,w.2.2.1],
      by linarith only [low.2.2.2,w.2.2.2]⟩
  apply (nat_combined_exact p (orderedOwner p 7) 3 (by decide)).mp
  simpa [auxPoints,fPoints,gPoints] using reach

def WingConditions (v : List (Finset Nat)) : Prop :=
  (5 ∈ v[6]! → 18 ∈ v[6]!) ∧ (16 ∈ v[7]! → 3 ∈ v[7]!)

instance (v : List (Finset Nat)) : Decidable (WingConditions v) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → _)))

theorem actual_wing_conditions (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : WingConditions (actualAuxiliaryVector p) := by
  unfold WingConditions
  rw [actual_auxiliary_slot p 6,actual_auxiliary_slot p 7]
  exact ⟨right_wing p hf,top_wing p hf⟩

def remainingVectors : List (List (Finset Nat)) :=
  C977OppositeWallExtras.remainingVectors.filter fun v => decide (WingConditions v)

theorem remaining_vector_count : remainingVectors.length = 50 := by decide

/-- Original coverage after the uniform wing implications. This retains
the complete geometric premises and does not claim the remaining ending. -/
theorem canonical_remaining_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q,
        WallHalfSpaces q w (expandWallBranch (false,false)) ∧
        actualAuxiliaryVector q ∈ remainingVectors := by
  obtain ⟨q,hframe,hq,hm,hbounds,w,hb,hv⟩ :=
    C977OppositeWallExtras.canonical_remaining_cover p hf
  refine ⟨q,hframe,hq,hm,hbounds,w,hb,?_⟩
  exact List.mem_filter.mpr ⟨hv,decide_eq_true (actual_wing_conditions q hq)⟩

#print axioms right_wing
#print axioms top_wing
#print axioms right_wing_point
#print axioms top_wing_point
#print axioms canonical_remaining_cover
end N12Compact.C977CentralWingReach
