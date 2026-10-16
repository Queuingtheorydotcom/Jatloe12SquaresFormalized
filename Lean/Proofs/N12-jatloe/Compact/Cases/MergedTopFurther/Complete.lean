import Compact.Cases.MergedTopFurther.Ownership
import Compact.Cases.MergedTopFurther.Geometry

/-! Complete original-family sources for 697, 698 and 699. Their singleton
right square supplies an actual interior segment through both needed row
points. Both signs of the merged-top square's canonical frame are covered.
No new geometry or ownership hypothesis is added to the packing. -/
namespace N12Compact.MergedTopFurther
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

theorem a_high (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) : (owner v p 5).Inside 2 (5/2) := by
  have input (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ v : Variant, P ∈ queryInsidePoints (masks v i) 2 (owned i)) :
      (owner v p i).Inside P.1 P.2 := inside v p hf i P (check v)
  have missing (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ v : Variant, P ∈ queryOutsidePoints (masks v i) 2 (owned i)) :
      ¬ (owner v p i).Inside P.1 P.2 := outside v p hf i P (check v)
  apply Geometry.a_high (owner v p 5) (owner v p 9) (owner v p 3)
  · change 1 < (p.square _).side
    rw [p.congruent]; exact p.side_gt_one
  · simpa using close (input 5 (2,113/50) (by decide +kernel))
  · simpa using close (input 5 (113/50,2) (by decide +kernel))
  · simpa using close (input 5 (47/20,47/20) (by decide +kernel))
  · simpa using missing 5 (33/20,33/20) (by decide +kernel)
  · simpa using missing 5 (47/20,33/20) (by decide +kernel)
  · simpa using close (input 9 (33/20,47/20) (by decide +kernel))
  · simpa using input 3 (3,113/50) (by decide +kernel)
  · simpa using input 3 (3,72/25) (by decide +kernel)
  · exact apart v p hf 5 9 (by decide)
  · exact apart v p hf 5 3 (by decide)

private theorem positive_impossible (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (B : OpenSquare)
    (sideB : B.side = (owner v p 9).side)
    (insideB : ∀ x y, B.Inside x y ↔ (owner v p 9).Inside x y)
    (closedB : ∀ x y, ClosedInside B x y ↔ ClosedInside (owner v p 9) x y)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c) : False := by
  have side (i : Fin 10) : (owner v p i).side = p.commonSide := p.congruent _
  have input (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ v : Variant, P ∈ queryInsidePoints (masks v i) 2 (owned i)) :
      (owner v p i).Inside P.1 P.2 := inside v p hf i P (check v)
  have missing (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ v : Variant, P ∈ queryOutsidePoints (masks v i) 2 (owned i)) :
      ¬ (owner v p i).Inside P.1 P.2 := outside v p hf i P (check v)
  have ePoint : (p.square (ownerIndex p 192)).Inside 1 3 := by
    simpa using seed_inside v p hf 192 (by cases v <;> decide +kernel)
      (1,3) (by decide +kernel)
  have rLow : (owner v p 3).Inside 3 (113/50) := by
    simpa using input 3 (3,113/50) (by decide +kernel)
  have rHigh : (owner v p 3).Inside 3 (72/25) := by
    simpa using input 3 (3,72/25) (by decide +kernel)
  have rRow := (Geometry.right_points (owner v p 3) rLow rHigh).1
  apply Geometry.positive_impossible (owner v p 5) B (owner v p 2)
    (p.square (ownerIndex p 192)) bc bs bsc
  · exact (side 5).trans ((sideB.trans (side 9)).symm)
  · rw [sideB,side]; exact p.side_gt_one
  · simpa using close (input 5 (2,113/50) (by decide +kernel))
  · simpa using close (input 5 (113/50,2) (by decide +kernel))
  · simpa using input 5 (47/20,47/20) (by decide +kernel)
  · exact a_high v p hf
  · simpa using missing 5 (47/20,33/20) (by decide +kernel)
  · intro h
    exact apart v p hf 5 3 (by decide) _ _ ⟨h,rRow⟩
  · apply (closedB _ _).mpr
    simpa using close (input 9 (33/20,47/20) (by decide +kernel))
  · apply (closedB _ _).mpr
    simpa using close (input 9 (8/5,3) (by decide +kernel))
  · apply (insideB _ _).mpr
    simpa using input 9 (2,1543/500) (by decide +kernel)
  · simpa using input 2 (113/50,3) (by decide +kernel)
  · exact ePoint
  · intro x y h
    exact apart v p hf 5 9 (by decide) x y ⟨h.1,(insideB _ _).mp h.2⟩
  · intro x y h
    exact apart v p hf 9 2 (by decide) x y ⟨(insideB _ _).mp h.1,h.2⟩
  · intro x y h
    exact owner_apart_mask v p hf 9 192 (by cases v <;> decide +kernel)
      (by cases v <;> decide +kernel) x y ⟨(insideB _ _).mp h.1,h.2⟩

/-- All three original families, without an orientation restriction. -/
theorem impossible (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) : False := by
  obtain ⟨B,bc,bsc,sideB,insideB,closedB⟩ := ClosedFrames.canonical_frame (owner v p 9)
  have bs : B.s < 0 := by
    apply lt_of_not_ge
    intro positive
    exact positive_impossible v p hf B sideB insideB closedB bc positive
      (by simpa only [abs_of_nonneg positive] using bsc)
  obtain ⟨L,lc,lsc,sideL,insideL,closedL⟩ := ClosedFrames.canonical_frame (owner v p 6)
  have side (i : Fin 10) : (owner v p i).side = p.commonSide := p.congruent _
  have input (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ v : Variant, P ∈ queryInsidePoints (masks v i) 2 (owned i)) :
      (owner v p i).Inside P.1 P.2 := inside v p hf i P (check v)
  have missing (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ v : Variant, P ∈ queryOutsidePoints (masks v i) 2 (owned i)) :
      ¬ (owner v p i).Inside P.1 P.2 := outside v p hf i P (check v)
  have lowBarrier : (p.square (ownerIndex p 2)).Inside (19/25) (187/100) := by
    simpa using seed_inside v p hf 2 (by cases v <;> decide +kernel)
      (19/25,187/100) (by decide +kernel)
  apply C849Negative.impossible B L (p.square (ownerIndex p 192)) bc bs.le
    (by simpa only [abs_of_neg bs] using bsc) lc lsc
  · rw [sideB,side]; exact p.side_gt_one
  · rw [sideB,side]; exact p.side_le
  · exact (sideB.trans (side 9)).trans ((sideL.trans (side 6)).symm)
  · exact (p.congruent _).trans ((sideB.trans (side 9)).symm)
  · intro x y h
    exact p.contained _ x y ((insideL x y).mp h)
  · exact p.contained _
  · apply (insideB _ _).mpr
    simpa using input 9 (33/20,47/20) (by decide +kernel)
  · apply (closedB _ _).mpr
    simpa using close (input 9 (8/5,3) (by decide +kernel))
  · apply (insideB _ _).mpr
    simpa using input 9 (2,1543/500) (by decide +kernel)
  · intro h
    exact apart v p hf 5 9 (by decide) _ _ ⟨a_high v p hf,(insideB _ _).mp h⟩
  · intro h
    exact apart v p hf 9 2 (by decide) _ _
      ⟨(insideB _ _).mp h,by simpa using input 2 (113/50,3) (by decide +kernel)⟩
  · apply (closedL _ _).mpr
    simpa using close (input 6 (457/500,2) (by decide +kernel))
  · apply (closedL _ _).mpr
    simpa using close (input 6 (1,12/5) (by decide +kernel))
  · intro h
    exact owner_apart_mask v p hf 6 2 (by cases v <;> decide +kernel)
      (by cases v <;> decide +kernel) _ _ ⟨(insideL _ _).mp h,lowBarrier⟩
  · intro h
    exact missing 6 (33/20,33/20) (by decide +kernel)
      (by simpa using (insideL _ _).mp h)
  · simpa using seed_inside v p hf 192 (by cases v <;> decide +kernel)
      (1,1543/500) (by decide +kernel)
  · simpa using seed_inside v p hf 192 (by cases v <;> decide +kernel)
      (457/500,3) (by decide +kernel)
  · intro x y h
    exact apart v p hf 9 6 (by decide) x y
      ⟨(insideB x y).mp h.1,(insideL x y).mp h.2⟩
  · intro x y h
    exact owner_apart_mask v p hf 9 192 (by cases v <;> decide +kernel)
      (by cases v <;> decide +kernel) x y ⟨(insideB x y).mp h.1,h.2⟩

#print axioms impossible
end N12Compact.MergedTopFurther
