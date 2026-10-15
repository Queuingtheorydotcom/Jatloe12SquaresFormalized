import Compact.Cases.C849851.Ownership
import Compact.Cases.MergedTopFurther.Geometry
import Compact.Geometry.FourSquareLowerBarrier

/-! The completed positive sector is connected to each original packing.
The canonical frame only reindexes B's faces; it does not move any square.
The negative canonical sector is handled by `C849851.Complete`.
-/
namespace N12Compact.C849851
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem seed_inside (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (mask : Nat) (hm : mask ∈ family b)
    (P : ℚ × ℚ) (hp : P ∈ seedPoints (maskSupport mask)) :
    (p.square (ownerIndex p mask)).Inside P.1 P.2 := by
  have code := ownerIndex_spec p mask (by rw [hf]; exact hm)
  exact seed_points_sound _
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    _ (by simpa only [code] using coded_exact p (ownerIndex p mask)) P hp

theorem owner_apart_mask (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 10) (mask : Nat)
    (hm : mask ∈ family b) (hne : masks b i ≠ mask) :
    ∀ x y, ¬ ((owner b p i).Inside x y ∧
      (p.square (ownerIndex p mask)).Inside x y) := by
  apply p.disjoint
  intro equal
  have code := ownerIndex_spec p mask (by rw [hf]; exact hm)
  exact hne ((owner_code b p hf i).symm.trans
    ((congrArg (markerCode p) equal).trans code))

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

/-- The actual right wall misses its lower auxiliary point. This is the
appropriate wall barrier for a merged lower-right corner: no singleton
corner seed is attributed to that merged square. -/
theorem a_high (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) : (owner b p 7).Inside 2 (5/2) := by
  have side (i : Fin 10) : (owner b p i).side = p.commonSide := p.congruent _
  have input (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ b : Bool, P ∈ queryInsidePoints (masks b i) 2 (owned i)) :
      (owner b p i).Inside P.1 P.2 := inside b p hf i P (check b)
  have missing (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ b : Bool, P ∈ queryOutsidePoints (masks b i) 2 (owned i)) :
      ¬ (owner b p i).Inside P.1 P.2 := outside b p hf i P (check b)
  have aP : ClosedInside (owner b p 7) 2 (113/50) :=
    close (by simpa using input 7 (2,113/50) (by decide +kernel))
  have aQ : ClosedInside (owner b p 7) (113/50) 2 :=
    close (by simpa using input 7 (113/50,2) (by decide +kernel))
  have aT : ClosedInside (owner b p 7) (47/20) (47/20) :=
    close (by simpa using input 7 (47/20,47/20) (by decide +kernel))
  have rHigh := FourSquareLowerBarrier.right_point (owner b p 8) (owner b p 7)
    (by rw [side]; exact p.side_gt_one) (p.contained _)
    (close (by simpa using input 8 (1543/500,2) (by decide +kernel)))
    (close (by simpa using input 8 (3,12/5) (by decide +kernel)))
    (by simpa using missing 8 (3,87/50) (by decide +kernel)) aQ
    (fun x y h => apart b p hf 7 8 (by decide) x y ⟨h.2,h.1⟩)
  obtain ⟨A,ac,aNonneg,shape,insideA,closedA⟩ := ClosedFrames.positive_frame (owner b p 7)
  apply (insideA _ _).mp
  apply FourSquareANarrow.point_of_higher_R A
    (by rw [shape,side]; exact p.side_gt_one) ac aNonneg
    ((closedA _ _).mpr aP) ((closedA _ _).mpr aQ) ((closedA _ _).mpr aT)
  · exact fun h => (by simpa using missing 7 (33/20,33/20) (by decide +kernel))
      ((insideA _ _).mp h)
  · exact fun h => (by simpa using missing 7 (47/20,33/20) (by decide +kernel))
      ((insideA _ _).mp h)
  · exact fun h => (by simpa using missing 7 (33/20,47/20) (by decide +kernel))
      ((insideA _ _).mp h)
  · exact fun h => (by simpa using missing 7 (3,12/5) (by decide +kernel))
      ((insideA _ _).mp h)
  · exact fun h => apart b p hf 7 8 (by decide) _ _
      ⟨(insideA _ _).mp h,rHigh⟩

/-- B is a face reindexing of the actual merged top owner. Every other
premise of the positive-sector theorem comes from the original packing. -/
theorem positive_impossible (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (B : OpenSquare)
    (sideB : B.side = (owner b p 9).side)
    (insideB : ∀ x y, B.Inside x y ↔ (owner b p 9).Inside x y)
    (closedB : ∀ x y, ClosedInside B x y ↔ ClosedInside (owner b p 9) x y)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c) : False := by
  have side (i : Fin 10) : (owner b p i).side = p.commonSide := p.congruent _
  have input (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ b : Bool, P ∈ queryInsidePoints (masks b i) 2 (owned i)) :
      (owner b p i).Inside P.1 P.2 := inside b p hf i P (check b)
  have missing (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ b : Bool, P ∈ queryOutsidePoints (masks b i) 2 (owned i)) :
      ¬ (owner b p i).Inside P.1 P.2 := outside b p hf i P (check b)
  have ePoint : (p.square (ownerIndex p 192)).Inside 1 3 := by
    simpa using seed_inside b p hf 192 (by cases b <;> decide +kernel)
      (1,3) (by decide +kernel)
  apply MergedTopFurther.Geometry.positive_impossible (owner b p 7) B (owner b p 2)
    (p.square (ownerIndex p 192)) bc bs bsc
  · exact (side 7).trans ((sideB.trans (side 9)).symm)
  · rw [sideB,side]; exact p.side_gt_one
  · simpa using close (input 7 (2,113/50) (by decide +kernel))
  · simpa using close (input 7 (113/50,2) (by decide +kernel))
  · simpa using input 7 (47/20,47/20) (by decide +kernel)
  · exact a_high b p hf
  · simpa using missing 7 (47/20,33/20) (by decide +kernel)
  · simpa using missing 7 (3,12/5) (by decide +kernel)
  · apply (closedB _ _).mpr
    simpa using close (input 9 (33/20,47/20) (by decide +kernel))
  · apply (closedB _ _).mpr
    simpa using close (input 9 (8/5,3) (by decide +kernel))
  · apply (insideB _ _).mpr
    simpa using input 9 (2,1543/500) (by decide +kernel)
  · simpa using input 2 (113/50,3) (by decide +kernel)
  · exact ePoint
  · intro x y h
    exact apart b p hf 7 9 (by decide) x y ⟨h.1,(insideB _ _).mp h.2⟩
  · intro x y h
    exact apart b p hf 9 2 (by decide) x y ⟨(insideB _ _).mp h.1,h.2⟩
  · intro x y h
    exact owner_apart_mask b p hf 9 192 (by cases b <;> decide +kernel)
      (by cases b <;> decide +kernel) x y ⟨(insideB _ _).mp h.1,h.2⟩

/-- The entire positive half of the canonical orientation cover is gone.
The original packing remains available for the unresolved negative sector. -/
theorem negative_frame (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) :
    ∃ B : OpenSquare, 0 < B.c ∧ |B.s| ≤ B.c ∧ B.s < 0 ∧
      B.side = (owner b p 9).side ∧
      (∀ x y, B.Inside x y ↔ (owner b p 9).Inside x y) ∧
      (∀ x y, ClosedInside B x y ↔ ClosedInside (owner b p 9) x y) := by
  obtain ⟨B,bc,canonical,side,hi,hcl⟩ := ClosedFrames.canonical_frame (owner b p 9)
  have negative : B.s < 0 := by
    apply lt_of_not_ge
    intro positive
    exact positive_impossible b p hf B side hi hcl bc positive
      (by simpa only [abs_of_nonneg positive] using canonical)
  exact ⟨B,bc,canonical,negative,side,hi,hcl⟩

#print axioms negative_frame
end N12Compact.C849851
