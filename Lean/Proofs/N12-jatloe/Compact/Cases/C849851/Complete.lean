import Compact.Cases.C849851.Positive
import Compact.Geometry.C849Negative

/-! Both canonical orientation sectors, bound to the unchanged original
849 and 851 families. The left and corner neighbours are complete physical
squares from the same packing. The source has not yet been compiled. -/
namespace N12Compact.C849851
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem closed_of_inside {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

/-- Whole original-family contradiction. Frame changes reindex faces only. -/
theorem impossible (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) : False := by
  obtain ⟨B,bc,bsc,bs,sideB,insideB,closedB⟩ := negative_frame b p hf
  obtain ⟨L,lc,lsc,sideL,insideL,closedL⟩ := ClosedFrames.canonical_frame (owner b p 3)
  have side (i : Fin 10) : (owner b p i).side = p.commonSide := p.congruent _
  have input (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ b : Bool, P ∈ queryInsidePoints (masks b i) 2 (owned i)) :
      (owner b p i).Inside P.1 P.2 := inside b p hf i P (check b)
  have missing (i : Fin 10) (P : ℚ × ℚ)
      (check : ∀ b : Bool, P ∈ queryOutsidePoints (masks b i) 2 (owned i)) :
      ¬ (owner b p i).Inside P.1 P.2 := outside b p hf i P (check b)
  have lowBarrier : (p.square (ownerIndex p 2)).Inside (19/25) (187/100) := by
    simpa using seed_inside b p hf 2 (by cases b <;> decide +kernel)
      (19/25,187/100) (by decide +kernel)
  apply C849Negative.impossible B L (p.square (ownerIndex p 192)) bc bs.le
    (by simpa only [abs_of_neg bs] using bsc) lc lsc
  · rw [sideB,side]; exact p.side_gt_one
  · rw [sideB,side]; exact p.side_le
  · exact (sideB.trans (side 9)).trans ((sideL.trans (side 3)).symm)
  · exact (p.congruent _).trans ((sideB.trans (side 9)).symm)
  · intro x y h
    exact p.contained _ x y ((insideL x y).mp h)
  · exact p.contained _
  · apply (insideB _ _).mpr
    simpa using input 9 (33/20,47/20) (by decide +kernel)
  · apply (closedB _ _).mpr
    simpa using closed_of_inside (input 9 (8/5,3) (by decide +kernel))
  · apply (insideB _ _).mpr
    simpa using input 9 (2,1543/500) (by decide +kernel)
  · intro h
    exact apart b p hf 7 9 (by decide) _ _ ⟨a_high b p hf,(insideB _ _).mp h⟩
  · intro h
    exact apart b p hf 9 2 (by decide) _ _
      ⟨(insideB _ _).mp h,by simpa using input 2 (113/50,3) (by decide +kernel)⟩
  · apply (closedL _ _).mpr
    simpa using closed_of_inside (input 3 (457/500,2) (by decide +kernel))
  · apply (closedL _ _).mpr
    simpa using closed_of_inside (input 3 (1,12/5) (by decide +kernel))
  · intro h
    exact owner_apart_mask b p hf 3 2 (by cases b <;> decide +kernel)
      (by cases b <;> decide +kernel) _ _ ⟨(insideL _ _).mp h,lowBarrier⟩
  · intro h
    apply missing 3 (33/20,33/20) (by decide +kernel)
    simpa using (insideL _ _).mp h
  · simpa using seed_inside b p hf 192 (by cases b <;> decide +kernel)
      (1,1543/500) (by decide +kernel)
  · simpa using seed_inside b p hf 192 (by cases b <;> decide +kernel)
      (457/500,3) (by decide +kernel)
  · intro x y h
    exact apart b p hf 9 3 (by decide) x y
      ⟨(insideB x y).mp h.1,(insideL x y).mp h.2⟩
  · intro x y h
    exact owner_apart_mask b p hf 9 192 (by cases b <;> decide +kernel)
      (by cases b <;> decide +kernel) x y ⟨(insideB x y).mp h.1,h.2⟩

#print axioms impossible
end N12Compact.C849851
