import Compact.Geometry.ScalarSATPositive
/-! Scalar SAT proof reused from EvolvingPrograms/SquaresLean, commit
c5c6144349a141e56ac43c81ed732f731c591eac, Lean/Squares/Separation/Signed.lean.
Only the import and namespace are adapted; the mathematical proof is unchanged.
This source must be replayed with this project's pinned Lean/Mathlib. -/

namespace N12Compact.SATSigned
noncomputable section

def Overlap (c s U V : ℝ) : Prop :=
  ∃ x y : ℝ, |x| < 1 ∧ |y| < 1 ∧ |c*x+s*y-U| < 1 ∧ |-s*x+c*y-V| < 1

theorem flip_s (c s U V : ℝ) (h : Overlap c (-s) U (-V)) : Overlap c s U V := by
  obtain ⟨x, y, hx, hy, hU, hV⟩ := h
  refine ⟨x, -y, hx, by simpa only [abs_neg] using hy, ?_, ?_⟩
  · simpa only [mul_neg, neg_mul] using hU
  · have he : -s*x+c*(-y)-V = -(-(-s)*x+c*y-(-V)) := by ring
    rw [he, abs_neg]
    exact hV

theorem flip_c (c s U V : ℝ) (h : Overlap (-c) s U (-V)) : Overlap c s U V := by
  obtain ⟨x, y, hx, hy, hU, hV⟩ := h
  refine ⟨-x, y, by simpa only [abs_neg] using hx, hy, ?_, ?_⟩
  · simpa only [mul_neg, neg_mul] using hU
  · have he : -s*(-x)+c*y-V = -(-s*x+(-c)*y-(-V)) := by ring
    rw [he, abs_neg]
    exact hV

theorem nonneg_c_overlap (c s X Y U V : ℝ)
    (hc : 0 ≤ c) (hunit : c^2+s^2=1)
    (hU : U = c*X+s*Y) (hV : V = -s*X+c*Y)
    (hX : |X| < 1+|c|+|s|) (hY : |Y| < 1+|c|+|s|)
    (hUB : |U| < 1+|c|+|s|) (hVB : |V| < 1+|c|+|s|) :
    Overlap c s U V := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hc, abs_of_nonneg hs] at hX hY hUB hVB
    exact SATPositive.nonnegative_overlap c s X Y U V hc hs hunit hU hV hX hY hUB hVB
  · have hsneg : s < 0 := lt_of_not_ge hs
    rw [abs_of_nonneg hc, abs_of_neg hsneg] at hX hY hUB hVB
    apply flip_s
    exact SATPositive.nonnegative_overlap c (-s) X (-Y) U (-V) hc (by linarith)
      (by simpa only [neg_sq] using hunit)
      (by nlinarith only [hU]) (by nlinarith only [hV])
      hX (by simpa only [abs_neg] using hY) hUB (by simpa only [abs_neg] using hVB)

/-- Absence of a separating edge direction gives an overlap witness for an
arbitrary independently rotated pair. This is purely real algebra. -/
theorem overlap (c s X Y U V : ℝ)
    (hunit : c^2+s^2=1)
    (hU : U = c*X+s*Y) (hV : V = -s*X+c*Y)
    (hX : |X| < 1+|c|+|s|) (hY : |Y| < 1+|c|+|s|)
    (hUB : |U| < 1+|c|+|s|) (hVB : |V| < 1+|c|+|s|) :
    Overlap c s U V := by
  by_cases hc : 0 ≤ c
  · exact nonneg_c_overlap c s X Y U V hc hunit hU hV hX hY hUB hVB
  · have hcneg : c < 0 := lt_of_not_ge hc
    apply flip_c
    exact nonneg_c_overlap (-c) s (-X) Y U (-V) (by linarith)
      (by simpa only [neg_sq] using hunit)
      (by nlinarith only [hU]) (by nlinarith only [hV])
      (by simpa only [abs_neg] using hX) (by simpa only [abs_neg] using hY)
      (by simpa only [abs_neg] using hUB) (by simpa only [abs_neg] using hVB)

#print axioms flip_s
#print axioms flip_c
#print axioms nonneg_c_overlap
#print axioms overlap
end
end N12Compact.SATSigned

