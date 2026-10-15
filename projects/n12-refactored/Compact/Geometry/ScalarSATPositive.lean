import Compact.Geometry.ScalarSATIntervals
/-! Scalar SAT proof reused from EvolvingPrograms/SquaresLean, commit
c5c6144349a141e56ac43c81ed732f731c591eac, Lean/Squares/Separation/Positive.lean.
Only the import and namespace are adapted; the mathematical proof is unchanged.
This source must be replayed with this project's pinned Lean/Mathlib. -/

namespace N12Compact.SATPositive
noncomputable section
open SATIntervals

/-- If all four projections overlap strictly, two open squares in a positive
relative orientation have a common point. Coordinates here use half-side 1. -/
theorem positive_overlap (c s X Y U V : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hunit : c^2+s^2=1)
    (hU : U = c*X+s*Y) (hV : V = -s*X+c*Y)
    (hX : |X| < 1+c+s) (hY : |Y| < 1+c+s)
    (hUB : |U| < 1+c+s) (hVB : |V| < 1+c+s) :
    ∃ x y : ℝ, |x| < 1 ∧ |y| < 1 ∧
      |c*x+s*y-U| < 1 ∧ |-s*x+c*y-V| < 1 := by
  obtain ⟨y, hl, hu⟩ := positive_y_intervals c s X Y U V hc hs hunit hU hV hX hY hUB hVB
  have hYi : s*U+c*V=Y := by
    calc
      _ = Y*(c^2+s^2) := by rw [hU, hV]; ring
      _ = Y := by rw [hunit, mul_one]
  have hyunit : y*(c^2+s^2)=y := by rw [hunit, mul_one]
  have hylU := (div_lt_iff₀ hs).1 hl.2.1
  have hyuU := (lt_div_iff₀ hs).1 hu.2.1
  have hylV := (div_lt_iff₀ hc).1 hl.2.2.1
  have hyuV := (lt_div_iff₀ hc).1 hu.2.2.1
  have h₀ : (-1:ℝ) < 1 ∧ -1 < (U+1-s*y)/c ∧ -1 < (c*y-V+1)/s := by
    refine ⟨by norm_num, ?_, ?_⟩
    · apply (lt_div_iff₀ hc).2; linarith only [hyuU]
    · apply (lt_div_iff₀ hs).2; linarith only [hylV]
  have h₁ : (U-1-s*y)/c < 1 ∧ (U-1-s*y)/c < (U+1-s*y)/c ∧
      (U-1-s*y)/c < (c*y-V+1)/s := by
    refine ⟨?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hc).2; linarith only [hylU]
    · apply (div_lt_div_iff_of_pos_right hc).2; linarith
    · apply (div_lt_div_iff₀ hc hs).2; nlinarith only [hYi, hyunit, hl.2.2.2]
  have h₂ : (c*y-V-1)/s < 1 ∧ (c*y-V-1)/s < (U+1-s*y)/c ∧
      (c*y-V-1)/s < (c*y-V+1)/s := by
    refine ⟨?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hs).2; linarith only [hyuV]
    · apply (div_lt_div_iff₀ hs hc).2; nlinarith only [hYi, hyunit, hu.2.2.2]
    · apply (div_lt_div_iff_of_pos_right hs).2; linarith
  obtain ⟨x, hxl, hxu⟩ := between_three _ _ _ _ _ _ h₀ h₁ h₂
  refine ⟨x, y, abs_lt.mpr ⟨hxl.1, hxu.1⟩, abs_lt.mpr ⟨hl.1, hu.1⟩, ?_, ?_⟩
  · have hlo := (div_lt_iff₀ hc).1 hxl.2.1
    have hhi := (lt_div_iff₀ hc).1 hxu.2.1
    apply abs_lt.mpr; constructor <;> linarith only [hlo, hhi]
  · have hlo := (div_lt_iff₀ hs).1 hxl.2.2
    have hhi := (lt_div_iff₀ hs).1 hxu.2.2
    apply abs_lt.mpr; constructor <;> linarith only [hlo, hhi]

theorem nonnegative_overlap (c s X Y U V : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hunit : c^2+s^2=1)
    (hU : U = c*X+s*Y) (hV : V = -s*X+c*Y)
    (hX : |X| < 1+c+s) (hY : |Y| < 1+c+s)
    (hUB : |U| < 1+c+s) (hVB : |V| < 1+c+s) :
    ∃ x y : ℝ, |x| < 1 ∧ |y| < 1 ∧
      |c*x+s*y-U| < 1 ∧ |-s*x+c*y-V| < 1 := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · have hc' : c=0 := hc0.symm
    have hs' : s=1 := by nlinarith [hunit]
    subst c; subst s
    rcases abs_lt.mp hX with ⟨hXl, hXu⟩
    rcases abs_lt.mp hY with ⟨hYl, hYu⟩
    refine ⟨X/2, Y/2, ?_, ?_, ?_, ?_⟩ <;>
      apply abs_lt.mpr <;> constructor <;> nlinarith only [hXl, hXu, hYl, hYu, hU, hV]
  · rcases eq_or_lt_of_le hs with hs0 | hspos
    · have hs' : s=0 := hs0.symm
      have hc' : c=1 := by nlinarith [hunit]
      subst s; subst c
      rcases abs_lt.mp hX with ⟨hXl, hXu⟩
      rcases abs_lt.mp hY with ⟨hYl, hYu⟩
      refine ⟨X/2, Y/2, ?_, ?_, ?_, ?_⟩ <;>
        apply abs_lt.mpr <;> constructor <;> nlinarith only [hXl, hXu, hYl, hYu, hU, hV]
    · exact positive_overlap c s X Y U V hcpos hspos hunit hU hV hX hY hUB hVB

#print axioms positive_overlap
#print axioms nonnegative_overlap
end
end N12Compact.SATPositive

