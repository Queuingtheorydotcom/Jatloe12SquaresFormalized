import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Small interval-intersection lemmas for the necessity direction of SAT.
No convex-separation, trigonometric, or calculus imports are required. -/
namespace N12Compact.SATIntervals
noncomputable section

theorem between_four (l₀ l₁ l₂ l₃ u₀ u₁ u₂ u₃ : ℝ)
    (h₀ : l₀ < u₀ ∧ l₀ < u₁ ∧ l₀ < u₂ ∧ l₀ < u₃)
    (h₁ : l₁ < u₀ ∧ l₁ < u₁ ∧ l₁ < u₂ ∧ l₁ < u₃)
    (h₂ : l₂ < u₀ ∧ l₂ < u₁ ∧ l₂ < u₂ ∧ l₂ < u₃)
    (h₃ : l₃ < u₀ ∧ l₃ < u₁ ∧ l₃ < u₂ ∧ l₃ < u₃) :
    ∃ y, (l₀ < y ∧ l₁ < y ∧ l₂ < y ∧ l₃ < y) ∧
      (y < u₀ ∧ y < u₁ ∧ y < u₂ ∧ y < u₃) := by
  have h : max l₀ (max l₁ (max l₂ l₃)) < min u₀ (min u₁ (min u₂ u₃)) := by
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨h₀.1, h₁.1, h₂.1, h₃.1⟩,
      ⟨h₀.2.1, h₁.2.1, h₂.2.1, h₃.2.1⟩,
      ⟨h₀.2.2.1, h₁.2.2.1, h₂.2.2.1, h₃.2.2.1⟩,
      ⟨h₀.2.2.2, h₁.2.2.2, h₂.2.2.2, h₃.2.2.2⟩⟩
  obtain ⟨y, hl, hu⟩ := exists_between h
  exact ⟨y, by simpa only [max_lt_iff] using hl, by simpa only [lt_min_iff] using hu⟩

theorem between_three (l₀ l₁ l₂ u₀ u₁ u₂ : ℝ)
    (h₀ : l₀ < u₀ ∧ l₀ < u₁ ∧ l₀ < u₂)
    (h₁ : l₁ < u₀ ∧ l₁ < u₁ ∧ l₁ < u₂)
    (h₂ : l₂ < u₀ ∧ l₂ < u₁ ∧ l₂ < u₂) :
    ∃ x, (l₀ < x ∧ l₁ < x ∧ l₂ < x) ∧ (x < u₀ ∧ x < u₁ ∧ x < u₂) := by
  obtain ⟨x, hl, hu⟩ := between_four l₀ l₁ l₂ l₂ u₀ u₁ u₂ u₂
    ⟨h₀.1, h₀.2.1, h₀.2.2, h₀.2.2⟩ ⟨h₁.1, h₁.2.1, h₁.2.2, h₁.2.2⟩
    ⟨h₂.1, h₂.2.1, h₂.2.2, h₂.2.2⟩ ⟨h₂.1, h₂.2.1, h₂.2.2, h₂.2.2⟩
  exact ⟨x, ⟨hl.1, hl.2.1, hl.2.2.1⟩, ⟨hu.1, hu.2.1, hu.2.2.1⟩⟩

/-- Fourier–Motzkin elimination of the x-coordinate: these four y-intervals
have a common point when all four pairs of projections overlap strictly. -/
theorem positive_y_intervals (c s X Y U V : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hunit : c^2+s^2=1)
    (hU : U = c*X+s*Y) (hV : V = -s*X+c*Y)
    (hX : |X| < 1+c+s) (hY : |Y| < 1+c+s)
    (hUB : |U| < 1+c+s) (hVB : |V| < 1+c+s) :
    ∃ y, (-1 < y ∧ (U-1-c)/s < y ∧ (V-1-s)/c < y ∧ Y-c-s < y) ∧
      (y < 1 ∧ y < (U+1+c)/s ∧ y < (V+1+s)/c ∧ y < Y+c+s) := by
  have hXi : c*U-s*V=X := by
    calc
      _ = X*(c^2+s^2) := by rw [hU, hV]; ring
      _ = X := by rw [hunit, mul_one]
  rcases abs_lt.mp hX with ⟨hXm, hXp⟩
  rcases abs_lt.mp hY with ⟨hYm, hYp⟩
  rcases abs_lt.mp hUB with ⟨hUm, hUp⟩
  rcases abs_lt.mp hVB with ⟨hVm, hVp⟩
  have hcXm := mul_lt_mul_of_pos_left hXm hc
  have hcXp := mul_lt_mul_of_pos_left hXp hc
  have hsXm := mul_lt_mul_of_pos_left hXm hs
  have hsXp := mul_lt_mul_of_pos_left hXp hs
  apply between_four
  · refine ⟨by norm_num, ?_, ?_, by linarith only [hYm]⟩
    · apply (lt_div_iff₀ hs).2; linarith only [hUm]
    · apply (lt_div_iff₀ hc).2; linarith only [hVm]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hs).2; linarith only [hUp]
    · apply (div_lt_div_iff_of_pos_right hs).2; linarith only [hc]
    · apply (div_lt_div_iff₀ hs hc).2; nlinarith only [hXi, hXp, hunit]
    · apply (div_lt_iff₀ hs).2; nlinarith only [hcXp, hU, hunit, sq_nonneg s]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hc).2; linarith only [hVp]
    · apply (div_lt_div_iff₀ hc hs).2; nlinarith only [hXi, hXm, hunit]
    · apply (div_lt_div_iff_of_pos_right hc).2; linarith only [hs]
    · apply (div_lt_iff₀ hc).2; nlinarith only [hsXm, hV, hunit, sq_nonneg c]
  · refine ⟨by linarith only [hYp], ?_, ?_, by linarith only [hc, hs]⟩
    · apply (lt_div_iff₀ hs).2; nlinarith only [hcXm, hU, hunit, sq_nonneg s]
    · apply (lt_div_iff₀ hc).2; nlinarith only [hsXp, hV, hunit, sq_nonneg c]

#print axioms between_four
#print axioms between_three
#print axioms positive_y_intervals

end
end N12Compact.SATIntervals

