import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Small analytic bounds that remove angle-bin certificates for a follower
whose center is already sufficiently close to the chosen cross-section. -/
namespace N12Compact.ChordRadius

noncomputable def radius (c s : ℝ) : ℝ := (c + s - 2 * c * s) / 2

/-- Uniform over the whole first-quadrant unit arc; no angle mesh occurs. -/
theorem one_fifth_le (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (unit : c ^ 2 + s ^ 2 = 1) : 1 / 5 ≤ radius c s := by
  have sum_nonneg : 0 ≤ c + s := add_nonneg hc hs
  have sum_lower : 1 ≤ c + s := by
    nlinarith [mul_nonneg hc hs]
  have sum_square : (c + s) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (c - s)]
  unfold radius
  by_cases high : 7 / 5 ≤ c + s
  · nlinarith
  · have prod := mul_nonneg
      (show 0 ≤ 7 / 5 - (c + s) by linarith) sum_nonneg
    nlinarith

/-- This entirely removes the angle-specific chord-radius table for the
last C696 root-one follower once its coarse center-height bound is known. -/
theorem last_follower_height (c s Y : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (unit : c ^ 2 + s ^ 2 = 1)
    (lower : 1 / 2 ≤ Y) (upper : Y ≤ 3 / 5) :
    Y - 45 / 98 ≤ radius c s := by
  have r := one_fifth_le c s hc hs unit
  linarith

/-- Exact polynomial form of the remaining next-follower requirement.
Here X is the original physical center coordinate, before the reflected
transpose used by the border transfer. -/
theorem next_follower_iff (c s X : ℝ) :
    4 - X - radius c s ≤ 45 / 98 ↔
      0 ≤ 98 * X + 49 * (c + s - 2 * c * s) - 347 := by
  unfold radius
  constructor <;> intro h <;> linarith

#print axioms one_fifth_le
#print axioms next_follower_iff

end N12Compact.ChordRadius
