import Compact.Core.IntegerSupport
import Mathlib.Tactic.FieldSimp

namespace N12Compact.CoordinateBound
open IntegerSupport

def lower (b : ℚ) (strict : Bool) : Row := ⟨b.den, 0, -b.num, strict⟩
def upper (b : ℚ) (strict : Bool) : Row := ⟨-(b.den : Int), 0, b.num, strict⟩

theorem lower_eval (b : ℚ) (strict : Bool) (p : Fin 2 → ℝ) :
    (lower b strict).eval p = (b.den : ℝ) * (p 0 - (b : ℝ)) := by
  have hd : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  simp only [lower, Row.eval, Int.cast_natCast, Int.cast_zero, Int.cast_neg,
    zero_mul, add_zero, Rat.cast_def]
  field_simp [hd] <;> ring

theorem upper_eval (b : ℚ) (strict : Bool) (p : Fin 2 → ℝ) :
    (upper b strict).eval p = (b.den : ℝ) * ((b : ℝ) - p 0) := by
  have hd : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  simp only [upper, Row.eval, Int.cast_natCast, Int.cast_zero, Int.cast_neg,
    zero_mul, add_zero, Rat.cast_def]
  field_simp [hd] <;> ring

theorem holds_lower (b : ℚ) (strict : Bool) (p : Fin 2 → ℝ) :
    (lower b strict).Holds p ↔
      if strict then (b : ℝ) < p 0 else (b : ℝ) ≤ p 0 := by
  have hd : (0 : ℝ) < b.den := by exact_mod_cast b.den_pos
  change (if strict then 0 < (lower b strict).eval p else 0 ≤ (lower b strict).eval p) ↔ _
  rw [lower_eval]
  cases strict <;> simp [mul_pos_iff_of_pos_left hd, mul_nonneg_iff_of_pos_left hd,
    sub_nonneg, sub_pos]

theorem holds_upper (b : ℚ) (strict : Bool) (p : Fin 2 → ℝ) :
    (upper b strict).Holds p ↔
      if strict then p 0 < (b : ℝ) else p 0 ≤ (b : ℝ) := by
  have hd : (0 : ℝ) < b.den := by exact_mod_cast b.den_pos
  change (if strict then 0 < (upper b strict).eval p else 0 ≤ (upper b strict).eval p) ↔ _
  rw [upper_eval]
  cases strict <;> simp [mul_pos_iff_of_pos_left hd, mul_nonneg_iff_of_pos_left hd,
    sub_nonneg, sub_pos]

#print axioms holds_lower
end N12Compact.CoordinateBound
