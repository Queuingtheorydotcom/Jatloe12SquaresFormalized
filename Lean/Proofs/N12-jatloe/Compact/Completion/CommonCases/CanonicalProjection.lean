import Compact.Completion.CommonCases.CanonicalScalars
import Mathlib.Tactic.Ring

/-! Projection monotonicity on the unit circle from two orthogonal dot
products. The endpoints can be exact rational unit vectors; no trigonometry,
differentiation, angle sampling, or half-angle substitution is needed. -/
namespace N12Compact.CommonCases.CanonicalProjection
set_option Elab.async false

private theorem dot_bound (c s c0 s0 : ℝ) (unit : c^2+s^2=1)
    (unit0 : c0^2+s0^2=1) : c0*c+s0*s ≤ 1 := by
  have normal : (c0*c+s0*s)^2+(c0*s-s0*c)^2=1 := by
    calc
      _ = (c0^2+s0^2)*(c^2+s^2) := by ring
      _ = 1 := by rw [unit0,unit]; norm_num
  nlinarith only [normal,sq_nonneg (c0*s-s0*c),sq_nonneg (c0*c+s0*s-1)]

theorem before (c s c0 s0 a b : ℝ) (unit : c^2+s^2=1)
    (unit0 : c0^2+s0^2=1) (cross : c0*s ≤ s0*c)
    (derivative : a*s0 ≤ b*c0) (value : 0 ≤ a*c0+b*s0) :
    a*c+b*s ≤ a*c0+b*s0 := by
  have bound := dot_bound c s c0 s0 unit unit0
  have tangent := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ b*c0-a*s0 by linarith only [derivative])
    (show c0*s-s0*c ≤ 0 by linarith only [cross])
  have radial := mul_le_mul_of_nonneg_left bound value
  have identity : a*c+b*s =
      (a*c0+b*s0)*(c0*c+s0*s)+(b*c0-a*s0)*(c0*s-s0*c) := by
    linear_combination -(a*c+b*s)*unit0
  nlinarith only [identity,tangent,radial]

theorem after (c s c0 s0 a b : ℝ) (unit : c^2+s^2=1)
    (unit0 : c0^2+s0^2=1) (cross : s0*c ≤ c0*s)
    (derivative : b*c0 ≤ a*s0) (value : 0 ≤ a*c0+b*s0) :
    a*c+b*s ≤ a*c0+b*s0 := by
  have bound := dot_bound c s c0 s0 unit unit0
  have tangent := mul_nonpos_of_nonpos_of_nonneg
    (show b*c0-a*s0 ≤ 0 by linarith only [derivative])
    (show 0 ≤ c0*s-s0*c by linarith only [cross])
  have radial := mul_le_mul_of_nonneg_left bound value
  have identity : a*c+b*s =
      (a*c0+b*s0)*(c0*c+s0*s)+(b*c0-a*s0)*(c0*s-s0*c) := by
    linear_combination -(a*c+b*s)*unit0
  nlinarith only [identity,tangent,radial]

end N12Compact.CommonCases.CanonicalProjection
