import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The degree-four Bernstein identity used by the completed continuous
support-point arguments. Strict positive coefficients prove positivity on
the entire closed unit interval, including both endpoints. -/
namespace N12Compact.CommonCases.BernsteinQuartic
set_option Elab.async false

def value (z b0 b1 b2 b3 b4 : ℝ) : ℝ :=
  b0*(1-z)^4+4*b1*z*(1-z)^3+6*b2*z^2*(1-z)^2+
    4*b3*z^3*(1-z)+b4*z^4

theorem positive (z b0 b1 b2 b3 b4 : ℝ) (zn : 0 ≤ z) (zu : z ≤ 1)
    (first : 0 < b0) (second : 0 < b1) (third : 0 < b2)
    (fourth : 0 < b3) (last : 0 < b4) : 0 < value z b0 b1 b2 b3 b4 := by
  by_cases endpoint : z=1
  · simpa [value,endpoint] using last
  · have rest : 0 < 1-z := by
      have strict : z < 1 := lt_of_le_of_ne zu endpoint
      linarith only [strict]
    dsimp only [value]
    positivity

end N12Compact.CommonCases.BernsteinQuartic
