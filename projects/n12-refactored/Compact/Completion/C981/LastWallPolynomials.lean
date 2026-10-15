import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Three rational polynomial margins in the final right-wall argument.
Explicit chord and square identities replace all derivative comparisons. -/
namespace N12Compact.C981CompletionLastWallPolynomials
set_option Elab.async false

theorem first (z : ℝ) (lo : 0 ≤ z) (hi : z ≤ 27/100) :
    -(367/2500)-(117/1000)*z+(1637/625)*z^2-(883/1000)*z^3 < 0 := by
  let N := fun x : ℝ => -(367/2500)-(117/1000)*x+(1637/625)*x^2-(883/1000)*x^3
  have factor : 0 ≤ 1637/625-(883/1000)*(z+27/100) := by linarith only [lo,hi]
  have span := mul_nonneg lo (sub_nonneg.mpr hi)
  have correction := mul_nonneg span factor
  have identity : (27/100)*N z = (27/100-z)*N 0+z*N (27/100)-
      (27/100)*z*(27/100-z)*(1637/625-(883/1000)*(z+27/100)) := by
    dsimp [N]; ring
  have a := mul_nonneg (sub_nonneg.mpr hi) (by norm_num : (0:ℝ) ≤ 367/2500)
  have b := mul_nonneg lo (by norm_num : (0:ℝ) ≤ 4830409/1000000000)
  have negative : N z < 0 := by
    dsimp [N] at identity ⊢
    nlinarith only [identity,correction,a,b,lo,hi]
  exact negative

theorem second (z : ℝ) (lo : 1/4 ≤ z) :
    87/250-(187/100)*z+(261/125)*z^2-(87/100)*z^3 < 0 := by
  have identity : 87/250-(187/100)*z+(261/125)*z^2-(87/100)*z^3 =
      -(83/32000)-(z-1/4)*((87/100)*(z-43/40)^2+63517/160000) := by ring
  have factor : 0 ≤ (87/100)*(z-43/40)^2+63517/160000 := by
    nlinarith only [sq_nonneg (z-43/40)]
  have product := mul_nonneg (sub_nonneg.mpr lo) factor
  nlinarith only [identity,product]

theorem third (z : ℝ) (lo : 0 ≤ z) (hi : z ≤ 1) :
    29/250-(4/5)*z+(471/250)*z^2-z^3 > 0 := by
  by_cases small : z ≤ 1/2
  · have product := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr small)
    have identity : 29/250-(4/5)*z+(471/250)*z^2-z^3 =
        (173/125)*(z-50/173)^2+17/43250+z^2*(1/2-z) := by ring
    nlinarith only [identity,product,sq_nonneg (z-50/173)]
  · let w := z-1/2
    have wn : 0 ≤ w := by dsimp [w]; linarith only [small]
    have wh : w ≤ 1/2 := by dsimp [w]; linarith only [hi]
    have span := mul_nonneg (sub_nonneg.mpr wh)
      (show 0 ≤ 1/2+w from add_nonneg (by norm_num) wn)
    have product := mul_nonneg wn span
    have identity : 29/250-(4/5)*z+(471/250)*z^2-z^3 =
        31/500+(167/500)*w+(48/125)*w^2-w^3 := by dsimp [w]; ring
    nlinarith only [identity,product,wn,sq_nonneg w]

#print axioms first
#print axioms second
#print axioms third
end N12Compact.C981CompletionLastWallPolynomials
