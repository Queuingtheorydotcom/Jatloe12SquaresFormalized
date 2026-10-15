import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace N12Compact.CommonCases.CanonicalScalars
set_option Elab.async false

theorem bounds (c t : ℝ) (cp : 0 < c) (tn : 0 ≤ t)
    (order : t ≤ c) (unit : c^2+t^2=1) :
    7/10 < c ∧ c ≤ 1 ∧ 1 ≤ c+t ∧ c+t ≤ 10/7 ∧
      1+(4/5)*c*t ≤ c+t := by
  have ct := mul_nonneg cp.le tn
  have difference := mul_nonneg (sub_nonneg.mpr order)
    (show 0 ≤ c+t by linarith only [cp,tn])
  have lower : 7/10 < c := by nlinarith only [unit,difference,cp]
  have upper : c ≤ 1 := by nlinarith only [unit,sq_nonneg t,cp]
  have sumlow : 1 ≤ c+t := by nlinarith only [unit,ct,cp,tn]
  have sumhigh : c+t ≤ 10/7 := by
    nlinarith only [unit,sq_nonneg (c-t),cp,tn]
  have product := mul_nonneg
    (show 0 ≤ 3/2-(c+t) by linarith only [sumhigh])
    (sub_nonneg.mpr sumlow)
  exact ⟨lower,upper,sumlow,sumhigh,by nlinarith only [unit,product]⟩

theorem c_small_sine (c t : ℝ) (cp : 0 < c) (tn : 0 ≤ t)
    (unit : c^2+t^2=1) (slope : c ≤ 5*t) :
    c+(43/500)*t < 1 := by
  have tp : 0 < t := by linarith only [cp,slope]
  have coefficient : 0 < (248151/250000)*t-(43/250)*c := by
    linarith only [slope,cp]
  have product := mul_pos tp coefficient
  nlinarith only [unit,product,cp,tn]

/-- The nonnegative-angle segment-normal comparison for C982.
The elementary K,D factorization replaces differentiation. -/
theorem positive_margin (c t : ℝ) (cp : 0 < c) (tn : 0 ≤ t)
    (order : t ≤ c) (unit : c^2+t^2=1) :
    244959/250000-(3/10)*t^2+(463/500)*c*t <
      (613/500)*c+(313/500)*t := by
  obtain ⟨_,_,sumlow,sumhigh,_⟩ := bounds c t cp tn order unit
  have term := mul_nonneg (sub_nonneg.mpr order)
    (show 0 ≤ 2-(c+t) by linarith only [sumhigh])
  have square := mul_nonneg
    (show 0 ≤ 3/7-((c+t)-1) by linarith only [sumhigh])
    (show 0 ≤ 3/7+((c+t)-1) by linarith only [sumlow])
  have identity :
      (613/500)*c+(313/500)*t-(244959/250000)+
        (3/10)*t^2-(463/500)*c*t =
      24041/250000-(463/1000)*((c+t)-1)^2+
        (3/20)*(c-t)*(2-(c+t)) := by
    linear_combination (613/1000)*unit
  nlinarith only [identity,term,square]

/-- The negative-angle segment-normal comparison for C982. -/
theorem negative_margin (c t : ℝ) (cp : 0 < c) (tn : 0 ≤ t)
    (order : t ≤ c) (unit : c^2+t^2=1) :
    3001/5000+(94909/250000)*t^2+(4501/5000)*c*t <
      (313/500)*c+(613/500)*t := by
  obtain ⟨_,_,_,sumhigh,strong⟩ := bounds c t cp tn order unit
  have coefficient : 0 ≤ 3/5-(1997/5000)*c-(94909/250000)*t := by
    linarith only [sumhigh,cp,tn]
  have product := mul_nonneg tn coefficient
  nlinarith only [strong,product]

end N12Compact.CommonCases.CanonicalScalars
