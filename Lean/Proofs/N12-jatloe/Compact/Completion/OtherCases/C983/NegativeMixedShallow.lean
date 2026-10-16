import Compact.Completion.OtherCases.C983.NegativeRightOwned

/-! The shallow right-angle interval in the remaining mixed separator
branch. A single square identity replaces an interval certificate. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeMixedShallow
set_option Elab.async false

theorem scalar (c t a b H : ℝ) (cp : 0<c) (tp : 0<t) (order : t≤c)
    (ap : 0<a) (bn : 0≤b) (eu : c^2+t^2=1) (ru : a^2+b^2=1)
    (shallow : b≤9/41) (height : (4/5)*t≤H) :
    0≤c*((26/25)*a-b)+b*H-(a*c+b*t)*(2-a-b) := by
  let v := b/(1+a)
  have denominator : 0<1+a := by linarith only [ap]
  have vn : 0≤v := by dsimp only [v]; exact div_nonneg bn denominator.le
  have vDen : (1+a)*v=b := by
    dsimp only [v]
    field_simp [ne_of_gt denominator]
  have relation : b*v=1-a := by
    have scaled : (1+a)*(b*v-(1-a))=0 := by
      linear_combination b*vDen+ru
    have zero := (mul_eq_zero.mp scaled).resolve_left (ne_of_gt denominator)
    linarith only [zero]
  have au : a≤1 := by nlinarith only [ru,sq_nonneg b,ap]
  have product := mul_nonneg bn (sub_nonneg.mpr au)
  have sum : a+b<6/5 := by
    apply lt_of_not_ge
    intro large
    have square := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤a+b+6/5 by linarith only [ap,bn])
    nlinarith only [ru,product,shallow,square]
  have vProduct := mul_nonneg vn (sub_nonneg.mpr au)
  have vLower : b/2≤v := by nlinarith only [vDen,vProduct]
  have coefficient : 1/2≤24/25-2*b := by linarith only [shallow]
  have first := mul_nonneg (mul_nonneg bn vn) (sub_nonneg.mpr coefficient)
  have last := mul_nonneg bn (sub_nonneg.mpr vLower)
  have bracket : 0≤1/25-b/5+b*v*(24/25-2*b) := by
    nlinarith only [first,last,sq_nonneg (b/2-1/5)]
  have bracketWeight := mul_nonneg cp.le bracket
  have angleWeight := mul_nonneg bn
    (mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr sum.le))
  have heightWeight := mul_nonneg bn (sub_nonneg.mpr height)
  have identity : c*((26/25)*a-b)+b*((4/5)*t)-(a*c+b*t)*(2-a-b)=
      c*(1/25-b/5+b*v*(24/25-2*b))+b*(c-t)*(6/5-a-b) := by
    linear_combination c*ru-c*(24/25-2*b)*relation
  nlinarith only [identity,bracketWeight,angleWeight,heightWeight]

#print axioms scalar
end N12Compact.Completion.OtherCases.C983.NegativeMixedShallow
