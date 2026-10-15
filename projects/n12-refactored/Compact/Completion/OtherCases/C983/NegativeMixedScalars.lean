import Compact.Completion.OtherCases.C983.NegativeMixedShallow
import Compact.Completion.OtherCases.C983.NegativeMixedCubic

/-! The remaining mixed separator uses the cubic monotonicity and four-term
Bernstein proof from C581 §7. The public scalar contract and its exact
half-angle denominator identity are unchanged. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeMixedScalars
open C1092WallProfileScalars
set_option Elab.async false

private def numerator (z w : ℝ) : ℝ :=
  4*w*z*(1+w^2)*(1+z^2) -
  ((1-w^2)*(1-z^2)+4*w*z)*(1-2*w+3*w^2)*(1+z) +
  (1-z^2)*(1-w)^2*(1+w^2)*(1+z)

private theorem triangle (z w : ℝ) (lo : 1/9≤w) (order : w≤z)
    (hi : z≤2/7) : 0≤numerator z w := by
  simpa only [numerator,NegativeMixedCubic.numerator] using
    NegativeMixedCubic.triangle z w lo order hi

/-- The stronger rational margin (45) from the cubic replacement. -/
theorem large_margin (c t a b : ℝ) (cp : 0<c) (tp : 0<t)
    (ap : 0<a) (bn : 0≤b) (eu : c^2+t^2=1) (ru : a^2+b^2=1)
    (cLarge : 6/7<c) (threshold : 9/41≤b) (order : b*c≤a*t) :
    153664/976781997≤c*(1-b)+b*(1-(1-t)/c)-(a*c+b*t)*(2-a-b) := by
  let z := half c t
  let w := half a b
  have ed := quarter_data c t cp.le tp.le eu
  have rd := quarter_data a b ap.le bn ru
  have zn : 0≤z := ed.1
  have wn : 0≤w := rd.1
  have ez : 0<1+z^2 := by positivity
  have rwpos : 0<1+w^2 := by positivity
  have ec : (1+z^2)*c=1-z^2 := ed.2.2.2.1
  have et : (1+z^2)*t=2*z := ed.2.2.2.2
  have ra : (1+w^2)*a=1-w^2 := rd.2.2.2.1
  have rb : (1+w^2)*b=2*w := rd.2.2.2.2
  have zSmall : z≤2/7 := by
    have weight := mul_pos ez (sub_pos.mpr cLarge)
    apply le_of_not_gt
    intro bad
    have square := mul_pos (sub_pos.mpr bad)
      (show 0<z+2/7 by linarith only [zn])
    nlinarith only [ec,weight,square]
  have aSmall : a≤40/41 := by
    have square := mul_nonneg (sub_nonneg.mpr threshold)
      (show 0≤b+9/41 by linarith only [bn])
    apply le_of_not_gt
    intro bad
    have other := mul_pos (sub_pos.mpr bad)
      (show 0<a+40/41 by linarith only [ap])
    nlinarith only [ru,square,other]
  have wLarge : 1/9≤w := by
    dsimp only [w,half]
    apply (le_div_iff₀ (by linarith only [ap])).mpr
    linarith only [threshold,aSmall]
  have crossIdentity : (1+z^2)*(1+w^2)*(a*t-b*c)=
      2*(z-w)*(1+z*w) := by
    calc
      _ = ((1+w^2)*a)*((1+z^2)*t)-
          ((1+w^2)*b)*((1+z^2)*c) := by ring
      _ = _ := by rw [ra,et,rb,ec]; ring
  have wz : w≤z := by
    have scaled := mul_nonneg (mul_nonneg ez.le rwpos.le) (sub_nonneg.mpr order)
    have zw : 0≤z*w := mul_nonneg zn wn
    rw [crossIdentity] at scaled
    have comparison : 0*(1+z*w)≤(2*(z-w))*(1+z*w) := by
      simpa only [zero_mul] using scaled
    have gap := (mul_le_mul_right (show 0<1+z*w by linarith only [zw])).mp comparison
    linarith only [gap]
  have positive := triangle z w wLarge wz zSmall
  have ceq : c=(1-z^2)/(1+z^2) := (eq_div_iff (ne_of_gt ez)).mpr (by nlinarith only [ec])
  have teq : t=2*z/(1+z^2) := (eq_div_iff (ne_of_gt ez)).mpr (by nlinarith only [et])
  have aeq : a=(1-w^2)/(1+w^2) := (eq_div_iff (ne_of_gt rwpos)).mpr (by nlinarith only [ra])
  have beq : b=2*w/(1+w^2) := (eq_div_iff (ne_of_gt rwpos)).mpr (by nlinarith only [rb])
  have zp : 0<1+z := by linarith only [zn]
  have zm : 0<1-z := by linarith only [zSmall]
  have zsq : 1-z^2≠0 := by
    apply ne_of_gt
    rw [←ec]
    exact mul_pos ez cp
  have height : 1-(1-t)/c=2*z/(1+z) := by
    rw [ceq,teq]
    field_simp [ne_of_gt ez,ne_of_gt zp,zsq]
    <;> ring
  have identity : (1+w^2)^2*(1+z^2)*(1+z)*
      (c*(1-b)+b*(1-(1-t)/c)-(a*c+b*t)*(2-a-b))=numerator z w := by
    rw [height,ceq,teq,aeq,beq]
    dsimp only [numerator]
    field_simp [ne_of_gt ez,ne_of_gt rwpos,ne_of_gt zp]
    <;> ring
  have scalePositive : 0<(1+w^2)^2*(1+z^2)*(1+z) := by positivity
  have scaled : 0≤(1+w^2)^2*(1+z^2)*(1+z)*
      (c*(1-b)+b*(1-(1-t)/c)-(a*c+b*t)*(2-a-b)) := by
    rw [identity]; exact positive
  have nonnegative := nonneg_of_mul_nonneg_right scaled scalePositive
  have numeratorMargin : 64/250047≤numerator z w := by
    simpa only [numerator,NegativeMixedCubic.numerator] using
      NegativeMixedCubic.triangle_margin z w wLarge wz zSmall
  have zSquare : z^2≤4/49 := by
    have product := mul_nonneg (sub_nonneg.mpr zSmall)
      (show 0≤2/7+z by linarith only [zn])
    nlinarith only [product]
  have wSquare : w^2≤4/49 := by
    have product := mul_nonneg (sub_nonneg.mpr (le_trans wz zSmall))
      (show 0≤2/7+w by linarith only [wn])
    nlinarith only [product]
  have wFourth : (1+w^2)^2≤(53/49)^2 := by
    have product := mul_nonneg (show 0≤53/49-(1+w^2) by linarith only [wSquare])
      (show 0≤53/49+(1+w^2) by positivity)
    nlinarith only [product]
  have denominatorBound : (1+w^2)^2*(1+z^2)*(1+z)≤(53/49)^3*(9/7) := by
    calc
      _ ≤ (53/49)^2*(1+z^2)*(1+z) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right wFourth ez.le) zp.le
      _ ≤ (53/49)^2*(53/49)*(1+z) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [zSquare]) (by positivity)) zp.le
      _ ≤ (53/49)^2*(53/49)*(9/7) := mul_le_mul_of_nonneg_left
        (by linarith only [zSmall]) (by positivity)
      _ = _ := by ring
  have comparison := mul_le_mul_of_nonneg_right denominatorBound nonnegative
  rw [identity] at comparison
  nlinarith only [comparison,numeratorMargin]

/-- The original API: the E-owned transverse support floor dominates the
corner allowed by N's parallel floor on the whole closed angle triangle. -/
theorem large (c t a b : ℝ) (cp : 0<c) (tp : 0<t)
    (ap : 0<a) (bn : 0≤b) (eu : c^2+t^2=1) (ru : a^2+b^2=1)
    (cLarge : 6/7<c) (threshold : 9/41≤b) (order : b*c≤a*t) :
    0≤c*(1-b)+b*(1-(1-t)/c)-(a*c+b*t)*(2-a-b) :=
  le_trans (by norm_num) (large_margin c t a b cp tp ap bn eu ru cLarge threshold order)

#print axioms large_margin
#print axioms large
end N12Compact.Completion.OtherCases.C983.NegativeMixedScalars
