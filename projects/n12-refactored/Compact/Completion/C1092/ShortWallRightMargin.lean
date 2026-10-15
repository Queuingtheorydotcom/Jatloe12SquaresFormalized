import Compact.Completion.C1092.ShortWallScalars

/-! The ordered narrow right-wall margin is proved by a concave chord
over the entire interval 0 ≤ t ≤ s. Its endpoints include t=s and t=0. -/
namespace N12Compact.C1092ShortWallRightMargin
open C977CornerCubic C977CornerSectorBounds C1092ShortWallScalars
set_option Elab.async false

noncomputable def X (c s : ℝ) : ℝ := 2+s^2/2-c*s-s*allowance c s
noncomputable def Y (c s : ℝ) : ℝ := 3-s^2-c*s/2+c*allowance c s

/-- Exact retained inequality (7), with no monotonicity assumption on
the full margin and no independent optimization of its support faces. -/
theorem ordered {c s r t : ℝ} (cn : Normal c s) (rn : Normal r t)
    (narrow : 4*s ≤ c) (order : t ≤ s) :
    0 ≤ r^2*X c s+r*t*(Y c s-2)+
      r*((c*r+s*t)-(c*t-s*r)+1)+(1543/500)*t^2-4 := by
  classical
  have cb := normal_bounds cn
  have rb := normal_bounds rn
  have nb := narrow_bounds cn narrow
  have ab := allowance_bounds cn narrow
  have cosine := cosine_order cn rn order
  have rNarrow : 4*t ≤ r := by linarith only [order,narrow,cosine]
  have rnb := narrow_bounds rn rNarrow
  let M0 := s^2/2-(1-c)*(1-s)-s*allowance c s
  let B := 1-c+s-s^2-c*s/2+c*allowance c s
  have baseline : (2/5)*s^3 ≤ M0 := cubic_baseline cn narrow
  have s3 : 0 ≤ s^3 := pow_nonneg cn.1 3
  have rSquare : 9/10 ≤ r^2 := by
    have product := mul_nonneg (show 0 ≤ r-24/25 by linarith only [cosine,nb.1])
      (show 0 ≤ r+24/25 by linarith only [rb.1])
    nlinarith only [product]
  have first := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr baseline)
  have second := mul_nonneg s3
    (show 0 ≤ (2/5)*r^2-9/25 by linarith only [rSquare])
  have cubic : (9/25)*s^3 ≤ r^2*M0 := by nlinarith only [first,second]
  have coefficientIdentity : B-(s/2-s^2/2) =
      (1-c)^2/2+s*(1-c)/2+c*allowance c s := by
    dsimp [B]
    linear_combination -cn.2.2/2
  have b0 := sq_nonneg (1-c)
  have b1 := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
  have b2 := mul_nonneg (show 0 ≤ c by linarith only [cb.1]) ab.1
  have coefficient : s/2-s^2/2 ≤ B := by
    nlinarith only [coefficientIdentity,b0,b1,b2]
  have lowerPositive : 0 ≤ s/2-s^2/2 := by
    have product := mul_nonneg cn.1 (show 0 ≤ 1-s by linarith only [nb.2.1])
    nlinarith only [product]
  have b3 := mul_nonneg (show 0 ≤ r by linarith only [rb.1])
    (sub_nonneg.mpr coefficient)
  have b4 := mul_nonneg (show 0 ≤ r-24/25 by linarith only [cosine,nb.1])
    lowerPositive
  have coefficientScaled : (12/25)*s-(12/25)*s^2 ≤ r*B := by
    nlinarith only [b3,b4]
  have b5 := mul_nonneg rn.1 (sub_nonneg.mpr coefficientScaled)
  let Q := fun z : ℝ => (9/25)*s^3+((12/25)*s-(12/25)*s^2)*z-(17/40)*z^2
  have radialGap := mul_nonneg (sq_nonneg t)
    (by norm_num : (0 : ℝ) ≤ 17/40-25/49+43/500)
  have identity : r^2*X c s+r*t*(Y c s-2)+
      r*((c*r+s*t)-(c*t-s*r)+1)+(1543/500)*t^2-4 =
      r^2*M0+r*t*B-(1-r)+(43/500)*t^2 := by
    dsimp [X,Y,M0,B]
    linear_combination 3*rn.2.2
  have bounded : Q t ≤ r^2*X c s+r*t*(Y c s-2)+
      r*((c*r+s*t)-(c*t-s*r)+1)+(1543/500)*t^2-4 := by
    dsimp [Q]
    nlinarith only [identity,cubic,b5,rnb.2.2,radialGap]
  have endpoint0 : 0 ≤ Q 0 := by dsimp [Q]; nlinarith only [s3]
  have endpointS : 0 ≤ Q s := by
    have product := mul_nonneg (sq_nonneg s)
      (show 0 ≤ 11/200-(3/25)*s by linarith only [nb.2.1])
    dsimp [Q]
    nlinarith only [product]
  have chordIdentity : s*Q t=(s-t)*Q 0+t*Q s+(17/40)*s*t*(s-t) := by
    dsimp [Q]
    ring
  have firstWeight := mul_nonneg (sub_nonneg.mpr order) endpoint0
  have lastWeight := mul_nonneg rn.1 endpointS
  have curve := mul_nonneg (mul_nonneg cn.1 rn.1) (sub_nonneg.mpr order)
  have positive : 0 ≤ Q t := by
    by_cases zero : s=0
    · have tz : t=0 := by linarith only [order,rn.1,zero]
      simpa only [tz] using endpoint0
    · have sp : 0 < s := lt_of_le_of_ne cn.1 (Ne.symm zero)
      have scaled : 0 ≤ s*Q t := by
        rw [chordIdentity]
        apply add_nonneg (add_nonneg firstWeight lastWeight)
        have weighted := mul_nonneg (by norm_num : (0 : ℝ) ≤ 17/40) curve
        simpa only [mul_assoc] using weighted
      exact nonneg_of_mul_nonneg_right scaled sp
  exact positive.trans bounded

#print axioms ordered
end N12Compact.C1092ShortWallRightMargin
