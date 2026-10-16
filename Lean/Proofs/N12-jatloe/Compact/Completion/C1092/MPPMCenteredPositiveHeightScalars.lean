import Compact.Completion.C1092.MPPMInwardFinalCapScalars

/-! CENTERED-POSITIVE-INWARD-ENDING sections 7--8: the three scalar
support margins, on the full closed predecessor canonical intervals. -/
namespace N12Compact.C1092MPPMCenteredPositive
open C977CornerCubic C1092MPPMInwardFinal
set_option Elab.async false
noncomputable section

theorem positive_own_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (close : 99/100<c) (small : s<7/50) :
    0<1-(543/500)*b-r+(c*r-s*b)*(1-(7/50)*c+s/2)+
      (c*b+s*r)*(17/125+s) := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cosineProduct := mul_nonneg (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤1+c-100/51 by linarith only [close])
  have deficit : 1-c≤(51/100)*s^2 := by nlinarith only [cosineProduct,cn.2.2]
  have square := mul_nonneg cn.1 (show 0≤7/50-s by linarith only [small])
  have closeProduct := mul_nonneg cn.1 (show 0≤c-99/100 by linarith only [close])
  have cross := mul_nonneg cn.1 (show 0≤c by linarith only [close])
  let P := 543/500-(17/125)*c+s-(57/50)*c*s+s^2/2
  let Q := 1-c+7/50-(57/50)*s^2-c*s/2-(17/125)*s
  have Pb : P≤19/20 := by dsimp [P]; nlinarith only [deficit,square,closeProduct,cn.1]
  have Qb : Q≤7/50 := by dsimp [Q]; nlinarith only [deficit,cross,cn.1,sq_nonneg s]
  have norm := dot_strict bn.2.2 (by norm_num : (0:ℝ)<1)
    (by norm_num : (19/20:ℝ)^2+(7/50)^2<1^2)
  have first := mul_nonneg (show 0≤b by linarith only [bb.1]) (sub_nonneg.mpr Pb)
  have last := mul_nonneg bn.1 (sub_nonneg.mpr Qb)
  have identity :
      1-(543/500)*b-r+(c*r-s*b)*(1-(7/50)*c+s/2)+(c*b+s*r)*(17/125+s)=
      1-P*b-Q*r := by
    dsimp [P,Q]
    linear_combination -(7/50)*r*cn.2.2
  nlinarith only [first,last,norm,identity]

theorem negative_right_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (close : 99/100<c) (small : s<7/50) :
    43/500<(c*b-s*r)*(17/125+s) := by
  have bb := normal_bounds bn
  have strict := mul_pos (sub_pos.mpr close)
    (show 0<17/125+s by linarith only [cn.1])
  have correction := mul_nonneg cn.1 (show 0≤427/500-s by linarith only [small])
  have base : 1683/12500<(c-s)*(17/125+s) := by
    nlinarith only [strict,correction]
  have weighted := mul_pos (show 0<b by linarith only [bb.1]) (sub_pos.mpr base)
  have order := mul_nonneg (mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1))
    (show 0≤17/125+s by linarith only [cn.1])
  nlinarith only [weighted,order,bb.1]

theorem negative_left_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (close : 99/100<c) :
    0<(43/50)*(c*b-s*r)+(c*r+s*b)*(17/125+s)-(7/20)*(b+r) := by
  have bb := normal_bounds bn
  let F := (43/50)*c+(17/125)*s+s^2-7/20
  let G := (17/125)*c+s*(c-43/50)-7/20
  have Fb : 2507/5000<F := by dsimp [F]; nlinarith only [close,cn.1,sq_nonneg s]
  have cross := mul_nonneg cn.1 (show 0≤c-43/50 by linarith only [close])
  have Gb : -673/3125<G := by dsimp [G]; nlinarith only [close,cross]
  have first := mul_pos (show 0<b by linarith only [bb.1]) (sub_pos.mpr Fb)
  have last := mul_nonneg bn.1 (sub_nonneg.mpr Gb.le)
  have compare := mul_nonneg (sub_nonneg.mpr bn.2.1) (by norm_num : (0:ℝ)≤673/3125)
  have identity : (43/50)*(c*b-s*r)+(c*r+s*b)*(17/125+s)-(7/20)*(b+r)=b*F+r*G := by
    dsimp [F,G]
    ring
  nlinarith only [first,last,compare,bb.1,identity]

theorem positive_coefficients_upper {b r : ℝ} (bn : Normal b r) :
    r^2+b-r-(43/500)*b*r≤1 ∧ r^2+b-r≤1 := by
  have bb := normal_bounds bn
  have square := mul_nonneg bn.1 (show 0≤1-r by linarith only [bb.2.2.2.1])
  have cross := mul_nonneg (show 0≤b by linarith only [bb.1]) bn.1
  constructor <;> nlinarith only [square,cross,bb.2.1]

theorem negative_coefficient_upper {b r : ℝ} (bn : Normal b r) :
    b^2-(43/500)*b*r-b+r≤1 := by
  have bb := normal_bounds bn
  have square := mul_nonneg (show 0≤b by linarith only [bb.1])
    (show 0≤1-b by linarith only [bb.2.1])
  have cross := mul_nonneg (show 0≤b by linarith only [bb.1]) bn.1
  nlinarith only [square,cross,bb.2.2.2.1]

end
end N12Compact.C1092MPPMCenteredPositive
