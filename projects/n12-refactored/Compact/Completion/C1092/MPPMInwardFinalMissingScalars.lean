import Compact.Completion.C1092.MPPMInwardFinalFloor

/-! The full missing-center predecessor scalar margin. This exact
quartic difference replaces the derivative estimates in §3 while using
the same full angle interval and sharp f/g bound. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

theorem missing_predecessor_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (close : 17/20<c) (small : s<13/25) (low : 1/10≤half c s)
    (steep : 8/17≤r) :
    c*(c*f b r-s*g b r)<c-1+s*(1-c+(13/50)*s) := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [close]
  have data := quarter_data c s cp.le cn.1 cn.2.2
  let x := half c s
  have xn : 0≤x := data.1
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have halfIdentity : x*(1+c)=s := by
    dsimp [x,half]
    exact div_mul_cancel₀ _ (by linarith only [cp] : (1+c)≠0)
  have xu : x≤3/10 := by
    apply le_of_not_gt
    intro large
    have product := mul_pos (show 0<x-3/10 by linarith only [large])
      (show 0<1+c by linarith only [cp])
    nlinarith only [product,halfIdentity,close,small]
  have Kp : 0<s-(2/11)*c := by
    have product := mul_nonneg (show 0≤x-1/10 by exact sub_nonneg.mpr low)
      (show 0≤1+c by linarith only [cp])
    nlinarith only [product,halfIdentity,cb.2.1]
  have cf : c=(1-x^2)/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
  have sf : s=2*x/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
  let G : ℝ := 104/289
  let P (z : ℝ) := (-22-2*G)*z^4+(44-22*G)*z^3+
    (-264/25+4*G)*z^2+22*G*z-2*G
  let D := (-22-2*G)*(x^3+x^2/10+x/100+1/1000)+
    (44-22*G)*(x^2+x/10+1/100)+(-264/25+4*G)*(x+1/10)+22*G
  have x2 : x^2≤9/100 := by
    have product := mul_nonneg (show 0≤3/10-x by linarith only [xu])
      (show 0≤3/10+x by linarith only [xn])
    nlinarith only [product]
  have x3 : x^3≤27/1000 := by
    have product := mul_nonneg (show 0≤3/10-x by linarith only [xu]) (sq_nonneg x)
    nlinarith only [product,x2]
  have Dp : 0<D := by
    have positive := sq_nonneg x
    dsimp [D,G]
    nlinarith only [x3,x2,xu,xn,positive]
  have difference : P x-P (1/10)=(x-1/10)*D := by dsimp [P,D]; ring
  have base : 0<P (1/10) := by norm_num [P,G]
  have monotone := mul_nonneg (show 0≤x-1/10 by exact sub_nonneg.mpr low) Dp.le
  have polynomial : 0<P x := by linarith only [base,difference,monotone]
  have identity :
      11*(1+x^2)^2*(c-1+s*(1-c+(13/50)*s)+c*(s-(2/11)*c)*G)=P x := by
    rw [cf,sf]
    dsimp [P]
    field_simp [den.ne']
    <;> ring
  have scaled : 0<11*(1+x^2)^2*(c-1+s*(1-c+(13/50)*s)+c*(s-(2/11)*c)*G) := by
    rw [identity]; exact polynomial
  have margin := pos_of_mul_pos_right scaled
    (show 0≤11*(1+x^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _))
  have ratio := mul_le_mul_of_nonneg_left (fg_bounds bn).2.1 cp.le
  have lower := mul_nonneg Kp.le (show 0≤g b r-G by exact sub_nonneg.mpr (g_lower bn steep))
  have combine := mul_nonneg cp.le
    (show 0≤-(s-(2/11)*c)*G-(c*f b r-s*g b r) by nlinarith only [ratio,lower])
  nlinarith only [margin,combine]

#print axioms missing_predecessor_margin
end N12Compact.C1092MPPMInwardFinal
