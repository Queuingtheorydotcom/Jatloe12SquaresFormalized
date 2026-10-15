import Compact.Completion.C1092.MPPMInwardFinalSuccessorScalars

/-! Exact rational successor endpoints printed in the two inward-final
chapters. Positivity of the three quartics uses only power bounds on the
entire closed interval, so no derivative or endpoint-exclusion premise
is introduced. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

private theorem powers {x a : ℝ} (xn : 0≤x) (bound : x≤a) :
    x^2≤a^2 ∧ x^3≤a^3 ∧ x^4≤a^4 := by
  have an := le_trans xn bound
  have two := mul_le_mul bound bound xn an
  have three := mul_le_mul two bound xn (mul_nonneg an an)
  have four := mul_le_mul two two (mul_nonneg xn xn) (mul_nonneg an an)
  exact ⟨by nlinarith only [two],by nlinarith only [three],by nlinarith only [four]⟩

private theorem rational_frame {c s : ℝ} (cn : Normal c s) :
    c=(1-(half c s)^2)/(1+(half c s)^2) ∧
      s=2*half c s/(1+(half c s)^2) := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have den : 0<1+(half c s)^2 := by nlinarith only [sq_nonneg (half c s)]
  exact ⟨(eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1]),
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])⟩

theorem half_cross {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (order : half c s≤half d t) : s*d≤c*t := by
  let x := half c s
  let y := half d t
  have cn' := rational_frame cn
  have dn' := rational_frame dn
  have xp : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have yp : 0<1+y^2 := by nlinarith only [sq_nonneg y]
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [(normal_bounds cn).1])
  have yn : 0≤y := div_nonneg dn.1 (by linarith only [(normal_bounds dn).1])
  have identity : (1+x^2)*(1+y^2)*(c*t-s*d)=2*(y-x)*(1+x*y) := by
    rw [cn'.1,cn'.2,dn'.1,dn'.2]
    change (1+x^2)*(1+y^2)*
      ((1-x^2)/(1+x^2)*(2*y/(1+y^2))-(2*x/(1+x^2))*((1-y^2)/(1+y^2)))=_
    field_simp [xp.ne',yp.ne']
    <;> ring
  have product := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (sub_nonneg.mpr order))
    (show 0≤1+x*y by nlinarith only [mul_nonneg xn yn])
  have scaled : 0≤(1+x^2)*(1+y^2)*(c*t-s*d) := by rw [identity]; exact product
  have result := nonneg_of_mul_nonneg_right scaled (mul_pos xp yp)
  linarith only [result]

theorem centered_half_endpoint {c s : ℝ} (cn : Normal c s) (small : half c s≤91/1000) :
    0<FE (1/2) (c/11-s/2) c s (95727000/103958161) (40541839/103958161) := by
  let x := half c s
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [(normal_bounds cn).1])
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have frame := rational_frame cn
  have identity :
      1143539771*(1+x^2)^2*
        FE (1/2) (c/11-s/2) c s (95727000/103958161) (40541839/103958161)=
      50000932-415582771*x+262169220*x^2-2012564313*x^3-2947913526*x^4 := by
    rw [frame.1,frame.2]
    change 1143539771*(1+x^2)^2*
      FE (1/2) (((1-x^2)/(1+x^2))/11-(2*x/(1+x^2))/2)
        ((1-x^2)/(1+x^2)) (2*x/(1+x^2))
        (95727000/103958161) (40541839/103958161)=_
    dsimp [FE,alpha]
    field_simp [den.ne']
    <;> ring
  have bounds := powers xn small
  have positive : 0<50000932-415582771*x+262169220*x^2-
      2012564313*x^3-2947913526*x^4 := by
    nlinarith only [small,bounds.2.1,bounds.2.2,sq_nonneg x]
  have scaled : 0<1143539771*(1+x^2)^2*
      FE (1/2) (c/11-s/2) c s (95727000/103958161) (40541839/103958161) := by
    rw [identity]; exact positive
  exact pos_of_mul_pos_right scaled (mul_pos (by norm_num) (pow_pos den 2)).le

theorem centered_final_endpoint {c s : ℝ} (cn : Normal c s) (small : half c s≤91/1000) :
    0<FE (13/50) (c/11-s/2) c s (4165/4813) (2412/4813) := by
  let x := half c s
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [(normal_bounds cn).1])
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have frame := rational_frame cn
  have identity : 1323575*(1+x^2)^2*FE (13/50) (c/11-s/2) c s (4165/4813) (2412/4813)=
      117900-823605*x-159768*x^2-1104695*x^3-3499450*x^4 := by
    rw [frame.1,frame.2]
    change 1323575*(1+x^2)^2*
      FE (13/50) (((1-x^2)/(1+x^2))/11-(2*x/(1+x^2))/2)
        ((1-x^2)/(1+x^2)) (2*x/(1+x^2)) (4165/4813) (2412/4813)=_
    dsimp [FE,alpha]
    field_simp [den.ne']
    <;> ring
  have bounds := powers xn small
  have positive : 0<117900-823605*x-159768*x^2-1104695*x^3-3499450*x^4 := by
    nlinarith only [small,bounds.1,bounds.2.1,bounds.2.2]
  have scaled : 0<1323575*(1+x^2)^2*FE (13/50) (c/11-s/2) c s (4165/4813) (2412/4813) := by
    rw [identity]; exact positive
  exact pos_of_mul_pos_right scaled (mul_pos (by norm_num) (pow_pos den 2)).le

theorem missing_final_endpoint {c s : ℝ} (cn : Normal c s) (small : half c s≤1/10) :
    0<FE (13/50) 0 c s (4165/4813) (2412/4813) := by
  let x := half c s
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [(normal_bounds cn).1])
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have frame := rational_frame cn
  have identity : 120325*(1+x^2)^2*FE (13/50) 0 c s (4165/4813) (2412/4813)=
      -312650*x^4-21195*x^3+182762*x^2-154105*x+16200 := by
    rw [frame.1,frame.2]
    change 120325*(1+x^2)^2*FE (13/50) 0
      ((1-x^2)/(1+x^2)) (2*x/(1+x^2)) (4165/4813) (2412/4813)=_
    dsimp [FE,alpha]
    field_simp [den.ne']
    <;> ring
  have bounds := powers xn small
  have positive : 0< -312650*x^4-21195*x^3+182762*x^2-154105*x+16200 := by
    nlinarith only [small,bounds.2.1,bounds.2.2,sq_nonneg x]
  have scaled : 0<120325*(1+x^2)^2*FE (13/50) 0 c s (4165/4813) (2412/4813) := by
    rw [identity]; exact positive
  exact pos_of_mul_pos_right scaled (mul_pos (by norm_num) (pow_pos den 2)).le

end
#print axioms centered_half_endpoint
#print axioms centered_final_endpoint
#print axioms missing_final_endpoint
end N12Compact.C1092MPPMInwardFinal
