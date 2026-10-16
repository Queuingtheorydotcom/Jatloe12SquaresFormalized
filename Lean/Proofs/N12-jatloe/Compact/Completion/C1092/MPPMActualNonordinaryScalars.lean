import Compact.Completion.C1092.ElbowProfile
import Compact.Completion.C1092.TwoFifthsSupport

/-! Exact scalar margins for ELBOW-EXCLUSION Theorem 3.  The source's
angle-derivative argument for the first margin reduces to a sum of
nonnegative unit-circle terms; the second is its printed half-angle
identity.  No angle mesh or side upper bound is used. -/
namespace N12Compact.C1092MPPMActualNonordinary
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem normal_sum (d t : ℝ) (dn : Normal d t) :
    1≤d+t ∧ d+t<10/7 ∧ (4/5)*(d*t)≤d+t-1 := by
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  have prod := mul_nonneg dp.le dn.1
  have low : 1≤d+t := by
    apply le_of_not_gt
    intro small
    have square := mul_pos (sub_pos.mpr small)
      (show 0<1+d+t by linarith only [dp,dn.1])
    nlinarith only [square,dn.2.2,prod]
  have high : d+t<10/7 := by
    apply lt_of_not_ge
    intro large
    have square := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤d+t+10/7 by linarith only [dp,dn.1])
    nlinarith only [square,dn.2.2,sq_nonneg (d-t)]
  have product := mul_nonneg (show 0≤d+t-1 by linarith only [low])
    (show 0≤3/2-d-t by linarith only [high])
  exact ⟨low,high,by nlinarith only [product,dn.2.2]⟩

theorem relative_bounds (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 24/25<c) (sp : 0<s) (small : s<7/25) :
    0<c*d-s*t ∧ 0<c*t+s*d ∧ c*d-s*t≤1 ∧ c*t+s*d≤1 := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  have first := mul_pos (show 0<c-s by linarith only [cp,small]) dp
  have last := mul_nonneg sp.le (sub_nonneg.mpr dn.2.1)
  have kp : 0<c*d-s*t := by nlinarith only [first,last]
  have a := mul_nonneg (show 0≤c by linarith only [cp]) dn.1
  have b := mul_pos sp dp
  have lp : 0<c*t+s*d := by linarith only [a,b]
  have unit : (c*d-s*t)^2+(c*t+s*d)^2=1 := by
    calc
      _ = (c^2+s^2)*(d^2+t^2) := by ring
      _ = 1 := by rw [cn.2.2,dn.2.2]; norm_num
  refine ⟨kp,lp,?_,?_⟩
  · nlinarith only [unit,sq_nonneg (c*t+s*d),sq_nonneg (c*d-s*t-1)]
  · nlinarith only [unit,sq_nonneg (c*d-s*t),sq_nonneg (c*t+s*d-1)]

/-- Theorem 3, equation (19), on the whole closed successor arc. -/
theorem source_longitudinal (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 0<c) (sp : 0<s) :
    0<1-c-(2/5)*s+(c*d-s*t)*(1-d-t)+(c*t+s*d)*(1-t+(2/5)*d) := by
  have cb := normal_bounds cn
  have sum := normal_sum d t dn
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  have prod := mul_nonneg dp.le dn.1
  have cSmall : c<1 := by nlinarith only [cn.2.2,sq_pos_of_pos sp,cp]
  have first := mul_nonneg cp.le
    (show 0≤d+t-1-(3/5)*(d*t) by linarith only [sum.2.2,prod])
  have last := mul_nonneg sp.le
    (show 0≤d-t+(3/5)*t^2 by nlinarith only [dn.2.1,sq_nonneg t])
  have identity :
      1-c-(2/5)*s+(c*d-s*t)*(1-d-t)+(c*t+s*d)*(1-t+(2/5)*d) =
        (1-c)+c*(d+t-1-(3/5)*(d*t))+s*(d-t+(3/5)*t^2) := by
    linear_combination (-(c)+(2/5)*s)*dn.2.2
  rw [identity]
  linarith only [cSmall,first,last]

/-- Theorem 3, equation (18), followed by the unit-vector dot bound. -/
theorem successor_longitudinal (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 0<c) (sp : 0<s) (half : s/(1+c)<7/50) :
    0<1-d-t+(c*d-s*t)*(1-c-(2/5)*s)+(c*t+s*d)*(1-s) := by
  let z := s/(1+c)
  let A := 2-c-s+(2/5)*c*s
  let B := 1-c+s-(2/5)*s^2
  have den : 0<1+c := by linarith only [cp]
  have zp : 0<z := div_pos sp den
  have zh : z<7/50 := half
  have dz : 0<1+z^2 := by positivity
  have angle : z*(1+c)=s := by dsimp [z]; field_simp [den.ne']
  have unitAngle : s*z=1-c := by
    dsimp [z]
    field_simp [den.ne']
    nlinarith only [cn.2.2]
  have cform : (1+z^2)*c=1-z^2 := by
    have product := congrArg (fun a : ℝ => a*z) angle
    nlinarith only [product,unitAngle]
  have sform : (1+z^2)*s=2*z := by
    have product := congrArg (fun a : ℝ => a*z) unitAngle
    nlinarith only [product,angle]
  have cv : c=(1-z^2)/(1+z^2) := by apply (eq_div_iff dz.ne').mpr; nlinarith only [cform]
  have sv : s=2*z/(1+z^2) := by apply (eq_div_iff dz.ne').mpr; nlinarith only [sform]
  have identity : 1-A^2-B^2 =
      4*z*(15-59*z+55*z^2-75*z^3)/(25*(1+z^2)^2) := by
    dsimp [A,B]
    rw [cv,sv]
    field_simp [dz.ne']
    ring
  have polynomial : 0<15-59*z+55*z^2-75*z^3 := by
    have last := mul_nonneg (sq_nonneg z)
      (show 0≤55-75*z by linarith only [zh])
    nlinarith only [last,zh]
  have norm : A^2+B^2<1 := by
    have positive : 0<4*z*(15-59*z+55*z^2-75*z^3)/(25*(1+z^2)^2) :=
      div_pos (mul_pos (by linarith only [zp]) polynomial) (by positivity)
    linarith only [identity,positive]
  have dot : (A*d+B*t)^2+(A*t-B*d)^2=A^2+B^2 := by
    calc
      _ = (A^2+B^2)*(d^2+t^2) := by ring
      _ = A^2+B^2 := by rw [dn.2.2]; ring
  have bound : A*d+B*t<1 := by
    apply lt_of_not_ge
    intro high
    have square := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤A*d+B*t+1 by linarith only [high])
    nlinarith only [square,dot,norm,sq_nonneg (A*t-B*d)]
  have expansion : 1-d-t+(c*d-s*t)*(1-c-(2/5)*s)+(c*t+s*d)*(1-s)=1-A*d-B*t := by
    dsimp [A,B]
    linear_combination -d*cn.2.2
  rw [expansion]
  linarith only [bound]

theorem source_transverse (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 24/25<c) (sp : 0<s) (small : s<7/25) :
    0<1-s+(c*d-s*t)*(1-(543/500)*d)+(c*t+s*d)*(1-d-t) := by
  have rel := relative_bounds c s d t cn dn cp sp small
  have db := normal_bounds dn
  have sum := normal_sum d t dn
  have first := mul_nonneg rel.1.le (sub_nonneg.mpr db.2.1)
  have last := mul_nonneg (sub_nonneg.mpr rel.2.2.2)
    (show 0≤d+t-1 by linarith only [sum.1])
  nlinarith only [first,last,rel.2.2.1,small,sum.2.1]

theorem successor_transverse (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 24/25<c) (sp : 0<s) (small : s<7/25) :
    0<1+((c*d-s*t)+(c*t+s*d))*(1-c)
      +(2/5)*((c*d-s*t)-(c*t+s*d))*s-t+(2/5)*d := by
  have rel := relative_bounds c s d t cn dn cp sp small
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have first := mul_nonneg (show 0≤(c*d-s*t)+(c*t+s*d) by linarith only [rel.1,rel.2.1])
    (sub_nonneg.mpr cb.2.1)
  have last := mul_nonneg (show 0≤(c*d-s*t)-(c*t+s*d)+1 by linarith only [rel.1,rel.2.2.2]) sp.le
  nlinarith only [first,last,dn.2.1,db.2.1,small]

end N12Compact.C1092MPPMActualNonordinary
