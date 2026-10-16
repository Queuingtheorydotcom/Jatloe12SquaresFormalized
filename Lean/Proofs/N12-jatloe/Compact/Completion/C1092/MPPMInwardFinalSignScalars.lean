import Compact.Completion.C1092.MPPMInwardFinalMargins

/-! Both full-angle scalar margins in NEGATIVE-INWARD-SUCCESSOR-SIGN.
The printed convex-quartic step is an explicit positive chord remainder;
the second angular maximization is a two-coordinate order identity. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

def signFirst (c s d t : ℝ) :=
  1-c+(13/50)*s+(c*d-s*t)*(1-d+(2/5)*t)+(c*t+s*d)*(1-d-t)
def signLast (c s d t : ℝ) :=
  1-d-t+(c*t+s*d)*(1-c+(13/50)*s)+(c*d-s*t)*(1-(7/20)*(c-s))

private theorem sign_polynomial_negative {z : ℝ} (low : 1/10≤z) (high : z≤5/12) :
    27569*z^4-30600*z^3+22458*z^2-6600*z+169<0 := by
  let a : ℝ := 1/10
  let b : ℝ := 5/12
  let P (x : ℝ) := 27569*x^4-30600*x^3+22458*x^2-6600*x+169
  let Q := 27569*(z^2+(a+b)*z+a^2+a*b+b^2)-30600*(z+a+b)+22458
  have positive : 0<Q := by
    dsimp [Q,a,b]
    nlinarith only [sq_nonneg z,high]
  have identity : (b-z)*P a+(z-a)*P b-(b-a)*P z=(b-a)*(z-a)*(b-z)*Q := by
    dsimp [P,Q]; ring
  have left : P a<0 := by norm_num [P,a]
  have right : P b<0 := by norm_num [P,b]
  have first := mul_nonpos_of_nonneg_of_nonpos (show 0≤b-z by exact sub_nonneg.mpr high) left.le
  have last := mul_nonpos_of_nonneg_of_nonpos (show 0≤z-a by exact sub_nonneg.mpr low) right.le
  have correction := mul_nonneg
    (mul_nonneg (mul_nonneg (show 0≤b-a by norm_num [a,b])
      (show 0≤z-a by exact sub_nonneg.mpr low))
      (show 0≤b-z by exact sub_nonneg.mpr high)) positive.le
  have strict : (b-z)*P a+(z-a)*P b<0 := by
    by_cases endpoint : z=a
    · have product := mul_neg_of_pos_of_neg (show 0<b-a by norm_num [a,b]) left
      simpa only [endpoint,sub_self,zero_mul,add_zero] using product
    · have product := mul_neg_of_pos_of_neg
        (sub_pos.mpr (lt_of_le_of_ne low (Ne.symm endpoint))) right
      exact add_neg_of_nonpos_of_neg first product
  have result : P z<0 := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg (show 0≤b-a by norm_num [a,b]) no
    linarith only [identity,correction,strict,bad]
  exact result

theorem sign_first_positive {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t) (tp : 0<t) :
    0<signFirst c s d t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  let A := 13/50+d-t-1+(3/5)*t^2
  let B := 2-d-t+(3/5)*d*t
  have formula : signFirst c s d t=1-B*c+A*s := by
    dsimp [signFirst,A,B]
    linear_combination -(c+s)*dn.2.2
  have data := quarter_data d t dp.le dn.1 dn.2.2
  let z := half d t
  by_cases low : z≤1/10
  · have small := small_tenth dn low
    have Ap : 0<A := by dsimp [A]; nlinarith only [small.1,small.2,sq_nonneg t]
    have Bp : 0<B := by
      have product := mul_nonneg dp.le dn.1
      dsimp [B]; nlinarith only [db.2.2.2.2.2,product]
    have chord := mul_nonneg
      (show 0≤3/2-d-t by linarith only [db.2.2.2.2.2])
      (show 0≤d+t-1 by linarith only [db.2.2.2.2.1])
    have arc : (4/5)*d*t≤d+t-1 := by nlinarith only [chord,dn.2.2]
    have product := mul_pos dp tp
    have Bu : B<1 := by dsimp [B]; nlinarith only [arc,product]
    have first := mul_nonneg Bp.le (show 0≤1-c by linarith only [cb.2.1])
    have last := mul_nonneg Ap.le cn.1
    rw [formula]
    nlinarith only [Bu,first,last]
  · have den : 0<1+z^2 := by nlinarith only [sq_nonneg z]
    have df : d=(1-z^2)/(1+z^2) :=
      (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
    have tf : t=2*z/(1+z^2) :=
      (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
    have zu : z≤5/12 := by
      have ordered := mul_nonneg den.le (sub_nonneg.mpr dn.2.1)
      apply le_of_not_gt
      intro large
      have square := mul_nonneg (show 0≤z-5/12 by linarith only [large])
        (show 0≤z+5/12 by linarith only [data.1])
      nlinarith only [ordered,data.2.2.2.1,data.2.2.2.2,square,large]
    have polynomial := sign_polynomial_negative (by linarith only [low]) zu
    have identity : 2500*(1+z^2)^2*(1-B^2-A^2)=
        -(27569*z^4-30600*z^3+22458*z^2-6600*z+169) := by
      dsimp [A,B]
      rw [df,tf]
      field_simp [den.ne']
      ring
    have scaled : 0<2500*(1+z^2)^2*(1-B^2-A^2) := by nlinarith only [identity,polynomial]
    have norm := pos_of_mul_pos_right scaled
      (show 0≤2500*(1+z^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _))
    have projection : (B*c-A*s)^2≤B^2+A^2 := by
      have identity : (B*c-A*s)^2+(B*s+A*c)^2=(B^2+A^2)*(c^2+s^2) := by ring
      rw [cn.2.2] at identity
      nlinarith only [identity,sq_nonneg (B*s+A*c)]
    rw [formula]
    apply lt_of_not_ge
    intro no
    have square := mul_nonneg (show 0≤B*c-A*s-1 by linarith only [no])
      (show 0≤B*c-A*s+1 by linarith only [no])
    nlinarith only [norm,projection,square]

theorem sign_last_positive {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t) :
    0<signLast c s d t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  let P := (7/20)*c^2+(13/20)*c*s-c-(13/50)*s^2-s+1
  let Q := c^2-(61/100)*c*s-c+(7/20)*s^2+s+1
  have formula : signLast c s d t=1-P*d-Q*t := by dsimp [signLast,P,Q]; ring
  have product := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤(13/20)*c-(61/100)*s by linarith only [cn.1,cn.2.1])
  have order : P≤Q := by dsimp [P,Q]; nlinarith only [product,cn.1]
  have chord := mul_nonneg (show 0≤c-7/10 by linarith only [cb.1])
    (show 0≤1-c by linarith only [cb.2.1])
  have deficit : 1-c≤(10/17)*s^2 := by nlinarith only [chord,cn.2.2]
  have cross : c*s≤1/2 := by nlinarith only [cn.2.2,sq_nonneg (c-s)]
  have sum : P+Q≤137/100 := by
    dsimp [P,Q]
    nlinarith only [deficit,cross,cn.2.2,sq_nonneg s]
  have compare := mul_nonneg (show 0≤Q-P by linarith only [order]) (sub_nonneg.mpr dn.2.1)
  have bound := mul_nonneg (show 0≤137/100-(P+Q) by linarith only [sum])
    (show 0≤d+t by linarith only [db.1,dn.1])
  rw [formula]
  nlinarith only [compare,bound,db.2.2.2.2.2]

#print axioms sign_first_positive
#print axioms sign_last_positive
end
end N12Compact.C1092MPPMInwardFinal
