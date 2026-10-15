import Compact.Geometry.CornerOuterOrderEndpoint
import Mathlib.Tactic.Positivity

/-! A continuous scalar margin for the negative left singleton. The
central angle is removed by a chord comparison. The remaining two
coefficients lie in a fixed unit disk, except near zero tilt where a
single linear bound suffices. No pose or angle enumeration is used. -/
namespace N12Compact.CornerWallNegativeMargin
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

theorem half_order {c s d t : ℝ}
    (on : Normal c s) (wn : Normal d t) (order : s≤t) :
    c*(1-t)≤d*(1-s) := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have first := mul_nonneg (sub_nonneg.mpr order)
    (add_nonneg
      (mul_nonneg (sub_nonneg.mpr wb.2.2.2.1)
        (sub_nonneg.mpr ob.2.2.2.1))
      (mul_nonneg (by linarith only [ob.1] : 0≤c)
        (by linarith only [wb.1] : 0≤d)))
  have identity : (c+d)*(d*(1-s)-c*(1-t))=
      (t-s)*((1-t)*(1-s)+c*d) := by
    linear_combination (1-s)*wn.2.2-(1-t)*on.2.2
  have scaled : 0≤(c+d)*(d*(1-s)-c*(1-t)) := by
    linarith only [first,identity]
  have gap := nonneg_of_mul_nonneg_right scaled
    (by linarith only [ob.1,wb.1] : 0<c+d)
  linarith only [gap]

private theorem coefficient_bound {d t l r : ℝ}
    (wn : Normal d t) (ln : Normal l r)
    (order : r≤t) (small : t≤51/100) :
    0≤1-l*(189/100-t-(1-t)/d)-r*(d^2/(1+d)) := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have dp : 0<d := by linarith only [wb.1]
  have dp1 : 0<1+d := by linarith only [dp]
  let a := 189/100-t-(1-t)/d
  let b := d^2/(1+d)
  have a_global : a≤89/100 := by
    have product := mul_nonneg (sub_nonneg.mpr wb.2.1)
      (sub_nonneg.mpr wb.2.2.2.1)
    have identity : d*(89/100-a)=(1-d)*(1-t) := by
      dsimp [a]; field_simp [dp.ne']; ring
    have scaled : 0≤d*(89/100-a) := by linarith only [identity,product]
    have gap := nonneg_of_mul_nonneg_right scaled dp
    linarith only [gap]
  have b_global : b≤1/2 := by
    apply (div_le_iff₀ dp1).mpr
    have product := mul_nonneg (sub_nonneg.mpr wb.2.1)
      (show 0≤d+1/2 by linarith only [dp])
    nlinarith only [product]
  by_cases low : t≤11/50
  · have first := mul_nonneg (by linarith only [lb.1] : 0≤l)
      (sub_nonneg.mpr a_global)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr b_global)
    change 0≤1-l*a-r*b
    clear_value a b
    nlinarith only [first,second,lb.2.1,order,low]
  · have high : 11/50≤t := le_of_lt (lt_of_not_ge low)
    have tSquare := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤t+11/50 by linarith only [wn.1])
    have d_high : d≤49/50 := by
      by_contra no
      have product := mul_pos (show 0<d-49/50 by linarith only [no])
        (show 0<d+49/50 by linarith only [dp])
      nlinarith only [product,tSquare,wn.2.2]
    have first := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤1-t by linarith only [small])
    have second := mul_nonneg (show (0:ℝ)≤11/25 by norm_num)
      (sub_nonneg.mpr small)
    have factor : 0≤(t+11/50)*(1-t)-(11/50)^2 := by
      nlinarith only [first,second]
    have product := mul_nonneg (sub_nonneg.mpr high) factor
    have cubic : 4719/125000≤t^2*(1-t) := by
      have identity : t^2*(1-t)-4719/125000=
          (t-11/50)*((t+11/50)*(1-t)-(11/50)^2) := by ring
      linarith only [product,identity]
    have dProduct := mul_nonneg (sub_nonneg.mpr d_high)
      (show 0≤99/50+d by linarith only [dp])
    have denominator_bound : d*(1+d)≤4851/2500 := by
      nlinarith only [dProduct]
    have scaled_margin : 0≤(1+d)*((1-d)*(1-t)-(19/1000)*d) := by
      have identity :
          (1+d)*((1-d)*(1-t)-(19/1000)*d)=
            t^2*(1-t)-(19/1000)*d*(1+d) := by
        linear_combination (t-1)*wn.2.2
      nlinarith only [identity,cubic,denominator_bound]
    have margin := nonneg_of_mul_nonneg_right scaled_margin dp1
    have a_high : a≤871/1000 := by
      have identity : d*(871/1000-a)=
          (1-d)*(1-t)-(19/1000)*d := by
        dsimp [a]; field_simp [dp.ne']; ring
      have scaled : 0≤d*(871/1000-a) := by linarith only [identity,margin]
      have gap := nonneg_of_mul_nonneg_right scaled dp
      linarith only [gap]
    have b_high : b≤49/100 := by
      apply (div_le_iff₀ dp1).mpr
      have product := mul_nonneg (sub_nonneg.mpr d_high)
        (show 0≤d+49/100 by linarith only [dp])
      nlinarith only [product]
    have disk : (871/1000)*l+(49/100)*r≤1 := by
      have identity :
          ((871/1000)*l+(49/100)*r)^2+
          ((871/1000)*r-(49/100)*l)^2=(998741/1000000:ℝ) := by
        linear_combination (998741/1000000)*ln.2.2
      nlinarith only [identity,
        sq_nonneg ((871/1000)*r-(49/100)*l),
        sq_nonneg ((871/1000)*l+(49/100)*r-1)]
    have first := mul_nonneg (by linarith only [lb.1] : 0≤l)
      (sub_nonneg.mpr a_high)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr b_high)
    change 0≤1-l*a-r*b
    clear_value a b
    nlinarith only [first,second,disk]

/-- The exact coefficient required by the actual O/L/W support cycle
for a negative left singleton whose tilt is no larger than W's. -/
theorem margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (leftOrder : r≤t)
    (small : t≤51/100) (wide : 43/50≤d) :
    0≤l+r-d+l*r*(c+t-72/25+(1-t)/d)+
      l^2*(s+d-2+(1-s)/c) := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have cp : 0<c := by linarith only [ob.1]
  have dp : 0<d := by linarith only [wb.1]
  have lp : 0<l := by linarith only [lb.1]
  have dc := cosine_order wn on order
  have dl := cosine_order wn ln leftOrder
  have chord := half_order on wn order
  have cross1 := mul_nonneg dp.le (sub_nonneg.mpr leftOrder)
  have cross2 := mul_nonneg wn.1 (sub_nonneg.mpr dl)
  have cross : d*r≤l*t := by nlinarith only [cross1,cross2]
  have slack : (24/25)*t≤1-t := by linarith only [small]
  have weighted1 := mul_nonneg lp.le (sub_nonneg.mpr chord)
  have weighted2 := mul_nonneg (mul_nonneg cp.le lp.le) (sub_nonneg.mpr slack)
  have weighted3 := mul_nonneg (show 0≤(24/25)*c by positivity)
    (sub_nonneg.mpr cross)
  have ratio : (24/25)*c*r≤l*(1-s) := by
    have scaled : 0≤d*(l*(1-s)-(24/25)*c*r) := by
      nlinarith only [weighted1,weighted2,weighted3]
    have gap := nonneg_of_mul_nonneg_right scaled dp
    linarith only [gap]
  let H := 1+t-289/100+(1-t)/d
  let F0 := l+r-d+l*r*H+l^2*(d-1)
  let F := l+r-d+l*r*(c+t-72/25+(1-t)/d)+
    l^2*(s+d-2+(1-s)/c)
  have central1 := mul_nonneg (mul_nonneg lp.le (sub_nonneg.mpr ob.2.1))
    (sub_nonneg.mpr ratio)
  have central2 := mul_nonneg (mul_nonneg (mul_nonneg lp.le ln.1) cp.le)
    (show 0≤1/100-(1-c)/25 by linarith only [wide,dc])
  have identity : c*(F-F0)=
      l*(1-c)*(l*(1-s)-(24/25)*c*r)+
      l*r*c*(1/100-(1-c)/25) := by
    dsimp [F,F0,H]
    field_simp [cp.ne',dp.ne']; ring
  have central : F0≤F := by
    have scaled : 0≤c*(F-F0) := by
      rw [identity]
      exact add_nonneg central1 central2
    have gap := nonneg_of_mul_nonneg_right scaled cp
    linarith only [gap]
  have lp1 : 0<1+l := by linarith only [lp]
  have dp1 : 0<1+d := by linarith only [dp]
  have ratioOrder : d/(1+d)≤l/(1+l) := by
    apply (div_le_div_iff₀ dp1 lp1).mpr
    nlinarith only [dl]
  have scalar := coefficient_bound wn ln leftOrder small
  have remainder := mul_nonneg ln.1 (sub_nonneg.mpr ratioOrder)
  have bracket : 0≤1+l*H-d*r+l*r/(1+l) := by
    have identity :
        1+l*H-d*r+l*r/(1+l)=
          (1-l*(189/100-t-(1-t)/d)-r*(d^2/(1+d)))+
          r*(l/(1+l)-d/(1+d)) := by
      dsimp [H]
      field_simp [lp1.ne',dp1.ne',dp.ne']; ring
    nlinarith only [identity,scalar,remainder]
  have endpoint : F0=r*(1+l*H-d*r+l*r/(1+l)) := by
    apply (mul_right_cancel₀ lp1.ne')
    calc
      F0*(1+l) = r*(1+l*H-d*r+l*r/(1+l))*(1+l)+
          (d*(1+l)-l)*(l^2+r^2-1) := by
        dsimp [F0]
        field_simp [lp1.ne']; ring
      _ = _ := by rw [ln.2.2]; ring
  have nonnegative : 0≤F0 := by rw [endpoint]; exact mul_nonneg ln.1 bracket
  change 0≤F
  linarith only [central,nonnegative]

#print axioms margin
end N12Compact.CornerWallNegativeMargin
