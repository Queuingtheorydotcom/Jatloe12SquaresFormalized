import Compact.Geometry.CentralRightCornerSupport

/-! Full-square support transfers in the center-owned right chain.
The inward auxiliary point remains explicit. When the wall is steeper,
the mixed separator forces its lower U face past the actual point (3,2).
No wall angle or point is asserted from the local marker alone. -/
namespace N12Compact.CentralRightMixedTransfer

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem steeper_direction_margin {c s d t : ℝ}
    (bn : Normal c s) (positive : 0≤d) (order : 0≤c*t-s*d) :
    d≤c*d+s*t-(13/50)*s*(c*t-s*d) := by
  have cb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  have first := mul_nonneg positive (sub_nonneg.mpr cb.2.1)
  have second := mul_nonneg (mul_nonneg bn.1 order)
    (show 0≤1-(13/50)*c by linarith only [cb.2.1])
  have identity : c*(c*d+s*t-(13/50)*s*(c*t-s*d)-d)=
      d*(1-c)+s*(c*t-s*d)*(1-(13/50)*c) := by
    linear_combination d*bn.2.2
  have scaled : 0≤c*(c*d+s*t-(13/50)*s*(c*t-s*d)-d) := by
    linarith only [identity,first,second]
  have result := nonneg_of_mul_nonneg_right scaled cp
  linarith only [result]

theorem steeper_margin {c s d t : ℝ}
    (bn : Normal c s) (rn : Normal d t) (order : 0≤c*t-s*d) :
    d≤c*d+s*t-(13/50)*s*(c*t-s*d) :=
  steeper_direction_margin bn (by linarith only [(normal_bounds rn).1]) order

/-- The entire steeper-wall mixed support branch forces a real inward
lower-U escape. The strict full side length supplies the strict result. -/
theorem steeper_direction_reach (B : OpenSquare) {d t : ℝ}
    (bn : Normal B.c B.s) (dp : 0<d) (ts : 0≤t)
    (side : 1<B.side) (inner : B.Inside (113/50) 2)
    (start : 2*(B.c+B.s)≤B.loU)
    (order : 0≤B.c*t-B.s*d) :
    3*d+2*t<upper B d t := by
  have cb := normal_bounds bn
  have cp : 0<B.c := by linarith only [cb.1]
  let K := d*B.c+t*B.s
  let H := t*B.c-d*B.s
  have kp : 0<K := by
    have first := mul_pos dp cp
    have second := mul_nonneg ts bn.1
    dsimp [K]; linarith only [first,second]
  have hp : 0≤H := by dsimp [H]; nlinarith only [order]
  have form : upper B d t=K*(B.loU+B.side)+H*(B.loV+B.side) := by
    rw [upper_in_bands]
    have first : d*B.c+t*B.s=K := rfl
    have second : -d*B.s+t*B.c=H := by dsimp [H]; ring
    rw [first,second,abs_of_nonneg kp.le,abs_of_nonneg hp]
    ring
  have faceWeight := mul_nonneg kp.le (sub_nonneg.mpr start)
  have pointWeight := mul_nonneg hp (sub_nonneg.mpr inner.2.2.2.le)
  have width := mul_pos (sub_pos.mpr side) kp
  have margin : d≤K-(13/50)*B.s*H := by
    simpa only [K,H,mul_comm,mul_left_comm] using steeper_direction_margin bn dp.le order
  have identity :
      K*(2*(B.c+B.s)+1)+H*(2*B.c-(113/50)*B.s)=
      2*(d+t)+K-(13/50)*B.s*H := by
    dsimp [K,H]
    linear_combination 2*(d+t)*bn.2.2
  rw [form]
  clear_value K H
  nlinarith only [faceWeight,pointWeight,width,margin,identity]

theorem steeper_reach (B : OpenSquare) {d t : ℝ}
    (bn : Normal B.c B.s) (rn : Normal d t)
    (side : 1<B.side) (inner : B.Inside (113/50) 2)
    (start : 2*(B.c+B.s)≤B.loU)
    (order : 0≤B.c*t-B.s*d) :
    3*d+2*t<upper B d t :=
  steeper_direction_reach B bn (by linarith only [(normal_bounds rn).1]) rn.1
    side inner start order

theorem steeper_wall_shift (B R : OpenSquare)
    (bn : Normal B.c B.s) (rn : Normal R.c R.s)
    (side : 1<B.side) (inner : B.Inside (113/50) 2)
    (start : 2*(B.c+B.s)≤B.loU)
    (order : 0≤B.c*R.s-B.s*R.c)
    (axis : upper B R.c R.s≤R.loU) :
    3*R.c+2*R.s<R.loU :=
  lt_of_lt_of_le (steeper_reach B bn rn side inner start order) axis

private theorem half_angle_coefficient {c s : ℝ} (normal : Normal c s) :
    s≤(7/20)*(c+s)*(1+c) := by
  have bounds := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr bounds.1)
    (show 0≤c+s+17/10 by linarith only [bounds.1,normal.1])
  nlinarith only [product,bounds.2.2.2.1]

theorem shallower_margin {c s d t : ℝ}
    (bn : Normal c s) (rn : Normal d t) (order : 0≤s*d-c*t) :
    1≤c*d+s*t+(7/20)*(c+s)*(s*d-c*t) := by
  have cb := normal_bounds bn
  have rb := normal_bounds rn
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0≤d := by linarith only [rb.1]
  let K := c*d+s*t
  let G := s*d-c*t
  have kp : 0≤K := add_nonneg (mul_nonneg cp.le dp) (mul_nonneg bn.1 rn.1)
  have gp : 0≤G := order
  have positive : 0<1+K := by linarith only [kp]
  have unit : K^2+G^2=1 := by
    calc
      _=(c^2+s^2)*(d^2+t^2) := by dsimp [K,G]; ring
      _=1 := by rw [bn.2.2,rn.2.2]; norm_num
  have half : G*(1+c)≤s*(1+K) := by
    have first := mul_nonneg bn.1 (sub_nonneg.mpr rb.2.1)
    have second := mul_nonneg rn.1 (show 0≤1+c by linarith only [cp])
    have identity : s*(1+K)-G*(1+c)=s*(1-d)+t*(1+c) := by
      dsimp [K,G]
      linear_combination t*bn.2.2
    linarith only [identity,first,second]
  have weighted := mul_nonneg positive.le (sub_nonneg.mpr (half_angle_coefficient bn))
  have scaled : 0≤(1+c)*((7/20)*(c+s)*(1+K)-G) := by
    clear_value K G
    nlinarith only [weighted,half]
  have coefficient := nonneg_of_mul_nonneg_right scaled
    (show 0<1+c by linarith only [cp])
  have product := mul_nonneg gp coefficient
  have identity :
      (1+K)*(K+(7/20)*(c+s)*G-1)=G*((7/20)*(c+s)*(1+K)-G) := by
    linear_combination unit
  have scaledMargin : 0≤(1+K)*(K+(7/20)*(c+s)*G-1) := by
    clear_value K G
    linarith only [identity,product]
  have margin := nonneg_of_mul_nonneg_right scaledMargin positive
  change 1≤K+(7/20)*(c+s)*G
  linarith only [margin]

/-- When the wall is shallower, the true southeast marker supplies the
other face of B and the mixed upper support passes center plus one. -/
theorem shallower_reach (B : OpenSquare) {d t : ℝ}
    (bn : Normal B.c B.s) (rn : Normal d t)
    (side : 1<B.side) (marker : B.Inside (47/20) (33/20))
    (start : 2*(B.c+B.s)≤B.loU)
    (order : 0≤B.s*d-B.c*t) :
    2*(d+t)+1<upper B d t := by
  have cb := normal_bounds bn
  have rb := normal_bounds rn
  have cp : 0<B.c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [rb.1]
  let K := d*B.c+t*B.s
  let G := d*B.s-t*B.c
  have kp : 0<K := by
    have first := mul_pos dp cp
    have second := mul_nonneg rn.1 bn.1
    dsimp [K]; linarith only [first,second]
  have gp : 0≤G := by dsimp [G]; nlinarith only [order]
  have form : upper B d t=K*(B.loU+B.side)-G*B.loV := by
    rw [upper_in_bands]
    have first : d*B.c+t*B.s=K := rfl
    have second : -d*B.s+t*B.c=-G := by dsimp [G]; ring
    rw [first,second,abs_of_nonneg kp.le,abs_of_nonpos (neg_nonpos.mpr gp)]
    ring
  have faceWeight := mul_nonneg kp.le (sub_nonneg.mpr start)
  have pointWeight := mul_nonneg gp (sub_nonneg.mpr marker.2.2.1.le)
  have width := mul_pos (sub_pos.mpr side) kp
  have margin : 1≤K+(7/20)*(B.c+B.s)*G := by
    simpa only [K,G,mul_comm,mul_left_comm] using shallower_margin bn rn order
  have identity :
      K*(2*(B.c+B.s)+1)-G*((33/20)*B.c-(47/20)*B.s)=
      2*(d+t)+K+(7/20)*(B.c+B.s)*G := by
    dsimp [K,G]
    linear_combination 2*(d+t)*bn.2.2
  rw [form]
  clear_value K G
  nlinarith only [faceWeight,pointWeight,width,margin,identity]

#print axioms steeper_margin
#print axioms steeper_direction_reach
#print axioms steeper_reach
#print axioms steeper_wall_shift
#print axioms shallower_margin
#print axioms shallower_reach
end N12Compact.CentralRightMixedTransfer
