import Compact.Geometry.CornerWallMarkerSharedBounds

/-! The other positive-left transverse selector with the genuine upper
marker. A single quartic disk estimate covers the larger left angles;
the exact shared support width covers the smaller ones. -/
namespace N12Compact.CornerWallMarkerOtherMixedBounds
open C977CornerCubic C977CornerSectorBounds

private theorem coefficient {c s : ℝ} (normal : Normal c s)
    (wide : 4/5≤c) (small : s≤3/5) :
    -(1/10)*s^2≤c+s-2+(1-(457/500)*s)/c := by
  have b := normal_bounds normal
  have cp : 0<c := by linarith only [wide]
  let E := c+s-2+(1-(457/500)*s)/c
  have identity : c*E=(1-c)^2+s*(c-457/500) := by
    dsimp [E]
    field_simp [cp.ne']; ring
  change -(1/10)*s^2≤E
  clear_value E
  by_cases large : 457/500≤c
  · have term := mul_nonneg normal.1 (sub_nonneg.mpr large)
    have scaled : 0≤c*E := by nlinarith only [identity,term,sq_nonneg (1-c)]
    have ep := nonneg_of_mul_nonneg_right scaled cp
    change -(1/10)*s^2≤E
    nlinarith only [ep,sq_nonneg s]
  · have replacement := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤457/500-c by linarith only [large])
    have factor : 0≤-(1/10)*c^2+(23/25)*c-141/250 := by
      nlinarith only [wide,normal.2.2,sq_nonneg s]
    have product := mul_nonneg (sub_nonneg.mpr wide) factor
    have polynomial :
        (1-c)^2+(3/5)*(c-457/500)+(1/10)*c*(1-c^2)=
          1/2500+(c-4/5)*(-(1/10)*c^2+(23/25)*c-141/250) := by ring
    have unit := congrArg (fun z : ℝ => c*z) normal.2.2
    have scaled : 0≤c*(E+(1/10)*s^2) := by
      nlinarith only [identity,replacement,product,polynomial,unit]
    have ep := nonneg_of_mul_nonneg_right scaled cp
    change -(1/10)*s^2≤E
    linarith only [ep]

private theorem quartic_disk {l r d t : ℝ} (ln : Normal l r) (wn : Normal d t) :
    0≤l+d*(1+l^2-3*l)+t*(l^2-l) := by
  have lb := normal_bounds ln
  have lp : 0<l := by linarith only [lb.1]
  let A := 1+l^2-3*l
  let B := l^2-l
  have smallDefect : (1-l)^2≤9/100 := by
    have product := mul_nonneg (show 0≤l-7/10 by linarith only [lb.1])
      (show 0≤13/10-l by linarith only [lb.2.1])
    nlinarith only [product]
  have remainder := mul_nonneg (sq_nonneg (1-l))
    (show 0≤1-2*(1-l)^2 by linarith only [smallDefect])
  have quartic : l^2-A^2-B^2=(1-l)^2*(1-2*(1-l)^2) := by
    dsimp [A,B]; ring
  have norm : A^2+B^2≤l^2 := by nlinarith only [quartic,remainder]
  have rotation : (d*A+t*B)^2+(d*B-t*A)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*wn.2.2
  change 0≤l+d*A+t*B
  clear_value A B
  have squared : (d*A+t*B)^2≤l^2 := by
    nlinarith only [norm,rotation,sq_nonneg (d*B-t*A)]
  have disk : 0≤l+d*A+t*B := by
    by_contra no
    have bad := mul_pos
      (show 0 < -(l+d*A+t*B) by linarith only [no])
      (show 0<l-(d*A+t*B) by linarith only [no,lp])
    nlinarith only [bad,squared]
  exact disk

theorem margin {c s d t l r extra : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d)
    (extra0 : 0≤extra) (extraD : s*l-c*r≤extra) :
    0≤1+d*c+t*l+d*r+d/l+(d*r/l)*(s-2+(1-(457/500)*s)/c)-
      (457/500)*t-3*d+(d/l)*extra := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have cp : 0<c := by linarith only [ob.1]
  have dp : 0<d := by linarith only [wide]
  have lp : 0<l := by linarith only [lb.1]
  have dc := cosine_order wn on order
  let b := s-2+(1-(457/500)*s)/c
  let H := 1+d*c+t*l+d*r+d/l+(d*r/l)*b-(457/500)*t-3*d+(d/l)*extra
  change 0≤H
  by_cases low : r≤t
  · have dl := cosine_order wn ln low
    have scalar := CornerWallMarkerSharedBounds.margin on wn ln order small wide extra0 extraD
    have first := mul_nonneg (div_nonneg dp.le lp.le) scalar
    have second := mul_nonneg
      (add_nonneg (mul_nonneg wn.1 lp.le) (mul_nonneg dp.le ln.1))
      (div_nonneg (sub_nonneg.mpr dl) lp.le)
    have identity : H=
        (d/l)*(1+l*CornerWallMarkerSharedBounds.first c d t+
          r*CornerWallMarkerSharedBounds.second c s d+extra)+
        (t*l+d*r)*(l-d)/l := by
      dsimp [H,b,CornerWallMarkerSharedBounds.first,CornerWallMarkerSharedBounds.second]
      field_simp [cp.ne',dp.ne',lp.ne']; ring
    clear_value H b
    rw [identity]
    exact add_nonneg first (by simpa only [mul_div_assoc] using second)
  · have ld := cosine_order ln wn (le_of_lt (lt_of_not_ge low))
    have lc := le_trans ld dc
    have disk := quartic_disk ln wn
    have extraWeight := mul_nonneg dp.le extra0
    have identity :
        l*H=d+l*(1-(457/500)*t+d*(c-3))+d*r*(l+b)+t*l^2+d*extra := by
      dsimp [H]
      field_simp [lp.ne']; ring
    have scaled : 0≤l*H := by
      by_cases sign : l+b≤0
      · have replace := mul_nonneg (mul_nonneg dp.le (sub_nonneg.mpr ln.2.1))
          (neg_nonneg.mpr sign)
        have lower := coefficient on (le_trans wide dc) (le_trans order small)
        have lowerWeight := mul_nonneg (mul_nonneg dp.le lp.le)
          (show 0≤c+b+(1/10)*s^2 by dsimp [b]; linarith only [lower])
        have square := mul_nonneg on.1
          (show 0≤3/5-s by linarith only [order,small])
        have cosine := mul_nonneg (sub_nonneg.mpr wb.2.1) (sq_nonneg s)
        have gain : 0≤(43/500)*t-(1/10)*d*s^2 := by
          nlinarith only [square,cosine,order,wn.1]
        have gainWeight := mul_nonneg lp.le gain
        clear_value H b
        nlinarith only [identity,replace,lowerWeight,gainWeight,disk,extraWeight]
      · have positive := mul_nonneg (mul_nonneg dp.le ln.1)
          (le_of_lt (lt_of_not_ge sign))
        have difference := mul_nonneg (mul_nonneg dp.le lp.le) (sub_nonneg.mpr lc)
        have gain := mul_nonneg wn.1 lp.le
        clear_value H b
        nlinarith only [identity,positive,difference,gain,disk,extraWeight]
    exact nonneg_of_mul_nonneg_right scaled lp

#print axioms margin
end N12Compact.CornerWallMarkerOtherMixedBounds
