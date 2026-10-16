import Compact.Geometry.C977CornerSectorBounds

/-! The genuine marker coefficient suffices for the common positive-L
transverse axis once the omitted full O width is retained. This source
uses only continuous unit-normal inequalities, not the unavailable
(1,72/25) point. It is uncompiled. -/
namespace N12Compact.CornerWallMarkerSharedBounds

open C977CornerCubic C977CornerSectorBounds

noncomputable def first (c d t : ℝ) : ℝ :=
  c+t-3+(1-(457/500)*t)/d

noncomputable def second (c s d : ℝ) : ℝ :=
  s+d-2+(1-(457/500)*s)/c

theorem first_coefficient {c s d t : ℝ}
    (on : Normal c s) (wn : Normal d t) (order : s≤t)
    (small : t≤3/5) (wide : 4/5≤d) :
    -(c+d)/2≤first c d t+s^2 := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have dc := cosine_order wn on order
  have dp : 0<d := by linarith only [wide]
  have cp : 1/2≤c := by linarith only [wide,dc]
  have cterm := mul_nonneg (sub_nonneg.mpr ob.2.1)
    (show 0≤c-1/2 by linarith only [cp])
  have range := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1-t by linarith only [small])
  have linear : d+2*t≤2 := by
    by_contra no
    have positive := mul_pos (show 0<d-(2-2*t) by linarith only [no])
      (show 0<d+(2-2*t) by linarith only [wide,small])
    nlinarith only [positive,range,wn.2.2]
  have dterm := mul_nonneg (sub_nonneg.mpr wb.2.1)
    (show 0≤2-d-2*t by linarith only [linear])
  have cweighted := mul_nonneg dp.le cterm
  have identity :
      2*d*(c+t-3+(1-t)/d+s^2+(c+d)/2) =
        2*d*((1-c)*(c-1/2))+(1-d)*(2-d-2*t) := by
    field_simp [ne_of_gt dp]
    linear_combination 2*d*on.2.2
  have scaled : 0≤2*d*(c+t-3+(1-t)/d+s^2+(c+d)/2) := by
    nlinarith only [identity,cweighted,dterm]
  have base := nonneg_of_mul_nonneg_right scaled
    (show 0<2*d by linarith only [dp])
  have improvement : 0≤((43/500)*t)/d :=
    div_nonneg (mul_nonneg (by norm_num) wn.1) dp.le
  have expansion : first c d t = c+t-3+(1-t)/d+((43/500)*t)/d := by
    unfold first
    field_simp [ne_of_gt dp]
    ; ring
  linarith only [base,improvement,expansion]

theorem second_coefficient {c s d t : ℝ}
    (on : Normal c s) (wn : Normal d t) (order : s≤t)
    (small : t≤3/5) (wide : 4/5≤d) :
    -(s+t)/2≤second c s d-c*s := by
  have ob := normal_bounds on
  have dc := cosine_order wn on order
  have cp : 0<c := by linarith only [wide,dc]
  have cw : 4/5≤c := le_trans wide dc
  let E := second c s d-c*s+(s+t)/2
  by_cases low : t≤7/25
  · have factor : 0≤c+d-2*(s+t) := by
      linarith only [wide,cw,order,low]
    have product := mul_nonneg (sub_nonneg.mpr order) factor
    have identity :
        (c+d)*(d+t/2-(c+s/2)) =
          ((t-s)/2)*(c+d-2*(s+t)) := by
      linear_combination wn.2.2-on.2.2
    have scaled : 0≤(c+d)*(d+t/2-(c+s/2)) := by
      nlinarith only [product,identity]
    have moving := nonneg_of_mul_nonneg_right scaled
      (show 0<c+d by linarith only [cw,wide])
    have square : 0≤c+1/c-2 := by
      have identity : c*(c+1/c-2)=(1-c)^2 := by
        field_simp [ne_of_gt cp]
        ; ring
      have scaled : 0≤c*(c+1/c-2) := by
        nlinarith only [identity,sq_nonneg (1-c)]
      exact nonneg_of_mul_nonneg_right scaled cp
    have endpoint := mul_nonneg
      (show 0≤1-s by linarith only [on.1,order,small]) square
    have gain : 0≤(43/500)*s/c :=
      div_nonneg (mul_nonneg (by norm_num) on.1) cp.le
    have form : E =
        (1-s)*(c+1/c-2)+(43/500)*s/c+(d+t/2-(c+s/2)) := by
      dsimp [E,second]
      field_simp [ne_of_gt cp]
      ; ring
    dsimp [E] at form
    linarith only [form,endpoint,gain,moving]
  · have high : 7/25≤t := le_of_lt (lt_of_not_ge low)
    have product := mul_nonneg (sub_nonneg.mpr high)
      (sub_nonneg.mpr small)
    have moving : 11/10≤d+t/2 := by
      by_contra no
      have positive := mul_pos
        (show 0<11/10-t/2-d by linarith only [no])
        (show 0<11/10-t/2+d by linarith only [wide,small])
      nlinarith only [positive,product,wn.2.2]
    have coefficient : c^2-(3/2)*c+457/500≤207/500 := by
      have factor := mul_nonneg (sub_nonneg.mpr ob.2.1)
        (show 0≤c-1/2 by linarith only [cw])
      nlinarith only [factor]
    have norm : (9/10)*c+(207/500)*s<1 := by
      have square := sq_nonneg ((207/500)*c-(9/10)*s)
      have normal := on.2.2
      nlinarith only [square,normal,
        sq_nonneg ((9/10)*c+(207/500)*s-1)]
    have cproduct := mul_nonneg cp.le (sub_nonneg.mpr moving)
    have sproduct := mul_nonneg on.1 (sub_nonneg.mpr coefficient)
    have identity :
        c*E = c*(d+t/2-11/10)+
          (1-(9/10)*c-(207/500)*s)+
          s*((207/500)-(c^2-(3/2)*c+457/500)) := by
      dsimp [E,second]
      field_simp [ne_of_gt cp]
      ; ring
    have scaled : 0<c*E := by
      rw [identity]
      nlinarith only [cproduct,sproduct,norm]
    have positive := pos_of_mul_pos_right scaled cp.le
    dsimp [E] at positive
    linarith only [positive]

/-- `extra` records the actual support-corner width. Its only required
properties are nonnegativity and domination of `sl-cr`. -/
theorem margin {c s d t l r extra : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d)
    (extra0 : 0≤extra) (extraD : s*l-c*r≤extra) :
    0≤1+l*first c d t+r*second c s d+extra := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have lp : 0≤l := by linarith only [lb.1]
  have firstBound := first_coefficient on wn order small wide
  have secondBound := second_coefficient on wn order small wide
  have firstWeighted := mul_nonneg lp (sub_nonneg.mpr firstBound)
  have secondWeighted := mul_nonneg ln.1 (sub_nonneg.mpr secondBound)
  have extraWeighted := mul_nonneg on.1 (sub_nonneg.mpr extraD)
  have extraRest := mul_nonneg
    (show 0≤1-s by linarith only [on.1,order,small]) extra0
  have dotO := dot_le_one on ln
  have dotW := dot_le_one wn ln
  nlinarith only [firstWeighted,secondWeighted,extraWeighted,extraRest,dotO,dotW]

end N12Compact.CornerWallMarkerSharedBounds
