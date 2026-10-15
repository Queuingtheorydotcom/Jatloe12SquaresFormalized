import Compact.Geometry.C977CornerSectorBounds

/-! Two continuous backward-negative-left margins. The actual bottom
corner forces c≤.914 and r≥.6 before either margin is used. This removes
the earlier small-left-angle case and its artificial top-seed gain. -/
namespace N12Compact.CornerWallMarkerNegativeBounds
open C977CornerCubic C977CornerSectorBounds

noncomputable def X (c s : ℝ) : ℝ := s-1+(1-(457/500)*s)/c

theorem x_lower {c s : ℝ} (normal : Normal c s)
    (cSmall : c≤457/500) (sSmall : s≤3/5) : 9/100≤X c s := by
  have b := normal_bounds normal
  have cp : 0<c := by linarith only [b.1]
  have replacement := mul_nonneg (sub_nonneg.mpr sSmall) (sub_nonneg.mpr cSmall)
  have identity : c*(X c s-9/100)=1-(109/100)*c+s*(c-457/500) := by
    dsimp [X]
    field_simp [cp.ne'] <;> ring
  have scaled : 0≤c*(X c s-9/100) := by
    nlinarith only [identity,replacement,cSmall]
  have gap := nonneg_of_mul_nonneg_right scaled cp
  linarith only [gap]

private theorem unit_sum {l r : ℝ} (normal : Normal l r) :
    -(43/500)≤l+r-1-l*r := by
  have b := normal_bounds normal
  have hi : l+r≤99/70 := by
    nlinarith only [normal.2.2,sq_nonneg (l-r),sq_nonneg (l+r-99/70)]
  have product := mul_nonneg (sub_nonneg.mpr hi)
    (show 0≤l+r+99/70-2 by linarith only [b.2.2.2.2.1])
  nlinarith only [product,normal.2.2]

theorem left_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d)
    (cSmall : c≤457/500) (leftOrder : t≤r) :
    0≤l+r-1+X c s*l^2+(c+d-2-d^2)*l*r+
      ((43/500)+t*(1-d))*r^2 := by
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have dc := cosine_order wn on order
  have lp : 0≤l := by linarith only [lb.1]
  have base := unit_sum ln
  have xl := x_lower on cSmall (le_trans order small)
  have xWeight := mul_nonneg (sq_nonneg l) (sub_nonneg.mpr xl)
  have angle := mul_nonneg wn.1 (sub_nonneg.mpr leftOrder)
  have defect := mul_nonneg (sub_nonneg.mpr wb.2.1)
    (show 0≤1+d-l by linarith only [wide,lb.2.1])
  have direction : 0≤t*r-l*(1-d) := by
    nlinarith only [angle,defect,wn.2.2]
  have correction := mul_nonneg
    (mul_nonneg ln.1 (sub_nonneg.mpr wb.2.1)) direction
  have shift := mul_nonneg (mul_nonneg lp ln.1) (sub_nonneg.mpr dc)
  have identity :
      l+r-1+X c s*l^2+(c+d-2-d^2)*l*r+((43/500)+t*(1-d))*r^2=
        (l+r-1-l*r)+X c s*l^2+(43/500)*r^2+
          l*r*(c-d)+r*(1-d)*(t*r-l*(1-d)) := by ring
  nlinarith only [identity,base,xWeight,correction,shift,ln.2.2,sq_nonneg l]

theorem wall_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d)
    (cSmall : c≤457/500) (rLarge : 3/5≤r) :
    0≤1-l+l*X c s+r*(c-3+(1-(457/500)*t)/d+l+r*t/d) := by
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have dc := cosine_order wn on order
  have dp : 0<d := by linarith only [wide]
  have lp : 0≤l := by linarith only [lb.1]
  have rSmall : r≤5/7 := by linarith only [ln.2.1,lb.2.2.2.2.2]
  have lSmall : l≤4/5 := by
    have large := mul_nonneg (sub_nonneg.mpr rLarge)
      (show 0≤r+3/5 by linarith only [ln.1])
    nlinarith only [large,ln.2.2,sq_nonneg (l-4/5)]
  have xl := x_lower on cSmall (le_trans order small)
  have xWeight := mul_nonneg lp (sub_nonneg.mpr xl)
  have shift := mul_nonneg ln.1 (sub_nonneg.mpr dc)
  have slope : t≤(3/4)*d := by linarith only [small,wide]
  have replacement := mul_nonneg
    (mul_nonneg ln.1 (show 0≤457/500-r by linarith only [rSmall]))
    (sub_nonneg.mpr slope)
  have lReplacement := mul_nonneg (sub_nonneg.mpr lSmall)
    (show 0≤91/100-r by linarith only [rSmall])
  have factor := mul_nonneg (sub_nonneg.mpr rLarge)
    (show 0≤(3/4)*r-871/2000 by linarith only [rLarge])
  have polynomial :
      34/125-r/5-(3/4)*r*(457/500-r)=
        (r-3/5)*((3/4)*r-871/2000)+107/10000 := by ring
  have base : 0≤(1-l)*(1-r)+l*X c s-(3/4)*r*(457/500-r) := by
    nlinarith only [factor,polynomial,lReplacement,xWeight]
  have baseWeight := mul_nonneg dp.le base
  have shiftWeight := mul_nonneg dp.le shift
  have square := mul_nonneg ln.1 (sq_nonneg (1-d))
  have identity :
      d*(1-l+l*X c s+r*(c-3+(1-(457/500)*t)/d+l+r*t/d))=
        d*((1-l)*(1-r)+l*X c s-(3/4)*r*(457/500-r))+
        d*r*(c-d)+r*(1-d)^2+r*(457/500-r)*((3/4)*d-t) := by
    field_simp [dp.ne'] <;> ring
  have scaled : 0≤d*(1-l+l*X c s+r*(c-3+(1-(457/500)*t)/d+l+r*t/d)) := by
    nlinarith only [identity,baseWeight,shiftWeight,square,replacement]
  exact nonneg_of_mul_nonneg_right scaled dp

#print axioms left_margin
#print axioms wall_margin
end N12Compact.CornerWallMarkerNegativeBounds
