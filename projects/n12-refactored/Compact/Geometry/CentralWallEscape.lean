import Compact.Geometry.CentralEscapeSegment
import S12.Container
import Mathlib.Tactic.FieldSimp

/-! A center-escaping elbow crosses the neighboring wall line at its
half-angle point.  The actual marker and container wall force that
half-angle below 1/5.  All statements concern original open squares;
no bound on the side from above is used. -/
namespace N12Compact.CentralWallEscape
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem right_wall (R : OpenSquare) (box : InsideContainer R) :
    R.c*(R.loU+R.side)-R.s*R.loV ≤ 4 := by
  have bound : 0 ≤ 4-R.c*(R.loU+R.side)+R.s*R.loV := by
    apply affine_endpoint_nonnegative R.side (R.c+R.s) _ R.side_pos
    intro e he0 he1
    let u := R.loU+R.side-e
    let v := R.loV+e
    have point : R.Inside (R.c*u-R.s*v) (R.s*u+R.c*v) := by
      apply (inside_iff_rotated_box R _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    have x := (box _ _ point).2.1
    dsimp [u,v] at x
    nlinarith only [x]
  linarith only [bound]

/-- This point is strict even when the center is only on a lower face.
The two algebraic half-angle identities avoid any division in the proof. -/
theorem crossing_point (A : OpenSquare) (ha : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (sector : A.s ≤ (16/25)*A.c)
    (z : ℝ) (hz : 0 ≤ z) (angle : (1+A.c)*z=A.s)
    (unitAngle : A.s*z=1-A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingTop : ¬ A.Inside (5/2) 3)
    (missingCenter : ¬ A.Inside 2 2) : A.Inside 3 (2+z) := by
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  have sum : 1 ≤ A.c+A.s := by
    nlinarith only [A.unit_normal,mul_nonneg hc.le hs,hc,hs]
  have zhi : z < 2/5 := by
    by_contra failure
    have large : 2/5 ≤ z := le_of_not_gt failure
    have product := mul_nonneg hc.le (sub_nonneg.mpr large)
    nlinarith only [angle,sector,cu,large,product]
  have centerUhi : A.c*2+A.s*2 < A.loU+A.side := by
    linarith only [m.2.1,hc,hs]
  have centerVlo : A.loV < -A.s*2+A.c*2 := by
    linarith only [q.2.2.1,hs]
  have centerVhi : -A.s*2+A.c*2 < A.loV+A.side := by
    linarith only [p.2.2.2,hc]
  have centerU : A.c*2+A.s*2 ≤ A.loU :=
    le_of_not_gt (fun h => missingCenter ⟨h,centerUhi,centerVlo,centerVhi⟩)
  have topUlo : A.loU < A.c*(5/2)+A.s*3 := by
    linarith only [m.1,hc,hs]
  have topUhi : A.c*(5/2)+A.s*3 < A.loU+A.side := by
    have projected : (A.c/2+A.s)^2 ≤ 1 := by
      nlinarith only [A.unit_normal,
        mul_nonneg hc.le (sub_nonneg.mpr sector),sq_nonneg A.c]
    have short : A.c/2+A.s ≤ 1 := by
      nlinarith only [projected,sq_nonneg (A.c/2+A.s-1)]
    linarith only [centerU,short,ha]
  have topVlo : A.loV < -A.s*(5/2)+A.c*3 := by
    linarith only [q.2.2.1,hc,sector]
  have topV : A.loV+A.side ≤ -A.s*(5/2)+A.c*3 :=
    le_of_not_gt (fun h => missingTop ⟨topUlo,topUhi,topVlo,h⟩)
  have lowerMargin : 0 ≤ z*(A.c+A.s)-A.s/2 := by
    have product := mul_nonneg hz (show 0 ≤ A.c+2*A.s-1 by linarith only [sum,hs])
    nlinarith only [product,angle]
  refine ⟨?_,?_,?_,?_⟩
  · have positive := mul_nonneg hs hz
    linarith only [q.1,hc,positive]
  · nlinarith only [centerU,unitAngle,ha]
  · nlinarith only [topV,unitAngle,lowerMargin,ha]
  · have cz : A.c*z ≤ A.s := by nlinarith only [angle,hz]
    nlinarith only [p.2.2.2,cz,hs,hc]

/-- Two original strict points select the lower longitudinal escape face
of a positive wall frame. -/
theorem lower_face (R : OpenSquare) (hc : 0 < R.c) (hs : 0 ≤ R.s)
    (z : ℝ) (hz : 0 ≤ z) (zhi : z < 2/5)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (missing : ¬ R.Inside 3 (2+z)) :
    R.c*3+R.s*(2+z) ≤ R.loU := by
  have uhi : R.c*3+R.s*(2+z) < R.loU+R.side := by
    have h := mul_nonneg hs (sub_nonneg.mpr zhi.le)
    nlinarith only [high.2.1,h]
  have vlo : R.loV < -R.s*3+R.c*(2+z) := by
    nlinarith only [marker.2.2.1,mul_nonneg hc.le hz,hs]
  have vhi : -R.s*3+R.c*(2+z) < R.loV+R.side := by
    nlinarith only [high.2.2.2,mul_pos hc (sub_pos.mpr zhi)]
  exact le_of_not_gt (fun h => missing ⟨h,uhi,vlo,vhi⟩)

/-- Exact scalar consequence of the actual marker and right container
wall. It is valid throughout the positive quadrant, including frames
whose angle exceeds 45 degrees. -/
theorem wall_inequalities (R : OpenSquare) (ha : 1 < R.side)
    (hc : 0 < R.c) (hs : 0 ≤ R.s) (box : InsideContainer R)
    (z : ℝ) (marker : R.Inside (1543/500) 2)
    (face : R.c*3+R.s*(2+z) ≤ R.loU) :
    R.s*z < (43/500)*R.c ∧
      R.c*R.s*z < 1-R.c-(43/500)*R.s^2 := by
  have wall := right_wall R box
  have lower := mul_le_mul_of_nonneg_left face hc.le
  have transverse := mul_le_mul_of_nonneg_left marker.2.2.1.le hs
  have strictSide := mul_pos hc (sub_pos.mpr ha)
  constructor
  · linarith only [face,marker.1]
  · nlinarith only [wall,lower,transverse,strictSide,R.unit_normal]

/-- The rational bound follows from two quadratic wall inequalities;
there is no sampled angle or side upper bound. -/
theorem half_angle_lt (r t z : ℝ) (hr : 0 < r) (ht : 0 ≤ t)
    (unit : r^2+t^2=1) (hz : 0 ≤ z)
    (marker : t*z < (43/500)*r)
    (wall : r*t*z < 1-r-(43/500)*t^2) : z < 1/5 := by
  by_contra notSmall
  have large : 1/5 ≤ z := le_of_not_gt notSmall
  have tsmall : t < (43/100)*r := by
    nlinarith only [marker,mul_nonneg ht (sub_nonneg.mpr large)]
  have rlarge : 9/10 < r := by
    have square := mul_pos (sub_pos.mpr tsmall)
      (show 0 < (43/100)*r+t by linarith only [hr,ht])
    by_contra failure
    have upper : r ≤ 9/10 := le_of_not_gt failure
    have bound := mul_nonneg (show 0 ≤ r+9/10 by linarith only [hr])
      (sub_nonneg.mpr upper)
    nlinarith only [square,unit,bound]
  have tone : 0 < t := by
    by_contra notPositive
    have zero : t=0 := le_antisymm (le_of_not_gt notPositive) ht
    rw [zero] at unit wall
    nlinarith only [unit,wall,hr]
  have rone : r ≤ 1 := by nlinarith only [unit,sq_nonneg t,hr]
  have radial : 1-r ≤ (10/19)*t^2 := by
    nlinarith only [unit,mul_nonneg (sub_nonneg.mpr rone)
      (show 0 ≤ r-9/10 by linarith only [rlarge])]
  have wall' : r*t*z < (4183/9500)*t^2 := by
    linarith only [wall,radial]
  have bound : r*z < (4183/9500)*t := by
    apply (mul_lt_mul_left tone).mp
    nlinarith only [wall']
  have multiply := mul_le_mul_of_nonneg_right bound.le hz
  have marker' := mul_lt_mul_of_pos_left marker (by norm_num : (0:ℝ)<4183/9500)
  have zsquare : z^2 < (1/5)^2 := by
    have product : r*z^2 < r*(179869/4750000) := by
      nlinarith only [multiply,marker']
    have bound := (mul_lt_mul_left hr).mp product
    norm_num at bound ⊢
    linarith only [bound]
  nlinarith only [zsquare,large]

theorem slope_of_half_angle (c s z : ℝ) (hc : 0 < c) (hz : 0 ≤ z)
    (angle : (1+c)*z=s) (unitAngle : s*z=1-c)
    (small : z < 1/5) : 12*s < 5*c := by
  have square : (1+c)*z^2=1-c := by
    have times := congrArg (fun x : ℝ => x*z) angle
    dsimp at times
    nlinarith only [times,unitAngle]
  have product := mul_pos (sub_pos.mpr small)
    (show 0 < 25+5*z by linarith only [hz])
  have weighted := mul_pos (show 0 < 1+c by linarith only [hc]) product
  nlinarith only [weighted,angle,square]

/-- Original geometric adapter for the new angle reduction. Reindexing
the wall square preserves all of its geometry, including its enclosure. -/
theorem shallow_slope_lt (A R : OpenSquare)
    (ha : 1 < A.side) (hr : 1 < R.side) (box : InsideContainer R)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (sector : A.s ≤ (16/25)*A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingTop : ¬ A.Inside (5/2) 3)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (missingCenter : ¬ A.Inside 2 2) : 12*A.s < 5*A.c := by
  let z := A.s/(1+A.c)
  have denominator : 0 < 1+A.c := by linarith only [hc]
  have hz : 0 ≤ z := div_nonneg hs denominator.le
  have angle : (1+A.c)*z=A.s := by
    dsimp [z]
    field_simp [ne_of_gt denominator]
  have unitAngle : A.s*z=1-A.c := by
    dsimp [z]
    field_simp [ne_of_gt denominator]
    nlinarith only [A.unit_normal]
  have zhi : z < 2/5 := by
    apply (div_lt_iff₀ denominator).mpr
    have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
    linarith only [sector,cu]
  have crossing := crossing_point A ha hc hs sector z hz angle unitAngle p q m
    missingTop missingCenter
  obtain ⟨W,wc,ws,side,inside,_⟩ := ClosedFrames.positive_frame R
  have wb : InsideContainer W := fun x y h => box x y ((inside x y).mp h)
  have wm := (inside _ _).mpr marker
  have wh := (inside _ _).mpr high
  have missing : ¬ W.Inside 3 (2+z) :=
    fun h => apart _ _ ⟨crossing,(inside _ _).mp h⟩
  have face := lower_face W wc ws z hz zhi wm wh missing
  have inequalities := wall_inequalities W (by simpa only [side] using hr)
    wc ws wb z wm face
  exact slope_of_half_angle A.c A.s z hc hz angle unitAngle
    (half_angle_lt W.c W.s z wc ws W.unit_normal hz inequalities.1 inequalities.2)

#print axioms crossing_point
#print axioms half_angle_lt
#print axioms shallow_slope_lt
end N12Compact.CentralWallEscape
