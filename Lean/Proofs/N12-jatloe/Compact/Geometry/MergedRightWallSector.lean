import Compact.Geometry.CentralWallPairSupport
import Compact.Geometry.MergedWallLongitudinalMargin

/-! A complete positive-angle sector for the merged right central pair.
Horizontal reflection gives the negative merged-left sector. All wall
separators refer to the full original squares. -/
namespace N12Compact.MergedRightWallSector
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open CentralWallEscape CentralWallPairAxes CentralWallPairSupport
set_option Elab.async false

theorem faces (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (sector : A.s ≤ (16/25)*A.c)
    (bottom : A.Inside (47/20) (33/20)) (top : A.Inside (47/20) (47/20))
    (center : ¬ A.Inside 2 2) (missing : ¬ A.Inside 3 (87/50)) :
    2*A.c+2*A.s ≤ A.loU ∧ (87/50)*A.c-3*A.s ≤ A.loV := by
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  have lower : 2*A.c+2*A.s ≤ A.loU := by
    apply le_of_not_gt
    intro low
    apply center
    exact ⟨by linarith only [low],by linarith only [top.2.1,hc,hs],
      by linarith only [bottom.2.2.1,hc,hs],
      by linarith only [top.2.2.2,hc,sector]⟩
  refine ⟨lower,?_⟩
  apply le_of_not_gt
  intro low
  apply missing
  exact ⟨by linarith only [top.1,hc,sector],
    by linarith only [lower,side,cu,hs],by linarith only [low],
    by linarith only [top.2.2.2,hc,hs]⟩

theorem crossing (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (sector : A.s ≤ (16/25)*A.c)
    (bottom : A.Inside (47/20) (33/20)) (top : A.Inside (47/20) (47/20))
    (lower : 2*A.c+2*A.s ≤ A.loU)
    (z : ℝ) (hz : 0 ≤ z) (angle : (1+A.c)*z=A.s)
    (unitAngle : A.s*z=1-A.c) : A.Inside 3 (2+z) := by
  have half : 1/2 ≤ A.c := by
    have square := mul_nonneg (sub_nonneg.mpr sector)
      (show 0 ≤ (16/25)*A.c+A.s by positivity)
    by_contra failure
    have bound := mul_pos (sub_pos.mpr (lt_of_not_ge failure))
      (show 0 < 1/2+A.c by positivity)
    nlinarith only [square,bound,A.unit_normal]
  have lowerAngle : A.s/3 ≤ A.c*z := by
    have product := mul_nonneg hz (show 0 ≤ 2*A.c-1 by linarith only [half])
    nlinarith only [angle,product]
  have upperAngle : A.c*z ≤ A.s := by nlinarith only [angle,hz]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [bottom.1,hc,hs,mul_nonneg hs hz]
  · nlinarith only [lower,unitAngle,side]
  · nlinarith only [bottom.2.2.1,lowerAngle,sector,hc]
  · nlinarith only [top.2.2.2,upperAngle,sector,hc]

private theorem axes (A R : OpenSquare) (side : 1 < A.side)
    (same : A.side=R.side) (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (sector : A.s ≤ (16/25)*A.c) (rc : 0 < R.c) (rs : 0 ≤ R.s)
    (bottom : A.Inside (47/20) (33/20))
    (lowerV : (87/50)*A.c-3*A.s ≤ A.loV)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (z : ℝ) (hz : 0 ≤ z) (zhi : z < 2/5)
    (crossing : A.Inside 3 (2+z))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side ≤ lower R A.c A.s ∨ upper A R.c R.s ≤ R.loU := by
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  have highVlo : A.loV < -A.s*3+A.c*(12/5) := by
    linarith only [bottom.2.2.1,sector,hc]
  have highVhi : -A.s*3+A.c*(12/5) < A.loV+A.side := by
    linarith only [lowerV,side,cu]
  have crossVlo : R.loV < -R.s*3+R.c*(2+z) := by
    nlinarith only [marker.2.2.1,mul_nonneg rc.le hz,rs]
  have crossVhi : -R.s*3+R.c*(2+z) < R.loV+R.side := by
    nlinarith only [high.2.2.2,mul_pos rc (sub_pos.mpr zhi)]
  have separatedAxes := CongruentSAT.faceSeparation_of_disjoint A R same apart
  change pairRadius A R ≤ |A.c*(centerX R-centerX A)+A.s*(centerY R-centerY A)| ∨
    pairRadius A R ≤ |-A.s*(centerX R-centerX A)+A.c*(centerY R-centerY A)| ∨
    pairRadius R A ≤ |R.c*(centerX R-centerX A)+R.s*(centerY R-centerY A)| ∨
    pairRadius R A ≤ |-R.s*(centerX R-centerX A)+R.c*(centerY R-centerY A)| at separatedAxes
  have split (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius R nx ny=radius)
      (sep : radius ≤ |nx*(centerX R-centerX A)+ny*(centerY R-centerY A)|) :=
    separated A R nx ny (by rwa [identity])
  rcases separatedAxes with au | av | ru | rv
  · have sep := split A.c A.s _ (parallel_radius A R) au
    rw [(ownU A).1,(ownU A).2] at sep
    rcases sep with forward | reverse
    · exact Or.inl forward
    · have bound := (strict_bounds R _ _ A.c A.s A.unit_normal marker).2
      exfalso
      linarith only [reverse,bound,bottom.1,hc,hs]
  · have sep := split (-A.s) A.c _ (transverse_radius A R) av
    rw [(ownV A).1,(ownV A).2] at sep
    have bounds := strict_bounds R _ _ (-A.s) A.c
      (by nlinarith only [A.unit_normal]) high
    rcases sep with sep | sep <;> exfalso <;>
      linarith only [sep,bounds.1,bounds.2,highVlo,highVhi]
  · have identity : supportRadius A R.c R.s+supportRadius R R.c R.s=pairRadius R A := by
      rw [add_comm]
      exact parallel_radius R A
    have sep := split R.c R.s _ identity ru
    rw [(ownU R).1,(ownU R).2] at sep
    rcases sep with forward | reverse
    · exact Or.inr forward
    · have bound := (strict_bounds A _ _ R.c R.s R.unit_normal bottom).1
      exfalso
      linarith only [reverse,bound,marker.2.1,rc,rs]
  · have identity : supportRadius A (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R A := by
      rw [add_comm]
      exact transverse_radius R A
    have sep := split (-R.s) R.c _ identity rv
    rw [(ownV R).1,(ownV R).2] at sep
    have bounds := strict_bounds A _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) crossing
    rcases sep with sep | sep <;> exfalso <;>
      linarith only [sep,bounds.1,bounds.2,crossVlo,crossVhi]

private theorem wall_axis (A R : OpenSquare) (side : 1 < A.side)
    (same : A.side=R.side) (box : InsideContainer R)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (rc : 0 < R.c) (rs : 0 ≤ R.s)
    (order : 0 ≤ A.c*R.s-A.s*R.c)
    (lowerU : 2*A.c+2*A.s ≤ A.loU)
    (top : A.Inside (47/20) (47/20)) (marker : R.Inside (1543/500) 2)
    (z : ℝ) (hz : 0 ≤ z) (zhi : z ≤ 1/5)
    (angle : (1+A.c)*z=A.s) (unitAngle : A.s*z=1-A.c)
    (wallScalar : R.c*R.s*z < 1-R.c-(43/500)*R.s^2)
    (axis : upper A R.c R.s ≤ R.loU) : False := by
  let k := A.c*R.c+A.s*R.s
  let d := A.c*R.s-A.s*R.c
  let H := 2*(R.c+R.s)+k+(7/20)*(A.c-A.s)*d
  have kp : 0 < k := add_pos_of_pos_of_nonneg (mul_pos hc rc) (mul_nonneg hs rs)
  have dn : 0 ≤ d := order
  have formula := (support_formulas A R kp.le dn).1
  change upper A R.c R.s=k*(A.loU+A.side)+d*(A.loV+A.side) at formula
  have along := mul_le_mul_of_nonneg_left lowerU kp.le
  have across := mul_le_mul_of_nonneg_left top.2.2.2.le dn
  have excess := mul_pos (sub_pos.mpr side) kp
  have compose : k*(2*A.c+2*A.s+1)+d*((47/20)*A.c-(47/20)*A.s)=H := by
    dsimp [k,d,H]
    linear_combination 2*(R.c+R.s)*A.unit_normal
  have support : H < R.loU := by
    nlinarith only [formula,along,across,excess,compose,axis]
  have margins := MergedWallLongitudinalMargin.margins A.c A.s R.c R.s z
    rc rs R.unit_normal hz zhi angle unitAngle wallScalar
  have rewriteMargin : A.c*R.c+A.s*R.s-(543/500)*R.c+
      (7/20)*(A.c-A.s)*(A.c*R.s-A.s*R.c) = H-(1543/500)*R.c-2*R.s := by
    dsimp [H,k,d]
    ring
  rw [rewriteMargin] at margins
  rcases margins with margin | margin
  · linarith only [support,marker.1,margin]
  · have scaled := mul_lt_mul_of_pos_left support rc
    have wall := right_wall R box
    have markerBound := mul_le_mul_of_nonneg_left marker.2.2.1.le rs
    have wallBound : R.c*R.loU+R.side*R.c+(1543/500)*R.s^2-2*R.c*R.s ≤ 4 := by
      nlinarith only [wall,markerBound]
    have sideR : 1 < R.side := by simpa only [same] using side
    have extra := mul_pos (sub_pos.mpr sideR) rc
    have identity : R.c*(H-(1543/500)*R.c-2*R.s)+R.c-457/500 =
        R.c*H+R.c+(1543/500)*R.s^2-2*R.c*R.s-4 := by
      linear_combination -(1543/500)*R.unit_normal
    nlinarith only [scaled,wallBound,extra,identity,margin]

/-- Complete orientation sector for the merged right pair and its actual
right wall. The wall's orientation is unrestricted. -/
theorem point (A R : OpenSquare) (side : 1 < A.side)
    (same : A.side=R.side) (box : InsideContainer R)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (sector : A.s ≤ (16/25)*A.c)
    (bottom : A.Inside (47/20) (33/20)) (top : A.Inside (47/20) (47/20))
    (missing : ¬ A.Inside 3 (87/50))
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : A.Inside 2 2 := by
  by_contra center
  have af := faces A side hc hs sector bottom top center missing
  let z := A.s/(1+A.c)
  have denominator : 0 < 1+A.c := by linarith only [hc]
  have hz : 0 ≤ z := div_nonneg hs denominator.le
  have angle : (1+A.c)*z=A.s := by dsimp [z]; field_simp [ne_of_gt denominator]
  have unitAngle : A.s*z=1-A.c := by
    dsimp [z]
    field_simp [ne_of_gt denominator]
    nlinarith only [A.unit_normal]
  have zhi : z < 2/5 := by
    have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
    by_contra failure
    have large : 2/5 ≤ z := le_of_not_gt failure
    have product := mul_nonneg hc.le (sub_nonneg.mpr large)
    nlinarith only [angle,sector,cu,large,product]
  have ac := crossing A side hc hs sector bottom top af.1 z hz angle unitAngle
  obtain ⟨W,wc,ws,shape,inside,_⟩ := ClosedFrames.positive_frame R
  have sameW : A.side=W.side := same.trans shape.symm
  have wb : InsideContainer W := fun x y h => box x y ((inside x y).mp h)
  have wm := (inside _ _).mpr marker
  have wh := (inside _ _).mpr high
  have disjoint : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(inside x y).mp h.2⟩
  have face := lower_face W wc ws z hz zhi wm wh
    (fun h => disjoint _ _ ⟨ac,h⟩)
  have wall := wall_inequalities W (by simpa only [←sameW] using side) wc ws wb z wm face
  have half := half_angle_lt W.c W.s z wc ws W.unit_normal hz wall.1 wall.2
  have narrow := slope_of_half_angle A.c A.s z hc hz angle unitAngle half
  have order := wall_angle_order A.c A.s W.c W.s z
    (cosine_bound A.c A.s hc hs A.unit_normal narrow.le) hs wc ws
    A.unit_normal W.unit_normal hz angle wall.2
  have cross : 0 ≤ A.c*W.s-A.s*W.c := sub_nonneg.mpr order.le
  rcases axes A W side sameW hc hs sector wc ws bottom af.2 wm wh z hz zhi ac disjoint with axis | axis
  · exact central_axis_impossible A W side sameW wb hc hs wc ws narrow.le cross af.1 wm wh axis
  · exact wall_axis A W side sameW wb hc hs wc ws cross af.1 top wm z hz half.le
      angle unitAngle wall.2 axis

#print axioms point
end N12Compact.MergedRightWallSector
