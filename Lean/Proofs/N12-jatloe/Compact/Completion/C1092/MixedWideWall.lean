import Compact.Geometry.ABTransverse
import Compact.Geometry.C977ChainBridge
import Compact.Geometry.ThreeSquareSupport
import Compact.Geometry.CentralWallEscape
import S12.SquareSupportBase
import S12.ShortCluster

/-! The actual wall spanning both sides of its center has a forced
negative canonical frame. The real wall and its original center cut are
kept throughout; this is the first physical mixed-wall crossing lemma. -/
namespace N12Compact.C1092MixedWideWall
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

private theorem positive_impossible (W : OpenSquare) (side : 1 < W.side)
    (cap : W.side ≤ 1001/1000) (cosine : 0 < W.c)
    (sine : 0 ≤ W.s) (order : W.s ≤ W.c)
    (wall : ∀ x y, W.Inside x y → x ≤ 2) (cut : centerY W ≤ 0)
    (marker : W.Inside (543/500) 0) (low : W.Inside 1 (-39/100))
    (high : W.Inside 1 (2/5)) (omitted : ¬ W.Inside 1 (-2/5))
    (foreign : ¬ W.Inside (7/20) (7/20)) : False := by
  classical
  have unit := W.unit_normal
  have upper : W.c ≤ 1 := by nlinarith only [unit,sq_nonneg W.s,cosine]
  have sumpos : 0 < W.c+W.s := by linarith only [cosine,sine]
  have exit : W.c-(2/5)*W.s ≤ W.loU := by
    by_contra absent
    have lowerU : W.loU < W.c-(2/5)*W.s := lt_of_not_ge absent
    have lowerV : -W.s-(2/5)*W.c ≤ W.loV := by
      apply le_of_not_gt
      intro h
      apply omitted
      exact ⟨by linarith only [lowerU],by linarith only [low.2.1,sine],
        by linarith only [h],by linarith only [low.2.2.2,cosine]⟩
    have markerLower : (7/20)*(W.c+W.s) ≤ W.loU := by
      apply le_of_not_gt
      intro h
      have vUpper : W.loV+W.side ≤ -(7/20)*W.s+(7/20)*W.c := by
        apply le_of_not_gt
        intro h'
        apply foreign
        exact ⟨by linarith only [h],by linarith only [high.2.1,cosine,sine],
          by linarith only [marker.2.2.1,cosine,sine],by linarith only [h']⟩
      have chord := short_projections W (-13/20) (3/4) (by norm_num)
      linarith only [lowerV,vUpper,side,chord.2.2.2]
    have uWeight := mul_nonneg sine (sub_nonneg.mpr markerLower)
    have vWeight := mul_nonneg cosine.le (sub_nonneg.mpr lowerV)
    have yLower : W.side*(W.c+W.s)/2-2/5+(3/4)*W.s^2-
        (13/20)*W.c*W.s ≤ centerY W := by
      dsimp [centerY]
      nlinarith only [uWeight,vWeight,unit]
    have strict := mul_pos (sub_pos.mpr side) sumpos
    have radial : 1-W.s^2 ≤ W.c := by
      nlinarith only [unit,mul_nonneg cosine.le (sub_nonneg.mpr upper)]
    have cs := mul_nonneg sine (sub_nonneg.mpr upper)
    nlinarith only [yLower,strict,radial,cs,sq_nonneg (W.s-3/10),cut]
  have uWeight := mul_nonneg sine (sub_nonneg.mpr exit)
  have vWeight := mul_pos cosine (sub_pos.mpr high.2.2.2)
  have yStrict : (W.c-W.s)*((2/5)*(W.c+W.s)-W.side/2) < centerY W := by
    dsimp [centerY]
    nlinarith only [uWeight,vWeight]
  have strictOrder : 0 < W.c-W.s := by
    apply lt_of_le_of_ne (sub_nonneg.mpr order)
    intro zero
    rw [←zero,zero_mul] at yStrict
    linarith only [yStrict,cut]
  have largeSide : (4/5)*(W.c+W.s) < W.side := by
    have negative : (W.c-W.s)*((2/5)*(W.c+W.s)-W.side/2) <
        (W.c-W.s)*0 := by linarith only [yStrict,cut]
    have h := (mul_lt_mul_iff_right₀ strictOrder).mp negative
    linarith only [h]
  have cosineLarge : 4/5 < W.c := by
    apply lt_of_not_ge
    intro small
    have cSquare : W.c^2 ≤ 16/25 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr small)
        (show 0 ≤ 4/5+W.c by linarith only [cosine])]
    have sineLarge : 3/5 ≤ W.s := by nlinarith only [unit,cSquare,sine]
    have diffSquare : (W.c-W.s)^2 ≤ 1/25 := by
      have h := mul_nonneg
        (show 0 ≤ 1/5-(W.c-W.s) by linarith only [small,sineLarge])
        (show 0 ≤ 1/5+(W.c-W.s) by linarith only [order])
      nlinarith only [h]
    have sum : 7/5 ≤ W.c+W.s := by
      apply le_of_not_gt
      intro bad
      have h := mul_pos (sub_pos.mpr bad)
        (show 0 < 7/5+(W.c+W.s) by linarith only [sumpos])
      nlinarith only [h,unit,diffSquare]
    linarith only [sum,largeSide,cap]
  have wallBound := square_support_bound W 1 0 2
    (by intro x y h; simpa only [one_mul,zero_mul,add_zero] using wall x y h)
  have wallCenter : centerX W+W.side*(W.c+W.s)/2 ≤ 2 := by
    simp only [squareRadius,one_mul,zero_mul,add_zero,neg_mul,abs_neg,
      abs_of_pos cosine,abs_of_nonneg sine] at wallBound
    nlinarith only [wallBound]
  have ownCenter := (center_coordinates W).1
  have wallScaled := mul_le_mul_of_nonneg_left wallCenter cosine.le
  have cutScaled := mul_nonpos_of_nonneg_of_nonpos sine cut
  have necessary : W.side*(1+W.c^2+W.c*W.s) ≤ 2*W.c+(4/5)*W.s := by
    nlinarith only [exit,ownCenter,wallScaled,cutScaled]
  have positive : 0 < 1+W.c^2+W.c*W.s := by
    nlinarith only [sq_nonneg W.c,mul_nonneg cosine.le sine]
  have strict := mul_pos (sub_pos.mpr side) positive
  have margin := mul_nonneg sine (sub_nonneg.mpr cosineLarge.le)
  nlinarith only [necessary,strict,margin,sq_nonneg (1-W.c)]

/-- Complete canonical conclusion for the actual wide wall. In particular
the diagonal frame and the zero angle are both excluded by strict anchors. -/
theorem canonical_profile (W : OpenSquare) (side : 1 < W.side)
    (cap : W.side ≤ 1001/1000) (cosine : 0 < W.c) (range : |W.s| ≤ W.c)
    (wall : ∀ x y, W.Inside x y → x ≤ 2) (cut : centerY W ≤ 0)
    (marker : W.Inside (543/500) 0) (low : W.Inside 1 (-39/100))
    (high : W.Inside 1 (2/5)) (omitted : ¬ W.Inside 1 (-2/5))
    (foreign : ¬ W.Inside (7/20) (7/20)) :
    W.s < 0 ∧ -W.s < W.c ∧ 5/4 < W.c-W.s ∧
      (7/20)*(W.c+W.s) ≤ W.loU ∧
      -W.s-(2/5)*W.c ≤ W.loV ∧ W.loU < W.c+(2/5)*W.s := by
  classical
  have sine : W.s < 0 := by
    apply lt_of_not_ge
    intro sign
    exact positive_impossible W side cap cosine sign (abs_le.mp range).2
      wall cut marker low high omitted foreign
  have order : -W.s ≤ W.c := by linarith only [(abs_le.mp range).1]
  have lowerU : (7/20)*(W.c+W.s) ≤ W.loU := by
    apply le_of_not_gt
    intro h
    apply foreign
    exact ⟨by linarith only [h],by linarith only [high.2.1,cosine,order],
      by linarith only [low.2.2.1,cosine,order],
      by linarith only [high.2.2.2,cosine,sine]⟩
  have lowerV : -W.s-(2/5)*W.c ≤ W.loV := by
    apply le_of_not_gt
    intro h
    have chord := short_projections W (13/20) (-3/4) (by norm_num)
    apply omitted
    exact ⟨by linarith only [high.1,sine],
      by linarith only [lowerU,side,chord.2.1],
      by linarith only [h],by linarith only [low.2.2.2,cosine]⟩
  have uWeight := mul_pos (show 0 < -W.s by linarith only [sine])
    (sub_pos.mpr high.1)
  have vWeight := mul_nonneg cosine.le (sub_nonneg.mpr lowerV)
  have yStrict : (W.c+W.s)*(W.side/2-(2/5)*(W.c-W.s)) < centerY W := by
    dsimp [centerY]
    nlinarith only [uWeight,vWeight]
  have strictOrder : 0 < W.c+W.s := by
    apply lt_of_le_of_ne (by linarith only [order])
    intro zero
    rw [←zero,zero_mul] at yStrict
    linarith only [yStrict,cut]
  have angle : 5/4 < W.c-W.s := by
    have negative : (W.c+W.s)*(W.side/2-(2/5)*(W.c-W.s)) < (W.c+W.s)*0 := by
      linarith only [yStrict,cut]
    have h := (mul_lt_mul_iff_right₀ strictOrder).mp negative
    linarith only [h,side]
  exact ⟨sine,by linarith only [strictOrder],angle,lowerU,lowerV,
    by nlinarith only [high.1]⟩

#print axioms canonical_profile
end N12Compact.C1092MixedWideWall
