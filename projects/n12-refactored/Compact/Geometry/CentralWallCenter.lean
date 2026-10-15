import Compact.Geometry.CentralWallPairSupport
import Compact.Geometry.CentralOuterReach
import Compact.Geometry.WallLowerReach
import S12.TransformFacts

/-! An elbow between two actual neighboring wall squares contains the
container center. Both full-square longitudinal separators are excluded,
and the argument is transported across the central square's two angle
sectors. Original wall exclusions supply the stronger outer points. -/
namespace N12Compact.CentralWallCenter
open S12 S12Pilot FourSquareAnchors
open CentralWallEscape CentralWallPairAxes CentralWallPairSupport
set_option Elab.async false

/-- Shared full-square endgame after a strict half-angle crossing has
been established. The crossing remains a point of the actual square. -/
theorem center_of_crossing (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side) (box : InsideContainer R)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (sector : A.s ≤ (16/25)*A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (missingR : ¬ A.Inside 3 (12/5))
    (missingTop : ¬ A.Inside (12/5) 3)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (z : ℝ) (hz : 0 ≤ z) (angle : (1+A.c)*z=A.s)
    (unitAngle : A.s*z=1-A.c) (crossing : A.Inside 3 (2+z)) : A.Inside 2 2 := by
  by_contra missing
  have zhi : z < 2/5 := by
    have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
    by_contra failure
    have large : 2/5 ≤ z := le_of_not_gt failure
    have product := mul_nonneg hc.le (sub_nonneg.mpr large)
    nlinarith only [angle,sector,cu,large,product]
  obtain ⟨W,wc,ws,side,inside,_⟩ := ClosedFrames.positive_frame R
  have sameW : A.side=W.side := same.trans side.symm
  have wb : InsideContainer W := fun x y h => box x y ((inside x y).mp h)
  have wm := (inside _ _).mpr marker
  have wh := (inside _ _).mpr high
  have disjoint : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(inside x y).mp h.2⟩
  have face := lower_face W wc ws z hz zhi wm wh
    (fun h => disjoint _ _ ⟨crossing,h⟩)
  have walls := wall_inequalities W (by simpa only [←sameW] using ha) wc ws wb z wm face
  have small := half_angle_lt W.c W.s z wc ws W.unit_normal hz walls.1 walls.2
  have narrow := slope_of_half_angle A.c A.s z hc hz angle unitAngle small
  have lower := central_lower_faces A hc hs narrow.le p q m missing missingG
  have outer := (CentralOuterReach.points A ha p q m missingG missingB missingR missingTop).1
  have turn := wall_angle_order A.c A.s W.c W.s z
    (cosine_bound A.c A.s hc hs A.unit_normal narrow.le) hs wc ws
    A.unit_normal W.unit_normal hz angle walls.2
  have cross : 0 ≤ A.c*W.s-A.s*W.c := sub_nonneg.mpr turn.le
  rcases alternatives A W ha sameW hc hs narrow.le wc ws q lower.2 wm wh
      z hz zhi crossing disjoint with axis | axis
  · exact central_axis_impossible A W ha sameW wb hc hs wc ws narrow.le cross lower.1 wm wh axis
  · exact wall_axis_impossible A W ha sameW wb hc hs wc ws narrow.le cross
      lower.1 lower.2 outer wm axis

theorem shallow (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side) (box : InsideContainer R)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (missingR : ¬ A.Inside 3 (12/5))
    (missingTop : ¬ A.Inside (12/5) 3)
    (missingTopStrong : ¬ A.Inside (5/2) 3)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : A.Inside 2 2 := by
  by_contra missing
  by_cases steep : (16/25)*A.c ≤ A.s
  · exact missing (CentralEscapeSegment.shallow_center A R ha hc hs order steep
      p q m missingTop marker high apart)
  have sector : A.s ≤ (16/25)*A.c := (lt_of_not_ge steep).le
  let z := A.s/(1+A.c)
  have denominator : 0 < 1+A.c := by linarith only [hc]
  have hz : 0 ≤ z := div_nonneg hs denominator.le
  have angle : (1+A.c)*z=A.s := by dsimp [z]; field_simp [ne_of_gt denominator]
  have unitAngle : A.s*z=1-A.c := by
    dsimp [z]
    field_simp [ne_of_gt denominator]
    nlinarith only [A.unit_normal]
  have crossing := crossing_point A ha hc hs sector z hz angle unitAngle
    p q m missingTopStrong missing
  exact missing (center_of_crossing A R ha same box hc hs sector p q m missingG
    missingB missingR missingTop marker high apart z hz angle unitAngle crossing)

theorem right_high (R : OpenSquare) (ha : 1 < R.side)
    (box : InsideContainer R) (marker : R.Inside (1543/500) 2)
    (high : R.Inside 3 (12/5)) (missing : ¬ R.Inside 3 (87/50))
    (inward : ¬ R.Inside (113/50) 2) : R.Inside 3 (5/2) := by
  have reach := WallLowerReach.point (pullX R) ha (container_pullX R box)
    ((inside_pullX R _ _).mpr (by convert marker using 1 <;> norm_num))
    ((inside_pullX R _ _).mpr (by convert high using 1 <;> norm_num))
    (fun h => missing (by convert (inside_pullX R _ _).mp h using 1 <;> norm_num))
    (fun h => inward (by convert (inside_pullX R _ _).mp h using 1 <;> norm_num))
  have point : R.Inside 3 (64/25) := by
    convert (inside_pullX R _ _).mp reach using 1 <;> norm_num
  convert inside_segment R 3 (12/5) 3 (64/25) (5/8)
    high point (by norm_num) (by norm_num) using 1 <;> norm_num

/-- All orientations of all three actual squares are included. The only
wall-point exclusions are the original lower auxiliary points; inward
exclusions follow from the central square's own compulsory points. -/
theorem point (A R T : OpenSquare) (ha : 1 < A.side)
    (sameR : A.side=R.side) (sameT : A.side=T.side)
    (boxR : InsideContainer R) (boxT : InsideContainer T)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (12/5))
    (rMissing : ¬ R.Inside 3 (87/50))
    (tMarker : T.Inside 2 (1543/500)) (tHigh : T.Inside (12/5) 3)
    (tMissing : ¬ T.Inside (87/50) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y)) : A.Inside 2 2 := by
  have rStrong := right_high R (by simpa only [sameR] using ha) boxR rMarker rHigh rMissing
    (fun h => ar _ _ ⟨q,h⟩)
  have tStrong : T.Inside (5/2) 3 := by
    have h := right_high (pullSwap T) (by simpa only [sameT] using ha)
      (container_pullSwap T boxT)
      ((inside_pullSwap T _ _).mpr tMarker) ((inside_pullSwap T _ _).mpr tHigh)
      (fun h => tMissing ((inside_pullSwap T _ _).mp h))
      (fun h => apartTop _ _ ⟨p,(inside_pullSwap T _ _).mp h⟩)
    exact (inside_pullSwap T _ _).mp h
  obtain ⟨a,hc,hs,side,inside,_⟩ := ClosedFrames.positive_frame A
  have ha' : 1 < a.side := by simpa only [side] using ha
  have sameR' : a.side=R.side := side.trans sameR
  have sameT' : a.side=T.side := side.trans sameT
  have p' := (inside _ _).mpr p
  have q' := (inside _ _).mpr q
  have m' := (inside _ _).mpr m
  have ar' : ∀ x y, ¬ (a.Inside x y ∧ R.Inside x y) :=
    fun x y h => ar x y ⟨(inside x y).mp h.1,h.2⟩
  have at' : ∀ x y, ¬ (a.Inside x y ∧ T.Inside x y) :=
    fun x y h => apartTop x y ⟨(inside x y).mp h.1,h.2⟩
  have g' : ¬ a.Inside (47/20) (33/20) := fun h => missingG ((inside _ _).mp h)
  have b' : ¬ a.Inside (33/20) (47/20) := fun h => missingB ((inside _ _).mp h)
  have r' : ¬ a.Inside 3 (12/5) := fun h => ar' _ _ ⟨h,rHigh⟩
  have t' : ¬ a.Inside (12/5) 3 := fun h => at' _ _ ⟨h,tHigh⟩
  by_cases order : a.s ≤ a.c
  · exact (inside _ _).mp (shallow a R ha' sameR' boxR hc hs order p' q' m'
      g' b' r' t' (fun h => at' _ _ ⟨h,tStrong⟩) rMarker rHigh ar')
  · have center := shallow (pullSwap a) (pullSwap T) ha' sameT'
      (container_pullSwap T boxT)
      (by dsimp [pullSwap]; linarith only [hc,lt_of_not_ge order]) hc.le
      (by dsimp [pullSwap]; exact (lt_of_not_ge order).le)
      ((inside_pullSwap a _ _).mpr q') ((inside_pullSwap a _ _).mpr p')
      ((inside_pullSwap a _ _).mpr m')
      (fun h => b' ((inside_pullSwap a _ _).mp h))
      (fun h => g' ((inside_pullSwap a _ _).mp h))
      (fun h => t' ((inside_pullSwap a _ _).mp h))
      (fun h => r' ((inside_pullSwap a _ _).mp h))
      (fun h => ar' _ _ ⟨(inside_pullSwap a _ _).mp h,rStrong⟩)
      ((inside_pullSwap T _ _).mpr tMarker) ((inside_pullSwap T _ _).mpr tHigh)
      (fun x y h => at' y x ⟨(inside_pullSwap a x y).mp h.1,
        (inside_pullSwap T x y).mp h.2⟩)
    exact (inside _ _).mp ((inside_pullSwap a _ _).mp center)

#print axioms point
end N12Compact.CentralWallCenter
