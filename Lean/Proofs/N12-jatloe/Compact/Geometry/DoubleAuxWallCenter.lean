import Compact.Geometry.DoubleAuxWallCoupling
import Compact.Geometry.CentralWallCenter

/-! A complete elbow-center theorem when one wall owns both auxiliary
heights. The outer auxiliary exclusion is used through the actual wall
square, not through a false uniform stronger-point assertion. -/
namespace N12Compact.DoubleAuxWallCenter
open S12 S12Pilot FourSquareAnchors
open CentralWallEscape CentralWallPairAxes
set_option Elab.async false

theorem moderate_crossing (A : OpenSquare) (ha : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (moderate : A.c ≤ 4*A.s)
    (z : ℝ) (hz : 0 ≤ z) (angle : (1+A.c)*z=A.s)
    (unitAngle : A.s*z=1-A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingTop : ¬ A.Inside (12/5) 3)
    (missingCenter : ¬ A.Inside 2 2) : A.Inside 3 (2+z) := by
  have centerUhi : A.c*2+A.s*2 < A.loU+A.side := by
    linarith only [m.2.1,hc,hs]
  have centerVlo : A.loV < -A.s*2+A.c*2 := by
    linarith only [q.2.2.1,hs]
  have centerVhi : -A.s*2+A.c*2 < A.loV+A.side := by
    linarith only [p.2.2.2,hc]
  have centerU : A.c*2+A.s*2 ≤ A.loU :=
    le_of_not_gt (fun h => missingCenter ⟨h,centerUhi,centerVlo,centerVhi⟩)
  have sum : (7/10)*(A.c+A.s) ≤ 1 := by
    nlinarith only [A.unit_normal,sq_nonneg (A.c-A.s),
      sq_nonneg ((7/10)*(A.c+A.s)-1)]
  have topUlo : A.loU < A.c*(12/5)+A.s*3 := by
    linarith only [m.1,hc,hs]
  have topUhi : A.c*(12/5)+A.s*3 < A.loU+A.side := by
    linarith only [centerU,sum,order,ha]
  have topVlo : A.loV < -A.s*(12/5)+A.c*3 := by
    linarith only [q.2.2.1,hc,order]
  have topV : A.loV+A.side ≤ -A.s*(12/5)+A.c*3 :=
    le_of_not_gt (fun h => missingTop ⟨topUlo,topUhi,topVlo,h⟩)
  have angular : 3/5 ≤ (2/5)*A.c+A.s := by
    have product := mul_nonneg (sub_nonneg.mpr moderate)
      (show 0 ≤ 4*A.s+6*A.c by linarith only [hc,hs])
    have nonnegative : 0 ≤ (2/5)*A.c+A.s := by linarith only [hc,hs]
    nlinarith only [product,A.unit_normal,sq_nonneg A.c,
      sq_nonneg ((2/5)*A.c+A.s-3/5),nonnegative]
  have margin : (3/5)*A.s ≤ z*(A.c+A.s) := by
    have product := mul_nonneg hz (sub_nonneg.mpr angular)
    nlinarith only [product,angle]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [q.1,hc,mul_nonneg hs hz]
  · nlinarith only [centerU,unitAngle,ha]
  · nlinarith only [topV,unitAngle,margin,ha]
  · have cz : A.c*z ≤ A.s := by nlinarith only [angle,hz]
    nlinarith only [p.2.2.2,cz,hs,hc]

/-- This orientation branch includes every positive shallow central
frame. The top square carries the double auxiliary ownership. -/
theorem shallow_point (A R T : OpenSquare) (ha : 1 < A.side)
    (sameR : A.side=R.side) (sameT : A.side=T.side)
    (boxR : InsideContainer R) (boxT : InsideContainer T)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (12/5))
    (tMarker : T.Inside 2 (1543/500)) (tHigh : T.Inside (12/5) 3)
    (tLow : T.Inside (87/50) 3) (tMissingLow : ¬ T.Inside (8/5) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y)) : A.Inside 2 2 := by
  by_contra missing
  have missingR : ¬ A.Inside 3 (12/5) := fun h => ar _ _ ⟨h,rHigh⟩
  have missingTop : ¬ A.Inside (12/5) 3 := fun h => apartTop _ _ ⟨h,tHigh⟩
  by_cases narrow : 4*A.s ≤ A.c
  · have faces := central_lower_faces A hc hs (by linarith only [narrow,hc])
      p q m missing missingG
    have strong := DoubleAuxWallCoupling.missing_strong A T ha sameT boxT hc hs narrow
      p m faces.1 tMarker tHigh tLow tMissingLow apartTop
    exact missing (CentralWallCenter.shallow A R ha sameR boxR hc hs order p q m
      missingG missingB missingR missingTop strong rMarker rHigh ar)
  · by_cases steep : (16/25)*A.c ≤ A.s
    · exact missing (CentralEscapeSegment.shallow_center A R ha hc hs order steep
        p q m missingTop rMarker rHigh ar)
    · have sector : A.s ≤ (16/25)*A.c := (lt_of_not_ge steep).le
      let z := A.s/(1+A.c)
      have denominator : 0 < 1+A.c := by linarith only [hc]
      have hz : 0 ≤ z := div_nonneg hs denominator.le
      have angle : (1+A.c)*z=A.s := by dsimp [z]; field_simp [ne_of_gt denominator]
      have unitAngle : A.s*z=1-A.c := by
        dsimp [z]
        field_simp [ne_of_gt denominator]
        nlinarith only [A.unit_normal]
      have crossing := moderate_crossing A ha hc hs order (lt_of_not_ge narrow).le
        z hz angle unitAngle p q m missingTop missing
      exact missing (CentralWallCenter.center_of_crossing A R ha sameR boxR hc hs sector
        p q m missingG missingB missingR missingTop rMarker rHigh ar z hz angle unitAngle crossing)

/-- Whole all-angle statement: the right wall owns the lower auxiliary
point, but excludes the still-lower point. The top wall retains the
ordinary lower auxiliary exclusion. -/
theorem point (A R T : OpenSquare) (ha : 1 < A.side)
    (sameR : A.side=R.side) (sameT : A.side=T.side)
    (boxR : InsideContainer R) (boxT : InsideContainer T)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (12/5))
    (rLow : R.Inside 3 (87/50)) (rMissingLow : ¬ R.Inside 3 (8/5))
    (tMarker : T.Inside 2 (1543/500)) (tHigh : T.Inside (12/5) 3)
    (tMissing : ¬ T.Inside (87/50) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y)) : A.Inside 2 2 := by
  have tStrong : T.Inside (5/2) 3 := by
    have h := CentralWallCenter.right_high (pullSwap T) (by simpa only [sameT,pullSwap] using ha)
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
  · exact (inside _ _).mp (CentralWallCenter.shallow a R ha' sameR' boxR hc hs order p' q' m'
      g' b' r' t' (fun h => at' _ _ ⟨h,tStrong⟩) rMarker rHigh ar')
  · have center := shallow_point (pullSwap a) (pullSwap T) (pullSwap R) ha' sameT' sameR'
      (container_pullSwap T boxT) (container_pullSwap R boxR)
      (by dsimp [pullSwap]; linarith only [hc,lt_of_not_ge order]) hc.le
      (by dsimp [pullSwap]; exact (lt_of_not_ge order).le)
      ((inside_pullSwap a _ _).mpr q') ((inside_pullSwap a _ _).mpr p')
      ((inside_pullSwap a _ _).mpr m')
      (fun h => b' ((inside_pullSwap a _ _).mp h))
      (fun h => g' ((inside_pullSwap a _ _).mp h))
      ((inside_pullSwap T _ _).mpr tMarker) ((inside_pullSwap T _ _).mpr tHigh)
      ((inside_pullSwap R _ _).mpr rMarker) ((inside_pullSwap R _ _).mpr rHigh)
      ((inside_pullSwap R _ _).mpr rLow)
      (fun h => rMissingLow ((inside_pullSwap R _ _).mp h))
      (fun x y h => at' y x ⟨(inside_pullSwap a x y).mp h.1,
        (inside_pullSwap T x y).mp h.2⟩)
      (fun x y h => ar' y x ⟨(inside_pullSwap a x y).mp h.1,
        (inside_pullSwap R x y).mp h.2⟩)
    exact (inside _ _).mp ((inside_pullSwap a _ _).mp center)

#print axioms point
end N12Compact.DoubleAuxWallCenter
